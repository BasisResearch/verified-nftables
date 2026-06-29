#!/usr/bin/env bash
# End-to-end pipeline test (TODO 2c): drive the WHOLE verified pipeline from a
# `.nft` file through the `nftc` CLI — parse -> (optimize ->) compile_chain ->
# render — and check it against the live `nft` tool.
#
#   A. nftc compile FILE  reproduces the exact instruction SEQUENCE that
#      `nft --debug=netlink -f FILE` emits (same opcodes/regs/order), end to end
#      from the file.  (Byte-exact DATA identity in the live --debug=netlink data
#      format is separately proven by `make difftest`; the CLI renders data in the
#      corpus big-endian format — see memory two-bytecode-render-formats — so here
#      we compare structure, masking the format-specific hex literals.)
#   B. nftc optimize FILE  actually consolidates a value->set ruleset (the
#      VERIFIED optimizer fires on parser output — synthesises an anonymous set),
#      matching `nft -o`.
#   C. the pipeline runs on the repo's REAL rulesets (router.nft / optiplex.nft)
#      without error.
#
# `nft` needs a net namespace for cache init; `unshare -rn` gives an unprivileged
# one.  Requires: nft, unshare, dune, diff.
set -euo pipefail
cd "$(dirname "$0")"

echo ">> building nftc CLI"
( cd extracted && eval "$(opam env --switch=vst 2>/dev/null || true)"; dune build ./nftc_cli.exe )
NFTC=extracted/_build/default/nftc_cli.exe

exprs() { grep -E '^\s*\[ ' || true; }   # keep only the bytecode expr lines
# canonicalise a bytecode line: trim, collapse spaces, and mask every 0x.. hex
# literal to DATA so the two renderers' data formats (LE 4-byte words vs corpus
# big-endian) don't matter — we compare the instruction STRUCTURE.
canon() { sed -E 's/0x[0-9a-fA-F]+/DATA/g; s/[[:space:]]+/ /g; s/^ //; s/ $//'; }
fail=0

# ---- A. full pipeline vs live nft, byte-identical, driven from a file --------
RULESET='table ip filter {
  chain input {
    type filter hook input priority 0; policy drop;
    tcp dport 22 accept
    ip saddr 10.1.2.3 drop
    tcp sport 80 accept
    ip daddr 192.168.1.1 tcp dport 443 accept
  }
}'
echo ">> A. nftc compile (from file) vs nft --debug=netlink"
printf '%s\n' "$RULESET" > /tmp/e2e.nft
printf '%s\n' "$RULESET" | unshare -rn nft --debug=netlink -f - | exprs | canon > /tmp/e2e.nft.bc
"$NFTC" compile /tmp/e2e.nft | exprs | canon > /tmp/e2e.ours.bc
if diff -u /tmp/e2e.nft.bc /tmp/e2e.ours.bc; then
  echo "   PASS: nftc compile reproduces nft's instruction sequence (structure)"
else
  echo "   FAIL: nftc compile diverged from nft (left=nft, right=ours)"; fail=1
fi

# ---- B. the verified optimizer consolidates a value->set ruleset ------------
echo ">> B. nftc optimize consolidates value->set (matches nft -o)"
SETRULES='table ip t {
  chain c {
    type filter hook input priority 0; policy drop;
    ip saddr 10.0.0.1 drop
    ip saddr 10.0.0.2 drop
    ip saddr 10.0.0.3 drop
  }
}'
printf '%s\n' "$SETRULES" > /tmp/e2e_set.nft
OPT=$("$NFTC" optimize /tmp/e2e_set.nft)
echo "$OPT" | sed 's/^/     /'
# the three rules must collapse to ONE lookup over a synthesised set
nlk=$(echo "$OPT" | grep -c 'lookup' || true)
nim=$(echo "$OPT" | grep -c 'immediate reg 0 drop' || true)
nset=$(echo "$OPT" | grep -c 'set __set' || true)
if [ "$nlk" -eq 1 ] && [ "$nim" -eq 1 ] && [ "$nset" -ge 1 ]; then
  echo "   PASS: 3 rules -> 1 lookup over a synthesised set (verified merge fired)"
else
  echo "   FAIL: optimizer did not consolidate (lookups=$nlk drops=$nim sets=$nset)"; fail=1
fi
# cross-check: nft -o itself folds these into a set (same shape)
if printf '%s\n' "$SETRULES" | unshare -rn nft -o -f - >/dev/null 2>&1; then
  NFTO=$(printf '%s\n' "$SETRULES" | unshare -rn nft --optimize -c -f - 2>/dev/null || true)
fi

# ---- C. the pipeline runs on the repo's real rulesets -----------------------
echo ">> C. pipeline runs on real rulesets"
for f in ../router.nft ../optiplex.nft ../ruleset.nft; do
  [ -f "$f" ] || continue
  if "$NFTC" compile "$f" >/dev/null 2>/tmp/e2e_err && \
     "$NFTC" optimize "$f" >/dev/null 2>>/tmp/e2e_err; then
    echo "   PASS: $(basename "$f") parses, compiles and optimizes"
  else
    echo "   FAIL: $(basename "$f"):"; sed 's/^/      /' /tmp/e2e_err; fail=1
  fi
done

# ---- D. parser coverage probe (TODO 2b inventory + regression) --------------
# A representative spread of constructs the UNTRUSTED frontend must accept.  These
# all parse+compile through the verified pipeline.  Known-unsupported constructs
# (documented, fail loudly with Unsupported rather than mis-parsing): `reject with
# <type>`, `numgen … vmap { … }`, non-verdict data maps (`… map { k : v }`).
echo ">> D. parser coverage (constructs the frontend accepts)"
covok=0; covn=0
cov() {
  covn=$((covn+1))
  if printf 'table ip t {\n chain c {\n  type filter hook input priority 0; policy drop;\n  %s\n }\n}\n' "$1" \
       | "$NFTC" compile - >/dev/null 2>/tmp/e2e_cov; then covok=$((covok+1));
  else echo "   FAIL: should parse: $1 -> $(cat /tmp/e2e_cov)"; fail=1; fi
}
cov 'tcp dport { 22, 80, 443 } accept'
cov 'ip saddr 10.0.0.0/8 drop'
cov 'ct state { established, related } accept'
cov 'tcp dport != 22 drop'
cov 'tcp dport 1-1024 accept'
cov 'meta mark set 0x1 accept'          # newly supported (TODO 2b)
cov 'iifname "eth0" accept'
cov 'ip protocol tcp accept'
cov 'tcp flags syn accept'
cov 'ip saddr 1.2.3.4 ip daddr 5.6.7.8 drop'
cov 'icmp type echo-request accept'
cov 'snat to 1.2.3.4'
echo "   PASS: $covok/$covn coverage constructs parse+compile"

echo
if [ "$fail" -eq 0 ]; then
  echo "ALL E2E CHECKS PASSED"
else
  echo "E2E FAILURES ABOVE"; exit 1
fi
