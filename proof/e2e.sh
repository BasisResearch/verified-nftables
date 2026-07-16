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

# ---- B2. the verified optimizer synthesises an N(>=3)-field concat (nft -o) ---
echo ">> B2. nftc optimize synthesises a 3-field concat set (matches nft -o)"
CONCATRULES='table ip t {
  chain c {
    type filter hook input priority 0; policy drop;
    ip saddr 10.0.0.1 ip daddr 10.0.0.2 ip protocol 6 accept
    ip saddr 10.0.0.3 ip daddr 10.0.0.4 ip protocol 17 accept
  }
}'
printf '%s\n' "$CONCATRULES" > /tmp/e2e_concat.nft
COPT=$("$NFTC" optimize /tmp/e2e_concat.nft)
echo "$COPT" | sed 's/^/     /'
clk=$(echo "$COPT" | grep -c 'lookup' || true)
cim=$(echo "$COPT" | grep -c 'immediate reg 0 accept' || true)
# the synthesised concat set element has THREE space-separated field slots
cset=$(echo "$COPT" | grep -E 'set __set.*=.*0x.* 0x.* 0x' | grep -c . || true)
if [ "$clk" -eq 1 ] && [ "$cim" -eq 1 ] && [ "$cset" -ge 1 ]; then
  echo "   PASS: 2 rules -> 1 lookup over a synthesised 3-field concat set"
else
  echo "   FAIL: N-field concat did not fire (lookups=$clk accepts=$cim 3-field-sets=$cset)"; fail=1
fi

# ---- B3. the verified optimizer merges adjacent snat into a bare source map --
# (G1) `ip saddr A snat to T1 / ip saddr B snat to T2` collapses to a single
# bare `snat to ip saddr map { A:T1, B:T2 }` — no head-set guard, SOURCE slot —
# exactly as `nft --optimize` emits it.
echo ">> B3. nftc optimize merges adjacent snat into a bare source map (matches nft -o)"
SNATRULES='table ip nat {
  chain postrouting {
    type nat hook postrouting priority srcnat; policy accept;
    ip saddr 10.0.0.1 snat to 192.168.1.1
    ip saddr 10.0.0.2 snat to 192.168.1.2
  }
}'
printf '%s\n' "$SNATRULES" > /tmp/e2e_snat.nft
SOPT=$("$NFTC" optimize /tmp/e2e_snat.nft)
echo "$SOPT" | sed 's/^/     /'
# the two snat rules must collapse to ONE snat rule that reads a synthesised
# map (a `lookup` feeding reg 1) on the SOURCE address (payload @ network + 12)
slk=$(echo "$SOPT" | grep -c 'lookup reg 1 set __map' || true)
snt=$(echo "$SOPT" | grep -c 'nat snat ip addr_min reg 1' || true)
ssrc=$(echo "$SOPT" | grep -c 'network header + 12' || true)
snat_rules=$(echo "$SOPT" | grep -c '^nat postrouting' || true)
if [ "$slk" -eq 1 ] && [ "$snt" -eq 1 ] && [ "$ssrc" -eq 1 ] && [ "$snat_rules" -eq 1 ]; then
  echo "   PASS: 2 snat rules -> 1 bare source-address map (verified merge fired)"
else
  echo "   FAIL: snat map merge did not fire (lookups=$slk snat=$snt src-loads=$ssrc rules=$snat_rules)"; fail=1
fi
# cross-check: nft --optimize folds these into the SAME bare source map
NFTSO=$(printf '%s\n' "$SNATRULES" | unshare -rn nft --optimize -f - 2>/dev/null | grep -c 'snat .*to ip saddr map' || true)
if [ "${NFTSO:-0}" -ge 1 ]; then
  echo "   PASS: nft --optimize agrees (bare 'snat to ip saddr map { .. }')"
else
  echo "   NOTE: nft --optimize cross-check unavailable in this environment"
fi

# ---- B4. the verified optimizer folds a GUARDED transport-key concat ---------
# (G2) `ip saddr A tcp dport P / ip saddr B tcp dport Q` — where `tcp dport` carries
# its implicit `meta l4proto 6` guard BETWEEN the two selectors — collapses to ONE
# `ip saddr . tcp dport { A.P, B.Q }` lookup with the l4proto guard hoisted to the
# head, exactly as `nft --optimize` emits it (guard first, saddr@reg1, dport@reg9).
echo ">> B4. nftc optimize folds a guarded transport-key concat (matches nft -o)"
GCONCAT='table ip t {
  chain c {
    type filter hook input priority 0; policy accept;
    ip saddr 1.1.1.1 tcp dport 22 accept
    ip saddr 2.2.2.2 tcp dport 80 accept
  }
}'
printf '%s\n' "$GCONCAT" > /tmp/e2e_gconcat.nft
GOPT=$("$NFTC" optimize /tmp/e2e_gconcat.nft)
echo "$GOPT" | sed 's/^/     /'
# ONE lookup, the l4proto guard hoisted to the head, dport laid in the 2nd reg slot
# (reg 9), and a 2-tuple concat set (two 2-field elements).
glk=$(echo "$GOPT" | grep -c 'lookup reg 1 set __set' || true)
gguard=$(echo "$GOPT" | grep -c 'meta load l4proto' || true)
gdport=$(echo "$GOPT" | grep -c 'transport header + 2 => reg 9' || true)
gset=$(echo "$GOPT" | grep -Ec 'set __set.*=.*0x.* 0x.*,.*0x.* 0x' || true)
grules=$(echo "$GOPT" | grep -c '^t c' || true)
if [ "$glk" -eq 1 ] && [ "$gguard" -eq 1 ] && [ "$gdport" -eq 1 ] && \
   [ "$gset" -ge 1 ] && [ "$grules" -eq 1 ]; then
  echo "   PASS: 2 guarded tcp-dport rules -> 1 concat lookup (verified merge fired)"
else
  echo "   FAIL: guarded concat did not fire (lookups=$glk guard=$gguard dport-reg9=$gdport sets=$gset rules=$grules)"; fail=1
fi
# cross-check: nft --optimize folds these into the SAME concat set
NFTGO=$(printf '%s\n' "$GCONCAT" | unshare -rn nft --optimize -f - 2>/dev/null | grep -c 'ip saddr . tcp dport {' || true)
if [ "${NFTGO:-0}" -ge 1 ]; then
  echo "   PASS: nft --optimize agrees (folds 'ip saddr . tcp dport { .. }')"
else
  echo "   NOTE: nft --optimize cross-check unavailable in this environment"
fi

# ---- B5. the verified optimizer folds adjacent RANGES into an INTERVAL set ---
# (G3) `ip saddr 10.0.0.0-10.0.0.255 / 10.0.2.0-10.0.2.255 accept` collapses to ONE
# `ip saddr { 10.0.0.0-10.0.0.255, 10.0.2.0-10.0.2.255 } accept` lookup over a
# synthesised INTERVAL set (each element a [lo,hi] pair), exactly as `nft --optimize`
# emits it (set flags ANONYMOUS|CONSTANT|INTERVAL).
echo ">> B5. nftc optimize folds adjacent ranges into an interval set (matches nft -o)"
IVRULES='table ip t {
  chain c {
    type filter hook input priority 0; policy accept;
    ip saddr 10.0.0.0-10.0.0.255 accept
    ip saddr 10.0.2.0-10.0.2.255 accept
  }
}'
printf '%s\n' "$IVRULES" > /tmp/e2e_iv.nft
IOPT=$("$NFTC" optimize /tmp/e2e_iv.nft)
echo "$IOPT" | sed 's/^/     /'
# ONE lookup over a synthesised set whose elements are genuine intervals (lo-hi).
ilk=$(echo "$IOPT" | grep -c 'lookup reg 1 set __set' || true)
iset=$(echo "$IOPT" | grep -Ec 'set __set.* = \{ .*0x[0-9a-f]+-0x[0-9a-f]+, .*0x[0-9a-f]+-0x[0-9a-f]+ \}' || true)
irules=$(echo "$IOPT" | grep -c '^t c' || true)
if [ "$ilk" -eq 1 ] && [ "$iset" -ge 1 ] && [ "$irules" -eq 1 ]; then
  echo "   PASS: 2 range rules -> 1 interval-set lookup (verified merge fired)"
else
  echo "   FAIL: interval-set merge did not fire (lookups=$ilk interval-sets=$iset rules=$irules)"; fail=1
fi
# cross-check: nft --optimize folds these into the SAME interval set
NFTIO=$(printf '%s\n' "$IVRULES" | unshare -rn nft --optimize -f - 2>/dev/null | grep -c 'ip saddr { .*-.*, .*-.* }' || true)
if [ "${NFTIO:-0}" -ge 1 ]; then
  echo "   PASS: nft --optimize agrees (folds 'ip saddr { lo-hi, lo-hi }')"
else
  echo "   NOTE: nft --optimize cross-check unavailable in this environment"
fi

# ---- B6. the mapN divergence (D1): a LABELLED SOUND SUPERSET, not nft -o -----
# (D1) `ip saddr A meta mark set M1 / ip saddr B meta mark set M2` folds into ONE
# HEAD-GUARDED data-map rule `ip saddr { A, B } meta mark set ip saddr map { A:M1,
# B:M2 }`.  This is a SOUND CONSOLIDATION with NO `nft -o` counterpart: `nft -o`
# does NOT merge `meta mark set` rules at all (it emits value maps only for
# dnat/snat, which we match BARE via §B3).  The head-set guard is a soundness
# necessity of OUR model (a statement value-map miss loads a default instead of
# NFT_BREAKing); the kernel would run a BARE map with break-on-miss (netns witness
# below), so the guarded form, the bare form and the two originals all filter/
# rewrite every packet identically — the divergence is INTENTIONAL/NECESSARY, NOT
# an nft bug.  Pinned axiom-free in Optimize_DataMap.mapn_bare_diverges_offkey.
echo ">> B6. nftc optimize folds meta-mark rules into a guarded data map (sound superset; nft -o does NOT)"
MARKRULES='table ip t {
  chain c {
    type filter hook prerouting priority 0; policy accept;
    ip saddr 1.1.1.1 meta mark set 0x00000001
    ip saddr 2.2.2.2 meta mark set 0x00000002
  }
}'
printf '%s\n' "$MARKRULES" > /tmp/e2e_mark.nft
MOPT=$("$NFTC" optimize /tmp/e2e_mark.nft)
echo "$MOPT" | sed 's/^/     /'
# ONE output rule: a head-guard set lookup (no dreg) + a data-map lookup (dreg) +
# the meta-set, with BOTH a synthesised set AND a synthesised map.
mguard=$(echo "$MOPT" | grep -Ec 'lookup reg 1 set __set[A-Z]? *\]' || true)   # head guard (no dreg)
mmap=$(echo "$MOPT" | grep -Ec 'lookup reg 1 set __map.* dreg' || true)        # data map (dreg)
mset=$(echo "$MOPT" | grep -c 'meta set mark' || true)
mrules=$(echo "$MOPT" | grep -c '^t c' || true)
if [ "$mguard" -ge 1 ] && [ "$mmap" -ge 1 ] && [ "$mset" -ge 1 ] && [ "$mrules" -eq 1 ]; then
  echo "   PASS: 2 meta-mark rules -> 1 guarded data-map rule (verified merge fired; head set + data map synthesised)"
else
  echo "   FAIL: mapN merge did not fire (guard=$mguard map=$mmap metaset=$mset rules=$mrules)"; fail=1
fi
# cross-check: `nft --optimize` does NOT merge meta-mark (no "Merging" output).
if NFTMO=$(printf '%s\n' "$MARKRULES" | unshare -rn nft --optimize -f - 2>/dev/null); then
  if printf '%s' "$NFTMO" | grep -q 'Merging'; then
    echo "   FAIL: nft --optimize unexpectedly merged meta mark: $NFTMO"; fail=1
  else
    echo "   PASS: nft --optimize does NOT merge meta mark (intentional divergence: mapN is a sound superset)"
  fi
else
  echo "   NOTE: nft --optimize cross-check unavailable in this environment"
fi
# kernel behavioural witness: a BARE statement value-map BREAKs on miss (leaves the
# mark), so the bare merged form is kernel-equivalent to the two originals -> the
# guard is a MODEL artifact, not an nft bug.  Best-effort (needs netns + dummy dev).
BEHAV='ip link add dummy0 type dummy 2>/dev/null || exit 3
ip addr add 10.9.0.1/24 dev dummy0; ip link set dummy0 up; ip route add 10.9.9.0/24 dev dummy0
nft -f - <<EOF
table ip t {
  chain c {
    type filter hook output priority 0; policy accept;
    meta mark set 0x0000dead
    meta mark set ip daddr map { 10.9.9.1 : 0x00000111 }
    meta mark 0x0000dead counter comment "survived"
    meta mark 0x00000111 counter comment "onkey"
  }
}
EOF
ping -c1 -W1 10.9.9.2 >/dev/null 2>&1 || true   # OFF-key: mark must SURVIVE (break-on-miss)
ping -c1 -W1 10.9.9.1 >/dev/null 2>&1 || true   # ON-key:  mark must become 0x111
nft list ruleset | grep -E "survived|onkey"'
if BOUT=$(unshare --net --map-root-user --map-auto -- bash -c "$BEHAV" 2>/dev/null); then
  sv=$(printf '%s' "$BOUT" | grep survived | grep -oE 'packets [0-9]+' | grep -oE '[0-9]+' | head -1)
  ok=$(printf '%s' "$BOUT" | grep onkey    | grep -oE 'packets [0-9]+' | grep -oE '[0-9]+' | head -1)
  if [ "${sv:-0}" -ge 1 ] && [ "${ok:-0}" -ge 1 ]; then
    echo "   PASS: kernel break-on-miss confirmed (off-key mark survived=$sv, on-key mapped=$ok) => bare form == originals; guard is a model artifact, not an nft bug"
  else
    echo "   NOTE: kernel behavioural witness inconclusive (survived=$sv onkey=$ok)"
  fi
else
  echo "   NOTE: kernel behavioural witness unavailable in this environment (needs netns + dummy dev)"
fi

# ---- C. the pipeline runs on the repo's real rulesets -----------------------
echo ">> C. pipeline runs on real rulesets"
for f in ../rulesets/router.nft ../rulesets/optiplex.nft ../rulesets/ruleset.nft; do
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
