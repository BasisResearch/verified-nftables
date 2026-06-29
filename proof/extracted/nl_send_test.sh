#!/usr/bin/env bash
# nl_send_test.sh — round-trip the VERIFIED-compiled rules into a live kernel
# via Nl_send (real NETLINK_NETFILTER), then read them back with `nft`.
#
# Run it inside an unprivileged net+user namespace:
#   eval $(opam env --switch=vst)
#   cd .../proof/extracted
#   dune build ./nftc_cli.exe
#   unshare --net --map-root-user --map-auto bash nl_send_test.sh
#
# Exit 0 = the kernel accepted our bytes AND `nft list ruleset` shows the
# expected matches/verdicts.  Any other exit = honest failure (printed).

set -u
cd "$(dirname "$0")"
CLI=./_build/default/nftc_cli.exe
fail() { echo "FAIL: $*" >&2; exit 1; }

[ -x "$CLI" ] || fail "build $CLI first (dune build ./nftc_cli.exe)"

# 1. namespace setup: lo up, table + base chain pre-created with nft.
ip link set lo up 2>/dev/null || true
nft add table ip t                                                   || fail "nft add table"
nft add chain ip t c '{ type filter hook input priority 0; policy drop; }' \
                                                                     || fail "nft add chain"

# 2. the ruleset we compile + send (verified pipeline, --no-optimize for a
#    predictable 1:1 rule mapping).
RS=$(mktemp)
cat > "$RS" <<'EOF'
table ip t {
  chain c {
    type filter hook input priority 0; policy drop;
    tcp dport 22 accept
    ip saddr 10.0.0.1 drop
  }
}
EOF

echo "=== dry run (hexdump of the exact bytes) ==="
"$CLI" send --no-optimize --table t --chain c < "$RS" || fail "dry-run crashed"

echo
echo "=== commit (real netlink send) ==="
"$CLI" send --no-optimize --table t --chain c --commit < "$RS" \
    || fail "sender reported a kernel error (see above)"

# 3. read the rules back and assert.
echo
echo "=== nft list ruleset ==="
OUT=$(nft list ruleset) || fail "nft list ruleset"
echo "$OUT"

echo
echo "=== assertions ==="
echo "$OUT" | grep -Eq 'tcp dport 22 accept' \
    && echo "  ok: 'tcp dport 22 accept' present" \
    || fail "missing 'tcp dport 22 accept'"
echo "$OUT" | grep -Eq 'ip saddr 10\.0\.0\.1 drop' \
    && echo "  ok: 'ip saddr 10.0.0.1 drop' present" \
    || fail "missing 'ip saddr 10.0.0.1 drop'"

# 4. best-effort: nft's own --debug=netlink expression bytes for one rule, for
#    visual comparison against our encoding (informational, non-fatal).
echo
echo "=== best-effort: nft --debug=netlink for 'tcp dport 22 accept' ==="
nft add table ip t2 2>/dev/null || true
nft add chain ip t2 c2 2>/dev/null || true
nft --debug=netlink add rule ip t2 c2 tcp dport 22 accept 2>&1 | sed 's/^/  nft| /' || true

rm -f "$RS"
echo
echo "PASS: verified-compiled rules landed in the kernel via Nl_send"
