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

# ---------------------------------------------------------------------------
# 5. STANDALONE stand-up (no preparatory `nft`): one atomic batch that creates
#    the table + base/jump chains + a named set/vmap and the rules referencing
#    them, exercising the conntrack / counter / nat / meta-set / verdict-chain /
#    set-lookup / vmap encoders end-to-end.
# ---------------------------------------------------------------------------
nft flush ruleset 2>/dev/null || true
RS2=$(mktemp)
cat > "$RS2" <<'EOF'
table ip fw {
  chain c {
    type filter hook input priority 0; policy drop;
    ct state established,related accept
    ct mark set 0x1
    counter accept
    tcp dport { 22, 80, 443 } accept
    meta mark set 0x1
    iifname vmap { lo : accept, eth0 : jump sub }
  }
  chain sub { }
  chain post {
    type nat hook postrouting priority 100; policy accept;
    masquerade
  }
}
EOF
echo
echo "=== standalone send --commit (no prior nft add) ==="
"$CLI" send --no-optimize --commit < "$RS2" || fail "standalone send reported a kernel error"
OUT2=$(nft list ruleset) || fail "nft list ruleset (standalone)"
echo "$OUT2"
echo
echo "=== assertions (standalone) ==="
for pat in 'chain c' 'ct mark set' 'counter ' 'meta mark set' 'chain sub' 'masquerade' '@__set' '@__map'; do
  echo "$OUT2" | grep -Eq "$pat" \
    && echo "  ok: '$pat' present" \
    || fail "standalone: missing '$pat'"
done
rm -f "$RS2"

# ---------------------------------------------------------------------------
# 6. EXIT-CODE + ATOMICITY contract (CLI-2 / CLI-5): a committed batch the
#    kernel REJECTS must exit non-zero (5) AND leave the kernel unchanged
#    (all-or-nothing — the bad table must NOT appear).  Documented codes:
#      4 = encode failure (Unsupported)  5 = kernel rejected  6 = no ack.
# ---------------------------------------------------------------------------
nft flush ruleset 2>/dev/null || true
RS3=$(mktemp)
cat > "$RS3" <<'EOF'
table ip bad {
  chain c {
    type filter hook input priority 0; policy drop;
    meta protocol vmap { ip : jump ghost }
  }
}
EOF
echo
echo "=== negative: jump to an undeclared chain (expect reject + rollback) ==="
"$CLI" send --no-optimize --commit < "$RS3"; RC=$?
[ "$RC" -ne 0 ] \
  && echo "  ok: non-zero exit ($RC) on kernel reject" \
  || fail "committed an invalid batch but exited 0 (CLI-2 regression)"
if nft list table ip bad >/dev/null 2>&1; then
  fail "kernel left partially mutated: table 'bad' exists (CLI-5 atomicity regression)"
else
  echo "  ok: nothing committed — table 'bad' absent (atomic rollback)"
fi
rm -f "$RS3"

echo
echo "PASS: verified-compiled rules landed in the kernel via Nl_send"
