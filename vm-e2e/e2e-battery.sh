#!/usr/bin/env bash
# e2e-battery.sh — the WHOLE nftc CLI, end to end, against this VM's REAL kernel.
#
# Runs INSIDE the booted mkosi VM (packaged Arch kernel + nftables + conntrack),
# driven by vm-e2e/vmtest.sh over `mkosi ssh`.  Baked into the image at
# /root/e2e/run.sh with the rulesets under /root/e2e/rules/ and the host-built
# verified CLI at /usr/local/bin/nftc.
#
# For a battery of rulesets it exercises `nftc compile`, `nftc optimize` and
# `nftc send --commit`, then confirms the kernel ACCEPTED the batch by reading
# it back with `nft list ruleset`; for a few rules it also confirms real packets
# MATCH (runtime counters).  It also probes the CLI's own robustness (bad input,
# missing/empty file, unsupported construct, --help, stdin, wrong flags) and the
# exit-code / atomicity contract.  Exit 0 iff every check passed.
set -u
NFTC=${NFTC:-nftc}
RULES=${RULES_DIR:-/root/e2e/rules}
pass=0 fail=0
ok()  { echo "  ok:   $*"; pass=$((pass+1)); }
bad() { echo "  FAIL: $*"; fail=$((fail+1)); }
sec() { echo; echo "== $* =="; }
flush() { nft flush ruleset 2>/dev/null || true; nft list ruleset 2>/dev/null | grep -q . && nft delete table >/dev/null 2>&1; nft flush ruleset 2>/dev/null || true; }

# run a command, capture exit code into $RC and output into $OUT
run() { OUT=$("$@" 2>&1); RC=$?; }

sec "VM sanity"
echo "  kernel: $(uname -r)   nft: $(nft --version)   conntrack: $(conntrack --version 2>&1|head -1)"
ip link set lo up 2>/dev/null || true

# ---------------------------------------------------------------------------
# 1. Hand-written feature rulesets: compile + optimize + send --commit + readback
#    Each entry: file | one|-separated grep -E patterns that MUST appear in the
#    kernel's `nft list ruleset` after a committed send.
# ---------------------------------------------------------------------------
sec "feature rulesets: compile / optimize / send --commit / readback"
declare -a CASES=(
  "ctstate.nft|ct state established counter|ct state \{ established, related \}|ct state invalid drop"
  "namedset.nft|set badhosts|ip saddr @badhosts drop|tcp dport \{ 22, 80, 443 \}"
  "metamark.nft|meta mark set 0x00000099|meta mark 0x00000099 counter|iifname vmap \{"
  "concat.nft|ip protocol \. th dport|accept"
  "nat.nft|dnat to 192.168.51.186|snat to 203.0.113.1|masquerade"
  "counters.nft|iif \"lo\" counter|tcp dport 22 counter"
)
for entry in "${CASES[@]}"; do
  f="${entry%%|*}"; pats="${entry#*|}"
  path="$RULES/$f"
  echo "-- $f"
  [ -f "$path" ] || { bad "$f: missing ruleset file"; continue; }
  run "$NFTC" compile "$path"
  { [ $RC -eq 0 ] && [ -n "$OUT" ]; } && ok "$f: compile (exit 0, non-empty)" || bad "$f: compile rc=$RC"
  run "$NFTC" optimize "$path"
  [ $RC -eq 0 ] && ok "$f: optimize (exit 0)" || { bad "$f: optimize rc=$RC: $OUT"; }
  flush
  run "$NFTC" send --commit "$path"
  if [ $RC -ne 0 ]; then bad "$f: send --commit rc=$RC: $OUT"; continue; fi
  ok "$f: send --commit (kernel acked)"
  LR=$(nft list ruleset 2>&1)
  IFS='|' read -ra PS <<< "$pats"
  for p in "${PS[@]}"; do
    echo "$LR" | grep -Eq -- "$p" && ok "$f: readback matches /$p/" || { bad "$f: readback MISSING /$p/"; echo "$LR" | sed 's/^/       | /'; }
  done
done

# ---------------------------------------------------------------------------
# 2. Real repo rulesets: compile + optimize must succeed; send --commit is
#    best-effort (exit 0 = kernel accepted; exit 4 = an honest "cannot encode
#    for netlink" — acceptable; any crash / other code = a CLI bug).
# ---------------------------------------------------------------------------
sec "real repo rulesets: compile / optimize / send"
for f in router.nft ruleset.nft optiplex.nft; do
  path="$RULES/$f"
  echo "-- $f"
  [ -f "$path" ] || { bad "$f: missing"; continue; }
  run "$NFTC" compile "$path";  [ $RC -eq 0 ] && ok "$f: compile" || bad "$f: compile rc=$RC: $OUT"
  run "$NFTC" optimize "$path"; [ $RC -eq 0 ] && ok "$f: optimize" || bad "$f: optimize rc=$RC: $OUT"
  flush
  run "$NFTC" send --commit "$path"
  case $RC in
    0) ok "$f: send --commit (kernel accepted)";
       nft list ruleset 2>/dev/null | grep -q 'table ' && ok "$f: readback shows a table" || bad "$f: sent ok but no table in readback" ;;
    4) ok "$f: send declined cleanly (exit 4, unencodable construct) — honest failure" ;;
    *) bad "$f: send --commit unexpected rc=$RC: $OUT" ;;
  esac
done

# ---------------------------------------------------------------------------
# 3. Runtime packet match: a committed rule must actually COUNT live packets.
# ---------------------------------------------------------------------------
sec "runtime packet match (counters increment on real traffic)"
flush
run "$NFTC" send --commit "$RULES/counters.nft"
if [ $RC -eq 0 ]; then
  ok "counters.nft: send --commit"
  ping -c 3 -W 1 127.0.0.1 >/dev/null 2>&1 || true
  LR=$(nft list ruleset 2>&1)
  echo "$LR" | grep -E 'iif "lo" counter' | grep -Eq 'packets [1-9]' \
    && ok "iif lo counter incremented on loopback ping" \
    || { bad "iif lo counter stuck at 0 after loopback traffic"; echo "$LR" | grep counter | sed 's/^/       | /'; }
else
  bad "counters.nft: send --commit rc=$RC: $OUT"
fi

# ---------------------------------------------------------------------------
# 4. ct_state runtime match (wire byte-order trap): an established loopback
#    connection must be COUNTED by `ct state established`.
# ---------------------------------------------------------------------------
sec "ct state runtime match (established loopback connection)"
flush
run "$NFTC" send --commit "$RULES/ctstate.nft"
if [ $RC -eq 0 ]; then
  ok "ctstate.nft: send --commit"
  LR=$(nft list ruleset 2>&1)
  echo "$LR" | grep -Fq '0x2000000' && bad "big-endian 'ct state 0x2000000' artefact on the wire" || ok "no big-endian ct_state artefact"
  if ! command -v python3 >/dev/null 2>&1; then
    echo "  WARN: python3 unavailable — skipping the runtime ct_state match assertion"
  else
  python3 - <<'PY' 2>/dev/null || true
import socket,threading,time
def srv():
    s=socket.socket(); s.setsockopt(socket.SOL_SOCKET,socket.SO_REUSEADDR,1)
    s.bind(("127.0.0.1",54321)); s.listen(1)
    try:
        c,_=s.accept()
        for _ in range(10):
            d=c.recv(200)
            if not d: break
            try: c.sendall(b"pong"*20)
            except OSError: break
        c.close()
    except OSError: pass
    s.close()
threading.Thread(target=srv,daemon=True).start(); time.sleep(0.4)
try:
    c=socket.socket(); c.connect(("127.0.0.1",54321))
    for _ in range(8):
        try: c.sendall(b"ping"*20); c.recv(200); time.sleep(0.03)
        except OSError: break
    c.close()
except OSError: pass
time.sleep(0.4)
PY
  LR=$(nft list ruleset 2>&1)
  if echo "$LR" | grep -E 'ct state established counter' | grep -Eq 'packets [1-9]'; then
    ok "ct state established counter MATCHED live packets"
  else
    bad "ct state established matched ZERO packets (wire byte-order regression)"; echo "$LR" | grep -E 'ct state' | sed 's/^/       | /'
  fi
  fi
else
  bad "ctstate.nft: send --commit rc=$RC: $OUT"
fi

# ---------------------------------------------------------------------------
# 5. Exit-code + atomicity contract: a kernel-rejected batch (jump to an
#    undeclared chain) must exit non-zero AND leave the kernel unchanged.
# ---------------------------------------------------------------------------
sec "exit-code + atomicity (kernel reject rolls back)"
flush
cat > /tmp/bad.nft <<'EOF'
table ip bad {
  chain c {
    type filter hook input priority 0; policy drop;
    meta protocol vmap { ip : jump ghost }
  }
}
EOF
run "$NFTC" send --commit /tmp/bad.nft
[ $RC -ne 0 ] && ok "rejected batch exits non-zero (rc=$RC)" || bad "committed an invalid batch but exited 0"
nft list table ip bad >/dev/null 2>&1 && bad "kernel left partially mutated: table 'bad' present" || ok "atomic rollback: table 'bad' absent"

# ---------------------------------------------------------------------------
# 6. CLI robustness — bad/edge inputs must fail CLEANLY (no stack trace,
#    correct exit codes), and --help/stdin must work.
# ---------------------------------------------------------------------------
sec "CLI robustness (clean errors, correct exit codes)"
robust() { # desc | expected_rc | must-not-contain-substring-of-stack-trace
  local desc="$1"; shift; local want="$1"; shift
  run "$@"
  local trace=0; echo "$OUT" | grep -Eq 'Fatal error|Stack overflow|Stdlib\.|exception ' && trace=1
  if [ "$want" = "0" ]; then
    { [ $RC -eq 0 ] && [ $trace -eq 0 ]; } && ok "$desc (exit 0, no trace)" || bad "$desc rc=$RC trace=$trace: $OUT"
  else
    { [ $RC -eq "$want" ] && [ $trace -eq 0 ]; } && ok "$desc (exit $RC, clean)" || bad "$desc want-rc=$want got-rc=$RC trace=$trace: $OUT"
  fi
}
: > /tmp/empty.nft
printf 'garbage @@@ not nft\n' > /tmp/garbage.nft
printf 'table ip t {\n chain c {\n  type filter hook input priority 0; policy drop;\n  reject with icmp type host-unreachable\n }\n}\n' > /tmp/uns.nft
robust "no arguments -> usage"              2 "$NFTC"
robust "unknown subcommand -> usage"        2 "$NFTC" frobnicate /tmp/empty.nft
robust "unknown flag -> usage"              2 "$NFTC" compile --bogus /tmp/empty.nft
robust "two positional files -> usage"      2 "$NFTC" compile /tmp/empty.nft /tmp/empty.nft
robust "missing file -> clean error"        1 "$NFTC" compile /tmp/does-not-exist.nft
robust "directory as file -> clean error"   1 "$NFTC" compile /tmp
robust "empty file -> clean error"          1 "$NFTC" compile /tmp/empty.nft
robust "garbage -> clean parse error"       1 "$NFTC" compile /tmp/garbage.nft
robust "unsupported construct -> clean"     1 "$NFTC" compile /tmp/uns.nft
robust "--help -> exit 0"                    0 "$NFTC" --help
robust "-h -> exit 0"                        0 "$NFTC" -h
# stdin ('-'): a valid ruleset on stdin compiles to non-empty bytecode, exit 0.
OUT=$(printf 'table ip t {\n chain c {\n  type filter hook input priority 0; policy drop;\n  tcp dport 22 accept\n }\n}\n' | "$NFTC" compile - 2>&1); RC=$?
{ [ $RC -eq 0 ] && echo "$OUT" | grep -q 'immediate reg 0 accept'; } && ok "stdin '-' compiles (exit 0)" || bad "stdin '-' rc=$RC: $OUT"
# send dry-run (no --commit) must NOT mutate the kernel.
flush
printf 'table ip dry {\n chain c {\n  type filter hook input priority 0; policy drop;\n  tcp dport 22 accept\n }\n}\n' | "$NFTC" send - >/dev/null 2>&1
nft list table ip dry >/dev/null 2>&1 && bad "send dry-run mutated the kernel (table 'dry' present)" || ok "send dry-run left kernel untouched"

flush
sec "RESULT"
echo "  passed: $pass   failed: $fail"
[ $fail -eq 0 ] && { echo "E2E-BATTERY: PASS"; exit 0; } || { echo "E2E-BATTERY: FAIL"; exit 1; }
