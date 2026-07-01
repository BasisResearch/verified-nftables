#!/usr/bin/env bash
# Kernel data-plane probe for the "overlapping-verdict concat vmap" cases
# (battery 14_concat_partial / 15_silent_daddr).
#
# nft --optimize FOLDS
#     ip saddr X tcp dport 22   drop
#     ip saddr X tcp dport 1-100 accept
# into a single concat vmap  { X . 22 : drop, X . 1-100 : accept }  whose
# intervals OVERLAP at dport 22 — and the kernel ACCEPTS it (unlike the pure
# interval case 13, which it rejects "conflicting intervals").  The question is
# whether that fold silently changes semantics.  This probe routes each vmap
# verdict through a named counter chain, fires one real TCP SYN per port from a
# dummy interface into the input hook, and reports which verdict actually wins.
#
# Result (nft v1.1.6): 22->DROP, 50..100->ACCEPT — i.e. the kernel resolves the
# overlap by preferring the MORE-SPECIFIC singleton (22) over the range, which
# HAPPENS to coincide with the original first-match here (the specific rule is
# first).  So nft's fold is kernel-faithful FOR THIS SHAPE, but only by the
# specific-element-first accident; reverse the two rules and it would diverge.
# Our verified optimizer therefore soundly DECLINES this fold in general.
#
# Run: unshare --net --map-root-user --map-auto -- bash probe_overlap_vmap.sh
set -uo pipefail
SADDR=10.0.0.1
ip link add dummy0 type dummy 2>/dev/null
ip addr add ${SADDR}/24 dev dummy0
ip link set dummy0 up
ip link set lo up
probe() {
  local DPORT="$1"
  nft flush ruleset
  nft -f - <<NFT
table ip t {
  counter c_drop {}
  counter c_accept {}
  chain drop_c {
    counter name "c_drop"
    drop
  }
  chain accept_c {
    counter name "c_accept"
    accept
  }
  chain c {
    type filter hook input priority filter; policy accept;
    ip saddr . tcp dport vmap { ${SADDR} . 22 : jump drop_c, ${SADDR} . 1-100 : jump accept_c }
  }
}
NFT
  python3 - "$SADDR" "$DPORT" <<'PY'
import socket,sys
saddr,dport=sys.argv[1],int(sys.argv[2])
s=socket.socket(socket.AF_INET,socket.SOCK_STREAM)
s.bind((saddr,0)); s.settimeout(0.5)
try: s.connect((saddr,dport))
except Exception: pass
s.close()
PY
  local d a
  d=$(nft list counter ip t c_drop   | grep -oE 'packets [0-9]+' | grep -oE '[0-9]+')
  a=$(nft list counter ip t c_accept | grep -oE 'packets [0-9]+' | grep -oE '[0-9]+')
  echo "dport=${DPORT}: drop=${d} accept=${a}"
}
echo "vmap = { ${SADDR} . 22 : drop, ${SADDR} . 1-100 : accept }  (overlap at 22)"
echo "original first-match: 22->DROP, 50->ACCEPT, 90->ACCEPT"
probe 22
probe 50
probe 90
