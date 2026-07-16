#!/usr/bin/env bash
# Bug 1, strongest realistic case: ct status on a NAT gateway.
#
# A single rule `ct status dnat` compiles to a BIT-TEST (status & 0x20 != 0),
# matching every packet of a DNAT'd (port-forwarded) flow.  `nft -o` folds
# `ct status dnat accept` + `ct status snat accept` into the exact-value set
# `ct status { snat, dnat }` (compiles to `lookup set`, i.e. status == 0x10 or
# == 0x20 EXACTLY).  Real conntrack status is ALWAYS multi-bit (a dnat'd packet
# also carries confirmed|assured|seen-reply|dst-nat-done|...), so the exact set
# matches NONE of the real traffic the original rule matched.
#
# Run: unshare --net --map-root-user --map-auto -- bash ct_status_dnat.sh
# Expected (nft v1.0.2 .. HEAD): bit-test matches N>0, exact-set matches 0.
set -u
ip link set lo up

python3 - <<'PY' &
import socket
s=socket.socket(); s.setsockopt(socket.SOL_SOCKET,socket.SO_REUSEADDR,1)
s.bind(("127.0.0.1",8080)); s.listen(5)
while True:
    try:
        c,_=s.accept(); c.recv(16); c.close()
    except Exception: break
PY
LPID=$!
sleep 0.5

nft -f - <<'NFT'
table ip t {
  chain pre {
    type nat hook output priority -100; policy accept;
    ip daddr 127.0.0.1 tcp dport 9999 dnat to 127.0.0.1:8080
  }
  counter c_bittest {}
  counter c_exactset {}
  chain out {
    type filter hook output priority 0; policy accept;
    ct status dnat            counter name "c_bittest"    # original single rule (bit-test)
    ct status { snat, dnat }  counter name "c_exactset"   # nft -o fold (exact-value set)
  }
}
NFT

for i in 1 2 3; do
  python3 - <<'PY'
import socket
try:
    s=socket.socket(); s.settimeout(1); s.connect(("127.0.0.1",9999)); s.send(b"hi"); s.close()
except Exception as e: print("conn:",e)
PY
done
sleep 0.3
echo "bit-test  (original 'ct status dnat'): $(nft list counter ip t c_bittest  | grep -o 'packets [0-9]*')"
echo "exact-set (nft -o '{ snat, dnat }')  : $(nft list counter ip t c_exactset | grep -o 'packets [0-9]*')"
kill $LPID 2>/dev/null
