#!/usr/bin/env bash
# Bug 1, fail-OPEN direction: an anti-scan drop rule that lets malformed-flag
# packets through after the fold.
#
# `tcp flags fin drop` + `tcp flags rst drop` (bit-tests: drop anything WITH the
# FIN, resp. RST, bit) is folded by `nft -o` into `tcp flags { fin, rst } drop`
# (exact set: drop only flags byte == 0x01 or == 0x04).  Crafted packets with
# SYN+FIN (0x03, a classic scan) and FIN+ACK (0x11) carry the FIN bit, so the
# original rule drops them, but they are not IN the exact set -> after the fold
# they pass.  Counters (gated on our crafted source port so kernel-generated
# RSTs don't contaminate the count) show the divergence.
#
# Run: unshare --net --map-root-user --map-auto -- bash tcp_flags_failopen.sh
# Expected (nft v1.0.2 .. HEAD): bit-test matches 2, exact-set matches 0.
set -u
ip link set lo up

nft -f - <<'NFT'
table ip t {
  counter c_bittest {}
  counter c_exactset {}
  chain c {
    type filter hook input priority 0; policy accept;
    tcp sport 44444 tcp flags fin          counter name "c_bittest"   # original anti-scan (bit-test)
    tcp sport 44444 tcp flags { fin, rst }  counter name "c_exactset"  # nft -o fold (exact set)
  }
}
NFT

python3 - <<'PY'
import socket, struct
def cksum(b):
    if len(b)%2: b+=b"\x00"
    s=0
    for i in range(0,len(b),2): s+=(b[i]<<8)+b[i+1]
    s=(s>>16)+(s&0xffff); s+=s>>16
    return ~s & 0xffff
def send(flags):
    src=dst=socket.inet_aton("127.0.0.1")
    tcp=struct.pack("!HHIIBBHHH",44444,9,0,0,(5<<4),flags,1024,0,0)
    pseudo=src+dst+struct.pack("!BBH",0,6,len(tcp))
    tcp=tcp[:16]+struct.pack("!H",cksum(pseudo+tcp))+tcp[18:]
    iph=struct.pack("!BBHHHBBH4s4s",0x45,0,20+len(tcp),0,0,64,6,0,src,dst)
    iph=iph[:10]+struct.pack("!H",cksum(iph))+iph[12:]
    s=socket.socket(socket.AF_INET,socket.SOCK_RAW,socket.IPPROTO_RAW)
    s.sendto(iph+tcp,("127.0.0.1",0)); s.close()
for name,f in [("SYN+FIN 0x03 (scan)",0x03),("FIN+ACK 0x11 (teardown)",0x11)]:
    send(f); print("sent",name,"- has FIN bit, anti-scan rule SHOULD catch it")
PY
sleep 0.3
echo "bit-test  (original 'tcp flags fin'): $(nft list counter ip t c_bittest  | grep -o 'packets [0-9]*')"
echo "exact-set (nft -o '{ fin, rst }')   : $(nft list counter ip t c_exactset | grep -o 'packets [0-9]*')"
