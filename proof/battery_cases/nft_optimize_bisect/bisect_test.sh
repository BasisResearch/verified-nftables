#!/bin/bash
# git bisect run script. $1 = bug1 | bug2
# exit 0 = bug ABSENT (old/good), 1 = bug PRESENT (new/bad), 125 = can't build (skip)
set -u
S=/tmp/claude-1000/-home-yiyun-Projects-certified-nft/be172073-b22d-459e-bc40-7d60b9c79b6d/scratchpad
BUG="$1"

git clean -fdx >/dev/null 2>&1
./autogen.sh >/dev/null 2>&1 || exit 125
PKG_CONFIG_PATH=$S/prefix/lib/pkgconfig ./configure --with-json=no --disable-man-doc >/dev/null 2>&1 || exit 125
make -j"$(nproc)" >/dev/null 2>&1 || exit 125
[ -x src/nft ] || exit 125

OUT=$(unshare --net --map-root-user --map-auto -- \
      env LD_LIBRARY_PATH=$S/prefix/lib ./src/nft -c --optimize -f "$S/case_$BUG.nft" 2>&1)
echo "== $(git rev-parse --short HEAD) $BUG ==" >> "$S/bisect_$BUG.log"
echo "$OUT" >> "$S/bisect_$BUG.log"

case "$BUG" in
  # bug1 present iff the optimizer proposes the mask-dropping exact-set fold
  bug1) echo "$OUT" | grep -qE 'tcp flags \{ *syn, *ack *\}' && exit 1 || exit 0 ;;
  # bug2 present iff the optimizer emits the overlapping /24+/16 merge (one line)
  bug2) echo "$OUT" | grep -qE '10\.0\.0\.0/24.*10\.0\.0\.0/16' && exit 1 || exit 0 ;;
esac
