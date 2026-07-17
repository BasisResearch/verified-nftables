#!/usr/bin/env bash
# Compile-from-source SOURCE-SWEEP — a TRACKED-COUNT RATCHET.
#
# For EVERY `.t.payload` block, compile its `# <src>` header from source through
# the parser + verified compiler + renderer and diff the rendered rule against
# the block's recorded instructions.  Unlike `byteorder-gate` (red/green
# byte-identity on the narrow host-order class), this is a broad sweep whose
# corpus goldens are endian-unportable for hton'd host-endian constants and
# whose several benign display/optimization classes render differently — so it
# can never be red/green.  It is a RATCHET: the byte-identical PASS count is
# pinned as a FLOOR below; a frontend regression that drops a block below the
# floor turns the build red, while the open display classes stay visible.
#
# The floor is a lower bound, not the exact count: raise it (never silently
# lower it) whenever a fix lifts the pass count.  See DEVELOPMENT.md
# § "The 83 source-divergences, adjudicated (T2A)".
#
# Requires: git, dune.  Reuses the corpus clone (NFT_CORPUS, default /tmp/nftables-src).
set -euo pipefail
cd "$(dirname "$0")"

# Pinned pass-count FLOOR (compile-from-source blocks byte-identical to corpus).
# Raised 1166 -> 1176 when the class-G in-frame-ethertype network guard landed
# (8 bridge/netdev vlan+icmp blocks moved from divergent to byte-identical).
SOURCE_SWEEP_FLOOR="${SOURCE_SWEEP_FLOOR:-1176}"

CORPUS_DIR="${NFT_CORPUS:-/tmp/nftables-src}"
if [ ! -d "$CORPUS_DIR/tests/py" ]; then
  echo ">> fetching nftables corpus into $CORPUS_DIR"
  git clone --depth 1 https://git.netfilter.org/nftables "$CORPUS_DIR" \
    || git clone --depth 1 https://github.com/torvalds/nftables "$CORPUS_DIR"
fi

echo ">> building parser + verified compiler + renderer"
( cd extracted && dune build ./parse_test.exe )

payloads=$(find "$CORPUS_DIR/tests/py" -name '*.t.payload*')
echo ">> source-sweep over $(echo "$payloads" | wc -l) payload files (floor $SOURCE_SWEEP_FLOOR)"
exec extracted/_build/default/parse_test.exe source-sweep-gate "$SOURCE_SWEEP_FLOOR" $payloads
