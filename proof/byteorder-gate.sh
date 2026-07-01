#!/usr/bin/env bash
# Compile-from-source byteorder gate.
#
# `make corpus` reconstructs bytecode FROM each .t.payload block and re-renders it
# — it never runs the SOURCE parser+compiler, so it is BLIND to a host/network
# byteorder divergence in the compile path (exactly where the `meta mark`/`ct mark`
# plain-cmp reversal lived).  This gate closes that blind spot: for every corpus
# block whose `# <src>` header our parser accepts and whose compiled bytecode loads
# a BYTEORDER_HOST_ENDIAN field (mark / iif / oif / ct-mark / fib-type) in a plain
# cmp/range, it COMPILES <src> FROM SOURCE and requires the rendered cmp/range/
# byteorder lines byte-identical to the corpus .payload.
#
# Requires: git, dune.  Reuses the corpus clone (NFT_CORPUS, default /tmp/nftables-src).
set -euo pipefail
cd "$(dirname "$0")"

CORPUS_DIR="${NFT_CORPUS:-/tmp/nftables-src}"
if [ ! -d "$CORPUS_DIR/tests/py" ]; then
  echo ">> fetching nftables corpus into $CORPUS_DIR"
  git clone --depth 1 https://git.netfilter.org/nftables "$CORPUS_DIR" \
    || git clone --depth 1 https://github.com/torvalds/nftables "$CORPUS_DIR"
fi

echo ">> building parser + verified compiler + renderer"
( cd extracted && dune build ./parse_test.exe )

payloads=$(find "$CORPUS_DIR/tests/py" -name '*.t.payload*')
echo ">> compiling host-order corpus blocks from source over $(echo "$payloads" | wc -l) payload files"
exec extracted/_build/default/parse_test.exe byteorder-gate $payloads
