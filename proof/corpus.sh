#!/usr/bin/env bash
# Differential test against the upstream nftables test corpus.
#
# The corpus is nftables' own tests/py/*.t.payload: thousands of
# rule -> expected-netlink-bytecode pairs maintained alongside nft itself.
# We parse each bytecode block, round-trip the supported subset through the
# *verified* compiler (extracted/corpus_test.ml -> Compile.compile_rule), and
# diff the re-rendered bytecode against the corpus.  Coverage is reported; any
# MISMATCH on a supported rule fails the run (a real compiler/model bug).
#
# Requires: git, dune.  Clones nftables once into a cache dir if absent.
set -euo pipefail
cd "$(dirname "$0")"

CORPUS_DIR="${NFT_CORPUS:-/tmp/nftables-src}"
if [ ! -d "$CORPUS_DIR/tests/py" ]; then
  echo ">> fetching nftables corpus into $CORPUS_DIR"
  git clone --depth 1 https://git.netfilter.org/nftables "$CORPUS_DIR" \
    || git clone --depth 1 https://github.com/torvalds/nftables "$CORPUS_DIR"
fi

echo ">> building verified compiler + harness"
( cd extracted && dune build ./corpus_test.exe )

payloads=$(find "$CORPUS_DIR/tests/py" -name '*.t.payload*')
echo ">> running round-trip over $(echo "$payloads" | wc -l) corpus payload files"
exec extracted/_build/default/corpus_test.exe $payloads
