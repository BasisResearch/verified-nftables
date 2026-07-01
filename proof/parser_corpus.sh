#!/usr/bin/env bash
# parser_corpus.sh — run the UNTRUSTED .nft frontend (nftc compile) over a large,
# diverse, REAL corpus of nftables rules and print an HONEST coverage table.
#
# Corpus sources (see parser_corpus/github/PROVENANCE.tsv for per-file origin):
#   1. nftables' own test suite  (the `;ok` rules in tests/py/**/*.t and the
#      `# <rule>` headers in tests/py/**/*.t.payload) — from $NFT_CORPUS.
#   2. nftables' shipped example rulesets (files/**, doc/**, examples/**).
#   3. real-world .nft configs mined from many independent GitHub repos, committed
#      under parser_corpus/github/.
#
# "parsed+compiled" = the frontend built an AST with NO error AND it compiled
# (Compile.compile_chain).  Failures are bucketed and classified parser-bug vs
# out-of-model (a construct the verified model genuinely does not carry).  Nothing
# is silently swallowed.  See parser_corpus.py for the (documented) classifier.
#
# Requires: dune, python3, and the nftables test corpus at $NFT_CORPUS
# (default /tmp/nftables-src; cloned on demand, same as corpus.sh).
set -euo pipefail
cd "$(dirname "$0")"

CORPUS_DIR="${NFT_CORPUS:-/tmp/nftables-src}"
if [ ! -d "$CORPUS_DIR/tests/py" ]; then
  echo ">> fetching nftables corpus into $CORPUS_DIR"
  git clone --depth 1 https://git.netfilter.org/nftables "$CORPUS_DIR" \
    || git clone --depth 1 https://github.com/torvalds/nftables "$CORPUS_DIR"
fi

echo ">> building the verified compiler CLI (nftc)"
( cd extracted && dune build ./nftc_cli.exe )

echo ">> running the frontend over the parser corpus"
NFT_CORPUS="$CORPUS_DIR" exec python3 parser_corpus.py
