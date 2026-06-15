#!/usr/bin/env bash
# Differential test: the *verified* extracted compiler vs. the real `nft`.
#
# We feed the same ruleset to `nft --debug=netlink` and to our extracted
# compiler (via extracted/glue.exe), then compare the emitted control-plane
# bytecode (the `[ ... ]` expression lines).  A clean diff is evidence that our
# formal model of the bytecode — and the compiler that targets it — matches the
# behaviour of the battle-tested upstream tool.
#
# `nft` needs a net namespace for cache init; `unshare -rn` gives an unprivileged
# one.  Requires: nft, unshare, dune, diff.
set -euo pipefail
cd "$(dirname "$0")"

NFT_INPUT='table ip filter {
  chain input {
    type filter hook input priority 0; policy drop;
    tcp dport 22 accept
    ip saddr 10.1.2.3 drop
    tcp sport 80 accept
    ip daddr 192.168.1.1 tcp dport 443 accept
  }
}'

extract_exprs() { grep -E '^\s*\[ ' ; }   # keep only the bytecode expr lines

echo ">> building extracted compiler"
( cd extracted && dune build ./glue.exe )
GLUE=extracted/_build/default/glue.exe

echo ">> real nft bytecode"
printf '%s\n' "$NFT_INPUT" | unshare -rn nft --debug=netlink -f - | extract_exprs > /tmp/nft.bc

echo ">> verified compiler bytecode"
"$GLUE" compile | extract_exprs > /tmp/ours.bc

if diff -u /tmp/nft.bc /tmp/ours.bc; then
  echo "PASS: verified compiler output is byte-identical to nft"
else
  echo "FAIL: divergence above (left=nft, right=ours)"
  exit 1
fi
