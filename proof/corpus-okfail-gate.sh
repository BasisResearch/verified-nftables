#!/usr/bin/env bash
# CORPUS OK/FAIL SWEEP — a BIDIRECTIONAL TRACKED-COUNT RATCHET.
#
# Run EVERY rule line of the model's supported corpus families (ip, inet, any)
# through the full frontend — parse -> structural inject -> verified typecheck
# -> verified lowering — and check its accept/reject against the corpus verdict
# (`;ok` must be accepted, `;fail` must be rejected).  Two counts are pinned:
#
#   pass          >= FLOOR   lines whose accept/reject matches the corpus.  A
#                            regression that newly REJECTS a supported `;ok`
#                            line, or newly ACCEPTS a `;fail` line, drops pass
#                            below the floor and turns the build red.
#   false_accept  <= CEIL    `;fail` lines the frontend still accepts.  These
#                            are the ledgered residual model boundaries
#                            (DEVELOPMENT.md § "T3 corpus ok/fail residual") —
#                            hook-context / family-scope / option-exclusion
#                            validations outside the model.  A NEW false-accept
#                            (an invalid line newly slipping through) raises this
#                            above the ceiling and turns the build red, even if a
#                            simultaneously-gained `;ok` line keeps pass level.
#
# So the residual reflects MODEL COVERAGE (not wrap artifacts), the harness wraps
# each rule in a fixed ip/filter/input base chain — a hook valid for the
# hardcoded family, so lowering never fails for a hook reason, NOT the rule's own
# (possibly netdev-egress) chain hook — strips the corpus `- ` list-output
# continuation prefix, skips `define`/variable and `?` set-element lines, and
# injects the `%`/`!` object/set/map DECLARATIONS that individually typecheck so
# `@name`/objref rules resolve.  The floor is a lower bound and the ceiling an
# upper bound: raise the floor / lower the ceiling (never the reverse) whenever a
# fix improves coverage.  This is broader and bidirectional where source-sweep-
# gate is a one-directional byte-identity PASS-count ratchet (blind to
# false-accepts of invalid input).
#
# Requires: git, dune.  Reuses the corpus clone (NFT_CORPUS, default /tmp/nftables-src).
set -euo pipefail
cd "$(dirname "$0")"

# Pinned bidirectional counts over ip+inet+any (1391 rule lines, after non-rule
# `?`/`define` directives are excluded).  pass FLOOR = matched lines (both
# directions); false_accept CEIL = the 47 ledgered residual `;fail` lines still
# accepted (NAT/tproxy hook-context, reject/ct nfproto scope, bridge-family
# selectors + empty ifname, log option mutual-exclusion, vmap interval overlap,
# ether payload-dependency, fib key-set, icmp field inter-dependency).  See
# DEVELOPMENT.md "T3 corpus ok/fail residual".
CORPUS_OKFAIL_FLOOR="${CORPUS_OKFAIL_FLOOR:-1003}"
CORPUS_OKFAIL_CEIL="${CORPUS_OKFAIL_CEIL:-47}"

CORPUS_DIR="${NFT_CORPUS:-/tmp/nftables-src}"
if [ ! -d "$CORPUS_DIR/tests/py" ]; then
  echo ">> fetching nftables corpus into $CORPUS_DIR"
  git clone --depth 1 https://git.netfilter.org/nftables "$CORPUS_DIR" \
    || git clone --depth 1 https://github.com/torvalds/nftables "$CORPUS_DIR"
fi

echo ">> building the frontend + verified typechecker/lowering"
( cd extracted && dune build ./parse_test.exe )

files=$(ls "$CORPUS_DIR"/tests/py/ip/*.t "$CORPUS_DIR"/tests/py/inet/*.t \
           "$CORPUS_DIR"/tests/py/any/*.t)
echo ">> corpus ok/fail sweep over ip+inet+any (floor $CORPUS_OKFAIL_FLOOR, false-accept ceil $CORPUS_OKFAIL_CEIL)"
exec extracted/_build/default/parse_test.exe corpus-okfail-gate \
  "$CORPUS_OKFAIL_FLOOR" "$CORPUS_OKFAIL_CEIL" $files
