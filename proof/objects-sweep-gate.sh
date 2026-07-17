#!/usr/bin/env bash
# OBJECTS OK/FAIL SWEEP — a TRACKED-COUNT RATCHET (T3).
#
# Run every RULE line of the nftables `objects.t` corpus (the `;ok` / `;fail`
# named-object REFERENCE forms — `counter name`, `quota name`, `ct helper set`,
# `limit name`, `synproxy name`, the objref verdict-maps) through the full
# frontend: parse -> config-op apply -> typecheck -> verified lowering.  A `;ok`
# line must be ACCEPTED by all three stages; a `;fail` line must be REJECTED
# (parse error / typecheck false / lowering lerr).  The bidirectional match
# count is pinned as a FLOOR; a frontend regression that drops a reference form
# below the floor turns the build red.
#
# Object DECLARATION lines (`%name type ...`) build the table's object
# environment (the `;ok` ones); their own verdicts test deep object-body
# validity (helper protocol modules, ct-timeout policy state names, l3proto) —
# kernel-module behaviour OUTSIDE this model — so the sweep scopes to RULE lines
# and ledgers that residual (DEVELOPMENT.md § "T3 named objects").
#
# The floor is a lower bound: raise it (never silently lower it) when a fix lifts
# the count.  Requires: git, dune.  Reuses the corpus clone (NFT_CORPUS).
set -euo pipefail
cd "$(dirname "$0")"

# Pinned floor: ip/objects.t has 14 rule lines; all 14 match bidirectionally
# (7 `;ok` reference forms incl. both objref-map shapes, and the `;fail`
# undeclared-object references).  100% within scope — no coverage gap.
OBJECTS_SWEEP_FLOOR="${OBJECTS_SWEEP_FLOOR:-14}"

CORPUS_DIR="${NFT_CORPUS:-/tmp/nftables-src}"
if [ ! -d "$CORPUS_DIR/tests/py" ]; then
  echo ">> fetching nftables corpus into $CORPUS_DIR"
  git clone --depth 1 https://git.netfilter.org/nftables "$CORPUS_DIR" \
    || git clone --depth 1 https://github.com/torvalds/nftables "$CORPUS_DIR"
fi

echo ">> building the frontend + verified typechecker/lowering"
( cd extracted && dune build ./parse_test.exe )

extracted/_build/default/parse_test.exe objects-sweep "$OBJECTS_SWEEP_FLOOR" \
  "$CORPUS_DIR/tests/py/ip/objects.t"
