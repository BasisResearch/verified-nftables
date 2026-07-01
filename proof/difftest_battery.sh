#!/usr/bin/env bash
# Differential nft-o BUG-HUNTER battery.
#
# For each ruleset: run OUR verified `nftc optimize` and `nft --optimize`,
# then load BOTH the original and nft's optimized recommendation into a fresh
# unprivileged netns kernel, and check whether nft --optimize's recommendation
# (a) fails to load, or (b) changes the kernel-visible ruleset semantics vs the
# original.  Classifies each case.
#
# Requires: nft (v1.1.6+), unshare, the built nftc CLI.
set -uo pipefail
cd "$(dirname "$0")"
NFTC=extracted/_build/default/nftc_cli.exe
CASE_DIR="${1:-battery_cases}"

# run nft --optimize on FILE inside a fresh netns; capture stdout(recommendation),
# stderr(diagnostics), exit code, and the committed ruleset.
nfto() {
  local file="$1"
  unshare --net --map-root-user --map-auto -- bash -c '
    f="$1"
    nft --optimize -f "$f" >/tmp/nfto.out 2>/tmp/nfto.err
    echo "EXIT=$?"
    echo "===STDOUT==="; cat /tmp/nfto.out
    echo "===STDERR==="; cat /tmp/nfto.err
    echo "===COMMITTED==="; nft list ruleset 2>/dev/null
  ' _ "$file" 2>&1
}
# does the original load cleanly?
origload() {
  local file="$1"
  unshare --net --map-root-user --map-auto -- bash -c '
    if nft -f "$1" 2>/tmp/ol.err; then echo ORIG_OK; else echo ORIG_FAIL; cat /tmp/ol.err; fi
  ' _ "$file" 2>&1
}

for f in "$CASE_DIR"/*.nft; do
  [ -f "$f" ] || continue
  name=$(basename "$f" .nft)
  echo "################################################################"
  echo "# CASE: $name"
  echo "################################################################"
  echo "--- input ---"; grep -vE 'type|policy' "$f" | sed 's/^/   /'
  echo "--- original load ---"; origload "$f"
  echo "--- OURS (nftc optimize) ---"
  $NFTC optimize "$f" 2>&1 | grep -E 'lookup|set __|map __|vmap|immediate|nat |meta set|^Unsupported|Error' | sed 's/^/   /'
  echo "--- nft --optimize ---"; nfto "$f"
  echo
done
