# parser_corpus — a real, diverse corpus for the .nft frontend

`make parser-corpus` (driver: `../parser_corpus.sh` -> `../parser_corpus.py`)
runs the UNTRUSTED frontend (`nftc compile`) over this corpus and prints an
honest coverage table: parsed+compiled / failed=parser-bug / failed=out-of-model.

## Sources

1. **nftables' own test suite** (read at run time from `$NFT_CORPUS`, default
   `/tmp/nftables-src`, cloned on demand exactly like `corpus.sh`):
   - the `;ok` rule lines across `tests/py/**/*.t`  (~1.9k rules)
   - the `# <rule>` header lines across `tests/py/**/*.t.payload` (~1.7k rules,
     each carrying its own `family table chain` context line)
2. **nftables' shipped example rulesets**: `files/**`, `doc/**`, `examples/**`
   under `$NFT_CORPUS` (also read at run time).
3. **`github/`** — 245 real-world `.nft` / `nftables.conf` files mined from many
   independent public GitHub repositories via `gh` code search (multiple distinct
   queries for diversity), deduplicated by content.  Per-file provenance
   (repo + path + URL) is in `github/PROVENANCE.tsv`.

Nothing here is hand-written or cherry-picked; the mining queries and the
test-suite extraction are reproducible from the driver.
