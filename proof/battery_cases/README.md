# nft-o differential BUG-HUNTER battery — definitive findings

Run: `bash difftest_battery.sh` (from `proof/`).

For each `battery_cases/*.nft`: runs OUR verified `nftc optimize` and
`nft --optimize`, loads the original and nft's recommendation into a fresh
unprivileged netns kernel, and reports divergences. Where the classification
turns on runtime semantics (overlapping intervals the kernel *accepts*) it is
settled by a real data-plane probe — see `probe_overlap_vmap.sh`.

## Classification of every ruleset shape

Legend: **MATCH** = we produce the same (or kernel-equivalent) consolidation as
`nft -o`. **EXCEED** = we consolidate soundly where nft does not. **GAP** =
`nft -o` performs a *safe* consolidation we currently decline (our
under-consolidation). **nft BUG** = `nft -o`'s recommendation is kernel-rejected
or unsafe; we soundly decline.

| # | case | shape | verdict |
|---|------|-------|---------|
| 01 | value_set | host `/32` values, same verdict → set | **MATCH** |
| 02 | vmap_distinct | host values, differing verdicts → vmap | **MATCH** |
| 03 | overlap_prefix_diffverdict | `/24`⊂`/16`, differing verdicts | **nft BUG** — kernel rejects `conflicting intervals` (fail-closed); we decline |
| 04 | overlap_concat_diffverdict | overlapping concat, differing verdicts | **nft BUG** — kernel rejects `Could not process rule: File exists`; we decline |
| 05 | overlap_prefix_sameverdict | `/24`⊂`/16`, same verdict → covering `/16` | **GAP (ours)** — same-verdict prefix absorption; deferred-hard |
| 06 | disjoint_prefix | adjacent `/24`s, same verdict → merged `/23` | **GAP (ours)** — same-verdict prefix normalization/union; deferred-hard |
| 07 | dnat_overlap | overlapping dnat → daddr map | **nft BUG** — kernel rejects `conflicting intervals`; we decline |
| 08 | snat_map | saddr → snat value map | **MATCH** |
| 09 | meta_mark_map | `saddr → meta mark set` pairs → map | **EXCEED** — sound superset; `nft -o` declines, we fold |
| 10 | interval_ranges | explicit ranges, same verdict → set | **MATCH** (we render ranges, nft renders `/24` prefixes; same interval set) |
| 11 | negated | `saddr != X` … | **MATCH** — both correctly decline (union of `!=` is unsound) |
| 12 | concat_tcp_dport | `saddr . tcp dport` concat set | **MATCH** |
| 13 | partial_range_diffverdict | overlapping ranges, differing verdicts | **nft BUG** — kernel rejects `conflicting intervals`; we decline |
| 14 | concat_partial | `saddr . tcp dport` concat, port `22` vs `1-100`, diff verdict | **GAP (ours), conservative** — soundness-necessary in general; nft's fold is kernel-faithful *here* (probe) only by specific-first accident |
| 15 | silent_daddr | `daddr . tcp dport` concat, same overlap shape as 14 | **GAP (ours), conservative** — as 14 |
| 16 | tcp_dport_set | bare `tcp dport` values, same verdict → set | **MATCH** — *landed this run* (bare-transport-port-set, `Optimize_Setg`) |
| 17 | udp_dport_set | bare `udp dport` values, same verdict → set | **MATCH** — *landed this run* (bare-transport-port-set) |
| 18 | tcp_dport_vmap | bare `tcp dport` distinct values, differing verdicts → vmap | **GAP (ours)** — transport-guarded value+verdict→vmap; deferred-hard |
| 19 | meta_mark_set | bare `meta mark` values, same verdict → set | **MATCH** — *landed this run* (metafield-fixedwidth-set, `Optimize_Merge`) |
| — | MINIMAL_…_failclosed_bug | canonical duplicate of 03 | **nft BUG** — minimal fail-closed repro |

## Is "absolutely no gap" achieved?

**No — not literally, and this is stated honestly.** The two families targeted
this run are now fully matched:

- **bare-transport-port-set** (16, 17): bare `tcp/udp dport { … }` fold to a
  2-byte `inet_service` set exactly as `nft -o`, kernel-byte-identical lowering.
- **metafield-fixedwidth-set** (19): bare `meta mark { … }` fold to a
  fixed-width meta set.

Both are verified, axiom-free, and composed into the shipped
`Optimize_Uncond.optimize_table_uncond` entry.

### Residue (documented, each with a reason)

- **05, 06 — same-verdict prefix union/absorption** (`/24`⊂`/16` → `/16`; two
  adjacent `/24` → `/23`). *deferred-hard*: needs prefix→interval canonicalization
  plus subset-absorption in the recogniser (our value→set fires on exact host
  values and explicit ranges, not on prefix-notation keys). We soundly leave the
  first-match rules.
- **18 — transport-guarded value+verdict→vmap** (bare `tcp dport vmap { 22:drop,
  80:accept, … }`). *deferred-hard*: the vmap sibling of `Optimize_Setg` (which
  builds a set); the network-key analogue `Optimize_Vmap` already exists, so this
  is a mechanical-but-real extension. We soundly leave the sequential guarded
  `cmp` rules (first-match-equivalent).
- **14, 15 — overlapping-verdict concat→vmap**. *soundness-necessary*: `nft -o`
  folds overlapping-interval concat vmaps that the kernel accepts and resolves by
  element specificity; that coincides with first-match only when the more-specific
  rule is written first (as in these cases — confirmed by `probe_overlap_vmap.sh`).
  The transformation is order-dependent and unsafe in general, so our verified
  optimizer conservatively declines it. This is not a gap we should close blindly.

### Not gaps

- **03, 04, 07, 13, MINIMAL — confirmed `nft --optimize` bugs.** `nft -o` turns a
  valid, loadable ruleset into an **unloadable** one: overlapping keys with
  differing verdicts are merged into an interval set/map the kernel rejects
  (`conflicting intervals` / `File exists`), leaving an **empty committed
  ruleset** (fail-closed). Kernel-verified against nft v1.1.6. Our verified
  optimizer soundly declines every such merge.
- **09 — we exceed nft** (sound superset).

## Provenance / trust

The three headline theorems are `Closed under the global context` (axiom-free):
`compile_chain_correct` (`theories/Correct.v`) and
`optimize_table_uncond_correct` / `optimize_table_uncond_compile_correct`
(`theories/Optimize_Uncond.v`, the shipped entry that composes every pass above).
Gates green: corpus 2532/2532 (0 mismatches), validate 28/28, semtest, parse-test,
e2e.
