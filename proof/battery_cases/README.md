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
| 05 | overlap_prefix_sameverdict | `/24`⊂`/16`, same verdict → covering `/16` | **MATCH** — *landed this run* (same-verdict prefix ABSORPTION, `Optimize_Absorb`): we drop the subsumed `/24`, keeping the covering `/16` — verdict-identical to the kernel's committed `{ 10.0.0.0/16 }` |
| 06 | disjoint_prefix | adjacent `/24`s, same verdict → merged `/23` | **MATCH** — the bare value→set pass (`Optimize_Merge`/`setsN`) folds the two same-field `/24` compares to `ip saddr { 10.0.0.0/24, 10.0.1.0/24 }`; kernel-equivalent interval coverage to nft's `{ 10.0.0.0/23 }` (both load, same verdict) |
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
| 18 | tcp_dport_vmap | bare `tcp dport` distinct values, differing verdicts → vmap | **MATCH** — *landed (`Optimize_Vmapg`, guarded value+verdict→vmap)*: the l4proto-guarded run folds to `tcp dport vmap { 22:drop, 80:accept, 443:drop }`, byte-identical to `nft -o`; kernel-loaded + data-plane-equivalent to the 3 originals |
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

### Newly closed this run

- **05 — same-verdict prefix ABSORPTION** (`/24`⊂`/16` → covering `/16`).
  `Optimize_Absorb`: a byte-aligned prefix lowers to an `MCmp (FPayload b off k)
  CEq …` k-byte payload compare, so the /24 is a 3-byte and the /16 a 2-byte
  compare over the SAME base+offset. The recogniser detects the prefix subsumption
  (`w2 ≤ w1`, `firstn w2 v1 = v2`, same tail/verdict) and DROPS the subsumed /24,
  keeping the covering /16 — verdict-identical to the kernel's committed
  `{ 10.0.0.0/16 }` normalisation of `nft -o`'s set. Verified, axiom-free, composed
  as the FIRST stage of `optimize_table` (`optimize_table_uncond_correct` /
  `_compile_correct` still print "Closed under the global context").
- **06 — adjacent same-verdict `/24`s** now fold via the pre-existing bare
  value→set pass (`Optimize_Merge`/`setsN`): the two same-field 3-byte compares
  become `ip saddr { 10.0.0.0/24, 10.0.1.0/24 }`, kernel-equivalent interval
  coverage to nft's `{ 10.0.0.0/23 }` (both load, same verdict). No new pass
  needed — the earlier "GAP" classification was stale.

### Newly closed (this run)

- **18 — transport-guarded value+verdict→vmap** (bare `tcp dport vmap { 22:drop,
  80:accept, 443:drop }`). `Optimize_Vmapg`: the guarded run
  `[ MCmp l4proto 6 ; MCmp tcp_dport v_i ] w_i` (differing terminal verdicts) folds
  to ONE `mk_vmap_rule` whose body keeps the l4proto guard and whose vmap key is
  `tcp dport`, over the N point entries `{ v_i : w_i }` — exactly `nft -o`'s
  `tcp dport vmap { … }` (guard `[ meta ][ cmp ]` then `[ lookup dreg 0 ]`).
  Soundness REDUCES the heavy N-way vmap outcome argument to the existing
  `Optimize_Vmap.eval_rules_vmap_mergeN` (on body `BMatch gm :: body`), composed
  with a per-rule SWAP equivalence `orig_ruleGv_eq_swap` that commutes the two
  leading pure matches. Verified, axiom-free, composed as the penultimate stage of
  `optimize_table` (before `vmapN`); `optimize_table_uncond_correct` /
  `_compile_correct` / `compile_chain_correct` still print "Closed under the global
  context". Fires non-vacuously (`Optimize_Vmapg_Witness.vmapg_fires`, `cbv`);
  kernel-loaded and data-plane-equivalent to the 3 originals (netns loopback probe:
  `22:DROP 80:ACCEPT 443:DROP 1234:ACCEPT` identical for both forms).

### Residue (documented, each with a reason)

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
