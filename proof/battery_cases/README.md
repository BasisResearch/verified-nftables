# nft-o differential BUG-HUNTER battery — definitive findings

Run: `bash difftest_battery.sh` (from `proof/`).

For each `battery_cases/*.nft`: runs OUR verified `nftc optimize` and
`nft --optimize`, loads the original and nft's recommendation into a fresh
unprivileged netns kernel, and reports divergences. Where the classification
turns on runtime semantics (overlapping intervals the kernel *accepts* and how it
*resolves* them) it is settled by a real data-plane probe — see
`probe_overlap_vmap.sh`. Key kernel facts established by source review
(`net/netfilter/nft_set_pipapo.c`, `nft_set_rbtree.c`) + datapath tests:
concatenated interval sets (`pipapo`) resolve a lookup to the **lowest rule
index** (`pipapo_refill`/`__builtin_ctzl`) = insertion order, and reject only
*dead* rules on insert (a new element wholly inside an existing one); so an
overlapping concat vmap emitted in **rule order** is a faithful first-match
encoding. Single-field interval sets (`rbtree`) and nft userspace forbid
overlaps entirely.

## Classification of every ruleset shape

Legend: **MATCH** = we produce the same (or kernel-equivalent) consolidation as
`nft -o`. **EXCEED** = we consolidate soundly where nft does not. **GAP
(modeling)** = `nft -o` performs a consolidation that is genuinely
verdict-preserving on the kernel, but we decline it because our semantics does
not yet model the kernel behavior it relies on (our under-consolidation — a
faithfulness limitation, not a soundness one). **nft BUG** = `nft -o`'s
recommendation is *unloadable* — rejected either by nft's own userspace
(`src/intervals.c`, before any netlink is sent) or by the kernel set backend; we
soundly decline. NB: the two are different layers — single-field interval
overlaps are caught in **userspace**; concatenated (multi-field) overlaps slip
past userspace and are adjudicated by the **kernel** set backend (`pipapo`).

| # | case | shape | verdict |
|---|------|-------|---------|
| 01 | value_set | host `/32` values, same verdict → set | **MATCH** |
| 02 | vmap_distinct | host values, differing verdicts → vmap | **MATCH** |
| 03 | overlap_prefix_diffverdict | `/24`⊂`/16`, differing verdicts | **nft BUG** — nft **userspace** (`intervals.c`) rejects `conflicting intervals` before netlink (single-field overlaps are unrepresentable in an rbtree interval set, either order); nothing committed (fail-closed); we decline |
| 04 | overlap_concat_diffverdict | overlapping concat, wider-first (dead-rule) | **nft BUG** — reaches the **kernel** and `pipapo` rejects `Could not process rule: File exists` (inserting the narrower element *after* the wider one that engulfs it = a dead rule); fail-closed; we decline |
| 05 | overlap_prefix_sameverdict | `/24`⊂`/16`, same verdict → covering `/16` | **MATCH** — *landed this run* (same-verdict prefix ABSORPTION, `Optimize_Absorb`): we drop the subsumed `/24`, keeping the covering `/16` — verdict-identical to the kernel's committed `{ 10.0.0.0/16 }` |
| 06 | disjoint_prefix | adjacent `/24`s, same verdict → merged `/23` | **MATCH** — the bare value→set pass (`Optimize_Merge`/`setsN`) folds the two same-field `/24` compares to `ip saddr { 10.0.0.0/24, 10.0.1.0/24 }`; kernel-equivalent interval coverage to nft's `{ 10.0.0.0/23 }` (both load, same verdict) |
| 07 | dnat_overlap | overlapping dnat → daddr map | **nft BUG** — nft **userspace** rejects `conflicting intervals` (single-field overlap); we decline |
| 08 | snat_map | saddr → snat value map | **MATCH** |
| 09 | meta_mark_map | `saddr → meta mark set` pairs → map | **EXCEED** — sound superset; `nft -o` declines, we fold |
| 10 | interval_ranges | explicit ranges, same verdict → set | **MATCH** (we render ranges, nft renders `/24` prefixes; same interval set) |
| 11 | negated | `saddr != X` … | **MATCH** — both correctly decline (union of `!=` is unsound) |
| 12 | concat_tcp_dport | `saddr . tcp dport` concat set | **MATCH** |
| 13 | partial_range_diffverdict | overlapping ranges, differing verdicts | **nft BUG** — nft **userspace** rejects `conflicting intervals` (single-field overlap); we decline |
| 14 | concat_partial | `saddr . tcp dport` concat, port `22` vs `1-100`, diff verdict, narrower-first | **GAP (modeling)** — nft's fold is **verdict-CORRECT**: the concat `pipapo` set is an *ordered* first-match structure (lowest rule index wins), and nft emits elements in rule order, so `22→drop, 50→accept` exactly matches first-match (data-plane-verified). We decline only because our set/vmap semantics doesn't model ordered/rule-indexed interval sets |
| 15 | silent_daddr | `daddr . tcp dport` concat, same overlap shape as 14 | **GAP (modeling)** — as 14 (daddr variant; data-plane-verified verdict-correct) |
| 16 | tcp_dport_set | bare `tcp dport` values, same verdict → set | **MATCH** — *landed this run* (bare-transport-port-set, `Optimize_Setg`) |
| 17 | udp_dport_set | bare `udp dport` values, same verdict → set | **MATCH** — *landed this run* (bare-transport-port-set) |
| 18 | tcp_dport_vmap | bare `tcp dport` distinct values, differing verdicts → vmap | **MATCH** — *landed (`Optimize_Vmapg`, guarded value+verdict→vmap)*: the l4proto-guarded run folds to `tcp dport vmap { 22:drop, 80:accept, 443:drop }`, byte-identical to `nft -o`; kernel-loaded + data-plane-equivalent to the 3 originals |
| 19 | meta_mark_set | bare `meta mark` values, same verdict → set | **MATCH** — *landed this run* (metafield-fixedwidth-set, `Optimize_Merge`) |
| — | MINIMAL_…_failclosed_bug | canonical duplicate of 03 | **nft BUG** — minimal fail-closed repro |

## Is "absolutely no gap" achieved?

**No.** A previous revision claimed no *sound-to-close* gap remained (treating
14/15 as principled soundness declines). That was an error — see the 2026-07
correction under Residue: shapes **14/15 are genuine, closeable modeling gaps**
(`nft -o`'s fold is verdict-correct; we can't yet produce it because we don't
model ordered interval sets). Every *disjoint-key* consolidation is matched or
exceeded, and every overlapping-key case `nft -o` gets wrong is soundly declined;
but closing 14/15 requires a real semantics extension and is **open work**. The
two families targeted this run are now fully matched:

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

### Residue — genuine GAPS on our side (modeling), not principled declines

- **14, 15 — overlapping-verdict concat→vmap (narrower rule first)**. Correction
  (2026-07): an earlier version of this file called these "soundness-necessary
  declines / kernel-faithful only by accident." That was **wrong**. The concat
  `pipapo` set is an *ordered* first-match structure — the kernel resolves a
  lookup to the lowest rule index (`pipapo_refill` → `__builtin_ctzl`), which is
  insertion order, and `nft -o` emits the vmap elements in rule order. So the fold
  is **verdict-preserving by construction**, not by accident: datapath probes show
  `dport 22 → drop` (rule 1) and `50/90 → accept` (rule 2), identical to the
  original sequential rules; and the *wrong* order (wider rule first, which would
  make the narrower one dead) is refused by the kernel (`File exists`), so nft
  cannot silently emit a verdict-changing fold. We decline **only** because our
  `Semantics.v` models set/vmap lookup as unordered/disjoint-key; we do not yet
  model the kernel's ordered/rule-indexed interval semantics, so we cannot *prove*
  this correct fold and conservatively refuse it. **Closing it is a real semantics
  extension** (model ordered interval sets + a pass that folds only the live,
  narrower-first overlap case), not a trivial addition.

### Not gaps

- **03, 07, 13, MINIMAL — `nft --optimize` bugs (userspace-caught).** `nft -o`
  folds overlapping single-field keys with differing verdicts into an interval
  set/map, but single-field overlaps are unrepresentable — nft's own **userspace**
  (`src/intervals.c`, `set_overlap`) rejects it with `conflicting intervals`
  *before any netlink is sent*, so `nft --optimize -f` exits non-zero and commits
  **nothing** (fail-closed). Our verified optimizer soundly declines.
- **04 — `nft --optimize` bug (kernel-caught).** Here the overlap is a *concat*
  (so it slips past userspace) but in the dead-rule order, so the **kernel**
  `pipapo` insert rejects it (`Could not process rule: File exists`); fail-closed.
- **09 — we exceed nft** (sound superset).

## Provenance / trust

The three headline theorems are `Closed under the global context` (axiom-free):
`compile_chain_correct` (`theories/Correct.v`) and
`optimize_table_uncond_correct` / `optimize_table_uncond_compile_correct`
(`theories/Optimize_Uncond.v`, the shipped entry that composes every pass above).
Gates green: corpus 2532/2532 (0 mismatches), validate 28/28, semtest, parse-test,
e2e.
