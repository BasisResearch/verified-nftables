# Optimizer gaps & divergences — TODO

The verified optimizer pipeline (`optimize_table`, all passes axiom-free) is:

```
normalize (MEq→MCmp)  →  optimize_chain (dedup / prune / DCE / singleton-range→cmp)
  →  dnat  (bare `dnat to <f> map {…}`)        # nft -o faithful, NFT_BREAK-on-miss
  →  setsN (value → anonymous set)
  →  concatK (≥3-field concat set)
  →  mapN  (`meta mark set … map`, HEAD-GUARDED)
  →  concatN (2-field concat set)
  →  vmapN (value+verdict → verdict map)
```

Goal of this track: **completely close the capability gaps and the fidelity
divergence vs `nft --optimize` (`nft -o`)**, each as a verified, axiom-free pass
composed into `optimize_table`, all gates staying green (corpus 2532/2532,
validate 28/28, semtest/parse-test/e2e/nl-send), the three headline theorems
`Closed under the global context`.

**IMPORTANT — `nft -o` may itself be buggy.** These fixes must be *differentially
validated against real `nft --optimize`* (host `nft` v1.1.6, and kernel round-trips
via the netns / VM setup), BUT do not blindly match `nft -o`: where our verified
output differs from `nft -o`, determine the **ground truth from kernel packet
semantics** (does the transformed ruleset filter/rewrite every packet identically
to the original?). If `nft -o` produces a semantically-different (i.e. *wrong*)
ruleset, that is an nft bug — capture a minimal reproducer, confirm it against the
kernel (load both the original and `nft -o` output, compare behaviour), and
document it (do NOT replicate the bug). Our theorems already pin our own output to
verdict-preservation, so any real divergence is either our gap or nft's bug.

---

## G1 — `snat to … map { … }` bare-map merge  ✅ DONE (theories/Optimize_Snat.v)

Landed: `Optimize_Snat.v` mirrors `Optimize_Dnat.v` for `nat_snat_kind` + the SOURCE
slot, reusing the kind-agnostic helpers (`dmap2`, `nat_map_key_single`,
`map_has_key_dmap2`, `apply_nat_tuple_indep`, `nat_orig_addr_indep`) verbatim. The
`snat` stage is composed into `optimize_table` right after `dnat`; the gen theorem
`optimize_table_correct_uncond_gen` is re-proved (new lemma
`optimize_chain_dnat_fresh_mapname` threads sd_maps-declaration freshness so the
`snat` stage mints disjoint mapnames on top of `dnat`). Fires end-to-end
(`nftc optimize` collapses 2 snat rules → 1 bare `snat to ip saddr map { … }`),
matching `nft --optimize` (netns-confirmed; no nft bug). Also fixed a latent gap in
the `dnat` template: the recogniser required `r_verdict = Continue` but the frontend
lowers a bare `snat`/`dnat` to a terminal **Accept**, so neither pass fired on real
rulesets — both `orig_{s,d}nat_rule` / `is_orig_{s,d}nat` now match `Accept` (sound:
`terminal_outcome` returns `Some Accept` for any `r_nat`-set rule regardless of
verdict). Witness: `theories/Snat_Witness.v`; regression gate: `e2e.sh` §B3. All
three headline theorems stay `Closed under the global context`; corpus 2532/2532,
validate 28/28, semtest/parse-test/e2e green.

Original plan (for reference):

`nft -o` merges adjacent `snat` rules into a bare map exactly like `dnat`; we only
do `dnat`. Reuse the `Optimize_Dnat.v` machinery verbatim with `nat_snat_kind` and
the SOURCE address slot:

- `orig_snat_rule` / `mk_snat_rule` (or generalise `Optimize_Dnat` over the kind),
  `snat_imm_spec` / `snat_map_spec` (kind = `nat_snat_kind`).
- The verdict merge (`eval_rules_*_merge`) is identical (terminal Accept +
  NFT_BREAK-on-miss); the data-plane `apply_nat` correctness uses `nat_is_src=true`
  (source slot) — `apply_nat_tuple`/`nat_orig_addr` already handle src via
  `nat_addrfamily`/`nat_is_src`, so the `_indep` lemmas carry over.
- Recogniser `snat_merge_pair`, pass `optimize_rules_snat`, env-threaded
  `optimize_rules_snat_eval`, chain wrapper, output-freshness lemmas, compose into
  `optimize_table` (as a stage right after `dnat`, on the same first-stage/empty
  reasoning), re-prove the gen theorem, extract, semtest, and
  **differentially check against `nft -o` on `snat`-map rulesets.**
- Consider generalising `Optimize_Dnat` to a shared `Optimize_Nat` parametric in
  the kind rather than copy-pasting, if it keeps the proofs clean.

## G2 — concat keys with meta-dependent transport fields  ✅ DONE (theories/Optimize_ConcatM.v)

Landed: a new verified pass `Optimize_ConcatM.v` (composed into `optimize_table`
right after `concatN`, before `vmapN`).  The frontend lowers `ip saddr X tcp dport Y`
to the THREE-item body `[MCmp ip_saddr X; MCmp meta_l4proto 6; MCmp tcp_dport Y]` — the
l4proto guard sits BETWEEN the two selectors, so `head_value2`/`concatN` never see two
adjacent selectors and under-consolidate.  `concatM` recognises the guarded run

    [ MCmp f1 CEq a_i ; GUARD ; MCmp f2 CEq b_i ] ++ rest   (GUARD = MCmp l4proto proto)

and folds it into ONE `[ GUARD ; MConcatSet [f1;f2] false __setN ] ++ rest` — the guard
HOISTED to the head, matching nft -o's netlink (`[ meta load l4proto ][ cmp ]` precedes
the `[ lookup ]`).  The guard is kept ABSTRACT in every lemma (guard-agnostic) and pinned
to `guard_ok` (l4proto) only in the recogniser for firing precision.  Verdict-preservation
REUSES `eval_rules_run_collapse` + `concat_two_fields_certificate_N` VERBATIM — the guard
is a pure conjunctive match, transparent to loadability/outcome and factored out of the
run-collapse `existsb` by boolean algebra (`existsb_guard_factor`, discharged by `btauto`).
The gen theorem `optimize_table_correct_uncond_gen` is re-proved with the 8th stage
(new `optimize_chain_concatN_fresh_setname` + `concatN_keys_bound` thread setname-freshness
past concatN into concatM).  All three headline theorems stay `Closed under the global
context`; corpus 2532/2532, validate 28/28, semtest/parse-test/e2e green.

Fires end-to-end: `nftc optimize` collapses `ip saddr 1.1.1.1 tcp dport 22 accept /
ip saddr 2.2.2.2 tcp dport 80 accept` → ONE `ip saddr . tcp dport { 1.1.1.1 . 22,
2.2.2.2 . 80 } accept` lookup (l4proto guard at head, saddr@reg1, dport@reg9) — BYTE-
FAITHFUL to `nft --optimize`'s netlink (confirmed in a netns; N-way runs fold too, and
tcp-vs-udp rulesets correctly do NOT cross-merge, matching nft; no nft bug found).
Witness: `theories/Concatm_Witness.v` (Compute + `concatm_fires` Example); regression
gate: `e2e.sh` §B4.

## G3 — interval / range set consolidation  ✅ DONE (theories/Optimize_Ivset.v)

Landed: a new verified pass `Optimize_Ivset.v` (composed into `optimize_table`
right after `concatM`, before `vmapN`).  It recognises a run of adjacent rules
whose differing head is a positive range `MRange f false lo_i hi_i` over the SAME
field/body/verdict and folds the WHOLE run into ONE `MConcatSet [f] false __setN`
lookup over an INTERVAL set holding the intervals `[(lo_1,hi_1); …; (lo_N,hi_N)]`
directly in `sd_sets` — exactly what `nft --optimize` emits
(`ip saddr { 10.0.0.0-10.0.0.255, 10.0.2.0-10.0.2.255 } accept`, set flags
ANONYMOUS|CONSTANT|INTERVAL; netns-confirmed vs host `nft` v1.1.6).

Verdict-preservation is CLEANER than the point-set pass: an `MRange`'s value test
is `data_le lo x && data_le x hi = data_in_iv x (lo,hi)` and a single-field
`MConcatSet`'s membership is `set_mem x = existsb (data_in_iv x)`, so the merged
head is EXACTLY the `existsb` disjunction of the run's ranges — with NO fixed-width
side-condition (`data_le` does not truncate, unlike `MCmp`'s prefix equality).  The
new certificate `concat_set_ivs_existsb` feeds `eval_rules_run_merge_abs`
(Optimize_Merge) VERBATIM.  The gen theorem `optimize_table_correct_uncond_gen` is
re-proved with the 8th stage (new `optimize_chain_concatM_fresh_setname` +
`optimize_chain_ivset_*` seam lemmas thread setname/vmap freshness past concatM into
ivset and on to vmapN).  All three headline theorems stay `Closed under the global
context`; corpus 2532/2532, validate 28/28, semtest/parse-test/e2e green.

Fires end-to-end: `nftc optimize` collapses two `ip saddr <lo>-<hi> accept` rules
into ONE interval-set lookup — faithful to `nft --optimize` (the `nftc`/glue
set-dump renderer was fixed to print genuine intervals `lo-hi`, points `lo`).
Witness: `theories/Ivset_Witness.v` (`ivset_fires` + `ivset_table_fires` Examples);
regression gate: `e2e.sh` §B5.  No nft bug: nft merges same-verdict ranges into an
interval set identically, uses an interval VMAP for DIFFERENT-verdict ranges (our
ivset correctly ABSTAINS there — see below), and does not coalesce contiguous ranges
(matching us).

Deferred (principled, not laziness): (1) **prefix** heads `ip saddr 10.0.0.0/24`
lower to `MMasked` (`(field & mask) == net`), NOT `MRange`; folding them needs the
contiguous-mask↔interval `[net, net|~mask]` arithmetic lemma over big-endian
`data_le`, a strict extension on top of this pass.  (2) **interval VMAP**
(different-verdict ranges) — nft emits `ip saddr vmap { lo-hi : accept, … }`; that is
the range analogue of the `vmapN` pass (Optimize_Vmap), a separate extension.
Neither is an nft bug; both build cleanly on this pass.

## D1 — `mapN` (`meta mark set … map`) fidelity divergence  ✅ RESOLVED

Landed (honest-contract resolution, kept axiom-free/green): the `mapN` divergence
is RESOLVED as an **intentional, necessary, labelled sound superset** — NOT an nft
bug, NOT an overstated fidelity claim. Backed by a committed `nft -o` differential
+ live-kernel witness and a machine-checked pin.

Ground truth (differential, `nft` v1.1.6 + kernel netns; gate `e2e.sh` §B6):
- `nft --optimize` does **NOT** merge `meta mark set` at all (no `Merging` output).
  So `mapN` has **no `nft -o` counterpart** — there is no bare form of *its* output
  to be byte-faithful to. `nft -o` is merely conservative; not a bug.
- The maps `nft -o` DOES emit (dnat/snat, **bare**) are already matched by
  `Optimize_Dnat`/`Optimize_Snat` (§B3).
- **Kernel witness** (netns, `hook output`, key `ip daddr`): a BARE statement
  value-map BREAKs on miss — an off-key packet keeps its prior mark (sentinel
  `0xdead` survives), an on-key packet gets the mapped value. So a bare merged form
  is kernel-equivalent to the two originals; the divergence between our GUARDED
  output and the (hypothetical) bare form is a pure **model artifact** (our
  `body_writes` on `SMetaSet _ (VMap …)` loads `map_lookup_data`'s default on a
  miss instead of NFT_BREAKing, `Bytes.v:43`).

Verified pin (axiom-free, `theories/Optimize_Mapn.v`): `mapn_bare_diverges_offkey`
+ `dsl_step_bare_offkey`/`dsl_step_orig_pair_offkey` prove that, off-key, the
guard-less ("bare") rule CLOBBERS the mark to the default `[]` while the two
originals are a no-op — so the head-set guard (= the map's key domain) is a
soundness necessity of THIS model, recovering exact equivalence
(`eval_rules_mut_map_merge`, already proven; semtest also exercises the off-key
miss). The fidelity contract is made precise in `optimize_table`'s docstring
(`Optimize_Table.v`): every stage EXCEPT `mapn` is `nft -o`-faithful; `mapn` is a
labelled sound superset outside the byte-fidelity claim.

**Why not the "bare" (preferred) form?** (principled, not laziness) Making `mapn`
bare needs NFT_BREAK-on-miss for the statement value-map in BOTH `body_writes` and
the compiler (route `SMetaSet`+`VMap` through `ILookupValBr`). The bytecode renders
identically (`codec.ml` `ILookupValBr` ≡ `ILookupVal`), and the *verdict* side is
insensitive (a `Continue` rule; `eval_rules` ignores `rule_loadable` for it) — BUT
it breaks the "value sources are verdict-neutral / reach the tail" invariant
(`Correct.run_vsrc_exists`) that the `compile_chain_correct` HEADLINE theorem is
built on, cascading across every `SMangle`/`SMetaSet`/`SCtSet` arm. That is a
change to a headline theorem for **zero `nft -o` fidelity gain** (nft never merges
`meta mark`). Deferred as a standalone core-semantics fidelity upgrade (kernel
break-on-miss for statement value-maps), which would benefit all such statements,
not just `mapn`.

Original analysis (for reference):

Adversarial review vs `nft v1.1.6` found: (1) `nft -o` does **not** merge
`meta mark set` at all, and (2) the maps it DOES emit (dnat/snat) are **bare**
(no head guard). Our `mapN` emits a **head-set-guarded** map — sound in our model
(a statement-map miss loads the lookup default rather than NFT_BREAK), but not
`nft -o`'s output.

Decide and implement ONE of:
- **(preferred) Make `mapN` bare** using the same NFT_BREAK-on-miss machinery the
  `dnat` pass uses: give the statement value-map lookup a breaking variant so a
  miss skips the write soundly, drop the head-set guard, and match `nft -o`'s form
  for the maps `nft -o` actually emits — *and* only fire `mapN` where `nft -o`
  would (do not consolidate `meta mark set` if that diverges from nft; or keep it
  as an explicitly-labelled *sound superset* pass, off by default in the
  nft-`-o`-fidelity mode).
- **(or) keep the guarded form but label it honestly** as a sound consolidation
  that is NOT `nft -o`-faithful, and gate it so the shipped `optimize_table`'s
  claim of `nft -o` fidelity is not overstated. The current headers already say
  this; make the pipeline's fidelity contract precise.
Whatever is chosen, back it with a `nft -o` differential test that documents where
we match and where we intentionally diverge (and whether the divergence is a
soundness necessity or an nft bug).

---

## Cross-cutting: differential-test the whole pipeline vs `nft -o`

Add a gate (mirroring `difftest.sh`/`e2e.sh`) that, for a battery of rulesets,
runs both **our** `optimize_table_uncond` and **`nft --optimize`**, compiles both
to bytecode, and compares — flagging (a) where we under-consolidate (our gap), and
(b) where `nft -o`'s output is *semantically* different from the input (an nft
bug, confirmed against the kernel). This is the harness the adversarial reviewer
uses to prove each gap is genuinely closed and to catch nft bugs.
