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

## G3 — interval / prefix set consolidation  (capability gap)

`nft -o` collapses several adjacent ranges/prefixes (`ip saddr 10.0.0.0/24`,
`10.0.1.0/24`, ranges `a-b`) into a single **interval set**. We fold distinct
POINT values (`setsN`) and simplify a singleton range to `cmp`, but there is no
pass that consolidates multiple ranges/prefixes into one interval set.

- Add an interval-set pass: recognise a run of adjacent rules whose differing head
  is an `MRange`/prefix (`MMasked` for `/n`) over the same field + same body/verdict,
  emit a single `lookup @s` over an interval (`NFT_SET_INTERVAL`) set, writing the
  intervals into `sd_sets`. The `Optimize_Merge` disjunction machinery already
  instantiates over `MRange` (`concat_set_two_points` / `eval_rules_merge2` with
  `m1 = MRange …`) — build on it.
- The interval set's element/flag encoding (`NFT_SET_INTERVAL`, the start/end
  element pairs) must match what `nft` emits — validate against `nft -o` + a
  netns/VM kernel load (`nft list ruleset`).
- Prove verdict-preservation (a packet is in the interval set iff some original
  range/prefix matched) and compose into `optimize_table`.

## D1 — `mapN` (`meta mark set … map`) fidelity divergence  (resolve)

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
