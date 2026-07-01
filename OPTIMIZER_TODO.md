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

## G1 — `snat to … map { … }` bare-map merge  (capability gap; highest value, lowest risk)

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

## G2 — concat keys with meta-dependent / non-fixed-width fields  (capability gap)

`Optimize_ConcatK`/`Optimize_Concat` fold a concat key only from **fixed-width
PAYLOAD** fields (`field_fixed_len = Some`). A key that includes a transport field
like `tcp dport` (which carries an implicit `l4proto == tcp` guard, and whose load
is gated on that meta match) is NOT folded — so `ip saddr . tcp dport { … }`
rulesets are only partially consolidated. `nft -o` folds these.

- Model the transport field's `l4proto` dependency faithfully: the concat key
  element is the transport field guarded by the L4-proto match; the merged
  `MConcatSet`/set element must carry both. Establish the per-field
  loadable+width facts under the guard (the concat correctness needs each field's
  width to split the concat back — a transport field IS fixed-width once the proto
  is fixed).
- Extend the recogniser + the width/loadability certificates
  (`Optimize_ConcatK`'s `Forall2 field_fixed_len` machinery) to admit the guarded
  transport fields; keep the register-slot padding correct.
- Verify verdict-preservation and **byte-fidelity against `nft -o`** on real
  `… . tcp dport` rulesets (these are common in the corpus's nat/set tests).

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
