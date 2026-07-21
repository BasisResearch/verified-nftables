# THEOREMS.md — the claim surface, mapped

What exactly is proved, by which theorem, under which evaluator, and is it
axiom-free — without reading 3000 lines of `Correct.v`.

- Machine-checked entry-point restatements: [`theories/Compiler/Main.v`](theories/Compiler/Main.v)
  (each followed by `Print Assumptions`).  Main.v also carries the
  **pre-split ratchet corollaries** (`pre_split_*`): every pre-state-split
  headline statement — which quantified over ONE packet record bundling the
  shared world — restated over the bundled pair `Packet.pstate`
  (`ps_env`/`ps_wire`), each an `exact`/`apply` of its post-split successor.
- Axiom gate: `make axioms` re-checks every HEADLINE theorem below (plus the
  supporting strata, the `Lower_Proofs.*_erasure` family, the representation
  ratchet `Semantics.run_rule_outcome_eq`, **and every result the README
  claims axiom-free** — anti-spoofing, established-accept, NAT-masquerade,
  multi-address, fib host-local, ct-state; see §4) from the compiled `.vo`
  files and fails on anything but `Closed under the global context`.
- Classes used below:
  - **HEADLINE** — the single top theorem of a verified axis; what the project claims.
  - **STAGE** — a per-pass/per-stage theorem composed into a headline.
  - **SUPPORTING** — a stratum or bridge a headline is derived from (or that
    scopes one); not independently a claim.
  - **SUPERSEDED** — kept for history; subsumed by a successor named in its marker.
  - **DEMO** — an executable regression pin / witness (`Example` in the source);
    not part of the claim surface.
- Where things live: `theories/` is split by trust role — `Core/` (bytes,
  verdict, packet, bytecode), `IR/` (rule IR + typed view + elaboration),
  `Semantics/`, `Compiler/` (compiler, strata, `Main.v`, extraction),
  `Optimizer/` (+ `Optimizer/Witness/` fires-witnesses), `Regression/`
  (invariant-named kernel-behaviour gates), `Examples/` (worked
  per-configuration proofs), `Generated/` (`nft2coq` output).  See
  `DEVELOPMENT.md` § "What exists" for the full table.

## 1. The entry points — exactly one top theorem per verified axis

| axis | HEADLINE theorem | file | what it says |
|---|---|---|---|
| compiler (rulesets/hooks) | `compile_hook_correct` | `Correct.v` | compiled hook dispatch (jump/goto/return, user chains, multi-table, priority order) = DSL `eval_hook`, for every fuel/ruleset/hook/packet/environment |
| sequence semantics / cross-packet carry | `compile_seq_hook_correct` | `Correct.v` | the between-packet env is **definitionally the ruleset's OWN env-out** (`seq_eval_env` over `eval_hook_env_u` / `run_ruleset_env_u`, the fst-of-state projections of the unified hook run — no external step function can be instantiated): dynset adds, limiter depletion and NAT mappings thread packet-to-packet through jumps and multi-chain/hook dispatch, compiler-preserved under `base_numgen_free` (discharged for every frontend program by `Lower_Proofs.lower_ruleset_numgen_free`); cross-packet pins `Regression/Seq_Hook_Carry.v`. Successor of the RETIRED external-step `compile_seq_correct` (strata-retirement note, §3) |
| mutation / cross-packet learning | `compile_seq_mut_correct` | `Correct.v` | compiled single-chain traversal threading the env each packet LEAVES (meta/ct writes, dynset learning) = DSL sequence, under `rule_numgen_free` (discharged for EVERY frontend program by `Lower_Proofs.lower_ruleset_numgen_free`) |
| optimizer pipeline | `optimize_table_uncond_compile_correct` | `Optimize_Uncond.v` | the shipped 18-stage `nft -o` pipeline + the DEFAULT compile (`compile_chain_default`) preserves every packet's verdict against the synthesised declarations, for **any input chain** (no `rules_clean`, no freshness precondition) |
| optimizer pipeline, EFFECT level | `Optimize_MutEnv.optimize_table_uncond_mut_st_correct` | `Optimize_MutEnv.v` | the same shipped pipeline under the FULL-STATE effect-observing `eval_chain_mut_st h`: for **any input chain**, at every hook/base env/packet, the optimised chain in the deployed environment yields the SAME verdict **and** the SAME resulting `(env, packet)` pair as the input — a stage can no longer preserve verdicts while altering an env-half write (dynset learning, limiter depletion, NAT mapping) **or** a packet-half write (`meta mark set`, ct set — pinned: the env-only observable is provably blind to `[meta mark set 0x1]` vs `[]`, `mutst_pin_mut_env_blind`/`mutst_pin_distinguishes`); the `(verdict, env)` form `optimize_table_uncond_mut_env_correct` survives only as a projection corollary. Jump scope: `eval_chain_mut_st` is the flat fold (callees of jump-bearing chains are skipped) — see the scope note below |
| DEFAULT compile pipeline | `Optimize_Linearize.compile_chain_default_correct` | `Optimize_Linearize.v` | the DEFAULT pipeline `compile_chain_default = compile_chain ∘ elide_chain ∘ xorfold_chain ∘ paymerge_chain` — nft's ALWAYS-ON netlink linearization (classes I + L, including the trivial-binop deletion) — yields exactly the source chain's DSL verdict, for every chain/env/packet; stage composition is `linearize_chain_eval`; non-vacuity Compute-pinned (`default_pipeline_merges_payload_loads`, `default_pipeline_folds_xor` — the folded xor now compiles to a bare load+cmp, NO bitwise — and `default_pipeline_elides_trivial_binop`) |
| intra-rule pass: adjacent-payload merge | `Optimize_PayMerge.paymerge_chain_eval` | `Optimize_PayMerge.v` | fusing two byte-contiguous full-width payload equalities in the same header into one wider load+compare (nft `payload_can_merge`; corpus class I) preserves `eval_chain` — **UNCONDITIONAL** (`forall c e p`, no hypotheses): the read and its loadability split at any interior offset for every packet |
| intra-rule pass: bitwise-xor constant fold | `Optimize_XorFold.xorfold_chain_eval` | `Optimize_XorFold.v` | transferring a pure-xor register operand onto the compare value (`(reg & 0xff..) ^ C <op> V  →  ^ 0 <op> V^C`; nft `binop_transfer`; corpus class L) preserves `eval_chain` — **UNCONDITIONAL** (`forall c e p`): bytewise xor is involutive, no width/byte-range side condition. The spent residue is deleted by the next stage (`Optimize_Elide`) |
| intra-rule pass: trivial-binop elision | `Optimize_Elide.elide_chain_eval` | `Optimize_Elide.v` | deleting the spent binop the xor fold leaves — `(reg & 0xff..ff) ^ 0x00` at the field's kernel register width becomes a bare compare, so no bitwise instruction reaches the wire (nft `binop_transfer_handle_lhs`, OP_XOR: the binop is replaced by its left operand; the class-L residue) — preserves `eval_chain` — **UNCONDITIONAL** (`forall c e p`): a register-normalised read is width-pinned AND octet-clamped BY CONSTRUCTION (`Bytes.fit`/`Bytes.octets` at the `do_load` boundary), so the all-ones/zero bitwise is definitionally the identity on it (`Syntax.do_load_bitops_id`) — no width, byte-range or well-formedness hypothesis |
| pass composition | `Optimize_Registry.run_passes_correct` | `Optimize_Registry.v` | ONE generic theorem: folding **any** list of registered `opt_pass`es (each bundling its own eval-preservation proof) preserves `eval_chain`, proved once quantified over the list — the `-O p1,p2,...` CLI only parses names into the list (`resolve_passes`) and folds them (`run_passes`) |
| typed source lowering (**`typed_erasure`**) | the `Lower_Proofs.*_erasure` family (composed: `txmatch_erasure`) | `Lower_Proofs.v` | the verified lowering of a typed source construct produces exactly the byte IR the compiler consumes, with genuine per-construct obligations — `eq_erasure`/`neq_erasure` (register decode at the value's byteorder), `prefix_erasure` (CIDR: both the byte-aligned truncated-load shortening and the full-width masked compare), `wildcard_erasure` (leading-bytes short compare), `range_erasure_be`/`range_erasure_host` (BE vs host-endian range order), `bitmask_erasure`, `bitfield_erasure` (mask+shift), `set_interval_erasure` (byte-interval = numeric membership), `concat_key_erasure` (slot-padding invertibility), `cidr_interval_agrees_prefix_expand` (one CIDR expansion, not two). Since M6 the generated sources (`*_Gen.v`) carry the **surface** ruleset (`<name>_surface : sruleset`) and define every table/chain/decl as `Lower.lower_ruleset` applied to it, kernel-reduced — **no raw byte is written by hand** and a refused construct fails the generated `<name>_lowers_ok` Example (fail-loud) |
| register-file discipline (W2) | `RegsValid_Proofs.lower_ruleset_default_regs_valid` (plain-compile mirror: `lower_ruleset_compile_regs_valid`) | `RegsValid_Proofs.v` | EVERY frontend-emitted program passes the kernel register validator: for every ruleset `lower_ruleset` accepts, every chain's DEFAULT-pipeline bytecode satisfies `RegsValid.regs_valid_prog` — `nft_validate_register_load`/`store` (index arithmetic of `nft_parse_register`, the 20-word/80-byte `struct nft_regs` file, data words 4..19, nonzero lengths, 16-byte `nft_data` values) mirrored per register operand of every `Bytecode.instr` constructor with its per-expression kernel length. Enforced BY CONSTRUCTION: `Lower.lower_rule` admits a rule only if its compiled image validates (fail-loud `LEregalloc`), and all three always-on linearization stages preserve validity from their own guards (`paymerge_rule_regs`, `xorfold_rule_regs`, `elide_rule_regs` — the elision only DELETES a spent instruction). No hypothesis |

Scope notes (each also sits on the theorem in the source):

- **Typed-layer M-D discharge level (`typed_erasure` vs `typed_progress` /
  `typed_source_vm`).** The M-D obligation is discharged at the **per-construct**
  level: `typed_erasure` is realized as the `Lower_Proofs.*_erasure` family (the
  Coq lowering of a typed construct = the byte IR the compiler consumes, with
  real round-trip / slot-padding / BE-range-order obligations — never
  `reflexivity` over an encode-defined term); **fail-loud** is the generated
  `<name>_lowers_ok` Example (an out-of-reach construct is an explicit
  `lower_ok = false`, never a silent OCaml byte); the **typecheck stuck
  witness** lives in `TypedEval.v` (a concrete ill-typed term whose typed
  evaluation is `None`/stuck, with the `Typecheck` gate rejecting it). The
  standalone whole-language `typed_progress` (`well_typed r -> eval_typed r <>
  stuck`) and `typed_source_vm` (typed⇔VM composition) theorems were **descoped
  by the project owner for this run** and are deliberately NOT built — the
  independent whole-language typed evaluator is future work, and the
  per-construct erasure lemmas above are the milestone's declared M-D level.
  `TypedEval.v`'s numeric evaluator stays **independent of the encode path**
  (the `make boundary` gate greps `encode|data_eqb|firstn|eval_matchcond|elab_m`
  in it to `0`).
- The optimizer headline is **per chain**: quantified over a single chain and
  all environments/packets. Multi-chain/hook preservation is the separate
  `compile_ruleset_correct`/`compile_hook_correct` family — **not composed
  with the optimizer**.
- The optimizer is certified at **two observation levels**, both unconditional:
  the VM-run/verdict headline `optimize_table_uncond_compile_correct`
  (`eval_chain`, through the DEFAULT compile) **and** the EFFECT-level headline
  `Optimize_MutEnv.optimize_table_uncond_mut_st_correct` — the same shipped
  pipeline related, at every hook, under the FULL-STATE effect-observing
  `eval_chain_mut_st h`: verdict **and** the resulting `(env, packet)` pair
  the `rule_step` fold leaves, nothing dropped (the `(verdict, env)` form
  `optimize_table_uncond_mut_env_correct` survives as a projection corollary
  via `Semantics.eval_chain_mut_env_st`). A stage can no longer preserve every
  verdict while altering a write a later hook observes — env writes because
  `seq_eval_env` carries them to the next packet, packet writes (e.g. `meta
  mark set`) because `eval_ruleset_u`'s priority dispatch hands the mutated
  packet to the next base chain (precision pin: `Optimize_MutEnv` Part H —
  the `[meta mark set 0x1]` chain and the empty chain are identified by the
  env-only observable but distinguished by the full-state one). Jump scope:
  `eval_chain_mut_st` is the flat fold (`terminal (Jump _) = false` skips the
  callee), so for jump-BEARING chains the guarantee is about that flat
  callee-skipping projection, not `eval_table_u`'s traversal.
  What makes the effect level compose: every pure-merge recogniser carries an
  **effect-safety guard** (`rule_mutfree`, `Optimize_ValueSet.value_merge_pair`)
  so its merges live on the write-free fold projection; the three
  effect-rewriting stages (`datamap`/`dnat`/`snat`) carry fold-level per-shape
  certificates (`Optimize_MutEnv.eval_rules_mut_st_map_merge` /
  `_dnat_merge` / `_snat_merge`); the base pass is effect-safe by construction
  (`dedup_rule` fires only on `rule_mutfree` rules); and `seed_start` now also
  clears every **dynset write target** (`chain_seed` includes
  `rule_dynset_names`), so no rule can clobber a minted declaration.
- **Mutation × jump/goto is jointly verified** at the UNIFIED evaluator
  (`Semantics.eval_rules_u`/`run_rules_u`, compile theorems
  `compile_table_u_correct` / `compile_ruleset_u_correct` /
  `compile_hook_u_correct` / `compile_seq_hook_correct`): one
  effect-threading, jump-following fold per side.  The historical pure jump
  strand (`eval_rules_j`/`eval_table`/`eval_ruleset`/`eval_hook`) and the flat
  mutation strand (`eval_rules_mut*`) survive only as **proven projections**
  of the unified fold on their licensed sub-domains (write-free,
  respectively transfer-free rules) — see the evaluator matrix, §3.
- The mutation/ct axis is **parametric in flow identity**: every ct/NAT
  statement is a congruence over the opaque key `pkt_flow` (and `e_ct`/`e_nat`
  keyed by it). Nothing ties `pkt_flow` to the packet's header bytes — no
  `flow_wf` analogous to `Fib_Local.fibkey_wf` exists yet — so transferring
  these theorems to a real skb assumes an injective direction-normalised
  (tuple + l4proto + zone) canonicalisation. A wrong canonicalisation makes
  them true *about the wrong flow* (two distinct real flows sharing one model
  key would merge their ct marks). Rationale + designated fix: the `pkt_flow`
  comment in `Core/Packet.v`; honest-gaps entry in `DEVELOPMENT.md`.

Known-gaps note: the known-infidelity ledger is EMPTY — all three historical
confirmed divergences are REPAIRED and pinned positively
(`theories/Regression/Known_Infidelities.v`): the limiter sweep past a failing
match and the intra-rule set-then-read (position-exact in the break-aware
fold), and — M3 — the `OVmapNat` vmap-hit trace NAT + spurious `e_nat` store:
the NAT data-plane effect (packet rewrite, flow-keyed `e_nat` establish/reuse,
no-usable-address NF_DROP) now lives INSIDE the single per-rule fold at the
NAT terminal, so a vmap HIT structurally never runs it (outcome provenance),
on BOTH sides — certified by `compile_nat_effect_correct` and the
traversal-level `_u` compile theorems, at every netfilter hook `h` (the fold
and every effect-threading evaluator now carry the hook, because the
redirect/masquerade data plane is hook-dependent).

## 2. Classification of every `Theorem`/`Corollary` in `Correct.v` and `Optimize*.v`

### `Correct.v` (the compiler strata, bottom-up)

| declaration | class | derivation edge |
|---|---|---|
| `compile_chain_correct` | SUPPORTING (stratum 1: one chain, pure verdict) | from `run_program_compile_chain`; consumed by the optimizer headline via `compile_chain_sets_correct` |
| `compile_chain_sets_correct` (Corollary) | SUPPORTING | corollary of `compile_chain_correct` at `env_with_sets`; consumed (via `compile_chain_default_sets_correct`) by `optimize_table_uncond_compile_correct` |
| `compile_chain_mut_correct` | SUPPORTING (stratum 2: + in-traversal mutation) | **derived**: the `fst` projection of stratum 3 (`run_program_mut_env_fst` / `eval_rules_mut_env_fst`), no second induction |
| `compile_chain_mut_env_correct` | SUPPORTING (stratum 3: + env the chain leaves) | from `run_program_mut_env_compile_chain`, one induction over the per-rule step equation `run_rule_step_compile_rule` (`run_rule_step empty_rf (compile_rule r) e p = rule_step r e p` under `rule_numgen_free`) |
| `compile_seq_mut_correct` | **HEADLINE** (mutation/sequence axis) | = `compile_chain_mut_env_correct` + `seq_eval_env_ext` |
| `compile_table_correct` | SUPPORTING (stratum 5: + jump/goto/return) | from `run_eval_rules_j`; consumed by `compile_ruleset_correct` |
| `eval_chain_eq_table_jumpfree` | SUPPORTING (fidelity bridge: `eval_chain` = `eval_table` on jump-free chains) | from `eval_rules_jumpfree_eq_j` |
| `compile_chain_faithful_jumpfree` (Corollary) | SUPPORTING | corollary of `compile_chain_correct` + `eval_chain_eq_table_jumpfree` |
| `faithful_table_jump_drops` (Example) | DEMO (regression pin: a jump into a dropping chain drops) | computes |
| `compiled_table_jump_drops` (Example) | DEMO | instance of `compile_table_correct` |
| `rg_base_not_jumpfree` (Example) | DEMO (the pin's chain is outside `eval_chain`'s faithful domain) | computes |
| `compile_ruleset_correct` | SUPPORTING (stratum 6: + multi-table dispatch) | from `compile_table_correct` per base chain |
| `compile_hook_correct` | **HEADLINE** (compiler axis) | = `compile_ruleset_correct` after pure hook selection/ordering |
| `compile_seq_correct` | **RETIRED** (M4 strata retirement, §3: the sequence congruence under an EXTERNAL caller-supplied step — deleted with `seq_eval`/`seq_eval_ext`; successor `compile_seq_hook_correct`) | — |
| `run_table_fuel_indep_compiled` (Corollary) | SUPPORTING (VM mirror of the M4 fuel-adequacy result, §3) | = `compile_table_correct` (at both fuels) + `Semantics.eval_table_fuel_indep` |
| `run_rules_u_compile` | SUPPORTING (stratum 8 induction: unified fold, rule list) | one induction over `run_rule_step_compile_rule`, jumps included |
| `compile_table_u_correct` | **HEADLINE** (stratum 8, unified axis: mutation × jump, one table) | from `run_rules_u_compile` |
| `compile_ruleset_u_correct` / `compile_hook_u_correct` | **HEADLINE** (stratum 8: + multi-table / hook dispatch, state threaded between bases) | from `compile_table_u_correct` per base chain |
| `compile_seq_hook_correct` | **HEADLINE** (stratum 8: + cross-packet env carry over the unified per-packet run — THE sequence semantics; named `compile_seq_hook_u_correct` until M4 retired the external-step stratum) | = `compile_ruleset_u_correct` + `seq_eval_env_ext` |
| `run_table_writefree_compiled` (Corollary) | SUPPORTING (VM-side projection license: pure `run_table` = `fst` of `run_table_u` on compiled write-free chains) | = `compile_table_u_correct` + `compile_table_correct` + `Semantics.eval_table_u_writefree` |
| `eval_chain_writefree_jumpfree_proj` (Corollary) | SUPPORTING (flat pure strand license, packaged) | = `Semantics.eval_table_u_writefree` + `eval_chain_eq_table_jumpfree` |
| `rg_jump_not_plain` / `unified_strand_jump_drops` (Examples) | DEMO (license-boundary pins beside `mut_strand_jump_pin`) | compute |

### `Optimize.v` / `Optimize_ValueSet.v` (base pass and history)

| declaration | class | note |
|---|---|---|
| `Optimize.optimize_chain_correct` | SUPERSEDED (as a standalone headline) | successor `optimize_table_uncond_correct`; `optimize_chain` survives as the pipeline's base stage and this theorem as that stage's lemma |
| `Optimize_ValueSet.eval_rules_value_merge` | SUPPORTING | 2-adjacent-rule merge certificate behind the `valueset` recogniser lineage |
| `Optimize_ValueSet.eval_rules_range_value_merge` | SUPERSEDED, **known-unfaithful** | models `6,7 => 6-7` as a RANGE where `nft -o` emits the SET `{6,7}`; used by no shipped pass (marker on the theorem) |
| `Optimize_ValueSet.optimize_chain2_correct` | SUPERSEDED | `optimize_chain2` is not composed into the shipped pipeline |

### Per-pass certificates and stages (`Optimize_*.v`)

| declaration | class | note |
|---|---|---|
| `Optimize_Vmap.eval_rules_vmap_merge2` | SUPPORTING | certificate consumed by the `vmap` stage lineage |
| `Optimize_Concat.eval_rules_concat_merge2` | SUPPORTING | certificate for the two-selector concat merge |
| `Optimize_ConcatMulti.eval_rules_concat_mergeK` | SUPPORTING | K-row concat certificate |
| `Optimize_DataMap.eval_rules_mut_map_merge` / `eval_rules_map_merge` | SUPPORTING | mark-map merge certificates (`datamap` stage; a labelled sound superset of `nft -o`, see Optimize_Table.v fidelity contract) |
| `Optimize_DataMap.mapn_bare_diverges_offkey` | DEMO | pins why the head guard cannot be dropped |
| `Optimize_DataMap.optimize_rules_datamap_eval` | STAGE | composed into `optimize_table` |
| `Optimize_Dnat.eval_rules_dnat_merge`, `apply_nat_dnat_eq`, `apply_nat_dnat_merge1` (Cor.) | SUPPORTING | bare-NAT-map merge: verdict + data-plane NAT-effect preservation |
| `Optimize_Snat.eval_rules_snat_merge`, `apply_nat_snat_eq`, `apply_nat_snat_merge1` (Cor.) | SUPPORTING | symmetric snat forms |
| `Optimize_Normalize.normalize_chain_eval` | STAGE | verdict-preserving head normalisation run first by `optimize_table_uncond` |
| `Optimize_Table.optimize_preserves_rules_clean` | **RETIRED** (M6 strata retirement: the whole-rule cleanliness family — the predicate, its env-irrelevance lemmas, this preservation seam, and the dead `Optimize_Table_Inv` ok-predicates — is deleted; nothing consumed it since the UNCONDITIONAL pipeline theorems landed, and its precise successor is the read-freshness generation `Optimize_Uncond.rule_set_fresh`/`rule_vmap_fresh`/`rule_nat_map_fresh`) |
| `Optimize_Uncond.optimize_rules_{dnat,snat}_eval`, `optimize_rules_{valueset,dscp,intervalsethostorder,intervalset,intervalsetguarded,mixedpointrangeguarded,concat,concatguarded,setguarded,concatmulti,vmap,vmapguarded,dscpvmap}_correct_uncond` (15) | STAGE | each tagged `STAGE — composed into [optimize_table_correct_uncond_gen]` in the source |
| `Optimize_Uncond.optimize_table_correct_uncond_gen` | SUPPORTING | the general `(n, d)`-threaded whole-pipeline form |
| `Optimize_Uncond.optimize_table_uncond_correct` | SUPPORTING | DSL-level form of the optimizer headline |
| `Optimize_Uncond.optimize_table_uncond_compile_correct` | **HEADLINE** (optimizer axis) | = `optimize_table_uncond_correct` + `Optimize_Linearize.compile_chain_default_sets_correct` (the DEFAULT compile: always-on paymerge + xorfold + elide, then `compile_chain`) |
| `Optimize_MutEnv.optimize_table_mut_st_correct_uncond_gen` | SUPPORTING | the general `(n, d)`-threaded whole-pipeline EFFECT form: same `eval_chain_mut_st h` result for output and input under the deployed declarations |
| `Optimize_MutEnv.optimize_table_uncond_mut_st_correct` | **HEADLINE** (optimizer EFFECT axis) | the shipped `optimize_table_uncond`, hypothesis-free, under the FULL-STATE effect-observing `eval_chain_mut_st h`: verdict AND resulting `(env, packet)` preserved at every hook/base env/packet (built on the per-stage `optimize_rules_*_mut_st` lemmas, the recogniser effect-safety guards, and the fold-level dnat/snat/datamap shape certificates) |
| `Optimize_MutEnv.optimize_table_uncond_mut_env_correct` | SUPPORTING (corollary) | the `(verdict, env)` view of the full-state headline, via the projection bridge `Semantics.eval_chain_mut_env_st` — kept for the cross-packet (`seq_eval_env`) reading |
| `Optimize_MutEnv.eval_rules_mut_st_{map,dnat,snat}_merge` | SUPPORTING | fold-level effect certificates for the three effect-rewriting merge shapes, at the full-state evaluator (verdict + `(env, packet)` out) |
| `Optimize_MutEnv.optimize_rules_*_mut_st` (15) + `optimize_{chain,rules}_absorb/ctmask_mut_st` + `optimize_chain_mut_st` + `normalize_chain_mut_st` | STAGE | each stage of the pipeline preserved under the full-state `eval_rules_mut_st h`, composed into `optimize_table_mut_st_correct_uncond_gen` |
| `Optimize_MutEnv.mutst_pin_{mut_env_blind,mark_observed,distinguishes}` | PIN | precision regression: `[meta mark set 0x1]` vs `[]` are identified by `eval_chain_mut_env` (packet-blind) but MUST stay distinguished by `eval_chain_mut_st` (the exported packet carries the mark) |
| `Optimize_Linearize.linearize_chain_eval` | STAGE | the always-on linearization (elide ∘ xorfold ∘ paymerge) preserves `eval_chain`; composed into both default-pipeline headlines |
| `Optimize_Linearize.compile_chain_default_sets_correct` (Corollary) | SUPPORTING | `compile_chain_default_correct` at `env_with_sets`; consumed by `optimize_table_uncond_compile_correct` |

## 3. The evaluator matrix

**THE semantics is the UNIFIED evaluator pair** (`Semantics.v` § "The unified
semantics"): DSL `eval_rules_u` / `eval_table_u` / `eval_ruleset_u` /
`eval_hook_u`, VM `run_rules_u` / `run_table_u` / `run_ruleset_u` — one
fuel-bounded fold per side that **threads every state effect** (packet
meta/ct writes, dynset env writes, notrack, position-exact
limiter/quota/connlimit consumption, via the per-rule fold
`rule_step`/`run_rule_step`) **and
follows control flow** (jump/goto/return, user chains, multi-table and
hook/priority dispatch), returning verdict AND the `(env, packet)` the
traversal leaves; cross-packet env carry is `seq_eval_env` over
`eval_hook_env_u` / `run_ruleset_env_u`.  A jumped-to chain sees the caller's
accumulated writes; the callee's writes persist into the resuming caller
(witness pins: `Regression/Setread_UnderJump.v`).  Compile theorems: stratum
8 in §2.

Every OTHER entry point is a **projection** of the unified fold, licensed by
a coincidence theorem on the sub-domain where it provably agrees — never an
independent semantics for a rule to be evaluated through.  An input outside
a projection's licensed sub-domain must be evaluated on the unified
evaluator.  (Strata retirement note, U1: no evaluator was deleted in U1 — the
historical strata keep their names, statements and theorems verbatim — but
their *status* changed from parallel semantics to licensed projections; the
successor for every out-of-domain input is the unified `_u` family.)

**Evaluator consolidation (M6): exactly ONE recursive rule-list/jump
traversal per side** — the Fixpoints `eval_rules_u` (DSL) and `run_rules_u`
(VM).  Every other entry point is now a NON-RECURSIVE `Definition`: the pure
strand (`eval_rules`, `run_program`) and the dispatch layers (`eval_ruleset`,
`run_ruleset`, `eval_ruleset_u`, `run_ruleset_u`) are stdlib folds; the
fueled pure jump strand (`eval_rules_j`, `run_rules_j`) is a `nat_rect` on
the fuel; the flat mutation strand is ONE full-state fold per side
(`eval_rules_mut_st` / `run_program_mut_st`, `fold_left` of
`rule_step`/`run_rule_step` with an absorbing stopped accumulator) of which
`eval_rules_mut(_env)` / `run_program_mut(_env)` are **projections BY
DEFINITION** — the in-strand bridges are `reflexivity`-level, not re-proved
inductions.  Names, statements and values are UNCHANGED: each conversion
carries `_nil`/`_cons` (or `_0`/`_S`) unfolding equations restating the
historical recursion verbatim, and every pre-existing theorem survives as
stated.  (`run_program_mut_st` is new — the VM twin of `eval_rules_mut_st`,
added so the VM projections have the same definitional source.)

| projection (DSL + VM mirror) | licensed sub-domain | coincidence equation |
|---|---|---|
| `eval_rules_j`/`eval_table` (VM `run_rules_j`/`run_table`) | write-free rules everywhere: `rule_writefree` (no meta/ct set, dynset, notrack, limiter/quota/connlimit) on the entry list, `chains_writefree` on the chain env | `eval_rules_u_writefree`: `eval_rules_u fuel cs rs e p = (eval_rules_j fuel cs rs e p, (e, p))`; table form `eval_table_u_writefree`; VM form `Correct.run_table_writefree_compiled` |
| `eval_rules_j`/`eval_table`/`eval_hook` (limiter-tolerant extension, Semantics.v § Projection 1b) | limiter-tolerant configs: every rule `rule_limiter_tol` = write-free OR a `rule_one_limiter` rule (match-only body whose ONE non-consume-free match is a tolerable limiter — non-inverted `limit`/`quota` or any `connlimit` — in last position, under a static terminal verdict); entry list + `chains_limiter_tol` on the chain env | VERDICT projection only (the unified run's bucket IS depleted): `eval_rules_u_limiter_tolerant`: `fst (eval_rules_u fuel cs rs e p) = eval_rules_j fuel cs rs e p`; table form `eval_table_u_limiter_tolerant`; single-base hook form `eval_hook_u_limiter_tolerant_1` — every fuel/env/packet, jumps, gotos and chain re-entries included |
| `eval_ruleset`/`eval_hook` (VM `run_ruleset`) | write-free bases (`bases_writefree`) | `eval_ruleset_u_writefree` / `eval_hook_u_writefree` |
| `eval_rules`/`eval_chain` (VM `run_program`/`run_chain`) | write-free **and** jump-free | `eval_rules_u_writefree` + `eval_rules_jumpfree_eq_j`; packaged as `Correct.eval_chain_writefree_jumpfree_proj`; ENTRY-STATE-FREE form (M6): the SYNTACTIC `chain_jumpfree_syn` (no (env, packet) in the hypothesis; implication `rules_jumpfree_syn_sound`/`chain_jumpfree_syn_sound`) packaged as `Correct.eval_chain_writefree_jumpfree_syn_proj` |
| `eval_rules_mut_st`/`eval_chain_mut_st` — full state — and its projections `eval_rules_mut(_env)`/`eval_chain_mut(_env)` (VM `run_program_mut(_env)`) | transfer-free rules: `rule_plain` (no realisable Jump/Goto/Return under the run's verdict maps — step-threaded: rule writes provably cannot touch `e_vmap`, `rule_step_vmap`) | `eval_rules_u_mut_st_proj`: `eval_rules_u fuel cs rs e p = eval_rules_mut_st rs e p` (whole verdict × (env, packet) triple); table form `eval_table_u_mut_st_proj`; component forms `eval_rules_u_mut_proj`/`eval_table_u_mut_proj`; in-strand bridges `eval_rules_mut_env_st` (`_env` = (fst, fst∘snd) of `_st`) and `eval_rules_mut_env_fst` |
| `rule_applies(_walk)`/`outcome`/`rule_loadable` (per-rule bools) | write-free rule (`rule_mutfree`: no mutating statement AND no limiter match — evaluating a limiter writes its bucket) | `rule_step_mutfree` |
| `rule_applies_walk` alone (the body walk, NOTRACK ADMITTED — its `set_untracked` threading is the SAME transform `body_step`'s `SNotrack` case applies, not a parallel semantics) | `body_purewalk` bodies (consume-free matches, non-mutating statements, `notrack` allowed) that load (`body_loadable_walk`) | `rule_purewalk_ok` (M6): the walk = the break/no-break projection of `body_step` |
| `run_rule`/`run_program` (per-rule pure VM) | `no_writes` programs (no mutating/limiter/incremental-numgen instruction) | `Correct.run_rule_step_no_writes` |
| (`seq_eval` — RETIRED, M4: the sequence combinator over an EXTERNAL caller-supplied step; successor `seq_eval_env` below) | — | — |
| `seq_eval_env` | generic in its per-packet evaluator; THE sequence semantics is its instantiation with the ruleset's own env-out `eval_hook_env_u` | `compile_seq_hook_correct` (unified), `compile_seq_mut_correct` (flat) |

**License coverage of the shipped example configs** (the `Nft_Tactics`
surface `nft_yields` is stated over the `eval_table` projection;
`nft_yields_unified` upgrades any statement to the unified semantics once the
one-`reflexivity` check `nft_writefree` holds): `tutorial.nft`
(`Tutorial_Proofs.tutorial_license`), `ruleset.nft`
(`Ruleset_Verified.firewall_inbound_license`), and the optiplex `vmfilter`
bridge table (`Optiplex_Antispoof.vmfilter_output_license`) are
Compute-verified write-free, so every `eval_table` theorem about them IS a
theorem about the unified semantics.  The router `global` table contains ONE
limiter rule (`inbound_private`'s `limit rate 5/second`), whose bucket
depletion is an env write — outside `rule_writefree` — and it is licensed by
the LIMITER-TOLERANT projection (the table row above): the config is
Compute-verified `chains_limiter_tol`, so every `Router_*` /
`Nft_Demo_Concrete` pure-strand statement is a proven VERDICT projection of
the unified semantics — per-file license instances
`Router_Input.inbound_licensed` / `Router_Input.router_rules_licensed` /
`Router_Forward.forward_licensed` (+ the `bug_*` mutation-kill envs) /
`Router_Private.private_rules_licensed` /
`Router_Hooks.input_hook_licensed`/`forward_hook_licensed`
(+ the swapped-registration bug) / `Router_Realistic.*_licensed_real` /
`Nft_Demo_Concrete.demo_dns_accepted_unified`/`demo_smtp_denied_unified`,
all axiom-gated.  **Since M3 a NAT-terminal rule is a WRITE** (packet rewrite
+ `e_nat` store + possible NF_DROP inside the fold), so a chain environment
CONTAINING the masquerade chain is genuinely outside every pure-strand
license (an env whose vmap jumps into it diverges: pure Accept vs kernel
Drop on an address-less interface); the router licenses are therefore stated
over the NAT-free chain restriction `Router_Input.global_tol_chains` /
`Router_Hooks.global_tol_hooks`, the historical `postrouting_hook_licensed`
(the masquerade hook as a pure projection) is RETIRED — successor: the
unified statements `Router_Hooks.postrouting_hook_unified` +
`Router_NatHook.postrouting_hook_verdict_trichotomy` — and the demo cruxes
are recomputed against `eval_table_u` at EVERY hook over the FULL chain env.
The effectful optiplex `filter`/NAT chains were
never evaluated through the pure strand — their proofs use the unified fold
(`eval_chain_u`, `Optiplex_Mark`, `Router_NatHook`, `Router_Reach`).

**Fuel adequacy (RESOLVED, M4 config-proof soundness; RESTATED, M6)**: the
jump strand is fuel-bounded, and `eval_table` maps fuel EXHAUSTION to the
chain policy — a verdict the kernel can never produce (nft rejects jump
loops at load time; kernel jump stack is 16 deep, `NFT_JUMP_STACK_SIZE`).
Naive fuel monotonicity (`eval_rules_j fuel = Some v -> eval_rules_j (S
fuel) = Some v`) is **false** — machine-refuted by
`Semantics.eval_rules_j_not_naively_monotone` (an under-fueled callee's
exhaustion reads as fall-through and more fuel flips the verdict).  The
honest results (Semantics.v § "Fuel discipline for the jump strand"): above
the computable `sufficient_fuel cs rs`, under the `chain_ranked` acyclicity
witness, the verdict is fuel-independent — proved by ONE direct rank-descent
induction (`eval_rules_j_fuel_indep_aux`: at adequate fuel, a jump's callee
and the resumed caller are each adequately fueled, so no branch can exhaust)
— `eval_rules_j_fuel_indep` / `eval_table_fuel_indep`, and the policy
fallback is genuine fall-through: a `None` at adequate fuel persists at
EVERY adequate fuel, which exhaustion (curable by more fuel) cannot
(`eval_table_policy_is_fallthrough`).  **The unified evaluator carries the
same discipline itself** (M6, § "Fuel discipline for the unified
evaluator"): no effect writes the verdict maps (`rule_step_vmap` /
`eval_rules_u_vmap`), so the `rule_step`-level rank witness `chain_ranked_u`
— stable under every state the traversal can reach — gives
`eval_rules_u_fuel_indep` / `eval_table_u_fuel_indep` (verdict AND state),
with `chains_plain_ranked_u` discharging the witness by computation for
transfer-free environments; effectful configs are inside the adequacy story,
not carved out of it.  (STRATA RETIREMENT, M6: the exhaustion-observable
TWIN evaluator `eval_rules_jx` — a third recursive jump traversal — and its
Kleene layer `eval_rules_jx_agree`/`eval_rules_jx_monotone`/
`eval_rules_jx_stable`/`eval_rules_jx_adequate`, plus the jx-witnessed
`eval_rules_j_fuel_stable`, are DELETED; successors are the direct
`eval_rules_j_fuel_indep(_aux)` at the pure strand and
`eval_rules_u_fuel_indep(_aux)` at the unified semantics.)  Compiled mirror:
`Correct.run_table_fuel_indep_compiled` (via `compile_table_correct`; no
second VM development — rationale on the corollary).  User surface:
`Nft_Tactics.nft_*_fuel_indep`, CONFIG_PROOFS.md § "Choosing the fuel
budget", worked instance `Tutorial_Proofs.tutorial_blocks_exactly_any_fuel`.

**Mutation × jump/goto is jointly verified** (U1): the unified evaluator
threads writes THROUGH control transfers on both sides, its compile theorems
(stratum 8, §2) hold for effectful rules under jumps/multi-chain with no
hypothesis excluding any effect or control-flow shape, and
`Regression/Setread_UnderJump.v` Compute-pins the behaviour (`meta mark set
0x1; meta mark 0x1; accept` ACCEPTS inside a jumped-to chain, on DSL and VM;
caller writes visible in the callee; callee writes surviving the return;
dynset learning across a jump).  The flat mutation theorems still carry **no
jump-freedom hypothesis** — they are unconditional DSL=VM agreement facts
that DO instantiate on a jump-bearing chain, where both sides treat the
realised `Jump`/`Goto` as a fall-through; their *faithful* domain is now
delimited **in-theorem** by the projection license `eval_rules_u_mut_proj`
(the step-threaded `rule_plain` predicate), with the license boundary pinned
by `Correct.mut_strand_jump_pin` / `rg_jump_not_plain` /
`unified_strand_jump_drops` (rationale block on the mutation strata in
`Correct.v`).

The bytecode VM mirrors the DSL rows one-for-one (`run_rule(s)`,
`run_program(_mut,_mut_env)`, `run_rules_j`/`run_table`, `run_ruleset`); each
compile theorem in §2 equates one DSL row with its VM mirror.  The VM mirror of
the `fst` bridge is `run_program_mut_env_fst` / `run_chain_mut_env_fst`.

Every mutation evaluator consumes the per-rule STEP function directly —
ONE left-to-right fold per rule, `Semantics.rule_step h` (DSL) /
`Semantics.run_rule_step h empty_rf` (bytecode), evaluated AT a netfilter
hook `h` (Semantics § Section AtHook; the terminal NAT data plane is
hook-dependent) — modelling exactly the
kernel's expression walk (nf_tables_core.c `nft_rule_dp_for_each_expr`):
every expression (match, statement operand, verdict-map key, limiter check)
sees the writes — packet-local meta/ct sets AND dynset env writes AND the
`limit`/`quota`/`connlimit` bucket consumption of an earlier limiter (the
kernel writes the bucket on every evaluation, pass or exhausted:
`body_step`'s `match_consume` / `run_rule_step`'s limiter cases) — of the
expressions BEFORE it in the SAME rule; a failing match or breaking load
stops the walk KEEPING the earlier writes (so a limiter AFTER the break is
never evaluated and never consumes); a statement after a terminal verdict
never runs; the post-outcome (`r_after`) statements run (writes included)
only on a `Continue` fall-through.  A dnat/snat/masquerade/redirect terminal
performs its DATA-PLANE effect in the fold at the position the walk reached
it: the kernel NAT core's no-usable-address NF_DROP (`nat_drops`), else the
flow-keyed tuple establish/reuse + packet rewrite (`apply_nat`), then
terminal Accept — a vmap HIT stops the rule before the terminal, so it never
runs the NAT (outcome provenance; positive pins
`Known_Infidelities.vmaphit_*`/`vm_vmaphit_*`).  On the VM side only, the fold also
advances the `numgen inc` counter at its `INumgen` instruction (the DSL
deliberately has no numgen surface; the lowering rejects it fail-loud).

The DSL/VM agreement obligation is the one per-rule equation
`run_rule_step_compile_rule : rule_numgen_free r = true ->
run_rule_step h empty_rf (compile_rule r) e p = rule_step h r e p` (`Correct.v`;
restated under its NAT-effect name as the headline
`compile_nat_effect_correct`;
degenerate zero-field operands included — `Compile.compile_vsrc` pins their
source register).  `rule_numgen_free` (IR/Syntax.v) is the strand's ONLY
hypothesis, and it is discharged by THEOREM over every frontend-emitted
program: `Lower.lower_rule` refuses incremental numgen fail-loud
(`LEnumgen`), and `Lower_Proofs.lower_ruleset_numgen_free` proves every
chain of every successful lowering numgen-free — not a per-ruleset gate
spot-check.

**Strata retirement (M2 in-fold limiter/numgen).**  The historical per-rule
boundary wrappers `Semantics.dsl_rule_step` / `Semantics.vm_rule_step` — the
fold plus an UNCONDITIONAL whole-body `limit_sweep_body`/`limit_sweep_prog`
(+ VM `numgen_sweep_prog`) applied at the step boundary, the source of
known-infidelity entry 1 (a limiter after a failing match was drained; the
kernel `NFT_BREAK`s first) — are RETIRED; their successor is the fold pair
`rule_step` / `run_rule_step empty_rf` itself, with the consumption
evaluated at each limiter's own body/instruction position (break-aware,
kernel-exact) and the VM `numgen inc` advance at its `INumgen` instruction.
With them retire: the sweeps (`limit_sweep_body`/`limit_sweep_prog`/
`numgen_sweep_prog`) and their identity lemmas, `limit_free_body`/
`limit_free_prog` (subsumed: `rule_mutfree`/`writes_instr` now count
limiter matches/instructions as writes), `dsl_rule_step_fst`/`_snd`/
`_vmap`/`_writefree` (successors: `rule_step` itself, `rule_step_vmap`,
`rule_step_writefree`), `dsl_step_limit_free` (successor:
`dsl_step_after_free` — the limit-freedom hypothesis existed only to cancel
the boundary sweep), `Correct.vm_rule_step_compile_rule` and the
sweep-agreement lemmas `limit_sweep_prog_compile_rule` etc. (successor: the
single equation `run_rule_step_compile_rule` above), and the dead
`no_writes` fragment family (`nw_load_fields` … `nw_compile_end`,
`straight_imp_nw`) whose statements would be false under the honest
`writes_instr`.  `dsl_step` (the state half, `snd ∘ rule_step`) remains as
the named notion the trace evaluator and the optimizer's effect certificates
consume.  Pins flipped: `Known_Infidelities.gate_limit_undrained` /
`vm_gate_limit_undrained` (from `gate_limit_drained`'s `= 0` to `= 1`), with
the position-exactness twins
`Limit_SharedBucket.limit_before_failing_match_consumed` /
`vm_limit_before_failing_match_consumed`.

**Strata retirement (M3 NAT-effect-in-fold): the trace strand is retired.**
The historical NAT side
strand — `Semantics.eval_rules_trace` / `eval_chain_trace` /
`trace_nat_drops` and their verdict bridges (`eval_rules_trace_verdict`,
`eval_chain_trace_verdict(_no_drop)`) — is RETIRED (deleted).  It was the
ONLY evaluator that performed the NAT data plane, dispatched OUT-OF-BAND on
the `r_nat` projection at any terminal verdict — the source of
known-infidelity entry 2 (a vmap HIT still ran the trailing NAT and stored a
spurious `e_nat` mapping) — and it had no VM twin and no compile theorem.
Successor: the single fold itself.  `terminal_step` (DSL) and the VM's
`INat` instruction case perform the NAT effect — `nat_drops` (the
no-usable-address NF_DROP) else `apply_nat` (flow-keyed tuple
establish/reuse + L3/L4 rewrite) — AT the terminal the walk actually
reached, so the vmap-hit provenance is structural; both folds and every
evaluator built on them now take the netfilter hook `h` (Section AtHook),
because the redirect/masquerade data plane is hook-dependent.  The
DSL and VM sides share the effect CORE verbatim (`apply_nat_c`/
`nat_drops_c`; the VM feeds the `INat` register operands, bridged by
`Correct.step_extra_inat`/`step_inat_terminal`), and the compile theorem the
strand never had is `compile_nat_effect_correct` (+ the `_u` traversal
family, which now certifies the NAT data plane under jumps/multi-chain/hook
dispatch).  `chain_out`/`chain_out_env` survive re-based on the unified fold
(`eval_chain_u`).  The model's DSL port coverage was extended in the same
move (kernel-faithfully): a masq/redir primary operand IS its port
(`nat_portonly`, `nat_port_val`), so the VM proto-min register discipline
and the DSL agree shape-for-shape; a port living in a concat-map value slot
(`NXmap_port`/`NXmap_full`) is skipped identically on both sides (unmodeled
feature, DEVELOPMENT.md).  Pins flipped: `Known_Infidelities`'s
`vmaphit_daddr_rewritten` (now `= [1;2;3;4]`, unrewritten) and
`vmaphit_stores_nat_mapping` (now `= None`), with vmap-MISS non-vacuity
twins (`vmapmiss_*`) and VM twins (`vm_vmaphit_*`/`vm_vmapmiss_*`); the
mut-vs-trace divergence pin `Nat_NoAddr_Drop.trace_diverges_from_mut_via_nat_drop`
retires WITH the strand — successors `mut_agrees_nat_drop` /
`vm_nat_drop_agrees` (the NAT drop through the compiler).

**Strata retirement (M4 cross-packet carry): the external-step sequence
stratum is retired.**  The historical `Semantics.seq_eval` — a packet-sequence
combinator whose between-packet env update was an EXTERNAL, caller-supplied
`step : verdict -> env -> env` — and its theorems (`Correct.seq_eval_ext`,
`Correct.compile_seq_correct`, `Main.main_compile_seq_correct`,
`Main.pre_split_compile_seq_correct`) are RETIRED (deleted).  Because `step`
was universally quantified, the stratum modeled the ruleset's own cross-packet
state evolution (dynset learning, limiter depletion, NAT mappings) by whatever
the caller wrote — i.e. an effectful ruleset run through it had its
between-packet effects replaced by an external guess; its theorems were
per-packet congruences, not proofs about ruleset-generated state.  Successor:
`seq_eval_env` instantiated with the ruleset's OWN env-out `eval_hook_env_u`
(VM: `run_ruleset_env_u`) — the fst-of-state projections of the unified hook
run — with compile theorem `compile_seq_hook_correct` (the former
`compile_seq_hook_u_correct`, renamed: with the external-step stratum gone it
is the unique sequence theorem).  The semtest sequence battery was moved off
the external step onto the unified env-out for the same reason (the limiter
battery's `step` hand-decremented a bucket the fold now depletes itself).
Cross-packet pins: `Regression/Seq_Hook_Carry.v` — limiter depletion through
a jump under hook dispatch (`seq_hook_limit_depletes` + VM twin), dynset
learning crossing a jump, a base-chain boundary and a packet boundary
(`seq_hook_dynset_learns` + VM twin).

**Strata retirement (T1 single-fold).**  The historical TWO-fold per-rule
split — an entry-packet verdict pass (`rule_applies`/`outcome` paired into
the old `dsl_rule_step`; `run_rule_writes` as a separate write pass) — is
RETIRED; its successor is the strictly stronger single fold above (it
additionally covers intra-rule set-then-read, intra-rule dynset feedback and
mutating `r_after` statements, and flipped known-infidelity entry 3 —
positive pins in `Regression/Setread_IntraRule.v`).  Concretely:
`Semantics.mut_wf` (with `simple_vsrc`/`simple_writes` and the no-mutation-
in-`r_after` conjunct) and `Correct.mut_wf_prog_eq` are DELETED — the
operand-degeneracy conjunct is proved correct instead, the `r_after` conjunct
is modelled instead, and the numgen conjunct survives as the discharged
`rule_numgen_free`; the `run_rule_writes`/`body_writes` fixpoints are folded
into `run_rule_step`/`body_step` (`body_writes` remains as the state
projection of the body fold); `stmts_after_outcome` remains in the pure
strand, coinciding with `after_step` on mutation-free statement lists
(`after_step_mutfree`).  `rule_applies`/`outcome`/`rule_loadable` and the
write-free `run_rule` REMAIN as the pure strand's evaluator (what
`eval_rules`/`run_program` and the optimizer theorems consume) and are proved
to be the mut-free projection of the fold: `Semantics.rule_step_mutfree`
(`rule_mutfree r = true -> rule_step r e p = (if rule_loadable && rule_applies
then outcome else None, (e, p))`) and `Correct.run_rule_step_no_writes`
(`no_writes is = true -> run_rule_step rf is e p = (run_rule rf is e p,
(e, p))`).

## 4. Axiom-freedom gates

- **`make axioms` is the build-FAILING gate** (`AXIOM_GATE_THEOREMS`,
  proof/Makefile): `Print Assumptions` over the listed theorems, failing on
  anything but `Closed under the global context`.  The list is
  - the HEADLINE set (§1) + the `Correct.v` strata + the optimizer DSL form +
    the representation ratchet `Semantics.run_rule_outcome_eq`,
  - the fuel-adequacy heads (§3; restated M6 — jx strand retired):
    `Semantics.eval_rules_j_fuel_indep`, `eval_table_fuel_indep`,
    `eval_rules_u_fuel_indep`, `eval_table_u_fuel_indep`,
    `eval_table_policy_is_fallthrough`,
    `Correct.run_table_fuel_indep_compiled`,
    `Nft_Tactics.nft_yields_fuel_indep`,
    `Tutorial_Proofs.tutorial_blocks_exactly_any_fuel` (8 theorems),
    plus the M6 projection heads `Semantics.rule_purewalk_ok` and
    `Correct.eval_chain_writefree_jumpfree_syn_proj`,
  - the M4 de-vacuized config heads (§5):
    `Optiplex_Antispoof.antispoof_general_any_env`,
    `Optiplex_Mark.genenv_fib_local_contradiction` + the three
    `Optiplex_Mark.streaming_*_real` heads +
    `Optiplex_Mark.streaming_whole_ruleset_witnessed` (6 theorems), and
  - **every result the README claims axiom-free** (README § "Headline
    guarantees are axiom-free", 29 theorems): anti-spoofing
    (`Optiplex_Antispoof.antispoof_general` + its 3 concrete corollaries),
    established-accept (`Example_Ruleset.established_accepted`),
    NAT-masquerade / multi-address primary selection
    (`Netstate_MultiAddr.masq_saddr_is_selected_primary`,
    `masq_drop_iff_no_eligible_addr`), fib host-local (all 17 `Fib_Local`
    heads), and ct-state (all 5 `Ct_State` theorems).

  The rule: **any result the README (or this file) presents as a claim is in
  `AXIOM_GATE_THEOREMS`, in the same commit that adds the claim.**
  Classification note: several of these live in `Examples/`/`Regression/` and
  are DEMO-class *within their axis derivation maps* (executable pins), but
  as README claim surface they are gated exactly like HEADLINEs — the gate
  follows the claim, not the file's directory.
- The in-file `Print Assumptions` lines (end of `Correct.v`,
  `Optimize_Uncond.v`, all of `Main.v`, `Fib_Local.v`, `Ct_State.v`,
  `Optiplex_Antispoof.v`, `Netstate_MultiAddr.v`, `Example_Ruleset.v`, …) are
  **informational**: they print a verdict into the `make proofs` build log
  for eyeball checks, but a `Print Assumptions` cannot fail a build and no CI
  greps that log.  The mechanical stop against an `Admitted` or a
  section-variable leak entering a claimed result is `make axioms` (run by
  the `make gates` aggregate).  The `pre_split_*` ratchet corollaries in
  `Main.v` carry in-file prints and are each an `exact`/`apply` of a gated
  theorem, so their assumption sets coincide with gated ones.
- One-liner (the historical gate):
  `cd theories && printf 'From Nft Require Import Correct Optimize.\nPrint Assumptions compile_chain_correct.\n' | coqtop -R . Nft`
  → `Closed under the global context`.

## 5. Config-proof claim surface (Examples/) — M4 de-vacuization

Per-configuration security theorems used to pin the WHOLE env to the parser's
`gen_env` (empty conntrack, no routes).  Where such a pin coexists with an
env-reading field hypothesis the hypotheses are jointly **unsatisfiable** and
the theorem certifies zero packets.  Status after M4:

| claim | pre-M4 statement | class | successor (headline) | vacuity proof / witness |
|---|---|---|---|---|
| optiplex streaming mark, end-to-end | `Optiplex_Mark.streaming_flow_whole_ruleset` (+ `streaming_prerouting_io`/`_mark`, per-rule lemmas) | SUPERSEDED-vacuous (kept verbatim, derived from the contradiction) | `streaming_flow_whole_ruleset_real` (+ `_io_real`/`_mark_real`; env relaxed to the three `e_set` contents the chain reads) | `genenv_fib_local_contradiction`; witness `env_stream`/`pkt_stream` + `streaming_whole_ruleset_witnessed` |
| optiplex anti-spoofing, general | `Optiplex_Antispoof.antispoof_general` (pin was INERT — memberships already hypothesised over `e_set e`) | SUPPORTING (verbatim corollary of the successor) | `antispoof_general_any_env` (no env pin at all) | proof = pre-M4 proof minus the `?Henv` rewrite; concrete corollaries unchanged (their pin is a satisfiable witnessing choice) |
| router new-conn cruxes (input/forward/private/hooks) | `Router_Input.world_ingress_locked_down` et al. (`e = gen_env` + `cts_new`) | SUPERSEDED-vacuous (M3-era finding; kept verbatim, headers marked) | `Router_Realistic.*_real` + `*_witnessed` | `Router_Realistic.ctstate_under_genenv_never_new` |
| workstation-firewall ct theorems (baseline + parser twin + notation demos) | `Example_Ruleset.established_accepted`, `Ruleset_Verified.established_accepted`/`smtp_dropped` et al., `Nft_Demo_Symbolic.demo_*` — the ones pairing the whole-env pin with an established/related/new ct hypothesis | **KNOWN-vacuous as stated, OPEN** (marked at the theorem sites; invalid/non-ct theorems in the same files are satisfiable and unaffected) | none yet — recorded follow-up: re-state over the `ctstate` vmap contents per the recipe | same contradiction shape (`ctstate_under_genenv_never_new`; `fw_env`/`gen_env` pin `e_ct` empty) |

The recipe (relax to exactly what the lookups read + concrete satisfiability
witness) is documented in CONFIG_PROOFS.md § "Pin only what the lookups read";
`Router_Realistic.v` is the reference implementation.  The `_real`/any-env
successors and the contradiction lemma are in `AXIOM_GATE_THEOREMS`.

## 6. Representation ratchets (M4)

Representation changes ship with an in-kernel equivalence to the shape they
replaced:

| change | ratchet |
|---|---|
| rule outcome: 1 verdict + 5 optional slots -> `Syntax.outcome` sum | `Semantics.run_rule_outcome_eq`: for every well-formed product (`Syntax.prod_wf`), `outcome (rule_of_prod rp) = outcome_prod rp` on all env/packets (`outcome_prod` is the pre-sum evaluation, verbatim, over the historical record `Syntax.rule_prod`) |
| typed source matches (`Typed.txmatch`) over the byte IR | the `Lower_Proofs.*_erasure` family (`eq/neq/prefix/wildcard_erasure` for the scalar shapes); byte-faithfulness of the typed encodings: `Nftval.encode_*` vm_compute witnesses + `Typed.prefix_aligned_24`/`prefix_unaligned_20`/`elab_port_22`/`elab_wildcard` |
| `MMasked` polarity bool -> `cmpop` | the eval clause is `eval_cmp op` (the VM's own comparator); `MFlagsSet` names the positive implicit-bitmask idiom (`(field & X) <> 0`, `CNe`) |
| `nat_kind`/`nat_family`/dynset-op strings -> `Bytecode.nat_op`/`nat_af`/`dynset_op` | rendering strings exist only at the codec/netlink boundary (extracted/codec.ml, nl_send.ml); `make corpus` (2532/2532) pins the rendered bytes unchanged |
| `BDep` dependency tag | a *definitional alias* of `BMatch` (`Syntax.BDep`): evaluation, loadability, compilation are those of the match it wraps, definitionally |

### Strata retirement: `IR/Elab.v` (the legacy 4-shape typed-match module)

Retired whole, per the TODO.md strata-retirement policy.  `Elab.tmatch`'s
four shapes (typed eq / neq / CIDR-prefix / ifname-wildcard) are first-class
`Surface.Typed.txmatch` constructors (`TXEq`/`TXNeq`/`TXPrefix`/`TXWildcard`
— the `TXElab` embedding wrapper is gone), and `prefix_expand` with its
helpers (`payload_prefix_field`/`mask_byte`/`prefix_mask`/`data_and`) moved
verbatim into `Surface/Typed.v`.  Two theorems were retired with the module:

- **`Elab.elab_matchcond_correct`** — a *definitional consistency check*
  (proved by `reflexivity`, because the legacy typed semantics
  `Elab.eval_tmatch` was itself defined through the byte encoding).
  **Superseded by** the NON-definitional per-shape erasure theorems
  `Lower_Proofs.eq_erasure`/`neq_erasure`/`prefix_erasure`/
  `wildcard_erasure` (composed into `txmatch_erasure`): the four shapes now
  have an *independent numeric* semantics in `Semantics/TypedEval.v` (under
  the `make boundary` encode-independence grep gate), and the agreement with
  the elaborated byte IR costs genuine decode/byteorder/mask-arithmetic
  obligations — the same treatment every other typed shape gets.
- **`Lower_Proofs.txelab_erasure`** — the `Some`-form restatement of the
  above over the `TXElab` wrapper; subsumed by the same four theorems.

The concrete elaboration witnesses (`prefix_aligned_24`/
`prefix_unaligned_20`/`elab_port_22`/`elab_wildcard`) and the dormant
set-element views `SEl`/`SRange` (+ `SEl_iv`/`SRange_iv`) moved with their
statements intact (to `Surface/Typed.v` and `Surface/Lower.v` respectively);
`make axioms` now gates the erasure family in `elab_matchcond_correct`'s
place.

## 7. Faithful widths (W1): oracle reads are width-normalised by construction

Every kernel-fixed-width packet/env oracle read — `meta`, `ct`, `rt`,
`socket`, `osf`, `numgen random`, `symhash` — is normalised at the semantics
boundary (`Syntax.do_load` and the VM's mirror instructions) to the exact
byte width the kernel eval writes into the destination register:
`Bytes.fit w d` (truncate to `w` / zero-fill, the register-store discipline
of `nft_reg_store8/16/64` + `struct nft_regs`) applied at the kernel width
from the cited, TOTAL tables `Syntax.meta_width` / `ct_width` / `rt_width` /
`socket_width` / `osf_width` / `numgen_width` / `symhash_width` (each entry
cites linux-6.18.33 eval source; cross-checked against the frontend dtype
table by `Selector.selector_widths_agree`).  The width facts are
DEFINITIONAL — `Bytes.fit_length`/`fit_exact`/`fit_idempotent` and the
per-family `Syntax.read_meta_length` / `meta_load_length` / `ct_load_length` /
`read_rt_length` / `read_socket_length` / `read_osf_length` /
`read_numgen_length` / `read_symhash_length` (all in `make axioms`) — and no
`packet_wf`/`env_wf` hypothesis exists anywhere.  Opaque abstractions
(`pkt_flow`, `pkt_fibkey` beyond `Fib_Local.fibkey_wf`, `pkt_ctdir` tuple
columns, `pkt_xfrm`, `pkt_tunnel`, `pkt_inner`, connlimit keys) are NOT
encodings and stay width-free.

**Octet clamp (W3).**  The same reads are additionally OCTET-clamped by
construction: `Bytes.octets` maps each abstract oracle byte to its low 8 bits
before `fit` (a register cell is a u8 lane of the `u32 data[NFT_REG32_NUM]`
word array — no register byte can exceed 0xff), so the all-ones/zero bitwise
at the read's register width is DEFINITIONALLY the identity on the read value
(`Bytes.data_bitops_fit_octets_id`, `Syntax.do_load_bitops_id`, both in
`make axioms`).  This is what discharges nft's trivial-binop elision as the
unconditional default pass `Optimize_Elide.elide_chain_eval` (see §1).
Restatement note: `Optiplex_Mark.mark_after_set` (an example-file lemma) was
`length v = 4 -> read-after-set = v`; its successor is the STRONGER
hypothesis-free form `read-after-set = fit 4 (octets v)` — the old statement
is false for an out-of-range byte the clamp now normalises, and every concrete
use computes identically.

Statement changes shipped with W1 (all non-headline; every headline theorem
in §1/§4 survives verbatim):

- `Syntax.meta_load_len` / `ct_load_len` (conditional on the old partial
  `meta_fixed_len`/`ct_fixed_len` option tables) are RETIRED with their
  tables; successors are the UNCONDITIONAL `meta_load_length` /
  `ct_load_length` / `read_meta_length` (strictly stronger: the old lemmas
  are the successor instantiated at the keys the old table pinned).
- `Regression/Limit_Over.v` `mtu_packet_overspends_small_quota` /
  `bytemode_length_is_live`: the `pkt_meta _ MKlen = …` hypotheses now pin
  the FULL 4-byte u32 register (`[0;0;5;220]` for 1500 etc.) — the
  kernel-possible oracle value (`skb->len` is a u32; a 1-/2-byte `meta len`
  was a model artifact).  `quota_consumes_packet_len`'s conclusion reads
  `read_meta p MKlen` (the normalised read the quota semantics consumes).
- `Semantics/TypedEval.v` `tev_stuck_undecodable` is RETIRED (its premise —
  an absent/undecodable ct zone register — is no longer a representable
  state: every conntrack entry has a zone, default id 0); successor
  `tev_ctzone_always_decodes` pins the read now EVALUATING (`Some false` on
  the default zone).
- `Optimize_Concat.concat_merge_pair` (and the K-field recogniser via
  `no_guard_fields`) now excludes the frontend's implicit-guard meta keys
  (`concat_guard_field`: l4proto, nfproto, iiftype, oiftype, protocol) from
  concat tuples: with every meta key fixed-width, the recognisers would
  otherwise absorb a hoistable guard into the tuple, diverging from `nft -o`
  (which hoists; see `Optimize_SetGuarded_LinkLayer_Witness`).  All
  optimizer pass theorems are unconditional as before.

## 8. Register-file discipline (W2): the kernel register validator, discharged

`Compiler/RegsValid.v` mirrors the kernel's register admission
(linux-6.18.33, net/netfilter/nf_tables_api.c) as a boolean over bytecode:
`nft_reg_index` is `nft_parse_register`'s netlink-number -> 32-bit-word-index
map (0..4 -> 4*reg, 8..23 -> reg-4, else invalid), `reg_load_ok`/`reg_store_ok`
are `nft_validate_register_load`/`store` (word index >= 4, length >= 1,
index*4 + len <= sizeof(struct nft_regs.data) = 80), and `imm_value_ok` is the
`struct nft_data` value bound (1..16 bytes).  `instr_regs_ok` has ONE ARM PER
`Bytecode.instr` CONSTRUCTOR (no catch-all), each register operand checked at
the length the kernel's expression init validates it with (per-arm citations
in the file; the W1 tables `meta_width`/`ct_width`/`rt_width`/`socket_width`/
`osf_width`/`numgen_width`/`symhash_width` are reused unchanged, plus
kernel-cited tables for fib/ct-directional/xfrm/tunnel/tproxy/fwd/nat operand
widths).  Set-keyed operands (lookup/vmap/dynset/objref-map, map data
registers), whose transfer length lives in the referenced SET object
(`set->klen`/`dlen`), are checked at word granularity — lossless, because the
loads/immediates that fill the span are store-checked at full width.

Discharge (no hypothesis, the `numgen_free` pattern): `Lower.lower_rule`
admits a rule only if `RegsValid.regs_valid (Compile.compile_rule r)` — the
frontend twin of nft's own evaluate-time register-allocation bound — so
`RegsValid_Proofs.lower_ruleset_compile_regs_valid` holds for every lowering;
`paymerge_rule_regs`/`xorfold_rule_regs`/`elide_rule_regs` show all three
always-on linearization stages preserve validity from their own guards
(`seg_can_merge`'s 16-byte cap; `xorfold_mc`'s length-pinning guard; the
elision only deletes the spent `IBitwise`), giving the DEFAULT-pipeline HEADLINE
`lower_ruleset_default_regs_valid` (both in `make axioms`).  Non-vacuity is
Compute-pinned in the file (`regs_valid_rejects_out_of_file`,
`regs_valid_rejects_wide_immediate`).  Runtime twin: the corpus round-trip
asserts `regs_valid` on every compiled corpus rule and fails the build on any
violation (extracted/corpus_test.ml, `make corpus`).  Scope: the `-O`
consolidation passes construct new rules outside the theorem; their outputs
are covered by the runtime corpus assertion.

## 9. Width audit (W4): the post-widths re-adjudication, and reject-lowering fidelity

W4 re-audited everything the linearization audit
(`reports/default-linearization-audit.md`) had ledgered as blocked, against
the W1–W3 by-construction width discipline.  Two classes were closed IN THE
VERIFIED LOWERING (no theorem statement changed; all pre-existing statements
survive verbatim — the W4 additions are new definitions and gated pins):

- **Class Q (reject guard placement).**  `Lower.ensure_dep_head` /
  `rl_push_head`: the reject dependency guard (`meta l4proto tcp` for
  `reject with tcp reset`, the family guard for `with icmp/icmpv6` on inet)
  lands at the RULE HEAD, mirroring nft's evaluate-time `list_add`
  (src/evaluate.c `stmt_reject_gen_dependency` — "Otherwise we'd log things
  that won't be rejected"); every match-synthesised dependency keeps its
  in-place `ensure_dep` position.  The placement is OBSERVABLE for stateful
  bodies (the audit's earlier "pure placement, packet-equal" claim was wrong
  and is corrected in the report and DEVELOPMENT.md class E):
  `Regression/Reject_GuardFirst.v` pins guard-before-effects on BOTH
  evaluators — `udp_guard_breaks_before_mark_write` /
  `tcp_mark_written_and_rejected` (DSL `rule_step`) and their `vm_*`
  twins over `Compile.compile_rule` (VM `run_rule_step`), plus
  `guard_last_leaks_the_write`, the counterfactual that the PRE-FIX
  guard-last body runs the write on the same non-TCP packet (all five in
  `make axioms`; the counter placement itself is pinned structurally by
  `counter_guard_first` — `SCounter`/`ICounter` are verdict-neutral and
  stateless in the model.  Since the M2 in-fold limiter fix the bucket CAN
  witness ordering: `Limit_SharedBucket.limit_before_failing_match_consumed`
  vs `Known_Infidelities.gate_limit_undrained`).
- **Class R (bare-reject family concretization).**  `Lower.reject_type_code`
  now takes the rule's pinned network family, computed by
  `Lower.deps_pinned_nfproto` from the per-rule guard/dedup set (`meta
  nfproto` value, or an IPv4/IPv6 ethertype under any of the `layer_class`
  spellings — `meta protocol`, `ether type`, in-frame `payload @
  link+12/+16`; the 0x8100 vlan tag does not pin): a BARE `reject` in a
  multi-L3 family concretizes from icmpx port-unreach (2,1) to icmp (0,3) /
  icmpv6 (0,4) exactly when nft's `stmt_evaluate_reject_default` does
  (network desc in scope), and an explicit `reject with icmpx …` never
  concretizes (Examples `reject_bare_inet_{unpinned,pinned_v4,pinned_v6}`,
  `reject_icmpx_explicit_stays_abstract`, `deps_pin_spellings` in
  `Lower.v`).

Every class that stays open is re-ledgered in the audit report with a
post-W1 blocker that is NOT a width fact: P (chains carry no family), P′
(oracle independence of `pkt_meta MKl4proto` vs the raw nexthdr byte — a
value-coupling; a blanket definitional equation would be kernel-unfaithful
on extension-header packets, so the faithful close is a tprot-deriving
packet-record restructure), S (frontend guard choice for inet+ether), log
canonicalization (attribute text), fib presence (the `e_routes` result
column is an env-oracle VALUE, `{0,1}`-ness is not a width fact; kernel
derives it, `nft_fib_store_result` stores `!!index`).  Sweep after W4:
pass=1209 (floor raised 1202 -> 1205 -> 1209), mismatch=38, all ledgered.
