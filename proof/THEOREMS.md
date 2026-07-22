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
  supporting strata, the `Lower_Proofs.*_erasure` family, **and every result
  the README claims axiom-free** — anti-spoofing, established-accept,
  NAT-masquerade, multi-address, fib host-local, ct-state; see §4) from the
  compiled `.vo` files and fails on anything but `Closed under the global
  context`.
- Classes used below:
  - **HEADLINE** — the single top theorem of a verified axis; what the project claims.
  - **STAGE** — a per-pass/per-stage theorem composed into a headline.
  - **SUPPORTING** — a stratum or bridge a headline is derived from (or that
    scopes one); not independently a claim.
  - **SUPERSEDED** — a config-vacuity or unshipped-pass form kept in the source,
    subsumed by a successor named in its marker (used only in §5 and for
    passes outside the shipped pipeline; never for an evaluator).
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

There is ONE stateful semantics per side (§3).  Every headline below is a
theorem about that semantics or about the optimizer's flat single-chain state
fold, which is itself the transfer-free projection of it.

| axis | HEADLINE theorem | file | what it says |
|---|---|---|---|
| compiler (rulesets/hooks) | `compile_hook_correct` | `Correct.v` | the compiled VM's hook dispatch = DSL `eval_hook`, for every fuel/ruleset/hook/packet/environment — the one evaluator that BOTH threads every state effect (meta/ct writes, dynset learning, notrack, limiter depletion) AND follows control flow (jump/goto/return, user chains, multi-table and priority dispatch), returning verdict AND the `(env, packet)` the traversal leaves |
| sequence semantics / cross-packet carry | `compile_seq_hook_correct` | `Correct.v` | the between-packet env is **definitionally the ruleset's OWN env-out** (`seq_eval_env` over `eval_hook_env` / `run_ruleset_env`, the `fst`-of-state projections of the hook run — no external step function can be instantiated): dynset adds, limiter depletion and NAT mappings thread packet-to-packet through jumps and multi-chain/hook dispatch, compiler-preserved under `base_numgen_free` (discharged for every frontend program by `Lower_Proofs.lower_ruleset_numgen_free`); cross-packet pins `Regression/Seq_Hook_Carry.v`. |
| NAT data plane (per-rule bridge) | `compile_nat_effect_correct` | `Correct.v` | the compiled per-rule fold performs the identical NAT effect at every hook `h`: `run_rule_step h empty_rf (compile_rule r) e p = rule_step h r e p` under `rule_numgen_free` — packet rewrite, flow-keyed `e_nat` establish/reuse, no-usable-address NF_DROP, all at the NAT terminal inside the fold |
| mutation / cross-packet learning (flat) | `compile_seq_flat_verdict_correct` | `Correct.v` | compiled single-chain traversal threading the env each packet LEAVES (meta/ct writes, dynset learning) = DSL sequence, under `rule_numgen_free` (discharged for EVERY frontend program by `Lower_Proofs.lower_ruleset_numgen_free`); an `add @s {…}` on an earlier packet provably reaches a `lookup @s` on a later one |
| optimizer pipeline → bytecode | `optimize_table_uncond_compile_flat_correct` | `Optimize_Linearize_MutSt.v` | the shipped 18-stage `nft -o` pipeline (`optimize_table_uncond`, the term the CLI runs) + the DEFAULT compile (`compile_chain_default`) preserves the source chain's STATE fold `eval_chain_flat` (verdict AND resulting `(env, packet)`) against the synthesised declarations, for **any input chain** (no `rules_clean`, no freshness precondition beyond numgen-freedom of the optimised chain) and every base env/packet |
| optimizer pipeline (consolidation) | `Optimize_MutEnv.optimize_table_uncond_flat_correct` | `Optimize_MutEnv.v` | the consolidation alone, hypothesis-free, under the full-state `eval_chain_flat h`: for **any input chain**, at every hook/base env/packet, the optimised chain yields the SAME verdict **and** the SAME resulting `(env, packet)` as the input — a stage cannot preserve verdicts while altering an env-half write (dynset learning, limiter depletion, NAT mapping) or a packet-half write (`meta mark set`, ct set); the `(verdict, env)` view `optimize_table_uncond_flat_env_correct` is its projection corollary (precision pin: the env-only observable is blind to `[meta mark set 0x1]` vs `[]`, but the full-state one distinguishes them — `mutst_pin_flat_env_blind`/`mutst_pin_distinguishes`).  Jump scope: `eval_chain_flat` is the flat fold (callees of jump-bearing chains are skipped) — see the scope note below |
| DEFAULT compile pipeline | `Optimize_Linearize_MutSt.compile_chain_default_flat_correct` | `Optimize_Linearize_MutSt.v` | the DEFAULT pipeline `compile_chain_default = compile_chain ∘ elide_chain ∘ xorfold_chain ∘ paymerge_chain` — nft's ALWAYS-ON netlink linearization (classes I + L, including the trivial-binop deletion) — reproduces the source chain's `eval_chain_flat` (verdict AND `(env, packet)`), for every chain/env/packet under `rule_numgen_free`; stage composition is `linearize_chain_flat`; non-vacuity Compute-pinned (`default_pipeline_merges_payload_loads`, `default_pipeline_folds_xor` — the folded xor compiles to a bare load+cmp, NO bitwise — and `default_pipeline_elides_trivial_binop`) |
| intra-rule pass: adjacent-payload merge | `Optimize_Linearize_MutSt.paymerge_chain_flat` | `Optimize_Linearize_MutSt.v` | fusing two byte-contiguous full-width payload equalities in the same header into one wider load+compare (nft `payload_can_merge`; corpus class I) preserves `eval_chain_flat` — **UNCONDITIONAL** (`forall h c e p`, no hypotheses): the read and its loadability split at any interior offset for every packet |
| intra-rule pass: bitwise-xor constant fold | `Optimize_Linearize_MutSt.xorfold_chain_flat` | `Optimize_Linearize_MutSt.v` | transferring a pure-xor register operand onto the compare value (`(reg & 0xff..) ^ C <op> V  →  ^ 0 <op> V^C`; nft `binop_transfer`; corpus class L) preserves `eval_chain_flat` — **UNCONDITIONAL**: bytewise xor is involutive, no width/byte-range side condition. The spent residue is deleted by the next stage |
| intra-rule pass: trivial-binop elision | `Optimize_Linearize_MutSt.elide_chain_flat` | `Optimize_Linearize_MutSt.v` | deleting the spent binop the xor fold leaves — `(reg & 0xff..ff) ^ 0x00` at the field's kernel register width becomes a bare compare (nft `binop_transfer_handle_lhs`, OP_XOR: the class-L residue) — preserves `eval_chain_flat` — **UNCONDITIONAL**: a register-normalised read is width-pinned AND octet-clamped BY CONSTRUCTION (`Bytes.fit`/`Bytes.octets` at the `do_load` boundary), so the all-ones/zero bitwise is definitionally the identity on it (`Syntax.do_load_bitops_id`) — no width, byte-range or well-formedness hypothesis |
| pass composition | `Optimize_Registry.run_passes_correct` | `Optimize_Registry.v` | ONE generic theorem: folding **any** list of registered `opt_pass`es (each bundling its own eval-preservation proof) preserves the chain's state fold, proved once quantified over the list — the `-O p1,p2,...` CLI only parses names into the list (`resolve_passes`) and folds them (`run_passes`) |
| single-chain compile | `compile_chain_flat_verdict_correct` / `compile_chain_flat_env_correct` | `Correct.v` | the compiled single chain reproduces its own DSL state fold — verdict only, and verdict + resulting env, respectively — under `rule_numgen_free`; consumed by the sequence and optimizer headlines |
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
- The optimizer is certified at the effect-observing STATE level: the shipped
  pipeline related, at every hook, under the FULL-STATE `eval_chain_flat h`
  (verdict **and** the resulting `(env, packet)` the `rule_step` fold leaves,
  nothing dropped), all the way to the bytecode
  (`optimize_table_uncond_compile_flat_correct`).  A stage cannot preserve a
  verdict while altering a write a later hook observes — env writes because
  `seq_eval_env` carries them to the next packet, packet writes (e.g. `meta
  mark set`) because `run_ruleset`'s priority dispatch hands the mutated packet
  to the next base chain.  Precision pin: the `[meta mark set 0x1]` chain and
  the empty chain are identified by the `(verdict, env)` projection but
  distinguished by the full-state fold (`Optimize_MutEnv` Part H).  Jump scope:
  `eval_chain_flat` is the flat single-chain fold (`terminal (Jump _) = false`
  skips the callee), so for jump-BEARING chains the guarantee is about that
  flat callee-skipping fold, not `eval_hook`'s cross-chain traversal.
  What makes the state level compose: every pure-merge recogniser carries an
  **effect-safety guard** (`rule_mutfree`, `Optimize_ValueSet.value_merge_pair`)
  so its merges live on the write-free part of the fold; the three
  effect-rewriting stages (`datamap`/`dnat`/`snat`) carry fold-level per-shape
  certificates (`Optimize_MutEnv.eval_rules_flat_map_merge` /
  `_dnat_merge` / `_snat_merge`); the base pass is effect-safe by construction
  (`dedup_rule` fires only on `rule_mutfree` rules); and `seed_start` also
  clears every **dynset write target** (`chain_seed` includes
  `rule_dynset_names`), so no rule can clobber a minted declaration.
- **Mutation × jump/goto is jointly verified** in THE semantics
  (`Semantics.eval_rules`/`run_rules` and their compile theorems
  `compile_table_correct` / `compile_ruleset_correct` / `compile_hook_correct` /
  `compile_seq_hook_correct`): one effect-threading, jump-following fold per
  side.  The optimizer's flat single-chain fold (`eval_rules_flat` /
  `eval_chain_flat`) is the **transfer-free projection** of it, proved on
  `rule_plain` chains by `Semantics.eval_table_flat_verdict_proj` /
  `eval_rules_flat_proj` — see the evaluator matrix, §3.
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
fold), and the `OVmapNat` vmap-hit trace NAT + spurious `e_nat` store: the NAT
data-plane effect (packet rewrite, flow-keyed `e_nat` establish/reuse,
no-usable-address NF_DROP) lives INSIDE the single per-rule fold at the NAT
terminal, so a vmap HIT structurally never runs it (outcome provenance),
certified by `compile_nat_effect_correct` at every netfilter hook `h` (the fold
carries the hook because the redirect/masquerade data plane is hook-dependent).

## 2. Classification of every `Theorem`/`Corollary` in `Correct.v` and `Optimize*.v`

### `Correct.v` (the compiler strata, bottom-up)

| declaration | class | derivation edge |
|---|---|---|
| `compile_chain_flat_verdict_correct` | SUPPORTING (stratum: one chain, verdict, in-traversal mutation) | the `fst` projection of `compile_chain_flat_env_correct` (`run_program_flat_env_fst` / `eval_rules_flat_env_fst`), no second induction |
| `compile_chain_flat_env_correct` | SUPPORTING (stratum: + env the chain leaves) | from `run_program_flat_env_compile_chain`, one induction over the per-rule step equation `run_rule_step_compile_rule` (`run_rule_step h empty_rf (compile_rule r) e p = rule_step h r e p` under `rule_numgen_free`) |
| `compile_seq_flat_verdict_correct` | **HEADLINE** (mutation/sequence axis) | = `compile_chain_flat_env_correct` + `seq_eval_env_ext` |
| `compile_table_correct` | SUPPORTING (stratum: + jump/goto/return) | from `run_rules_compile`; consumed by `compile_ruleset_correct` |
| `compile_ruleset_correct` | SUPPORTING (stratum: + multi-table dispatch, state threaded between bases) | from `compile_table_correct` per base chain |
| `compile_hook_correct` | **HEADLINE** (compiler axis) | = `compile_ruleset_correct` after pure hook selection/ordering |
| `compile_seq_hook_correct` | **HEADLINE** (+ cross-packet env carry over the per-packet run — THE sequence semantics) | = `compile_ruleset_correct` + `seq_eval_env_ext` |
| `compile_nat_effect_correct` | **HEADLINE** (NAT data-plane axis) | the per-rule bridge `run_rule_step_compile_rule` under its NAT-effect name — the compiled fold performs the identical NAT effect at every hook |
| `run_rule_step_compile_rule` (Lemma) | SUPPORTING (the one DSL/VM per-rule agreement obligation) | one `run_rule_step` = `rule_step` equation under `rule_numgen_free`, every strata induct over it |
| `run_rule_step_no_writes` (Lemma) | SUPPORTING (write-free per-rule VM projection) | `no_writes is = true -> run_rule_step h rf is e p = (run_rule rf is e p, (e, p))` |
| `mut_strand_jump_pin` / `rg_jump_not_plain` / `unified_strand_jump_drops` (Examples) | DEMO (license-boundary pins for the flat fold's transfer-free `rule_plain` domain) | compute |

### `Optimize.v` / `Optimize_ValueSet.v` (base pass and unshipped forms)

| declaration | class | note |
|---|---|---|
| `Optimize.optimize_chain_correct` (Lemma) | SUPPORTING (the rule-local base stage) | `optimize_chain` is the pipeline's base pass; the shipped pipeline theorem is `optimize_table_uncond_flat_correct` |
| `Optimize_ValueSet.eval_rules_value_merge` (Lemma) | SUPPORTING | 2-adjacent-rule merge certificate behind the `valueset` recogniser lineage |
| `Optimize_ValueSet.eval_rules_range_value_merge` (Lemma) | SUPERSEDED, **known-unfaithful** | models `6,7 => 6-7` as a RANGE where `nft -o` emits the SET `{6,7}`; used by no shipped pass (marker on the lemma) |
| `Optimize_ValueSet.optimize_chain2_correct` (Lemma) | SUPERSEDED | `optimize_chain2` is not composed into the shipped pipeline |

### Per-pass certificates and stages (`Optimize_*.v`)

| declaration | class | note |
|---|---|---|
| `Optimize_Vmap.eval_rules_vmap_merge2` | SUPPORTING | certificate consumed by the `vmap` stage lineage |
| `Optimize_Concat.eval_rules_concat_merge2` | SUPPORTING | certificate for the two-selector concat merge |
| `Optimize_ConcatMulti.eval_rules_concat_mergeK` | SUPPORTING | K-row concat certificate |
| `Optimize_DataMap.eval_rules_map_merge` (+ the flat form `Optimize_MutEnv.eval_rules_flat_map_merge`) | SUPPORTING | mark-map merge certificates (`datamap` stage; a labelled sound superset of `nft -o`, see Optimize_Table.v fidelity contract) |
| `Optimize_DataMap.mapn_bare_diverges_offkey` | DEMO | pins why the head guard cannot be dropped |
| `Optimize_Dnat.eval_rules_dnat_merge`, `apply_nat_dnat_eq` (Cor.) | SUPPORTING | bare-NAT-map merge: verdict + data-plane NAT-effect preservation |
| `Optimize_Snat.eval_rules_snat_merge`, `apply_nat_snat_eq` (Cor.) | SUPPORTING | symmetric snat forms |
| `Optimize_MutEnv.normalize_chain_flat` | STAGE | verdict-preserving head normalisation run first by `optimize_table_uncond` |
| `Optimize_MutEnv.optimize_rules_{valueset,dscp,intervalset,intervalsethostorder,intervalsetguarded,mixedpointrangeguarded,concat,concatguarded,setguarded,concatmulti,vmap,vmapguarded,dscpvmap,dnat,snat,datamap,absorb,ctmask}_flat` + `optimize_chain_flat` | STAGE | each stage of the pipeline preserved under the full-state `eval_rules_flat h`, composed into `optimize_table_flat_correct_uncond_gen` |
| `Optimize_MutEnv.optimize_table_flat_correct_uncond_gen` | SUPPORTING | the general `(n, d)`-threaded whole-pipeline STATE form: same `eval_chain_flat h` result for output and input under the deployed declarations |
| `Optimize_MutEnv.optimize_table_uncond_flat_correct` | **HEADLINE** (optimizer axis) | the shipped `optimize_table_uncond`, hypothesis-free, under the FULL-STATE `eval_chain_flat h`: verdict AND resulting `(env, packet)` preserved at every hook/base env/packet (built on the per-stage `optimize_rules_*_flat` lemmas, the recogniser effect-safety guards, and the fold-level dnat/snat/datamap shape certificates) |
| `Optimize_MutEnv.optimize_table_uncond_flat_env_correct` | SUPPORTING (corollary) | the `(verdict, env)` view of the full-state headline — kept for the cross-packet (`seq_eval_env`) reading |
| `Optimize_MutEnv.eval_rules_flat_{map,dnat,snat}_merge` | SUPPORTING | fold-level effect certificates for the three effect-rewriting merge shapes, at the full-state evaluator (verdict + `(env, packet)` out) |
| `Optimize_MutEnv.mutst_pin_{flat_env_blind,mark_observed,distinguishes}` | PIN | precision regression: `[meta mark set 0x1]` vs `[]` are identified by the `(verdict, env)` projection (packet-blind) but MUST stay distinguished by `eval_chain_flat` (the exported packet carries the mark) |
| `Optimize_Linearize_MutSt.linearize_chain_flat` | STAGE | the always-on linearization (elide ∘ xorfold ∘ paymerge) preserves `eval_chain_flat`; composed into both default-pipeline headlines |
| `Optimize_Linearize_MutSt.compile_chain_flat_correct` | SUPPORTING | the compiled optimised chain's VM state run reproduces its own DSL state fold; consumed by `optimize_table_uncond_compile_flat_correct` |

## 3. The evaluator matrix

**THE semantics is one stateful evaluator per side** (`Semantics.v` § "THE
UNIFIED SEMANTICS"): DSL `eval_rules` / `eval_table` / `eval_ruleset` /
`eval_hook`, VM `run_rules` / `run_table` / `run_ruleset` — one fuel-bounded
fold per side that **threads every state effect** (packet meta/ct writes,
dynset env writes, notrack, position-exact limiter/quota/connlimit consumption,
via the per-rule fold `rule_step`/`run_rule_step`) **and follows control flow**
(jump/goto/return, user chains, multi-table and hook/priority dispatch),
returning verdict AND the `(env, packet)` the traversal leaves; cross-packet
env carry is `seq_eval_env` over `eval_hook_env` / `run_ruleset_env`.  A
jumped-to chain sees the caller's accumulated writes; the callee's writes
persist into the resuming caller (witness pins:
`Regression/Setread_UnderJump.v`).  Compile theorems: §2.

**The optimizer's flat single-chain state fold** (`eval_rules_flat` /
`eval_chain_flat`, VM `run_program_flat` / `run_chain_flat`) is the tool the
optimizer and default-compile headlines are stated over: ONE `fold_left` of
`rule_step`/`run_rule_step` with an absorbing stopped accumulator, returning
verdict AND `(env, packet)`.  Its verdict and env views (`eval_*_flat_verdict`,
`eval_*_flat_env`) are **projections BY DEFINITION** — the in-strand bridges
(`eval_rules_flat_env_fst`, `run_program_flat_env_fst`) are `reflexivity`-level.
And the whole fold is the **transfer-free projection of THE semantics**:

| projection (DSL + VM mirror) | licensed sub-domain | coincidence equation |
|---|---|---|
| `eval_rules_flat`/`eval_chain_flat` (VM `run_program_flat`/`run_chain_flat`) — full state — and its verdict/env views | `rule_plain` chains: no realisable Jump/Goto/Return under the run's verdict maps (step-threaded: rule writes provably cannot touch `e_vmap`, `rule_step_vmap`) | `eval_rules_flat_proj`: `eval_rules fuel cs rs e p = eval_rules_flat rs e p` (whole verdict × (env, packet) triple); table form `eval_table_flat_proj`; verdict-only forms `eval_rules_flat_verdict_proj` / `eval_table_flat_verdict_proj` |
| `rule_loadable` / `outcome` (per-rule bools) + write-free `run_rule` | write-free rule (`rule_mutfree`: no mutating statement AND no limiter match — evaluating a limiter writes its bucket) | `Semantics.rule_step_state_mutfree`: `rule_mutfree r = true -> rule_step h r e p = (…, (e, p))` (the loadable/outcome verdict on unchanged state); VM twin `Correct.run_rule_step_no_writes` |
| `seq_eval_env` | generic in its per-packet evaluator; THE sequence semantics is its instantiation with the ruleset's own env-out `eval_hook_env` | `compile_seq_hook_correct` (whole-ruleset), `compile_seq_flat_verdict_correct` (single flat chain) |

**Kept structural predicates.** Load-liveness — `rule_loadable`,
`body_loadable_walk`, `body_synproxy_stops` — decides whether a rule's body can
load its operands (a broken load stops the walk); it is correct on effectful
rules and is consumed by the optimizer's shape obligations.  Write-freeness
guards — `rule_mutfree`, `is_mut_stmt`, `match_consumefree` — are the boolean
side conditions that let a merge recogniser fire only where it is effect-safe
(above).

**Fuel adequacy (RESOLVED, M4 config-proof soundness; RESTATED, M6)**: the
semantics is fuel-bounded, and `eval_table` maps fuel EXHAUSTION to the chain
policy — a verdict the kernel can never produce (nft rejects jump loops at load
time; kernel jump stack is 16 deep, `NFT_JUMP_STACK_SIZE`).  Naive fuel
monotonicity is **false** for jump loops (an under-fueled callee's exhaustion
reads as fall-through and more fuel flips the verdict), so adequacy is stated
above a computable bound: no effect writes the verdict maps
(`rule_step_vmap`), so the `rule_step`-level rank witness `chain_ranked` —
stable under every state the traversal can reach — gives
`Semantics.eval_rules_fuel_indep` / `eval_table_fuel_indep` (verdict AND
state) above `sufficient_fuel cs rs`; effectful configs are inside the adequacy
story, not carved out of it.  User surface:
`Nft_Tactics.nft_yields`/`nft_yields_fuel_indep`, CONFIG_PROOFS.md § "Choosing
the fuel budget", worked instance
`Tutorial_Proofs.tutorial_blocks_exactly_any_fuel`.  License-boundary pins for
the flat fold's transfer-free domain: `Correct.mut_strand_jump_pin` /
`rg_jump_not_plain` / `unified_strand_jump_drops` (a chain that realises a jump
is evaluated by `eval_hook`, not the flat fold).

The bytecode VM mirrors the DSL rows one-for-one (`run_rule(s)`,
`run_program_flat`, `run_table`, `run_ruleset`); each compile theorem in §2
equates one DSL row with its VM mirror.

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

**Write-free projection.**  `rule_loadable`/`outcome` and the write-free
`run_rule` are the per-rule evaluator on effect-free rules — proved to be the
mut-free projection of the single fold: `Semantics.rule_step_state_mutfree`
(`rule_mutfree r = true -> rule_step h r e p = (if rule_loadable && … then
outcome else None, (e, p))`) and `Correct.run_rule_step_no_writes`
(`no_writes is = true -> run_rule_step h rf is e p = (run_rule rf is e p,
(e, p))`).

## 4. Axiom-freedom gates

- **`make axioms` is the build-FAILING gate** (`AXIOM_GATE_THEOREMS`,
  proof/Makefile): `Print Assumptions` over the listed theorems, failing on
  anything but `Closed under the global context`.  The list is
  - the HEADLINE set (§1) + the `Correct.v` strata
    (`compile_chain_flat_verdict_correct`/`_env_correct`,
    `compile_table_correct`, `compile_ruleset_correct`,
    `compile_seq_flat_verdict_correct`, `run_rule_step_compile_rule`),
  - the flat-fold projection heads
    `Semantics.eval_rules_flat_proj` / `eval_table_flat_proj` /
    `eval_rules_flat_verdict_proj` / `eval_table_flat_verdict_proj`
    and the write-free projection `Semantics.rule_step_state_mutfree`,
  - the optimizer STATE forms
    `Optimize_MutEnv.optimize_table_uncond_flat_correct` / `_flat_env_correct`
    and `Optimize_Linearize_MutSt.optimize_table_uncond_compile_flat_correct`,
    the per-stage linearization certs
    (`paymerge_chain_flat`/`xorfold_chain_flat`/`elide_chain_flat`/`linearize_chain_flat`/`compile_chain_flat_correct`/`compile_chain_default_flat_correct`),
    and `Optimize_Registry.run_passes_correct`,
  - the fuel-adequacy heads (§3):
    `Semantics.eval_rules_fuel_indep`, `eval_table_fuel_indep`,
    `Nft_Tactics.nft_yields_fuel_indep`,
    `Tutorial_Proofs.tutorial_blocks_exactly_any_fuel`,
    plus the surface projection `Nft_Tactics.nft_yields_writefree_at`,
  - the M4 de-vacuized config heads (§5):
    `Optiplex_Antispoof.antispoof_general_any_env`,
    `Optiplex_Mark.genenv_fib_local_contradiction` + the three
    `Optiplex_Mark.streaming_*_real` heads +
    `Optiplex_Mark.streaming_whole_ruleset_witnessed`, the `Router_Realistic.*_real`
    heads, and
  - **every result the README claims axiom-free** (README § "Headline
    guarantees are axiom-free"): anti-spoofing
    (`Optiplex_Antispoof.antispoof_general` + its 3 concrete corollaries),
    established-accept (`Example_Ruleset.established_accepted`),
    NAT-masquerade / multi-address primary selection
    (`Netstate_MultiAddr.masq_saddr_is_selected_primary`,
    `masq_drop_iff_no_eligible_addr`), fib host-local (all 17 `Fib_Local`
    heads), ct-state (all 5 `Ct_State` theorems), the `Lower_Proofs.*_erasure`
    family + `lower_ruleset_numgen_free`, and the W1/W2 width/register heads
    (`Bytes.fit_*`, `Syntax.read_*_length`/`*_load_length`/`do_load_bitops_id`,
    `RegsValid_Proofs.lower_ruleset_default_regs_valid`/`_compile_regs_valid`).

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
  `cd theories && printf 'From Nft Require Import Correct Optimize.\nPrint Assumptions compile_chain_flat_verdict_correct.\n' | coqtop -R . Nft`
  → `Closed under the global context`.

## 5. Config-proof claim surface (Examples/) — M4 de-vacuization

Some per-configuration security theorems pin the WHOLE env to the parser's
`gen_env` (empty conntrack, no routes).  Where such a pin coexists with an
env-reading field hypothesis the hypotheses are jointly **unsatisfiable** and
the theorem certifies zero packets.  Status after M4:

| claim | whole-env-pinned statement | class | successor (headline) | vacuity proof / witness |
|---|---|---|---|---|
| optiplex streaming mark, end-to-end | `Optiplex_Mark.streaming_flow_whole_ruleset` (+ `streaming_prerouting_io`/`_mark`, per-rule lemmas) | SUPERSEDED-vacuous (kept verbatim, derived from the contradiction) | `streaming_flow_whole_ruleset_real` (+ `_io_real`/`_mark_real`; env relaxed to the three `e_set` contents the chain reads) | `genenv_fib_local_contradiction`; witness `env_stream`/`pkt_stream` + `streaming_whole_ruleset_witnessed` |
| optiplex anti-spoofing, general | `Optiplex_Antispoof.antispoof_general` (pin is INERT — memberships already hypothesised over `e_set e`) | SUPPORTING (verbatim corollary of the successor) | `antispoof_general_any_env` (no env pin at all) | proof = general proof minus the `?Henv` rewrite; concrete corollaries unchanged (their pin is a satisfiable witnessing choice) |
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
| rule outcome: 1 verdict + 5 optional slots -> `Syntax.outcome` sum | the outcome sum is the representation the semantics reads directly; per-rule the evaluated outcome is the fold's terminal value (`rule_step`/`run_rule_step`), pinned against the compiler by `run_rule_step_compile_rule` |
| typed source matches (`Typed.txmatch`) over the byte IR | the `Lower_Proofs.*_erasure` family (`eq/neq/prefix/wildcard_erasure` for the scalar shapes); byte-faithfulness of the typed encodings: `Nftval.encode_*` vm_compute witnesses + `Typed.prefix_aligned_24`/`prefix_unaligned_20`/`elab_port_22`/`elab_wildcard` |
| `MMasked` polarity bool -> `cmpop` | the eval clause is `eval_cmp op` (the VM's own comparator); `MFlagsSet` names the positive implicit-bitmask idiom (`(field & X) <> 0`, `CNe`) |
| `nat_kind`/`nat_family`/dynset-op strings -> `Bytecode.nat_op`/`nat_af`/`dynset_op` | rendering strings exist only at the codec/netlink boundary (extracted/codec.ml, nl_send.ml); `make corpus` (2532/2532) pins the rendered bytes unchanged |
| `BDep` dependency tag | a *definitional alias* of `BMatch` (`Syntax.BDep`): evaluation, loadability, compilation are those of the match it wraps, definitionally |

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
unconditional default pass `Optimize_Linearize_MutSt.elide_chain_flat` (see §1).
Restatement note: `Optiplex_Mark.mark_after_set` (an example-file lemma) is the
hypothesis-free `read-after-set = fit 4 (octets v)` — the clamp normalises an
out-of-range byte and every concrete use computes identically.

Width lemmas shipped with W1 (all non-headline; every headline theorem
in §1/§4 survives verbatim):

- `Syntax.meta_load_length` / `ct_load_length` / `read_meta_length` are the
  UNCONDITIONAL width lemmas (total, no option table) — the read length is
  always the kernel register width.
- `Regression/Limit_Over.v` `mtu_packet_overspends_small_quota` /
  `bytemode_length_is_live`: the `pkt_meta _ MKlen = …` hypotheses pin
  the FULL 4-byte u32 register (`[0;0;5;220]` for 1500 etc.) — the
  kernel-possible oracle value (`skb->len` is a u32).
  `quota_consumes_packet_len`'s conclusion reads
  `read_meta p MKlen` (the normalised read the quota semantics consumes).
- `Semantics/TypedEval.v` `tev_ctzone_always_decodes` pins the ct zone read
  EVALUATING (`Some false` on the default zone): every conntrack entry has a
  zone (default id 0), so an "absent/undecodable ct zone" is not a
  representable state.
- `Optimize_Concat.concat_merge_pair` (and the K-field recogniser via
  `no_guard_fields`) excludes the frontend's implicit-guard meta keys
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
  bodies:
  `Regression/Reject_GuardFirst.v` pins guard-before-effects on BOTH
  evaluators — `udp_guard_breaks_before_mark_write` /
  `tcp_mark_written_and_rejected` (DSL `rule_step`) and their `vm_*`
  twins over `Compile.compile_rule` (VM `run_rule_step`), plus
  `guard_last_leaks_the_write`, the counterfactual that a guard-last body runs
  the write on the same non-TCP packet (all five in
  `make axioms`; the counter placement itself is pinned structurally by
  `counter_guard_first` — `SCounter`/`ICounter` are verdict-neutral and
  stateless in the model.  Since the M2 in-fold limiter fix the bucket CAN
  witness ordering: `Limit_SharedBucket.limit_before_failing_match_consumed`
  vs `Known_Infidelities.gate_limit_undrained`).
- **Class R (bare-reject family concretization).**  `Lower.reject_type_code`
  takes the rule's pinned network family, computed by
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
