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
| compiler, sequence form | `compile_seq_correct` | `Correct.v` | the same, lifted over a packet sequence under an **arbitrary step** `verdict -> env -> env` — a per-packet **congruence corollary** of `compile_hook_correct`, *not* a proof about ruleset-generated state (that is the next axis) |
| mutation / cross-packet learning | `compile_seq_mut_correct` | `Correct.v` | compiled single-chain traversal threading the env each packet LEAVES (meta/ct writes, dynset learning) = DSL sequence, under `rule_numgen_free` (discharged for EVERY frontend program by `Lower_Proofs.lower_ruleset_numgen_free`) |
| optimizer pipeline | `optimize_table_uncond_compile_correct` | `Optimize_Uncond.v` | the shipped 18-stage `nft -o` pipeline + compilation preserves every packet's verdict against the synthesised declarations, for **any input chain** (no `rules_clean`, no freshness precondition) |
| typed source lowering (**`typed_erasure`**) | the `Lower_Proofs.*_erasure` family (composed: `txmatch_erasure`) | `Lower_Proofs.v` | the verified lowering of a typed source construct produces exactly the byte IR the compiler consumes, with genuine per-construct obligations — `eq_erasure`/`neq_erasure` (register decode at the value's byteorder), `prefix_erasure` (CIDR: both the byte-aligned truncated-load shortening and the full-width masked compare), `wildcard_erasure` (leading-bytes short compare), `range_erasure_be`/`range_erasure_host` (BE vs host-endian range order), `bitmask_erasure`, `bitfield_erasure` (mask+shift), `set_interval_erasure` (byte-interval = numeric membership), `concat_key_erasure` (slot-padding invertibility), `cidr_interval_agrees_prefix_expand` (one CIDR expansion, not two). Since M6 the generated sources (`*_Gen.v`) carry the **surface** ruleset (`<name>_surface : sruleset`) and define every table/chain/decl as `Lower.lower_ruleset` applied to it, kernel-reduced — **no raw byte is written by hand** and a refused construct fails the generated `<name>_lowers_ok` Example (fail-loud) |

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
- The optimizer headline is **verdict-only**: quantified over `eval_chain`,
  the write-blind/NAT-blind/jump-free evaluator — even though stages rewrite
  write-effectful statements (`datamap` folds `meta mark set`, `dnat`/`snat`
  fold NAT terminals) whose effects later hooks observe. The per-stage effect
  certificates (`Optimize_DataMap.eval_rules_mut_map_merge`,
  `Optimize_Dnat.apply_nat_dnat_eq`, snat forms) are **per-merge-shape lemmas,
  not composed through `optimize_table`** — no theorem lifts the pipeline to
  `eval_chain_mut`/`eval_rules_trace`. The full statement of the gap and the
  not-lifted rationale sit on `optimize_table_uncond_compile_correct`
  (Optimize_Uncond.v, "Scope note 2").
- The compiler axis (jump strand) threads **no writes**; the mutation axis
  follows **no jumps**. **Mutation × jump/goto is not jointly verified** (see
  the evaluator matrix, §3).
- The mutation/ct axis is **parametric in flow identity**: every ct/NAT
  statement is a congruence over the opaque key `pkt_flow` (and `e_ct`/`e_nat`
  keyed by it). Nothing ties `pkt_flow` to the packet's header bytes — no
  `flow_wf` analogous to `Fib_Local.fibkey_wf` exists yet — so transferring
  these theorems to a real skb assumes an injective direction-normalised
  (tuple + l4proto + zone) canonicalisation. A wrong canonicalisation makes
  them true *about the wrong flow* (two distinct real flows sharing one model
  key would merge their ct marks). Rationale + designated fix: the `pkt_flow`
  comment in `Core/Packet.v`; honest-gaps entry in `DEVELOPMENT.md`.

Known-gaps note: three **confirmed model-vs-kernel divergences** (limiter
sweep past a failing match; `OVmapNat` vmap-hit trace NAT + spurious `e_nat`
store; intra-rule set-then-read) hold **inside** the theorems above — DSL and
VM agree on them, so no compile theorem is weakened, but the *model* is not
kernel-exact there. Ledger with kernel citations, repros, and `vm_compute`
lock-in pins: `DEVELOPMENT.md` § "Known model infidelities" +
`theories/Regression/Known_Infidelities.v`.

## 2. Classification of every `Theorem`/`Corollary` in `Correct.v` and `Optimize*.v`

### `Correct.v` (the compiler strata, bottom-up)

| declaration | class | derivation edge |
|---|---|---|
| `compile_chain_correct` | SUPPORTING (stratum 1: one chain, pure verdict) | from `run_program_compile_chain`; consumed by the optimizer headline via `compile_chain_sets_correct` |
| `compile_chain_sets_correct` (Corollary) | SUPPORTING | corollary of `compile_chain_correct` at `env_with_sets`; consumed by `optimize_table_uncond_compile_correct` |
| `compile_chain_mut_correct` | SUPPORTING (stratum 2: + in-traversal mutation) | **derived**: the `fst` projection of stratum 3 (`run_program_mut_env_fst` / `eval_rules_mut_env_fst`), no second induction |
| `compile_chain_mut_env_correct` | SUPPORTING (stratum 3: + env the chain leaves) | from `run_program_mut_env_compile_chain`, one induction over the per-rule step equation `vm_rule_step_compile_rule` (`vm_rule_step (compile_rule r) e p = dsl_rule_step r e p` under `rule_numgen_free`) |
| `compile_seq_mut_correct` | **HEADLINE** (mutation/sequence axis) | = `compile_chain_mut_env_correct` + `seq_eval_env_ext` |
| `compile_table_correct` | SUPPORTING (stratum 5: + jump/goto/return) | from `run_eval_rules_j`; consumed by `compile_ruleset_correct` |
| `eval_chain_eq_table_jumpfree` | SUPPORTING (fidelity bridge: `eval_chain` = `eval_table` on jump-free chains) | from `eval_rules_jumpfree_eq_j` |
| `compile_chain_faithful_jumpfree` (Corollary) | SUPPORTING | corollary of `compile_chain_correct` + `eval_chain_eq_table_jumpfree` |
| `faithful_table_jump_drops` (Example) | DEMO (regression pin: a jump into a dropping chain drops) | computes |
| `compiled_table_jump_drops` (Example) | DEMO | instance of `compile_table_correct` |
| `rg_base_not_jumpfree` (Example) | DEMO (the pin's chain is outside `eval_chain`'s faithful domain) | computes |
| `compile_ruleset_correct` | SUPPORTING (stratum 6: + multi-table dispatch) | from `compile_table_correct` per base chain |
| `compile_hook_correct` | **HEADLINE** (compiler axis) | = `compile_ruleset_correct` after pure hook selection/ordering |
| `compile_seq_correct` | **HEADLINE** (congruence corollary — see scope note §1) | = `compile_hook_correct` + `seq_eval_ext` |
| `run_table_fuel_indep_compiled` (Corollary) | SUPPORTING (VM mirror of the M4 fuel-adequacy result, §3) | = `compile_table_correct` (at both fuels) + `Semantics.eval_table_fuel_indep` |

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
| `Optimize_Table.optimize_preserves_rules_clean` | SUPPORTING | seam lemma: the base pass preserves `rules_clean` |
| `Optimize_Uncond.optimize_rules_{dnat,snat}_eval`, `optimize_rules_{valueset,dscp,intervalsethostorder,intervalset,intervalsetguarded,mixedpointrangeguarded,concat,concatguarded,setguarded,concatmulti,vmap,vmapguarded,dscpvmap}_correct_uncond` (15) | STAGE | each tagged `STAGE — composed into [optimize_table_correct_uncond_gen]` in the source |
| `Optimize_Uncond.optimize_table_correct_uncond_gen` | SUPPORTING | the general `(n, d)`-threaded whole-pipeline form |
| `Optimize_Uncond.optimize_table_uncond_correct` | SUPPORTING | DSL-level form of the optimizer headline |
| `Optimize_Uncond.optimize_table_uncond_compile_correct` | **HEADLINE** (optimizer axis) | = `optimize_table_uncond_correct` + `compile_chain_sets_correct` |

## 3. The evaluator matrix

Nine DSL entry points (`Semantics.v`) have **disjoint** feature coverage.
Every evaluator takes the shared mutable world as an explicit `env` argument
(`eval : … -> env -> packet -> …`); an evaluator that "returns env" hands back
the world it LEAVES (`… -> option verdict * env`), so the signature shows the
state flow — but not which features an evaluator silently drops.  Rows are the
entry points; every "no" cell names the bridging theorem that relates the
evaluator to the one that does cover the feature, or says `no bridging
theorem`.

| entry point | threads writes | returns env | jump/goto/return | NAT effect | multi-chain |
|---|---|---|---|---|---|
| `eval_rules` (+`eval_chain`) | no — *no bridging theorem* | no — *no bridging theorem* | no — bridge `eval_rules_jumpfree_eq_j` (= `eval_rules_j` on jump-free rules) | no — *no bridging theorem* | no — bridge `eval_chain_eq_table_jumpfree` (jump-free chains) |
| `eval_rules_mut` (+`eval_chain_mut`) | **yes** (`dsl_rule_step`) | no — bridge `eval_rules_mut_env_fst` / `eval_chain_mut_env_fst` (`eval_rules_mut` = `fst` of `eval_rules_mut_env`) | no — *no bridging theorem* | no — bridge `eval_rules_trace_verdict` (trace verdict = mut verdict unless `trace_nat_drops`) | no — *no bridging theorem* |
| `eval_rules_mut_env` (+`eval_chain_mut_env`) | **yes** | **yes** | no — *no bridging theorem* | no — *no bridging theorem* | no — *no bridging theorem* |
| `eval_rules_trace` (+`eval_chain_trace`) | **yes** | **yes** (returns `env * packet`; `chain_out`) | no — *no bridging theorem* | **yes** (`apply_nat`, `trace_nat_drops`; known infidelity: fires on an `OVmapNat` vmap **hit** too — see the ledger) | no — *no bridging theorem* (chains composed manually via `chain_out`) |
| `eval_rules_j` / `eval_table` | no — *no bridging theorem* | no — *no bridging theorem* | **yes** (fuel-bounded) | no — *no bridging theorem* | **user chains** (jump targets) |
| `eval_ruleset` | no — *no bridging theorem* | no — *no bridging theorem* | **yes** (via `eval_table`) | no — *no bridging theorem* | **base chains** across tables |
| `eval_hook` | no — *no bridging theorem* | no — *no bridging theorem* | **yes** | no — *no bridging theorem* | **hook dispatch** (priority-ordered) |
| `seq_eval` | no — the between-packet step is external/arbitrary; *no bridging theorem* | threaded between packets (by `step`) | **yes** (instantiated with `eval_hook`) | no — *no bridging theorem* | **yes** (via `eval_hook`) |
| `seq_eval_env` | **yes** (instantiated with `eval_chain_mut_env`) | threaded between packets (by the evaluator itself) | no — *no bridging theorem* | no — *no bridging theorem* | no — *no bridging theorem* |

**Fuel adequacy (RESOLVED, M4 config-proof soundness)**: the jump strand is
fuel-bounded, and `eval_table` maps fuel EXHAUSTION to the chain policy — a
verdict the kernel can never produce (nft rejects jump loops at load time;
kernel jump stack is 16 deep, `NFT_JUMP_STACK_SIZE`).  Naive fuel
monotonicity (`eval_rules_j fuel = Some v -> eval_rules_j (S fuel) = Some v`)
is **false** — machine-refuted by
`Semantics.eval_rules_j_not_naively_monotone` (an under-fueled callee's
exhaustion reads as fall-through and more fuel flips the verdict).  The
honest results (Semantics.v § "Fuel discipline for the jump strand"):
`eval_rules_jx` makes exhaustion observable; clean runs agree with
`eval_rules_j` (`eval_rules_jx_agree`), are Kleene-monotone
(`eval_rules_jx_monotone`), and are the verdict at every larger fuel
(`eval_rules_j_fuel_stable`); above the computable
`sufficient_fuel cs rs`, under the `chain_ranked` acyclicity witness, every
run is clean (`eval_rules_jx_adequate`), the verdict is fuel-independent
(`eval_table_fuel_indep`), and the policy fallback is provably genuine
fall-through (`eval_table_policy_is_fallthrough`).  Compiled mirror:
`Correct.run_table_fuel_indep_compiled` (via `compile_table_correct`; no
second VM development — rationale on the corollary).  User surface:
`Nft_Tactics.nft_*_fuel_indep`, CONFIG_PROOFS.md § "Choosing the fuel
budget", worked instance `Tutorial_Proofs.tutorial_blocks_exactly_any_fuel`.

**Mutation × jump/goto is not jointly verified**: no evaluator both threads
writes and follows jumps, and no theorem relates the mutation strand
(`eval_rules_mut*`, `eval_rules_trace`, `seq_eval_env`) to the jump strand
(`eval_rules_j`/`eval_table`/`eval_ruleset`/`eval_hook`/`seq_eval`). A
`meta mark set` inside a jump target is out of scope of every theorem above.
Note the mutation theorems themselves carry **no jump-freedom hypothesis** —
they are unconditional DSL=VM agreement facts that DO instantiate on a
jump-bearing chain, where both sides treat the realised `Jump`/`Goto` as a
(kernel-wrong) fall-through; the faithful domain is delimited by prose + the
pin `Correct.mut_strand_jump_pin`, not in-theorem. Why a `chain_jumpfree`
hypothesis was deliberately NOT added (it would shrink the agreement facts'
domain without making any chain faithful; no jump-aware *mutating* evaluator
exists to bridge to; `chain_jumpfree` is defined at the fixed entry state and
would need a step-threaded redefinition): the rationale block on the mutation
strata in `Correct.v` (before the fidelity bridge).

The bytecode VM mirrors the DSL rows one-for-one (`run_rule(s)`,
`run_program(_mut,_mut_env)`, `run_rules_j`/`run_table`, `run_ruleset`); each
compile theorem in §2 equates one DSL row with its VM mirror.  The VM mirror of
the `fst` bridge is `run_program_mut_env_fst` / `run_chain_mut_env_fst`.

Every mutation/trace evaluator consumes a single per-rule STEP function —
`dsl_rule_step` (DSL) / `vm_rule_step` (VM).  Since the T1 single-fold rework,
each is a projection of ONE left-to-right fold per rule —
`Semantics.rule_step` (DSL) / `Semantics.run_rule_step` (bytecode) — modelling
exactly the kernel's expression walk (nf_tables_core.c
`nft_rule_dp_for_each_expr`): every expression (match, statement operand,
verdict-map key, limiter check) sees the writes — packet-local meta/ct sets
AND dynset env writes — of the expressions BEFORE it in the SAME rule; a
failing match or breaking load stops the walk KEEPING the earlier writes; a
statement after a terminal verdict never runs; the post-outcome (`r_after`)
statements run (writes included) only on a `Continue` fall-through.  The step
adds the limiter consumption sweep, and on the VM side only the `numgen inc`
counter advance (`numgen_sweep_prog` — the DSL step deliberately has no
numgen twin; rationale on `Semantics.dsl_rule_step`).

The DSL/VM agreement obligation is the one per-rule equation
`vm_rule_step_compile_rule : rule_numgen_free r = true ->
vm_rule_step (compile_rule r) e p = dsl_rule_step r e p` (`Correct.v`), built
on the UNCONDITIONAL fold bridge `run_rule_step_compile_rule :
run_rule_step empty_rf (compile_rule r) e p = rule_step r e p` (degenerate
zero-field operands included — `Compile.compile_vsrc` pins their source
register).  `rule_numgen_free` (IR/Syntax.v) is the strand's ONLY hypothesis,
and it is discharged by THEOREM over every frontend-emitted program:
`Lower.lower_rule` refuses incremental numgen fail-loud (`LEnumgen`), and
`Lower_Proofs.lower_ruleset_numgen_free` proves every chain of every
successful lowering numgen-free — not a per-ruleset gate spot-check.

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
  - the M4 fuel-adequacy heads (§3): `Semantics.eval_rules_jx_monotone`,
    `eval_rules_j_fuel_stable`, `eval_rules_jx_adequate`,
    `eval_table_fuel_indep`, `eval_table_policy_is_fallthrough`,
    `Correct.run_table_fuel_indep_compiled`,
    `Nft_Tactics.nft_yields_fuel_indep`,
    `Tutorial_Proofs.tutorial_blocks_exactly_any_fuel` (8 theorems),
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
