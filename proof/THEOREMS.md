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
  supporting strata, `Elab.elab_matchcond_correct`, and the representation
  ratchet `Semantics.run_rule_outcome_eq`) from the compiled `.vo` files and
  fails on anything but `Closed under the global context`.
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
| mutation / cross-packet learning | `compile_seq_mut_correct` | `Correct.v` | compiled single-chain traversal threading the env each packet LEAVES (meta/ct writes, dynset learning) = DSL sequence, under `mut_wf` well-formedness |
| optimizer pipeline | `optimize_table_uncond_compile_correct` | `Optimize_Uncond.v` | the shipped 18-stage `nft -o` pipeline + compilation preserves every packet's verdict against the synthesised declarations, for **any input chain** (no `rules_clean`, no freshness precondition) |
| typed source elaboration | `elab_matchcond_correct` | `Elab.v` | the typed source-match layer (`Elab.tmatch`: typed immediates, CIDR-with-plen, ifname wildcards) elaborates onto the byte IR **evaluation-exactly**, for every match/env/packet — generated sources (`*_Gen.v`) carry typed terms whose meaning is the byte IR's by this theorem |

Scope notes (each also sits on the theorem in the source):

- The optimizer headline is **per chain**: quantified over a single chain and
  all environments/packets. Multi-chain/hook preservation is the separate
  `compile_ruleset_correct`/`compile_hook_correct` family — **not composed
  with the optimizer**.
- The compiler axis (jump strand) threads **no writes**; the mutation axis
  follows **no jumps**. **Mutation × jump/goto is not jointly verified** (see
  the evaluator matrix, §3).

## 2. Classification of every `Theorem`/`Corollary` in `Correct.v` and `Optimize*.v`

### `Correct.v` (the compiler strata, bottom-up)

| declaration | class | derivation edge |
|---|---|---|
| `compile_chain_correct` | SUPPORTING (stratum 1: one chain, pure verdict) | from `run_program_compile_chain`; consumed by the optimizer headline via `compile_chain_sets_correct` |
| `compile_chain_sets_correct` (Corollary) | SUPPORTING | corollary of `compile_chain_correct` at `env_with_sets`; consumed by `optimize_table_uncond_compile_correct` |
| `compile_chain_mut_correct` | SUPPORTING (stratum 2: + in-traversal mutation) | **derived**: the `fst` projection of stratum 3 (`run_program_mut_env_fst` / `eval_rules_mut_env_fst`), no second induction |
| `compile_chain_mut_env_correct` | SUPPORTING (stratum 3: + env the chain leaves) | from `run_program_mut_env_compile_chain`, one induction over the per-rule step equation `vm_rule_step_compile_rule` (`vm_rule_step (compile_rule r) e p = dsl_rule_step r e p` under `mut_wf`) |
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
| `eval_rules_trace` (+`eval_chain_trace`) | **yes** | **yes** (returns `env * packet`; `chain_out`) | no — *no bridging theorem* | **yes** (`apply_nat`, `trace_nat_drops`) | no — *no bridging theorem* (chains composed manually via `chain_out`) |
| `eval_rules_j` / `eval_table` | no — *no bridging theorem* | no — *no bridging theorem* | **yes** (fuel-bounded) | no — *no bridging theorem* | **user chains** (jump targets) |
| `eval_ruleset` | no — *no bridging theorem* | no — *no bridging theorem* | **yes** (via `eval_table`) | no — *no bridging theorem* | **base chains** across tables |
| `eval_hook` | no — *no bridging theorem* | no — *no bridging theorem* | **yes** | no — *no bridging theorem* | **hook dispatch** (priority-ordered) |
| `seq_eval` | no — the between-packet step is external/arbitrary; *no bridging theorem* | threaded between packets (by `step`) | **yes** (instantiated with `eval_hook`) | no — *no bridging theorem* | **yes** (via `eval_hook`) |
| `seq_eval_env` | **yes** (instantiated with `eval_chain_mut_env`) | threaded between packets (by the evaluator itself) | no — *no bridging theorem* | no — *no bridging theorem* | no — *no bridging theorem* |

**Mutation × jump/goto is not jointly verified**: no evaluator both threads
writes and follows jumps, and no theorem relates the mutation strand
(`eval_rules_mut*`, `eval_rules_trace`, `seq_eval_env`) to the jump strand
(`eval_rules_j`/`eval_table`/`eval_ruleset`/`eval_hook`/`seq_eval`). A
`meta mark set` inside a jump target is out of scope of every theorem above.

The bytecode VM mirrors the DSL rows one-for-one (`run_rule(s)`,
`run_program(_mut,_mut_env)`, `run_rules_j`/`run_table`, `run_ruleset`); each
compile theorem in §2 equates one DSL row with its VM mirror.  The VM mirror of
the `fst` bridge is `run_program_mut_env_fst` / `run_chain_mut_env_fst`.

Every mutation/trace evaluator consumes a single per-rule STEP function —
`dsl_rule_step` (DSL) / `vm_rule_step` (VM), each returning the pair
(loadability-guarded verdict, `(env, packet)` left: writes + numgen advance +
limiter consumption).  The DSL/VM agreement obligation is the one equation
`vm_rule_step_compile_rule : mut_wf r = true -> vm_rule_step (compile_rule r) e p
= dsl_rule_step r e p` (`Correct.v`).  `mut_wf` itself is stated entirely on the
source AST: its numgen conjunct is the syntactic `rule_numgen_free`
(`Semantics.v`), which equals the bytecode-side `numgen_free_prog (compile_rule
r)` by `Correct.numgen_free_compile_rule` (the old-shape hypothesis is restored
verbatim by `Correct.mut_wf_prog_eq`).

## 4. Axiom-freedom gates

- `make axioms` — `Print Assumptions` over the HEADLINE set + the `Correct.v`
  strata + the optimizer DSL form (10 theorems); fails on anything but
  `Closed under the global context`.  The `pre_split_*` ratchet corollaries in
  `Main.v` are guarded by in-file `Print Assumptions` on every `make proofs`.
- In-file build-time guards (`Print Assumptions` runs on every `make proofs`):
  end of `Correct.v` (all 8 compiler strata), end of `Optimize_Uncond.v` (both
  optimizer entry points), all of `theories/Compiler/Main.v` (the four entry-point
  aliases), plus per-file guards in demo/side files (`Fib_Local.v`,
  `Optimize_Table.v`, …).
- One-liner (the historical gate):
  `cd theories && printf 'From Nft Require Import Correct Optimize.\nPrint Assumptions compile_chain_correct.\n' | coqtop -R . Nft`
  → `Closed under the global context`.

## 6. Representation ratchets (M4)

Representation changes ship with an in-kernel equivalence to the shape they
replaced:

| change | ratchet |
|---|---|
| rule outcome: 1 verdict + 5 optional slots -> `Syntax.outcome` sum | `Semantics.run_rule_outcome_eq`: for every well-formed product (`Syntax.prod_wf`), `outcome (rule_of_prod rp) = outcome_prod rp` on all env/packets (`outcome_prod` is the pre-sum evaluation, verbatim, over the historical record `Syntax.rule_prod`) |
| typed source matches (`Elab.tmatch`) over the byte IR | `Elab.elab_matchcond_correct` (evaluation-exact elaboration); byte-faithfulness of the typed encodings: `Nftval.encode_*` vm_compute witnesses + `Elab.prefix_aligned_24`/`prefix_unaligned_20`/`elab_port_22`/`elab_wildcard` |
| `MMasked` polarity bool -> `cmpop` | the eval clause is `eval_cmp op` (the VM's own comparator); `MFlagsSet` names the positive implicit-bitmask idiom (`(field & X) <> 0`, `CNe`) |
| `nat_kind`/`nat_family`/dynset-op strings -> `Bytecode.nat_op`/`nat_af`/`dynset_op` | rendering strings exist only at the codec/netlink boundary (extracted/codec.ml, nl_send.ml); `make corpus` (2532/2532) pins the rendered bytes unchanged |
| `BDep` dependency tag | a *definitional alias* of `BMatch` (`Syntax.BDep`): evaluation, loadability, compilation are those of the match it wraps, definitionally |
