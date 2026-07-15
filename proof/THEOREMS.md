# THEOREMS.md — the claim surface, mapped

What exactly is proved, by which theorem, under which evaluator, and is it
axiom-free — without reading 3000 lines of `Correct.v`.

- Machine-checked entry-point restatements: [`theories/Main.v`](theories/Main.v)
  (each followed by `Print Assumptions`).
- Axiom gate: `make axioms` re-checks every HEADLINE theorem below (plus the
  supporting strata) from the compiled `.vo` files and fails on anything but
  `Closed under the global context`.
- Classes used below:
  - **HEADLINE** — the single top theorem of a verified axis; what the project claims.
  - **STAGE** — a per-pass/per-stage theorem composed into a headline.
  - **SUPPORTING** — a stratum or bridge a headline is derived from (or that
    scopes one); not independently a claim.
  - **SUPERSEDED** — kept for history; subsumed by a successor named in its marker.
  - **DEMO** — an executable regression pin / witness (`Example` in the source);
    not part of the claim surface.

## 1. The entry points — exactly one top theorem per verified axis

| axis | HEADLINE theorem | file | what it says |
|---|---|---|---|
| compiler (rulesets/hooks) | `compile_hook_correct` | `Correct.v` | compiled hook dispatch (jump/goto/return, user chains, multi-table, priority order) = DSL `eval_hook`, for every fuel/ruleset/hook/packet/environment |
| compiler, sequence form | `compile_seq_correct` | `Correct.v` | the same, lifted over a packet sequence under an **arbitrary step** `verdict -> env -> env` — a per-packet **congruence corollary** of `compile_hook_correct`, *not* a proof about ruleset-generated state (that is the next axis) |
| mutation / cross-packet learning | `compile_seq_mut_correct` | `Correct.v` | compiled single-chain traversal threading the env each packet LEAVES (meta/ct writes, dynset learning) = DSL sequence, under `mut_wf` well-formedness |
| optimizer pipeline | `optimize_table_uncond_compile_correct` | `Optimize_Uncond.v` | the shipped 18-stage `nft -o` pipeline + compilation preserves every packet's verdict against the synthesised declarations, for **any input chain** (no `rules_clean`, no freshness precondition) |

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
| `compile_chain_mut_correct` | SUPPORTING (stratum 2: + in-traversal mutation) | from `run_program_mut_compile_chain` / `vm_step_dsl_step` |
| `compile_chain_mut_env_correct` | SUPPORTING (stratum 3: + env the chain leaves) | from `run_program_mut_env_compile_chain` |
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

### `Optimize.v` / `Optimize_Merge.v` (base pass and history)

| declaration | class | note |
|---|---|---|
| `Optimize.optimize_chain_correct` | SUPERSEDED (as a standalone headline) | successor `optimize_table_uncond_correct`; `optimize_chain` survives as the pipeline's base stage and this theorem as that stage's lemma |
| `Optimize_Merge.eval_rules_value_merge` | SUPPORTING | 2-adjacent-rule merge certificate behind the `setsN` recogniser lineage |
| `Optimize_Merge.eval_rules_range_value_merge` | SUPERSEDED, **known-unfaithful** | models `6,7 => 6-7` as a RANGE where `nft -o` emits the SET `{6,7}`; used by no shipped pass (marker on the theorem) |
| `Optimize_Merge.optimize_chain2_correct` | SUPERSEDED | `optimize_chain2` is not composed into the shipped pipeline |

### Per-pass certificates and stages (`Optimize_*.v`)

| declaration | class | note |
|---|---|---|
| `Optimize_Vmap.eval_rules_vmap_merge2` | SUPPORTING | certificate consumed by the `vmapN` stage lineage |
| `Optimize_Concat.eval_rules_concat_merge2` | SUPPORTING | certificate for the two-selector concat merge |
| `Optimize_ConcatK.eval_rules_concat_mergeK` | SUPPORTING | K-row concat certificate |
| `Optimize_Mapn.eval_rules_mut_map_merge` / `eval_rules_map_merge` | SUPPORTING | mark-map merge certificates (`mapn` stage; a labelled sound superset of `nft -o`, see Optimize_Table.v fidelity contract) |
| `Optimize_Mapn.mapn_bare_diverges_offkey` | DEMO | pins why the head guard cannot be dropped |
| `Optimize_Mapn.optimize_rules_mapn_eval` | STAGE | composed into `optimize_table` |
| `Optimize_Dnat.eval_rules_dnat_merge`, `apply_nat_dnat_eq`, `apply_nat_dnat_merge1` (Cor.) | SUPPORTING | bare-NAT-map merge: verdict + data-plane NAT-effect preservation |
| `Optimize_Snat.eval_rules_snat_merge`, `apply_nat_snat_eq`, `apply_nat_snat_merge1` (Cor.) | SUPPORTING | symmetric snat forms |
| `Optimize_Normalize.normalize_chain_eval` | STAGE | verdict-preserving head normalisation run first by `optimize_table_uncond` |
| `Optimize_Table.optimize_chain_clean` | SUPPORTING | seam lemma: the base pass preserves `rules_clean` |
| `Optimize_Uncond.optimize_rules_{dnat,snat}_eval`, `optimize_rules_{setsN,dscp,ivsett,ivset,ivsetg,ivmixg,concatN,concatM,setg,concatK,vmapN,vmapNg,dscpv}_correct_uncond` (15) | STAGE | each tagged `STAGE — composed into [optimize_table_correct_uncond_gen]` in the source |
| `Optimize_Uncond.optimize_table_correct_uncond_gen` | SUPPORTING | the general `(n, d)`-threaded whole-pipeline form |
| `Optimize_Uncond.optimize_table_uncond_correct` | SUPPORTING | DSL-level form of the optimizer headline |
| `Optimize_Uncond.optimize_table_uncond_compile_correct` | **HEADLINE** (optimizer axis) | = `optimize_table_uncond_correct` + `compile_chain_sets_correct` |

## 3. The evaluator matrix

Nine DSL entry points (`Semantics.v`) with near-identical signatures have
**disjoint** feature coverage; nothing in a signature reveals what an
evaluator silently drops. Rows are the entry points; every "no" cell names the
bridging theorem that relates the evaluator to the one that does cover the
feature, or says `no bridging theorem`.

| entry point | threads writes | returns env | jump/goto/return | NAT effect | multi-chain |
|---|---|---|---|---|---|
| `eval_rules` (+`eval_chain`) | no — *no bridging theorem* | no — *no bridging theorem* | no — bridge `eval_rules_jumpfree_eq_j` (= `eval_rules_j` on jump-free rules) | no — *no bridging theorem* | no — bridge `eval_chain_eq_table_jumpfree` (jump-free chains) |
| `eval_rules_mut` (+`eval_chain_mut`) | **yes** (`dsl_step`) | no — *no bridging theorem* | no — *no bridging theorem* | no — bridge `eval_rules_trace_verdict` (trace verdict = mut verdict unless `trace_nat_drops`) | no — *no bridging theorem* |
| `eval_rules_mut_env` (+`eval_chain_mut_env`) | **yes** | **yes** | no — *no bridging theorem* | no — *no bridging theorem* | no — *no bridging theorem* |
| `eval_rules_trace` (+`eval_chain_trace`) | **yes** | returns whole packet (`chain_out`) | no — *no bridging theorem* | **yes** (`apply_nat`, `trace_nat_drops`) | no — *no bridging theorem* (chains composed manually via `chain_out`) |
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
compile theorem in §2 equates one DSL row with its VM mirror.

## 4. Axiom-freedom gates

- `make axioms` — `Print Assumptions` over the HEADLINE set + the `Correct.v`
  strata + the optimizer DSL form (10 theorems); fails on anything but
  `Closed under the global context`.
- In-file build-time guards (`Print Assumptions` runs on every `make proofs`):
  end of `Correct.v` (all 8 compiler strata), end of `Optimize_Uncond.v` (both
  optimizer entry points), all of `theories/Main.v` (the four entry-point
  aliases), plus per-file guards in demo/side files (`Fib_Local.v`,
  `Optimize_Table.v`, …).
- One-liner (the historical gate):
  `cd theories && printf 'From Nft Require Import Correct Optimize.\nPrint Assumptions compile_chain_correct.\n' | coqtop -R . Nft`
  → `Closed under the global context`.
