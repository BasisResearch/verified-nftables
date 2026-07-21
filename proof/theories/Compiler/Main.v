(** * Main: the entry-point theorems of the development.

    ONE theorem per verified axis, restated verbatim from its home file, so an
    external reviewer can answer "what exactly is proved, under which
    evaluator, and is it axiom-free?" from this file alone.  Each restatement
    is a definitional alias ([exact] of the original — no new proof term) and
    is followed by [Print Assumptions], so the build log carries an
    axiom-freedom verdict for every entry point; `make axioms` re-checks the
    same set from the compiled .vo files and fails on anything but "Closed
    under the global context".

    The classification of EVERY other Theorem/Corollary (HEADLINE / STAGE /
    SUPPORTING / SUPERSEDED / DEMO, with derivation edges) and the evaluator
    feature matrix live in [proof/THEOREMS.md]. *)

From Stdlib Require Import List.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics Compile
  Correct Optimize Optimize_Table Optimize_Uncond Optimize_Linearize.

(** ** Axis 0 — THE UNIFIED SEMANTICS ([compile_hook_u_correct] /
    [compile_seq_hook_u_correct]): mutation x jump/goto/return x multi-chain
    x hook dispatch, jointly.

    For every fuel, ruleset, hook, environment and packet: the compiled VM's
    unified fold — the evaluator that BOTH threads every state effect
    (meta/ct writes, dynset learning, notrack, limiter depletion) AND follows
    control flow (jump/goto/return, user chains, multi-table and
    hook/priority dispatch) — reproduces the DSL's unified fold, verdict AND
    the (env, packet) the traversal leaves.  Effectful rules under control
    flow are certified HERE; every other evaluator axis below is a proven
    projection of this one on its licensed sub-domain (the evaluator matrix
    in Semantics.v's header / THEOREMS.md).  Since M3 the state carried
    includes the NAT data plane: the dnat/snat/masquerade/redirect packet
    rewrite, the flow-keyed [e_nat] tuple establish/reuse and the
    no-usable-address NF_DROP, all evaluated AT the NAT terminal inside the
    per-rule fold (outcome provenance: a vmap hit never runs it) — see
    [compile_nat_effect_correct].  The only hypothesis is
    numgen-freedom, discharged for every frontend-emitted program by
    [Lower_Proofs.lower_ruleset_numgen_free]. *)
Theorem main_compile_hook_u_correct : forall h fuel rs e p,
  forallb base_numgen_free (select_hook rs h) = true ->
  run_ruleset_u h fuel (map compile_base (select_hook rs h)) e p
  = eval_hook_u h fuel rs e p.
Proof. exact compile_hook_u_correct. Qed.
Print Assumptions main_compile_hook_u_correct.

(** NAT data-plane axis (M3): the per-rule bridge under its NAT-effect name —
    the compiled fold performs the identical NAT effect, at every hook. *)
Theorem main_compile_nat_effect_correct : forall h r e p,
  rule_numgen_free r = true ->
  run_rule_step h empty_rf (compile_rule r) e p = rule_step h r e p.
Proof. exact compile_nat_effect_correct. Qed.
Print Assumptions main_compile_nat_effect_correct.

(** Cross-packet form: the ruleset's own learning (dynset adds, limiter
    depletion) threads packet-to-packet through jumps and multi-chain
    dispatch, compiler-preserved. *)
Theorem main_compile_seq_hook_u_correct : forall h fuel rs e packets,
  forallb base_numgen_free (select_hook rs h) = true ->
  seq_eval_env (run_ruleset_env_u h fuel (map compile_base (select_hook rs h))) e packets
  = seq_eval_env (eval_hook_env_u h fuel rs) e packets.
Proof. exact compile_seq_hook_u_correct. Qed.
Print Assumptions main_compile_seq_hook_u_correct.

(** ** Axis 1 — the compiler, at ruleset/hook level ([compile_hook_correct]).

    For every fuel, every registered ruleset [rs], every netfilter hook [h] and
    every packet [p]: selecting and priority-ordering the base chains for [h],
    compiling each (with its jump-target chain environment), and running the
    netfilter dispatch over the compiled bases yields exactly the verdict of
    the DSL dispatch [eval_hook].  This is the top of the jump-aware,
    mutation-free strand: it covers jump/goto/return, user chains, multi-table
    and hook/priority dispatch, and quantifies over the whole environment
    (sets/maps/conntrack/routes), but threads no writes between rules: it is
    the WRITE-FREE projection of axis 0 ([Semantics.eval_hook_u_writefree]
    licenses it on write-free bases; a base with writes is evaluated by
    axis 0's unified evaluator). *)
Theorem main_compile_hook_correct : forall fuel rs h e p,
  run_ruleset fuel (map compile_base (select_hook rs h)) e p = eval_hook fuel rs h e p.
Proof. exact compile_hook_correct. Qed.
Print Assumptions main_compile_hook_correct.

(** ** Axis 1, sequence form ([compile_seq_correct]) — a congruence corollary.

    Lifting axis 1 over a packet sequence whose shared environment is updated
    between packets by an ARBITRARY, caller-supplied
    [step : verdict -> env -> env].  Because [step] is unconstrained, this is a
    per-packet congruence lifted over a sequence — it does NOT assert that the
    ruleset's own state accumulation is preserved (that is axis 2 below, where
    the env evolution is generated by the ruleset itself). *)
Theorem main_compile_seq_correct : forall fuel rs h step e packets,
  seq_eval (fun e' p => run_ruleset fuel (map compile_base (select_hook rs h)) e' p)
           step e packets
  = seq_eval (fun e' p => eval_hook fuel rs h e' p) step e packets.
Proof. exact compile_seq_correct. Qed.
Print Assumptions main_compile_seq_correct.

(** ** Axis 2 — mutation and cross-packet learning ([compile_seq_mut_correct]).

    For a single chain [c] whose rules are numgen-free ([rule_numgen_free] —
    the ONLY hypothesis of the mutation strand; incremental `numgen` has no
    parser/DSL surface and the LOWERING rejects it fail-loud
    ([Lower.LEnumgen]), so [Lower_Proofs.lower_ruleset_numgen_free] discharges
    this hypothesis for EVERY frontend-emitted program — not a gate
    spot-check).  Per rule the semantics is the SINGLE left-to-right fold
    [rule_step]/[run_rule_step] (kernel nft_rule_dp_for_each_expr): every
    expression sees the writes — packet-local meta/ct sets AND dynset env
    writes — of the expressions before it in the SAME rule.  With that:
    running a packet sequence with the compiled bytecode, threading the
    environment each traversal LEAVES (meta/ct writes, dynset-learned set/map
    elements) into the next packet, reproduces the DSL sequence verdict-for-
    verdict.  Here — unlike axis 1's sequence form — the env evolution is
    generated by the ruleset itself, so an `add @s {…}` on an earlier packet
    provably reaches a `lookup @s` on a later one.  This strand is flat
    (single chain, no chain environment): it is the TRANSFER-FREE projection
    of axis 0 ([Semantics.eval_table_u_mut_proj] licenses it on [rule_plain]
    chains; a chain that realises a jump/goto/return is evaluated by axis 0's
    unified evaluator). *)
Theorem main_compile_seq_mut_correct : forall h c e packets,
  forallb rule_numgen_free (c_rules c) = true ->
  seq_eval_env (fun e' p => run_chain_mut_env h (compile_chain c) (c_policy c) e' p) e packets
  = seq_eval_env (fun e' p => eval_chain_mut_env h c e' p) e packets.
Proof. exact compile_seq_mut_correct. Qed.
Print Assumptions main_compile_seq_mut_correct.

(** ** Axis 3 — the optimizer pipeline, end-to-end to the bytecode
    ([optimize_table_uncond_compile_correct]).

    For every input chain [c] — NO cleanliness or freshness precondition —
    running the shipped 18-stage `nft -o` consolidation pipeline
    ([optimize_table_uncond], the term the CLI executes), then DEFAULT-
    compiling the optimised chain ([compile_chain_default]: nft's always-on
    payload-merge + xor-fold linearization, then [compile_chain] — the term
    `nftc optimize`/`nftc send` emit) and running the VM against the
    synthesised set/map declarations, yields exactly the DSL verdict of the
    ORIGINAL chain, for every packet and every base environment.  Scope: PER
    CHAIN — the optimizer is quantified over a single chain and all
    environments/packets; multi-chain/hook preservation is axis 1's separate
    family, not composed with the optimizer. *)
Theorem main_optimize_table_uncond_compile_correct : forall c base p n' d' c',
  optimize_table_uncond c = (n', d', c') ->
  run_chain (compile_chain_default c') (c_policy c') (env_with_sets base d') p
  = eval_chain c (env_with_sets base empty_decls) p.
Proof. exact optimize_table_uncond_compile_correct. Qed.
Print Assumptions main_optimize_table_uncond_compile_correct.

(** ** Axis 3b — the DEFAULT compile pipeline
    ([Optimize_Linearize.compile_chain_default_correct]).

    nft applies two single-rule rewrites UNCONDITIONALLY at netlink
    linearization — no `nft -o` involved: the adjacent-payload-load merge
    (class I, [Optimize_PayMerge]) and the bitwise-xor constant fold (class L,
    [Optimize_XorFold]).  [compile_chain_default] composes them into the
    default compile — the term `nftc compile` emits — and this headline
    carries [compile_chain_correct] through both stages: for every chain,
    environment and packet, the default pipeline's bytecode yields exactly the
    source chain's DSL verdict. *)
Theorem main_compile_chain_default_correct : forall c e p,
  run_chain (compile_chain_default c) (c_policy c) e p = eval_chain c e p.
Proof. exact compile_chain_default_correct. Qed.
Print Assumptions main_compile_chain_default_correct.

(* ================================================================== *)
(** ** Ratchet corollaries: every pre-split headline claim, restated.

    The state split moved the shared mutable world out of [packet] into an
    explicit [env] argument, so the pre-split statements — quantified over ONE
    bundled record carrying both — do not survive verbatim.  [Packet.pstate]
    is that bundled shape ([ps_env] + [ps_wire]); each corollary below is the
    corresponding pre-split headline statement transported through it: a
    pre-split packet value [p] becomes [s : pstate], its embedded world
    [ps_env s], its wire/flag/oracle half [ps_wire s], and the pre-split
    [set_env p e'] (install [e'] as [p]'s world) becomes evaluating [ps_wire s]
    under [e'].  Every proof is [exact]/[apply] of the new theorem — no new
    proof terms, so strength is preserved in both directions by definition. *)

Corollary pre_split_compile_chain_correct : forall c (s : pstate),
  run_chain (compile_chain c) (c_policy c) (ps_env s) (ps_wire s)
  = eval_chain c (ps_env s) (ps_wire s).
Proof. intros c s. apply compile_chain_correct. Qed.
Print Assumptions pre_split_compile_chain_correct.

Corollary pre_split_compile_chain_mut_correct : forall h c (s : pstate),
  forallb rule_numgen_free (c_rules c) = true ->
  run_chain_mut h (compile_chain c) (c_policy c) (ps_env s) (ps_wire s)
  = eval_chain_mut h c (ps_env s) (ps_wire s).
Proof. intros h c s H. apply compile_chain_mut_correct. exact H. Qed.
Print Assumptions pre_split_compile_chain_mut_correct.

Corollary pre_split_compile_chain_mut_env_correct : forall h c (s : pstate),
  forallb rule_numgen_free (c_rules c) = true ->
  run_chain_mut_env h (compile_chain c) (c_policy c) (ps_env s) (ps_wire s)
  = eval_chain_mut_env h c (ps_env s) (ps_wire s).
Proof. intros h c s H. apply compile_chain_mut_env_correct. exact H. Qed.
Print Assumptions pre_split_compile_chain_mut_env_correct.

(** Pre-split [compile_seq_mut_correct] ran each traversal on
    [set_env p e'] — the sequence packet's WIRE under the THREADED env [e'] —
    so the transported claim quantifies over pre-split packets ([pstate]s) and
    evaluates their wire halves under the threaded env. *)
Corollary pre_split_compile_seq_mut_correct : forall h c e (packets : list pstate),
  forallb rule_numgen_free (c_rules c) = true ->
  seq_eval_env (fun e' s => run_chain_mut_env h (compile_chain c) (c_policy c) e' s)
               e (map ps_wire packets)
  = seq_eval_env (fun e' s => eval_chain_mut_env h c e' s) e (map ps_wire packets).
Proof. intros h c e packets H. apply compile_seq_mut_correct. exact H. Qed.
Print Assumptions pre_split_compile_seq_mut_correct.

Corollary pre_split_compile_table_correct : forall fuel cs base (s : pstate),
  run_table fuel (compile_env cs) (compile_chain base) (c_policy base) (ps_env s) (ps_wire s)
  = eval_table fuel cs base (ps_env s) (ps_wire s).
Proof. intros fuel cs base s. apply compile_table_correct. Qed.
Print Assumptions pre_split_compile_table_correct.

Corollary pre_split_compile_ruleset_correct : forall fuel bases (s : pstate),
  run_ruleset fuel (map compile_base bases) (ps_env s) (ps_wire s)
  = eval_ruleset fuel bases (ps_env s) (ps_wire s).
Proof. intros fuel bases s. apply compile_ruleset_correct. Qed.
Print Assumptions pre_split_compile_ruleset_correct.

Corollary pre_split_compile_hook_correct : forall fuel rs h (s : pstate),
  run_ruleset fuel (map compile_base (select_hook rs h)) (ps_env s) (ps_wire s)
  = eval_hook fuel rs h (ps_env s) (ps_wire s).
Proof. intros fuel rs h s. apply compile_hook_correct. Qed.
Print Assumptions pre_split_compile_hook_correct.

Corollary pre_split_compile_seq_correct : forall fuel rs h step e (packets : list pstate),
  seq_eval (fun e' s => run_ruleset fuel (map compile_base (select_hook rs h)) e' s)
           step e (map ps_wire packets)
  = seq_eval (fun e' s => eval_hook fuel rs h e' s) step e (map ps_wire packets).
Proof. intros. apply compile_seq_correct. Qed.
Print Assumptions pre_split_compile_seq_correct.

(** Pre-split [optimize_table_uncond_correct] evaluated
    [set_env p (env_with_sets base d')] — the packet's wire under the
    decls-extended base env — so only the wire half of the pre-split packet
    survives into the transported claim. *)
Corollary pre_split_optimize_table_uncond_correct : forall c base (s : pstate) n' d' c',
  optimize_table_uncond c = (n', d', c') ->
  eval_chain c' (env_with_sets base d') (ps_wire s)
  = eval_chain c (env_with_sets base empty_decls) (ps_wire s).
Proof. intros c base s n' d' c' H. exact (optimize_table_uncond_correct c base (ps_wire s) n' d' c' H). Qed.
Print Assumptions pre_split_optimize_table_uncond_correct.

(** (The pre-split-era claim compiled with PLAIN [compile_chain] — the default
    pipeline's linearization stage did not exist yet — so the transported
    statement keeps that form; it is re-derived from
    [optimize_table_uncond_correct] + [compile_chain_sets_correct] now that the
    shipped headline [optimize_table_uncond_compile_correct] is stated over
    [compile_chain_default].) *)
Corollary pre_split_optimize_table_uncond_compile_correct : forall c base (s : pstate) n' d' c',
  optimize_table_uncond c = (n', d', c') ->
  run_chain (compile_chain c') (c_policy c') (env_with_sets base d') (ps_wire s)
  = eval_chain c (env_with_sets base empty_decls) (ps_wire s).
Proof.
  intros c base s n' d' c' H.
  rewrite (compile_chain_sets_correct c' base d' (ps_wire s)).
  exact (optimize_table_uncond_correct c base (ps_wire s) n' d' c' H).
Qed.
Print Assumptions pre_split_optimize_table_uncond_compile_correct.
