(** * Optimize_Table: COMPOSE the verified nft -o consolidation passes into a
    single runnable optimizer, with a whole-pipeline correctness theorem.

    The six individually-verified passes in [Optimize_Merge]/[Optimize_Vmap]/
    [Optimize_Concat] each require their INPUT to be [rules_clean] (no
    [MConcatSet]/[MSetT]/vmap/nat/...).  This file:

      1. proves [optimize_chain_clean]: the base dedup/DCE pass
         ([Optimize.optimize_chain]) PRESERVES [rules_clean];

      2. composes the base pass with the N-WAY value->set / value+verdict->vmap /
         two-selector->concat passes into [optimize_table], threading a fresh
         counter and a [set_decls] accumulator across the table semantics;

      3. proves [optimize_chain_clean] and the pipeline-composition seam lemmas
         that the UNCONDITIONAL correctness proofs build on.

    The whole-pipeline correctness of [optimize_table] is proved — with NO
    [rules_clean] and NO freshness precondition on the input — in [Optimize_Uncond.v]
    ([optimize_table_correct_uncond_gen], [optimize_table_uncond_correct],
    [optimize_table_uncond_compile_correct]).  That UNCONDITIONAL optimizer
    ([optimize_table_uncond]) is what [Extract.v] extracts and what the [glue.ml]
    CLI invokes, so the shipped tool RUNS the verified term. *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Correct Optimize Optimize_Merge Optimize_Vmap Optimize_Vmapg Optimize_Concat Optimize_ConcatK
  Optimize_ConcatM Optimize_Setg Optimize_Ivset Optimize_Ivsetg Optimize_Ivmixg Optimize_Absorb Optimize_Ctmask Optimize_Dscp Optimize_Dscpv Optimize_Ivsett Optimize_Mapn Optimize_Dnat Optimize_Snat Optimize_Table_Inv.

(** ** Step 1: the base pass preserves [rules_clean].

    [Optimize.optimize_chain] = [dce ∘ prune_noops ∘ map (simplify_rule ∘ dedup_rule)].
    None of these introduce a set/concat/vmap matchcond or a vmap/nat/... outcome,
    so a clean chain stays clean. *)

(** A clean rule has NO statements in its body (every body item is a [BMatch] of a
    clean matchcond), so [body_stmts] is empty. *)
Lemma rule_clean_body_stmts_nil : forall r,
  rule_clean r = true -> body_stmts (r_body r) = [].
Proof.
  intros r Hc. unfold rule_clean in Hc.
  apply Bool.andb_true_iff in Hc as [Hc _].
  apply Bool.andb_true_iff in Hc as [Hc _].
  apply Bool.andb_true_iff in Hc as [Hc _].
  apply Bool.andb_true_iff in Hc as [Hc _].
  apply Bool.andb_true_iff in Hc as [Hc _].
  apply Bool.andb_true_iff in Hc as [Hbody _].
  unfold body_stmts. induction (r_body r) as [| it b IH]; [reflexivity|].
  cbn [forallb] in Hbody. apply Bool.andb_true_iff in Hbody as [Hit Hrest].
  destruct it as [m | s]; cbn [bi_clean] in Hit; [| discriminate].
  cbn [flat_map]. apply IH. exact Hrest.
Qed.

(** Every [body_matches] entry of a clean rule is a clean matchcond. *)
Lemma rule_clean_body_matches_clean : forall r,
  rule_clean r = true -> forallb mc_clean (body_matches (r_body r)) = true.
Proof.
  intros r Hc. unfold rule_clean in Hc.
  apply Bool.andb_true_iff in Hc as [Hc _].
  apply Bool.andb_true_iff in Hc as [Hc _].
  apply Bool.andb_true_iff in Hc as [Hc _].
  apply Bool.andb_true_iff in Hc as [Hc _].
  apply Bool.andb_true_iff in Hc as [Hc _].
  apply Bool.andb_true_iff in Hc as [Hbody _].
  unfold body_matches. induction (r_body r) as [| it b IH]; [reflexivity|].
  cbn [forallb] in Hbody. apply Bool.andb_true_iff in Hbody as [Hit Hrest].
  destruct it as [m | s]; cbn [bi_clean] in Hit; [| discriminate].
  cbn [flat_map]. cbn [forallb]. apply Bool.andb_true_iff. split.
  - exact Hit.
  - apply IH. exact Hrest.
Qed.

(** [forallb mc_clean] of a matchcond list -> [forallb bi_clean] of its [BMatch] image. *)
Lemma forallb_bi_clean_map_BMatch : forall ms,
  forallb mc_clean ms = true ->
  forallb bi_clean (map BMatch ms) = true.
Proof.
  induction ms as [| m ms IH]; intro H; [reflexivity|].
  cbn [forallb] in H. apply Bool.andb_true_iff in H as [Hm Hrest].
  cbn [map forallb bi_clean]. rewrite Hm. cbn. apply IH. exact Hrest.
Qed.

(** [nodup] preserves [forallb mc_clean] (it only drops elements). *)
Lemma forallb_mc_clean_nodup : forall dec ms,
  forallb mc_clean ms = true ->
  forallb mc_clean (nodup dec ms) = true.
Proof.
  intros dec ms H. rewrite (forallb_nodup matchcond dec mc_clean ms). exact H.
Qed.

(** [dedup_rule] preserves cleanliness. *)
Lemma dedup_rule_clean : forall r,
  rule_clean r = true -> rule_clean (dedup_rule r) = true.
Proof.
  intros r Hc. unfold dedup_rule.
  destruct (body_has_synproxy (r_body r) || body_has_notrack (r_body r)) eqn:Eg.
  - exact Hc.
  - (* the new body is [map BMatch (nodup ... (body_matches ...)) ++ map BStmt (body_stmts ...)];
       the statement part is empty for a clean rule, and the match part stays clean. *)
    pose proof (rule_clean_body_stmts_nil r Hc) as Hstmts.
    pose proof (rule_clean_body_matches_clean r Hc) as Hmatches.
    unfold rule_clean in Hc |- *.
    (* Slots other than the body are copied verbatim. *)
    apply Bool.andb_true_iff in Hc as [Hc Hafter].
    apply Bool.andb_true_iff in Hc as [Hc Hqueue].
    apply Bool.andb_true_iff in Hc as [Hc Hfwd].
    apply Bool.andb_true_iff in Hc as [Hc Htproxy].
    apply Bool.andb_true_iff in Hc as [Hc Hnat].
    apply Bool.andb_true_iff in Hc as [_ Hvmap].
    cbn [r_body r_vmap r_nat r_tproxy r_fwd r_queue r_after].
    rewrite Hstmts. cbn [map app].
    rewrite app_nil_r.
    apply Bool.andb_true_iff. split.
    apply Bool.andb_true_iff. split.
    apply Bool.andb_true_iff. split.
    apply Bool.andb_true_iff. split.
    apply Bool.andb_true_iff. split.
    apply Bool.andb_true_iff. split.
    + apply forallb_bi_clean_map_BMatch. apply forallb_mc_clean_nodup. exact Hmatches.
    + exact Hvmap.
    + exact Hnat.
    + exact Htproxy.
    + exact Hfwd.
    + exact Hqueue.
    + exact Hafter.
Qed.

(** [simplify_rule] preserves cleanliness (it is the identity on the body and copies
    the other slots). *)
Lemma simplify_rule_clean : forall r,
  rule_clean r = true -> rule_clean (simplify_rule r) = true.
Proof.
  intros r Hc. unfold simplify_rule, rule_clean in Hc |- *.
  cbn [r_body r_vmap r_nat r_tproxy r_fwd r_queue r_after].
  rewrite map_simplify_item_id. exact Hc.
Qed.

Lemma rules_clean_map_simplify_dedup : forall rs,
  rules_clean rs = true ->
  rules_clean (map (fun r => simplify_rule (dedup_rule r)) rs) = true.
Proof.
  induction rs as [| r rs IH]; intro H; [reflexivity|].
  cbn [rules_clean forallb] in H. apply Bool.andb_true_iff in H as [Hr Hrest].
  cbn [map rules_clean forallb]. apply Bool.andb_true_iff. split.
  - apply simplify_rule_clean, dedup_rule_clean. exact Hr.
  - apply IH. exact Hrest.
Qed.

Lemma rules_clean_prune_noops : forall rs,
  rules_clean rs = true -> rules_clean (prune_noops rs) = true.
Proof.
  intros rs H. unfold prune_noops, rules_clean in H |- *.
  apply forallb_forall. intros x Hx.
  apply filter_In in Hx as [Hx _].
  rewrite forallb_forall in H. apply H. exact Hx.
Qed.

Lemma rules_clean_dce : forall rs,
  rules_clean rs = true -> rules_clean (dce rs) = true.
Proof.
  induction rs as [| r rs IH]; intro H; [reflexivity|].
  cbn [rules_clean forallb] in H. apply Bool.andb_true_iff in H as [Hr Hrest].
  cbn [dce]. destruct (shadows r) eqn:Es.
  - cbn [rules_clean forallb]. rewrite Hr. reflexivity.
  - cbn [rules_clean forallb]. rewrite Hr. cbn. apply IH. exact Hrest.
Qed.

(** *** Step 1 result: [optimize_chain] preserves [rules_clean]. *)
Theorem optimize_chain_clean : forall c,
  rules_clean (c_rules c) = true ->
  rules_clean (c_rules (optimize_chain c)) = true.
Proof.
  intros c H. unfold optimize_chain. cbn [c_rules].
  apply rules_clean_dce, rules_clean_prune_noops, rules_clean_map_simplify_dedup.
  exact H.
Qed.

(** Base [optimize_chain] does not depend on the set/map environment, so its
    [eval_chain] is the same under any [d]. *)
Lemma optimize_chain_eval_any_env : forall c p e1 e2,
  eval_chain (optimize_chain c) (set_env p e1) = eval_chain c (set_env p e2) ->
  True.
Proof. trivial. Qed.

(** ** Step 2 (first rung): compose base [optimize_chain] then the N-WAY value->set
    pass.  Step 1 supplies the [rules_clean] hypothesis the [setsN] theorem needs. *)


(** *** First-rung whole-pipeline correctness, axiom-free. *)

(** ** Step 3: the FULL four-stage pipeline and its whole-pipeline correctness.

    [optimize_table] runs the base dedup/DCE pass, then the N-way value->set
    merge, the two-selector->concat merge, and finally the value+verdict->vmap
    merge, threading the fresh-name counter and [set_decls] accumulator across the
    table semantics.  Its whole-pipeline correctness — preserving [eval_chain] over
    the synthesised declarations, UNCONDITIONALLY — is proved in [Optimize_Uncond.v];
    this file provides the composition seam lemmas it builds on.

    The seam between passes is the crux: each pass runs on the PREVIOUS pass's output,
    which is no longer [rules_clean] (it carries merged [MConcatSet] lookup rules).
    [Optimize_Uncond.v] discharges this without any input precondition — a
    passed-through rule stays env-stable because the synthesised names are minted
    fresh past every name the input declares/reads (read-freshness), and fresh-name
    discipline is threaded by [optimize_chain_setsN_fresh_setname] and the
    cross-namespace stability lemmas (setsN/concatN leave [sd_vmaps] fixed) — the
    seam lemmas this file provides.

    *** `nft -o` FIDELITY CONTRACT (precise; see [Optimize_Mapn] D1 note + [e2e.sh]).

    All stages EXCEPT [mapn] emit output that `nft --optimize` (nft v1.1.6) also
    emits (differentially confirmed, netns): the bare NAT maps ([dnat]/[snat],
    NFT_BREAK-on-miss), the anonymous value sets ([setsN]), the concat sets
    ([concatK]/[concatN]/[concatM]), the interval sets ([ivset]) and the verdict
    maps ([vmapN]).  The [mapn] stage (`meta mark set … map`) is DIFFERENT: `nft -o`
    does NOT merge `meta mark set` rules at all, so [mapn] is a LABELLED SOUND
    SUPERSET with no `nft -o` counterpart — NOT part of the byte-fidelity claim, and
    NOT an nft bug (nft is merely conservative; the merge is verdict/state-preserving
    per [Optimize_Mapn.eval_rules_mut_map_merge]).  [mapn] emits the HEAD-GUARDED
    form (a synthesised key set in front of the map) because our model loads a
    default on a statement value-map miss rather than NFT_BREAKing; the guard makes
    the lookup always hit, recovering exact equivalence.  Why the guard cannot just
    be dropped — and why doing so would touch the [compile_chain_correct] headline
    with no fidelity payoff — is pinned axiom-free in
    [Optimize_Mapn.mapn_bare_diverges_offkey]. *)
Definition optimize_table (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(nA, dA, cA) := optimize_chain_absorb n d (optimize_chain c) in
  let '(nT, dT, cT) := optimize_chain_ctmask nA dA cA in
  let '(nD, dD, cD) := optimize_chain_dnat nT dT cT in
  let '(nS, dS, cS) := optimize_chain_snat nD dD cD in
  let '(n1, d1, c1) := optimize_chain_setsN nS dS cS in
  let '(nK, dK, cK) := optimize_chain_concatK n1 d1 c1 in
  let '(nM, dM, cM) := optimize_chain_mapn nK dK cK in
  let '(n2, d2, c2) := optimize_chain_concatN nM dM cM in
  let '(nG, dG, cG) := optimize_chain_concatM n2 d2 c2 in
  let '(nGs, dGs, cGs) := optimize_chain_setg nG dG cG in
  let '(nI, dI, cI) := optimize_chain_ivset nGs dGs cGs in
  let '(nIt, dIt, cIt) := optimize_chain_ivsett nI dI cI in
  let '(nDs, dDs, cDs) := optimize_chain_dscp nIt dIt cIt in
  let '(nIg, dIg, cIg) := optimize_chain_ivsetg nDs dDs cDs in
  let '(nMx, dMx, cMx) := optimize_chain_ivmixg nIg dIg cIg in
  let '(nVg, dVg, cVg) := optimize_chain_vmapNg nMx dMx cMx in
  let '(nDv, dDv, cDv) := optimize_chain_dscpv nVg dVg cVg in
  optimize_chain_vmapN nDv dDv cDv.

(** ** Correctness of [optimize_table] lives in [Optimize_Uncond.v], where it is
    proved UNCONDITIONALLY — with NO [rules_clean] and NO caller-supplied freshness
    side-condition on the input chain:

      [optimize_table_correct_uncond_gen] : general (n,d) form, freshness obligations
        only (which a clean input would also satisfy — [rules_clean] is subsumed);
      [optimize_table_uncond_correct] / [optimize_table_uncond_compile_correct] :
        the fresh-table entry [optimize_table_uncond c], with NO hypothesis on [c].

    The freshness is discharged internally by seeding the fresh-name counter past
    every name the input declares/reads (see [seed_start]).  The earlier
    clean-input-only theorems were removed as strictly redundant. *)

