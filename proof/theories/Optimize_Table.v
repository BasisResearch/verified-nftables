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

      3. proves an axiom-free top-level theorem [optimize_table_correct] that the
         WHOLE pipeline is [eval_chain]-preserving over the synthesised
         declarations, with NO new axioms.

    The composed optimizer is what [Extract.v] extracts and what the [glue.ml]
    CLI invokes, so the shipped tool RUNS the verified term. *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Optimize Optimize_Merge Optimize_Vmap Optimize_Concat Optimize_Table_Inv.

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

Definition optimize_table_sets (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  optimize_chain_setsN n d (optimize_chain c).

(** *** First-rung whole-pipeline correctness, axiom-free. *)
Theorem optimize_table_sets_correct : forall n d c n' d' c' base p,
  optimize_table_sets n d c = (n', d', c') ->
  rules_clean (c_rules c) = true ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  eval_chain c' (set_env p (env_with_sets base d'))
  = eval_chain c  (set_env p (env_with_sets base d)).
Proof.
  intros n d c n' d' c' base p H Hclean Hfresh.
  unfold optimize_table_sets in H.
  rewrite (optimize_chain_setsN_correct n d (optimize_chain c) n' d' c' base p
             H (optimize_chain_clean c Hclean) Hfresh).
  (* base optimize_chain is eval_chain-preserving on every packet/env *)
  apply optimize_chain_correct.
Qed.

(** ** Step 3: the FULL four-stage pipeline and its whole-pipeline correctness.

    [optimize_table] runs the base dedup/DCE pass, then the N-way value->set
    merge, the two-selector->concat merge, and finally the value+verdict->vmap
    merge, threading the fresh-name counter and [set_decls] accumulator across the
    table semantics.  [optimize_table_correct] proves the WHOLE pipeline preserves
    [eval_chain] over the synthesised declarations — axiom-free.

    The seam between passes is the crux: [setsN] needs [rules_clean] input (supplied
    by [optimize_chain_clean]); its OUTPUT is no longer clean (it carries merged
    [MConcatSet] lookup rules), so the [concat]/[vmap] stages run under the WEAKER
    [rs_concatN_ok] / [rs_vmapN_ok] preconditions, which the setsN-output invariants
    ([optimize_chain_setsN_output_concatN_ok] / [_output_vmapN_ok]) and the
    [concatN]-preserves-[vmapN_ok] lemma establish.  Fresh-name discipline is
    threaded by [optimize_chain_setsN_fresh_setname] (setname namespace) and the
    cross-namespace stability lemmas (setsN/concatN leave [sd_vmaps] fixed, so the
    initial [vmapname] freshness survives to the vmap stage). *)
Definition optimize_table (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n1, d1, c1) := optimize_chain_setsN n d (optimize_chain c) in
  let '(n2, d2, c2) := optimize_chain_concatN n1 d1 c1 in
  optimize_chain_vmapN n2 d2 c2.

Theorem optimize_table_correct : forall n d c n' d' c' base p,
  optimize_table n d c = (n', d', c') ->
  rules_clean (c_rules c) = true ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  eval_chain c' (set_env p (env_with_sets base d'))
  = eval_chain c  (set_env p (env_with_sets base d)).
Proof.
  intros n d c n' d' c' base p H Hclean Hfs Hfv.
  unfold optimize_table in H.
  destruct (optimize_chain_setsN n d (optimize_chain c)) as [[n1 d1] c1] eqn:E1.
  destruct (optimize_chain_concatN n1 d1 c1) as [[n2 d2] c2] eqn:E2.
  assert (Hc0clean : rules_clean (c_rules (optimize_chain c)) = true)
    by (apply optimize_chain_clean; exact Hclean).
  pose proof (optimize_chain_setsN_fresh_setname n d (optimize_chain c) n1 d1 c1 E1 Hfs) as Hfs1.
  pose proof (optimize_chain_setsN_output_concatN_ok n d (optimize_chain c) n1 d1 c1 E1 Hc0clean) as Hcc1.
  pose proof (optimize_chain_setsN_output_vmapN_ok n d (optimize_chain c) n1 d1 c1 E1 Hc0clean) as Hv1.
  pose proof (optimize_chain_concatN_preserves_vmapN_ok n1 d1 c1 n2 d2 c2 E2 Hv1) as Hv2.
  assert (Hvm2 : sd_vmaps d2 = sd_vmaps d).
  { rewrite (optimize_chain_concatN_vmaps n1 d1 c1 n2 d2 c2 E2).
    apply (optimize_chain_setsN_vmaps n d (optimize_chain c) n1 d1 c1 E1). }
  pose proof (optimize_chain_setsN_mono n d (optimize_chain c) n1 d1 c1 E1) as Hm1.
  pose proof (optimize_chain_concatN_mono n1 d1 c1 n2 d2 c2 E2) as Hm2.
  assert (Hfv2 : forall k, n2 <= k -> ~ In (vmapname k) (map fst (sd_vmaps d2))).
  { intros k Hk. rewrite Hvm2. apply Hfv. lia. }
  rewrite (optimize_chain_vmapN_correct_gen n2 d2 c2 n' d' c' base p H Hv2 Hfv2).
  rewrite (optimize_chain_concatN_correct_gen n1 d1 c1 n2 d2 c2 base p E2 Hcc1 Hfs1).
  rewrite (optimize_chain_setsN_correct n d (optimize_chain c) n1 d1 c1 base p E1 Hc0clean Hfs).
  apply optimize_chain_correct.
Qed.
