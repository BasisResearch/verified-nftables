(** * Optimize_Linearize_MutSt: the DEFAULT-compile linearization pipeline over
    the STATE-THREADING fold.

    [Optimize_Linearize] certifies nft's always-on single-rule linearization
    (payload merge, xor fold, trivial-binop elision) and the DEFAULT compile
    pipeline [compile_chain_default] against the write-blind verdict semantics —
    verdicts only.  This file lifts that guarantee to the FULL-STATE
    effect-observing chain semantics [eval_chain_mut_st h] (the single per-rule
    fold [rule_step]: packet meta/ct writes, dynset env writes, the notrack
    latch, limiter/quota/connlimit consumption, and the NAT data plane — with
    the state pair the fold threads exported IN FULL, verdict AND resulting
    (env, packet)).

    The three linearization passes rewrite BMATCH conditions only — a payload
    load geometry ([Optimize_PayMerge]) or a bitwise operand ([Optimize_XorFold]/
    [Optimize_Elide]) — never a statement, and every matchcond they touch or
    emit ([MEq]/[MCmp]/[MMasked] over a payload/meta/ct field) is
    limiter-consume-free ([match_consumefree]).  So a rewritten body threads the
    SAME (env, packet) through [body_step] as the original, at every position,
    for every env and packet; the write path is untouched.  This makes each pass
    STATE-PRESERVING unconditionally.

    The composed headline [compile_chain_default_mut_st_correct] carries the
    plain-compile full-state bridge [compile_chain_mut_st_correct] (built here
    from [Correct.run_rule_step_compile_rule]) through the three stages, under
    the single [rule_numgen_free] hypothesis every frontend-emitted chain
    discharges ([Lower_Proofs.lower_ruleset_numgen_free]) — no NEW effectful
    carve. *)

From Stdlib Require Import List Bool.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Correct Optimize_PayMerge Optimize_XorFold Optimize_Elide
  Optimize_Linearize Optimize_Uncond Optimize_MutEnv.

(* ================================================================== *)
(** ** Generic congruence: [body_step] is congruent in its tail.

    Prepending the SAME body item to two tails that agree under [body_step] for
    every (env, packet) keeps them agreeing: the head item threads its own
    write / break / stop identically, and either falls through to the tail (where
    the hypothesis applies) or ends the walk with a state the head alone fixes. *)
Lemma body_step_tail_cong : forall it tl1 tl2,
  (forall e p, body_step tl1 e p = body_step tl2 e p) ->
  forall e p, body_step (it :: tl1) e p = body_step (it :: tl2) e p.
Proof.
  intros it tl1 tl2 H e p.
  destruct it as [m | s].
  - cbn [body_step]. destruct (eval_matchcond m e p); [apply H | reflexivity].
  - destruct s; cbn [body_step];
      try (destruct (stmt_loadable _ p); [apply H | reflexivity]).
    + (* SNotrack *) apply H.
    + (* SMetaSet *) destruct (vsrc_loadable vs p); [apply H | reflexivity].
    + (* SCtSet *) destruct (vsrc_loadable vs p); [apply H | reflexivity].
    + (* SSynproxy *) destruct (synproxy_loadable p);
        [destruct (synproxy_stops p); [reflexivity | apply H] | reflexivity].
    + (* SDynset *) destruct dataf as [| d ds].
      * destruct (fields_loadable keyfs p); [apply H | reflexivity].
      * destruct (fields_loadable (keyfs ++ d :: ds) p); [apply H | reflexivity].
Qed.

(* ================================================================== *)
(** ** Payload-merge ([Optimize_PayMerge]) preserves the full-state body fold. *)

(** A recognised payload segment is limiter-consume-free: [payload_seg] only
    accepts [MEq]/[MCmp _ CEq], neither of which is [MLimit]/[MQuota]/
    [MConnlimit]. *)
Lemma payload_seg_consumefree : forall m x,
  payload_seg m = Some x -> match_consumefree m = true.
Proof.
  intros m x H. unfold payload_seg in H.
  destruct m; try discriminate; reflexivity.
Qed.

(** The fused matchcond is a payload equality ([MEq]) — consume-free. *)
Lemma try_merge_consumefree : forall m1 m2 m,
  try_merge m1 m2 = Some m -> match_consumefree m = true.
Proof.
  intros m1 m2 m H. unfold try_merge in H.
  destruct (payload_seg m1) as [[[[b1 o1] l1] v1]|] eqn:S1; [|discriminate].
  destruct (payload_seg m2) as [[[[b2 o2] l2] v2]|] eqn:S2; [|discriminate].
  destruct (seg_can_merge b1 o1 l1 b2 o2 l2); [|discriminate].
  injection H as <-. reflexivity.
Qed.

(** One fusion at the head of a body preserves [body_step] — the three-case
    argument (both operands pass, the first fails, or the second fails), using
    that the fused match's eval is the conjunction ([try_merge_eval]) and every
    match involved consumes nothing. *)
Lemma try_merge_body_step : forall m1 m2 m rest e p,
  try_merge m1 m2 = Some m ->
  body_step (BMatch m :: rest) e p
  = body_step (BMatch m1 :: BMatch m2 :: rest) e p.
Proof.
  intros m1 m2 m rest e p H.
  assert (Hm : match_consumefree m = true) by (eapply try_merge_consumefree; eauto).
  assert (Hm1 : match_consumefree m1 = true).
  { unfold try_merge in H.
    destruct (payload_seg m1) as [[[[b1 o1] l1] v1]|] eqn:S1; [|discriminate].
    eapply payload_seg_consumefree; eauto. }
  assert (Hm2 : match_consumefree m2 = true).
  { unfold try_merge in H.
    destruct (payload_seg m1) as [[[[b1 o1] l1] v1]|] eqn:S1; [|discriminate].
    destruct (payload_seg m2) as [[[[b2 o2] l2] v2]|] eqn:S2; [|discriminate].
    eapply payload_seg_consumefree; eauto. }
  cbn [body_step].
  rewrite (try_merge_eval m1 m2 m e p H).
  rewrite (match_consume_free_id m e p Hm).
  rewrite (match_consume_free_id m1 e p Hm1).
  rewrite (match_consume_free_id m2 e p Hm2).
  destruct (eval_matchcond m1 e p); destruct (eval_matchcond m2 e p);
    reflexivity.
Qed.

Lemma merge_body_fuel_step : forall fuel b e p,
  body_step (merge_body_fuel fuel b) e p = body_step b e p.
Proof.
  induction fuel as [| fk IH]; intros b e p; [reflexivity|].
  destruct b as [| it1 [| it2 rest]].
  - reflexivity.
  - (* single item: it1 :: [] -> it1 :: merge_body_fuel fk [] *)
    cbn [merge_body_fuel]. destruct it1 as [m1 | s1];
      apply body_step_tail_cong; intros e' p'; apply IH.
  - cbn [merge_body_fuel]. destruct it1 as [m1 | s1].
    + destruct it2 as [m2 | s2].
      * destruct (try_merge m1 m2) as [m |] eqn:T.
        -- rewrite <- (try_merge_body_step m1 m2 m rest e p T). apply IH.
        -- apply body_step_tail_cong; intros e' p'. apply IH.
      * apply body_step_tail_cong; intros e' p'. apply IH.
    + apply body_step_tail_cong; intros e' p'. apply IH.
Qed.

Lemma merge_body_step : forall b e p,
  body_step (merge_body b) e p = body_step b e p.
Proof. intros b e p. apply merge_body_fuel_step. Qed.

(* ================================================================== *)
(** ** Xor-fold ([Optimize_XorFold]) preserves the full-state body fold. *)

(** [xorfold_mc] keeps the compared field, so it keeps the limiter-consume
    behaviour ([MMasked] is consume-free, and every other shape is left
    verbatim). *)
Lemma xorfold_mc_consume : forall m e p,
  match_consume (xorfold_mc m) e p = match_consume m e p.
Proof.
  intros m e p. destruct m; try reflexivity.
  cbn [xorfold_mc].
  destruct (data_eqb _ _ && Nat.eqb _ _ && match _ with CEq | CNe => true | _ => false end)%bool;
    reflexivity.
Qed.

Lemma xorfold_body_step : forall b e p,
  body_step (map xorfold_bi b) e p = body_step b e p.
Proof.
  induction b as [| it b IH]; intros e p; [reflexivity|].
  destruct it as [m | s]; cbn [map xorfold_bi].
  - cbn [body_step].
    rewrite (xorfold_mc_matchcond m e p), (xorfold_mc_consume m e p).
    destruct (eval_matchcond m e p); [apply IH | reflexivity].
  - apply body_step_tail_cong; intros e' p'. apply IH.
Qed.

(* ================================================================== *)
(** ** Trivial-binop elision ([Optimize_Elide]) preserves the full-state body
    fold. *)

(** [elide_mc] rewrites a spent [MMasked] to an [MCmp] on the SAME field — both
    consume-free — and leaves every other shape verbatim. *)
Lemma elide_mc_consume : forall m e p,
  match_consume (elide_mc m) e p = match_consume m e p.
Proof.
  intros m e p. destruct m; try reflexivity.
  cbn [elide_mc].
  destruct (load_octet_width (field_load f)); [|reflexivity].
  destruct (Nat.eqb _ _ && data_eqb _ _ && data_eqb _ _)%bool; reflexivity.
Qed.

Lemma elide_body_step : forall b e p,
  body_step (map elide_bi b) e p = body_step b e p.
Proof.
  induction b as [| it b IH]; intros e p; [reflexivity|].
  destruct it as [m | s]; cbn [map elide_bi].
  - cbn [body_step].
    rewrite (elide_mc_matchcond m e p), (elide_mc_consume m e p).
    destruct (eval_matchcond m e p); [apply IH | reflexivity].
  - apply body_step_tail_cong; intros e' p'. apply IH.
Qed.

(* ================================================================== *)
(** ** [end_step] depends only on [r_outcome] and the post-terminal statements.

    Every terminal accessor ([r_vmap]/[r_nat]/[r_tproxy]/[r_fwd]/[r_queue]/
    [r_verdict]) is a function of [r_outcome], and [after_step] reads [r_after];
    [end_step] reads nothing else of the rule (in particular not [r_body]).  So
    two rules that agree on [r_outcome] and [r_after] have the same [end_step] —
    the linearization passes keep both. *)
Lemma end_step_outcome_after_cong : forall h r1 r2 e p,
  r_outcome r1 = r_outcome r2 ->
  r_after r1 = r_after r2 ->
  end_step h r1 e p = end_step h r2 e p.
Proof.
  intros h [b1 o1 a1] [b2 o2 a2] e p Hout Haft.
  cbn in Hout, Haft. subst o2 a2.
  unfold end_step, terminal_step, has_effect_terminal, terminal_loadable,
         vmap_loadable, r_vmap, r_nat, r_tproxy, r_fwd, r_queue, r_verdict,
         nat_drops, apply_nat.
  reflexivity.
Qed.

(** A per-rule step is preserved when the body threads identically and the
    [r_outcome] / post-terminal statements are untouched — the shape of every
    linearization pass. *)
Lemma rule_step_body_cong : forall h r1 r2 e p,
  (forall e' p', body_step (r_body r1) e' p' = body_step (r_body r2) e' p') ->
  r_outcome r1 = r_outcome r2 ->
  r_after r1 = r_after r2 ->
  rule_step h r1 e p = rule_step h r2 e p.
Proof.
  intros h r1 r2 e p Hbody Hout Haft.
  unfold rule_step. rewrite (Hbody e p).
  destruct (body_step (r_body r2) e p) as [e' p' | e' p' | e' p'];
    try reflexivity.
  apply end_step_outcome_after_cong; assumption.
Qed.

(* ================================================================== *)
(** ** Per-rule and per-chain state preservation for the three passes. *)

Lemma paymerge_rule_step : forall h r e p,
  rule_step h (paymerge_rule r) e p = rule_step h r e p.
Proof.
  intros h r e p. apply rule_step_body_cong; try reflexivity.
  intros e' p'. rewrite paymerge_rule_body. apply merge_body_step.
Qed.

Lemma xorfold_rule_step : forall h r e p,
  rule_step h (xorfold_rule r) e p = rule_step h r e p.
Proof.
  intros h r e p. apply rule_step_body_cong; try reflexivity.
  intros e' p'. rewrite xorfold_r_body. apply xorfold_body_step.
Qed.

Lemma elide_rule_step : forall h r e p,
  rule_step h (elide_rule r) e p = rule_step h r e p.
Proof.
  intros h r e p. apply rule_step_body_cong; try reflexivity.
  intros e' p'. rewrite elide_r_body. apply elide_body_step.
Qed.

(** A per-rule map whose step is preserved preserves the full-state rule fold. *)
Lemma eval_rules_mut_st_map_cong : forall h (f : rule -> rule) rs e p,
  (forall r e' p', rule_step h (f r) e' p' = rule_step h r e' p') ->
  eval_rules_mut_st h (map f rs) e p = eval_rules_mut_st h rs e p.
Proof.
  intros h f rs e p Hstep. revert e p.
  induction rs as [| r rs IH]; intros e p; [reflexivity|].
  cbn [map]. rewrite !eval_rules_mut_st_cons. rewrite Hstep.
  destruct (rule_step h r e p) as [[v|] [e' p']].
  - destruct (terminal v); [reflexivity | apply IH].
  - apply IH.
Qed.

Lemma paymerge_chain_mut_st : forall h c e p,
  eval_chain_mut_st h (paymerge_chain c) e p = eval_chain_mut_st h c e p.
Proof.
  intros h c e p. unfold eval_chain_mut_st, paymerge_chain. cbn [c_rules c_policy].
  rewrite (eval_rules_mut_st_map_cong h paymerge_rule (c_rules c) e p
             (paymerge_rule_step h)). reflexivity.
Qed.

Lemma xorfold_chain_mut_st : forall h c e p,
  eval_chain_mut_st h (xorfold_chain c) e p = eval_chain_mut_st h c e p.
Proof.
  intros h c e p. unfold eval_chain_mut_st, xorfold_chain. cbn [c_rules c_policy].
  rewrite (eval_rules_mut_st_map_cong h xorfold_rule (c_rules c) e p
             (xorfold_rule_step h)). reflexivity.
Qed.

Lemma elide_chain_mut_st : forall h c e p,
  eval_chain_mut_st h (elide_chain c) e p = eval_chain_mut_st h c e p.
Proof.
  intros h c e p. unfold eval_chain_mut_st, elide_chain. cbn [c_rules c_policy].
  rewrite (eval_rules_mut_st_map_cong h elide_rule (c_rules c) e p
             (elide_rule_step h)). reflexivity.
Qed.

(** The composed always-on linearization is STATE-PRESERVING: for every chain,
    env and packet the linearized chain yields the SAME verdict, the SAME
    resulting env AND the SAME resulting packet as the source chain. *)
Theorem linearize_chain_mut_st : forall h c e p,
  eval_chain_mut_st h (linearize_chain c) e p = eval_chain_mut_st h c e p.
Proof.
  intros h c e p. unfold linearize_chain.
  rewrite elide_chain_mut_st, xorfold_chain_mut_st, paymerge_chain_mut_st.
  reflexivity.
Qed.

(* ================================================================== *)
(** ** The plain-compile full-state bridge, then the DEFAULT-pipeline headline.

    The full-state compile bridge — [run_program_mut_st] of the compiled rules
    IS [eval_rules_mut_st] — is the [_st] analogue of
    [Correct.run_program_mut_env_compile_chain] (which drops the packet half):
    one induction, driven by [Correct.run_rule_step_compile_rule]. *)
Lemma run_program_mut_st_compile_chain : forall h rs e p,
  forallb rule_numgen_free rs = true ->
  run_program_mut_st h (map compile_rule rs) e p = eval_rules_mut_st h rs e p.
Proof.
  induction rs as [| r rs IH]; intros e p Hall; [reflexivity|].
  cbn [forallb] in Hall. apply Bool.andb_true_iff in Hall. destruct Hall as [Hr Hrs].
  cbn [map]. rewrite run_program_mut_st_cons, eval_rules_mut_st_cons.
  rewrite (Correct.run_rule_step_compile_rule h r e p Hr).
  destruct (rule_step h r e p) as [[v |] [e' p']].
  - destruct (terminal v); [reflexivity | apply IH; exact Hrs].
  - apply IH; exact Hrs.
Qed.

(** The state VM run of a chain: the [run_program_mut_st] fold, falling through
    to the chain policy on no verdict — the full-state ((env, packet)-returning)
    twin of [run_chain_mut_env]. *)
Definition run_chain_mut_st (h : hook_id) (prog : program) (policy : verdict)
    (e : env) (p : packet) : verdict * (env * packet) :=
  match run_program_mut_st h prog e p with
  | (Some v, s) => (v, s)
  | (None, s)   => (policy, s)
  end.

(** Plain-compile full-state correctness: the compiled chain's VM run
    reproduces the DSL state fold — verdict AND resulting (env, packet). *)
Theorem compile_chain_mut_st_correct : forall h c e p,
  forallb rule_numgen_free (c_rules c) = true ->
  run_chain_mut_st h (compile_chain c) (c_policy c) e p = eval_chain_mut_st h c e p.
Proof.
  intros h c e p Hall.
  unfold run_chain_mut_st, eval_chain_mut_st, compile_chain.
  rewrite run_program_mut_st_compile_chain by exact Hall.
  destruct (eval_rules_mut_st h (c_rules c) e p) as [[v|] s]; reflexivity.
Qed.

(* ================================================================== *)
(** ** The linearization preserves [rule_numgen_free], so the composed headline
    carries the SAME hypothesis on the SOURCE chain.

    Every pass keeps [r_outcome] and [r_after], so the [vmap_ngfree]/
    [terminal_ngfree]/[stmt_ngfree] parts of [rule_numgen_free] are untouched;
    only the body changes, and each rewrite emits a numgen-free match (a payload
    [MEq], or an [MMasked]/[MCmp] on the SAME field). *)

Lemma xorfold_mc_ngfree : forall m, match_ngfree (xorfold_mc m) = match_ngfree m.
Proof.
  intro m. destruct m; try reflexivity.
  cbn [xorfold_mc].
  destruct (data_eqb _ _ && Nat.eqb _ _ && match _ with CEq | CNe => true | _ => false end)%bool;
    reflexivity.
Qed.

Lemma elide_mc_ngfree : forall m, match_ngfree (elide_mc m) = match_ngfree m.
Proof.
  intro m. destruct m; try reflexivity.
  cbn [elide_mc].
  destruct (load_octet_width (field_load f)); [|reflexivity].
  destruct (Nat.eqb _ _ && data_eqb _ _ && data_eqb _ _)%bool; reflexivity.
Qed.

Lemma xorfold_body_ngfree : forall b,
  forallb body_item_ngfree (map xorfold_bi b) = forallb body_item_ngfree b.
Proof.
  induction b as [| it b IH]; [reflexivity|].
  destruct it as [m | s]; cbn [map xorfold_bi forallb body_item_ngfree];
    rewrite IH; [rewrite xorfold_mc_ngfree|]; reflexivity.
Qed.

Lemma elide_body_ngfree : forall b,
  forallb body_item_ngfree (map elide_bi b) = forallb body_item_ngfree b.
Proof.
  induction b as [| it b IH]; [reflexivity|].
  destruct it as [m | s]; cbn [map elide_bi forallb body_item_ngfree];
    rewrite IH; [rewrite elide_mc_ngfree|]; reflexivity.
Qed.

(** The fused payload match is unconditionally numgen-free ([MEq (FPayload ..)]),
    and the fusion only fires on two payload segments (themselves numgen-free);
    so a numgen-free body stays numgen-free through the merge. *)
Lemma merge_body_fuel_nil : forall fuel, merge_body_fuel fuel [] = [].
Proof. intro fuel; destruct fuel; reflexivity. Qed.

Lemma merge_body_fuel_ngfree : forall fuel b,
  forallb body_item_ngfree b = true ->
  forallb body_item_ngfree (merge_body_fuel fuel b) = true.
Proof.
  induction fuel as [| fk IH]; intros b Hb; [exact Hb|].
  destruct b as [| it1 [| it2 rest]].
  - reflexivity.
  - cbn [merge_body_fuel]. destruct it1 as [m1 | s1];
      rewrite merge_body_fuel_nil; exact Hb.
  - cbn [forallb] in Hb. apply Bool.andb_true_iff in Hb. destruct Hb as [H1 Hb].
    apply Bool.andb_true_iff in Hb. destruct Hb as [H2 Hrest].
    cbn [merge_body_fuel]. destruct it1 as [m1 | s1].
    + destruct it2 as [m2 | s2].
      * destruct (try_merge m1 m2) as [m |] eqn:T.
        -- (* fused: BMatch m :: rest, m = MEq(FPayload..) is ngfree *)
           assert (Hm : body_item_ngfree (BMatch m) = true).
           { unfold try_merge in T.
             destruct (payload_seg m1) as [[[[b1 o1] l1] v1]|]; [|discriminate].
             destruct (payload_seg m2) as [[[[b2 o2] l2] v2]|]; [|discriminate].
             destruct (seg_can_merge b1 o1 l1 b2 o2 l2); [|discriminate].
             injection T as <-. reflexivity. }
           apply IH. cbn [forallb]. rewrite Hm, Hrest. reflexivity.
        -- cbn [forallb]. rewrite H1. cbn [andb].
           apply IH. cbn [forallb]. rewrite H2, Hrest. reflexivity.
      * cbn [forallb]. rewrite H1. cbn [andb].
        apply IH. cbn [forallb]. rewrite H2, Hrest. reflexivity.
    + cbn [forallb]. rewrite H1. cbn [andb].
      apply IH. cbn [forallb]. rewrite H2, Hrest. reflexivity.
Qed.

Lemma merge_body_ngfree : forall b,
  forallb body_item_ngfree b = true ->
  forallb body_item_ngfree (merge_body b) = true.
Proof. intros b Hb. unfold merge_body. apply merge_body_fuel_ngfree; exact Hb. Qed.

Lemma paymerge_rule_ngfree : forall r,
  rule_numgen_free r = true -> rule_numgen_free (paymerge_rule r) = true.
Proof.
  intros r Hr. unfold rule_numgen_free in Hr |- *.
  apply Bool.andb_true_iff in Hr. destruct Hr as [Hr Haft].
  apply Bool.andb_true_iff in Hr. destruct Hr as [Hr Hterm].
  apply Bool.andb_true_iff in Hr. destruct Hr as [Hbody Hvmap].
  (* [paymerge_rule] keeps [r_outcome]/[r_after], so the vmap/terminal/after
     conjuncts are definitionally those of [r]; only the body changes. *)
  apply Bool.andb_true_iff; split;
    [apply Bool.andb_true_iff; split;
      [apply Bool.andb_true_iff; split |] |].
  - change (r_body (paymerge_rule r)) with (merge_body (r_body r)).
    apply merge_body_ngfree; exact Hbody.
  - exact Hvmap.
  - exact Hterm.
  - exact Haft.
Qed.

Lemma xorfold_rule_ngfree : forall r,
  rule_numgen_free r = true -> rule_numgen_free (xorfold_rule r) = true.
Proof.
  intros r Hr. unfold rule_numgen_free in Hr |- *.
  rewrite xorfold_r_body. rewrite xorfold_body_ngfree.
  exact Hr.
Qed.

Lemma elide_rule_ngfree : forall r,
  rule_numgen_free r = true -> rule_numgen_free (elide_rule r) = true.
Proof.
  intros r Hr. unfold rule_numgen_free in Hr |- *.
  rewrite elide_r_body. rewrite elide_body_ngfree.
  exact Hr.
Qed.

Lemma forallb_map_impl : forall (f : rule -> rule) (rs : list rule),
  (forall r, rule_numgen_free r = true -> rule_numgen_free (f r) = true) ->
  forallb rule_numgen_free rs = true ->
  forallb rule_numgen_free (map f rs) = true.
Proof.
  intros f rs Himpl. induction rs as [| r rs IH]; intro Hall; [reflexivity|].
  cbn [forallb] in Hall. apply Bool.andb_true_iff in Hall. destruct Hall as [Hr Hrs].
  cbn [map forallb]. rewrite (Himpl r Hr), (IH Hrs). reflexivity.
Qed.

Lemma linearize_chain_numgen_free : forall c,
  forallb rule_numgen_free (c_rules c) = true ->
  forallb rule_numgen_free (c_rules (linearize_chain c)) = true.
Proof.
  intros c Hc. unfold linearize_chain, elide_chain, xorfold_chain, paymerge_chain.
  cbn [c_rules].
  apply forallb_map_impl; [exact elide_rule_ngfree|].
  apply forallb_map_impl; [exact xorfold_rule_ngfree|].
  apply forallb_map_impl; [exact paymerge_rule_ngfree|].
  exact Hc.
Qed.

(* ================================================================== *)
(** ** HEADLINE (default-pipeline axis, full state): the DEFAULT pipeline's
    bytecode, run on the state VM, reproduces the source chain's DSL STATE fold
    — verdict AND resulting (env, packet) — for every chain, env and packet,
    under the single [rule_numgen_free] hypothesis (discharged for every
    frontend-emitted chain by [Lower_Proofs.lower_ruleset_numgen_free]).  Re-exported
    as the Main headline [Main.main_compile_chain_default_correct]. *)
Theorem compile_chain_default_mut_st_correct : forall h c e p,
  forallb rule_numgen_free (c_rules c) = true ->
  run_chain_mut_st h (compile_chain_default c) (c_policy c) e p
  = eval_chain_mut_st h c e p.
Proof.
  intros h c e p Hall.
  unfold compile_chain_default.
  change (c_policy c) with (c_policy (linearize_chain c)).
  rewrite (compile_chain_mut_st_correct h (linearize_chain c) e p
             (linearize_chain_numgen_free c Hall)).
  apply linearize_chain_mut_st.
Qed.

(* ================================================================== *)
(** ** HEADLINE (optimizer axis, full state): the shipped optimize∘default-compile
    guarantee over the effect-observing state fold.  Re-exported as the Main
    headline [Main.main_optimize_table_uncond_compile_mut_st_correct].

    Run the shipped 18-stage `nft -o` consolidation
    ([Optimize_Uncond.optimize_table_uncond]), DEFAULT-compile the optimised
    chain, and run the bytecode on the state VM: the result — verdict AND the
    resulting (env, packet) the [rule_step] fold leaves — is exactly the source
    chain's DSL state fold.  Composed from [compile_chain_default_mut_st_correct]
    (the compiled optimised chain reproduces its own state fold, under the single
    [rule_numgen_free] hypothesis every frontend chain discharges via
    [Lower_Proofs.lower_ruleset_numgen_free]) and
    [Optimize_MutEnv.optimize_table_uncond_mut_st_correct] (the pipeline
    preserves the source chain's state fold at every hook).

    Both sides run under [env_with_sets base d'].  A verdict-only chain semantics
    would read the SOURCE at [empty_decls] because it discards the env; the
    state fold RETURNS the threaded env, so the synthesised declarations [d'] the
    compiled side needs to resolve its set/map lookups are part of the observable
    and must appear on both sides for the returned (env, packet) pairs to match —
    reading the source at [empty_decls] would drop [d'] from the returned env and
    break the equality. *)
Theorem optimize_table_uncond_compile_mut_st_correct :
  forall h c base p n' d' c',
  forallb rule_numgen_free (c_rules c') = true ->
  Optimize_Uncond.optimize_table_uncond c = (n', d', c') ->
  run_chain_mut_st h (compile_chain_default c') (c_policy c')
                   (env_with_sets base d') p
  = eval_chain_mut_st h c (env_with_sets base d') p.
Proof.
  intros h c base p n' d' c' Hng H.
  rewrite (compile_chain_default_mut_st_correct
             h c' (env_with_sets base d') p Hng).
  exact (Optimize_MutEnv.optimize_table_uncond_mut_st_correct h c base p n' d' c' H).
Qed.

(** Axiom-freedom audit (build-time guard; enforcement is `make axioms`). *)
Print Assumptions linearize_chain_mut_st.
Print Assumptions compile_chain_default_mut_st_correct.
Print Assumptions optimize_table_uncond_compile_mut_st_correct.
