(** * Optimize_MutEnv: EFFECT-LEVEL correctness of the whole [nft -o] pipeline.

    [Optimize_Uncond] certifies the composed 18-stage optimizer against the
    write-blind pure chain view — verdicts only.  This file lifts that composed,
    hypothesis-free guarantee to the FULL-STATE effect-observing chain
    semantics [eval_chain_mut_st h] (the single per-rule fold [rule_step]:
    packet meta/ct writes, dynset env writes, the notrack latch,
    limiter/quota/connlimit consumption, and the NAT data plane, each at its
    own body position — with the state pair the fold threads exported IN FULL,
    nothing dropped):

      [optimize_table_uncond_mut_st_correct] :
        optimize_table_uncond c = (n', d', c') ->
        eval_chain_mut_st h c' (env_with_sets base d') p
        = eval_chain_mut_st h c (env_with_sets base d') p

    — the optimised chain, run in the deployed environment (the synthesised
    declarations [d'] present), yields for EVERY packet the SAME verdict, the
    SAME resulting environment AND the SAME resulting packet as the original
    chain in that same environment.  No hypothesis on [c]: a stage can no
    longer preserve every verdict while altering a write a later hook
    observes — the env half (dynset learning, limiter/quota depletion, ct/nat
    stores) because it is carried to the next packet ([seq_eval_env]), and the
    PACKET half (meta mark/priority/nftrace, the notrack latch, the NAT
    rewrite) because the unified semantics' own priority dispatch hands the
    mutated packet to the next base chain at the same hook ([eval_ruleset_u]);
    Part H pins a pair of chains that agree under the old (verdict, env)
    observable yet differ here.  The (verdict, env) form
    [optimize_table_uncond_mut_env_correct] survives as a projection corollary
    ([Semantics.eval_chain_mut_env_st]).

    SCOPE (jumps): [eval_chain_mut_st] is the FLAT fold — [terminal (Jump _)]
    is [false], so a jump-bearing rule falls through WITHOUT running the
    callee.  On transfer-free chains ([rule_plain], the flat license) the flat
    fold IS the unified semantics ([Semantics.eval_table_u_mut_st_proj]); for
    jump-BEARING chains this theorem equates the two sides only under the flat
    callee-skipping projection — it does NOT by itself certify the pipeline
    against [eval_table_u]'s callee-following traversal, and no such claim is
    made here.

    HOW the proof is structured:

    - The 12 pure-merge stages (valueset, concatmulti, concat, concatguarded,
      setguarded, intervalset, intervalsethostorder, dscp, intervalsetguarded,
      mixedpointrangeguarded, vmapguarded, dscpvmap, vmap) carry an
      EFFECT-SAFETY GUARD in their pair recognisers ([rule_mutfree r1], see
      [Optimize_ValueSet.value_merge_pair]): a merged run is WRITE-FREE, so the
      fold is state-invariant across it ([rule_step_state_mutfree]) and the existing
      pure run-merge lemmas supply the verdicts
      ([eval_rules_mut_st_mutfree_prefix] below).
    - The three EFFECT-REWRITING stages keep their exact-shape recognisers and
      get per-shape effect certificates threaded through the fold:
      [datamap] ([Optimize_DataMap.dsl_step_map_merge] + the new payload-key
      guard), [dnat]/[snat] (the M3 NAT-in-fold semantics +
      [apply_nat_dnat_eq]/[apply_nat_snat_eq]).
    - The base pass ([Optimize.optimize_chain]) is effect-safe by construction:
      [dce] cuts after an unconditionally-terminal EMPTY rule (nothing after it
      ever runs), [prune_noops] deletes rules whose step is the identity, and
      [dedup_rule] now fires only on [rule_mutfree] rules.
    - PASSED-THROUGH rules are evaluated by the SAME [rule_step] on both sides
      under the SAME env, so (unlike the verdict-level proofs) no env-agreement
      seam machinery is needed; what IS needed is that the threaded env keeps
      the minted set/map declarations intact — dynset writes must miss every
      minted name.  [rule_dynset_fresh] (write-target freshness) mirrors the
      read-freshness discipline and is discharged BY CONSTRUCTION at the entry
      point: [Optimize_Uncond.chain_seed] includes the dynset target names, so
      [seed_start] mints past them. *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import String.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Correct Optimize Optimize_ValueSet Optimize_Vmap Optimize_VmapGuarded
  Optimize_Concat Optimize_ConcatMulti Optimize_ConcatGuarded Optimize_SetGuarded
  Optimize_IntervalSet Optimize_IntervalSetGuarded Optimize_MixedPointRangeGuarded
  Optimize_Absorb Optimize_CtMask Optimize_Dscp Optimize_DscpVmap
  Optimize_IntervalSetHostOrder Optimize_DataMap Optimize_Dnat Optimize_Snat
  Optimize_Table_Inv Optimize_Table Optimize_Normalize Optimize_Uncond.

Local Open Scope nat_scope.

(** ** Part A: dynset WRITE-target names and env-component stability.

    The per-rule fold writes the shared set/map environment through exactly one
    statement family: [SDynset] ([env_set_upd] on [e_set] for a pure set,
    [env_map_upd] on [e_map] for a map).  Every other writer touches other env
    components ([e_limit]/[e_quota]/[e_connlimit]/[e_ct]/[e_nat]) or the packet.
    So a rule's step preserves [e_set]/[e_map] at every name OUTSIDE its dynset
    targets, and [e_vmap] everywhere ([Semantics.rule_step_vmap]). *)

(** [stmt_dynset_names]/[body_dynset_names]/[rule_dynset_names] and the
    write-target freshness predicate [rule_dynset_fresh] live in
    [Optimize_Uncond] (next to [chain_seed], which now includes them).

    Writer micro-lemmas: which env components each write helper touches. *)
Lemma e_set_match_consume : forall m e p, e_set (match_consume m e p) = e_set e.
Proof. intros m e p; destruct m; reflexivity. Qed.
Lemma e_map_match_consume : forall m e p, e_map (match_consume m e p) = e_map e.
Proof. intros m e p; destruct m; reflexivity. Qed.

Lemma e_set_set_ct : forall e p k v, e_set (set_ct e p k v) = e_set e.
Proof. intros; unfold set_ct; destruct (pkt_ct_present p); reflexivity. Qed.
Lemma e_map_set_ct : forall e p k v, e_map (set_ct e p k v) = e_map e.
Proof. intros; unfold set_ct; destruct (pkt_ct_present p); reflexivity. Qed.

Lemma e_set_env_set_upd_other : forall e op n k nm,
  nm <> n -> e_set (env_set_upd e op n k) nm = e_set e nm.
Proof.
  intros e op n k nm Hne. unfold env_set_upd, with_e_set. cbn [e_set].
  rewrite (proj2 (String.eqb_neq nm n) Hne). reflexivity.
Qed.
Lemma e_map_env_set_upd : forall e op n k, e_map (env_set_upd e op n k) = e_map e.
Proof. reflexivity. Qed.
Lemma e_set_env_map_upd : forall e op n k d, e_set (env_map_upd e op n k d) = e_set e.
Proof. reflexivity. Qed.
Lemma e_map_env_map_upd_other : forall e op n k d nm,
  nm <> n -> e_map (env_map_upd e op n k d) nm = e_map e nm.
Proof.
  intros e op n k d nm Hne. unfold env_map_upd, with_e_map. cbn [e_map].
  rewrite (proj2 (String.eqb_neq nm n) Hne). reflexivity.
Qed.

Lemma e_set_apply_nat : forall h' r e p,
  e_set (fst (apply_nat h' r e p)) = e_set e.
Proof.
  intros h' r e p. unfold apply_nat.
  destruct (r_nat r) as [ns|]; [| reflexivity].
  destruct (e_nat e (pkt_flow p)); [reflexivity|].
  destruct (pkt_ctdir_orig p); cbv zeta; reflexivity.
Qed.
Lemma e_map_apply_nat : forall h' r e p,
  e_map (fst (apply_nat h' r e p)) = e_map e.
Proof.
  intros h' r e p. unfold apply_nat.
  destruct (r_nat r) as [ns|]; [| reflexivity].
  destruct (e_nat e (pkt_flow p)); [reflexivity|].
  destruct (pkt_ctdir_orig p); cbv zeta; reflexivity.
Qed.

(** The body fold preserves [e_set]/[e_map] at every non-target name. *)
Lemma body_step_sm_stable : forall body e p nm,
  ~ In nm (body_dynset_names body) ->
  e_set (fst (body_res_state (body_step body e p))) nm = e_set e nm
  /\ e_map (fst (body_res_state (body_step body e p))) nm = e_map e nm.
Proof.
  induction body as [| it body IH]; intros e p nm Hnm; [split; reflexivity|].
  destruct it as [m | s].
  - cbn [body_step].
    destruct (eval_matchcond m e p).
    + destruct (IH (match_consume m e p) p nm Hnm) as [Hs Hm].
      rewrite Hs, Hm, e_set_match_consume, e_map_match_consume. split; reflexivity.
    + cbn [body_res_state fst].
      rewrite e_set_match_consume, e_map_match_consume. split; reflexivity.
  - assert (Hrest : ~ In nm (body_dynset_names body)).
    { intro Hin. apply Hnm. unfold body_dynset_names in *. cbn [flat_map].
      apply in_or_app; right; exact Hin. }
    assert (Hhd : ~ In nm (stmt_dynset_names s)).
    { intro Hin. apply Hnm. unfold body_dynset_names. cbn [flat_map].
      apply in_or_app; left; exact Hin. }
    destruct s; cbn [body_step];
      try (destruct (stmt_loadable _ p);
           [ apply (IH e p nm Hrest) | cbn [body_res_state fst]; split; reflexivity ]).
    + (* SNotrack *) apply (IH e (set_untracked p) nm Hrest).
    + (* SMetaSet *) destruct (vsrc_loadable _ p);
        [ apply (IH e _ nm Hrest) | cbn [body_res_state fst]; split; reflexivity ].
    + (* SCtSet *) destruct (vsrc_loadable vs p).
      * destruct (IH (set_ct e p k (eval_vsrc vs e p)) p nm Hrest) as [Hs Hm].
        rewrite Hs, Hm, e_set_set_ct, e_map_set_ct. split; reflexivity.
      * cbn [body_res_state fst]; split; reflexivity.
    + (* SSynproxy *) destruct (synproxy_loadable p).
      * destruct (synproxy_stops p);
          [ cbn [body_res_state fst]; split; reflexivity | apply (IH e p nm Hrest) ].
      * cbn [body_res_state fst]; split; reflexivity.
    + (* SDynset *) cbn [stmt_dynset_names] in Hhd.
      assert (Hne : nm <> name) by (intro; subst; apply Hhd; left; reflexivity).
      destruct dataf as [| d ds].
      * (* pure set: env_set_upd *)
        destruct (fields_loadable keyfs p).
        -- destruct (IH (env_set_upd e op name
                           (List.concat (map (fun f => field_value f e p) keyfs)))
                       p nm Hrest) as [Hs Hm].
           rewrite Hs, Hm, (e_set_env_set_upd_other e op name _ nm Hne),
                   e_map_env_set_upd.
           split; reflexivity.
        -- cbn [body_res_state fst]; split; reflexivity.
      * (* map: env_map_upd *)
        destruct (fields_loadable (keyfs ++ d :: ds) p).
        -- destruct (IH (env_map_upd e op name
                           (List.concat (map (fun f => field_value f e p) keyfs))
                           (field_value d e p))
                       p nm Hrest) as [Hs Hm].
           rewrite Hs, Hm, e_set_env_map_upd,
                   (e_map_env_map_upd_other e op name _ _ nm Hne).
           split; reflexivity.
        -- cbn [body_res_state fst]; split; reflexivity.
Qed.

Lemma after_step_sm_stable : forall ss e p nm,
  ~ In nm (flat_map stmt_dynset_names ss) ->
  e_set (fst (snd (after_step ss e p))) nm = e_set e nm
  /\ e_map (fst (snd (after_step ss e p))) nm = e_map e nm.
Proof.
  induction ss as [| s ss IH]; intros e p nm Hnm; [split; reflexivity|].
  assert (Hrest : ~ In nm (flat_map stmt_dynset_names ss)).
  { intro Hin. apply Hnm. cbn [flat_map]. apply in_or_app; right; exact Hin. }
  assert (Hhd : ~ In nm (stmt_dynset_names s)).
  { intro Hin. apply Hnm. cbn [flat_map]. apply in_or_app; left; exact Hin. }
  destruct s; cbn [after_step];
    try (destruct (stmt_loadable _ p);
         [ apply (IH e p nm Hrest) | cbn [fst snd]; split; reflexivity ]).
  - (* SNotrack *) apply (IH e (set_untracked p) nm Hrest).
  - (* SMetaSet *) destruct (vsrc_loadable _ p);
      [ apply (IH e _ nm Hrest) | cbn [fst snd]; split; reflexivity ].
  - (* SCtSet *) destruct (vsrc_loadable vs p).
    + destruct (IH (set_ct e p k (eval_vsrc vs e p)) p nm Hrest) as [Hs Hm].
      rewrite Hs, Hm, e_set_set_ct, e_map_set_ct. split; reflexivity.
    + cbn [fst snd]; split; reflexivity.
  - (* SSynproxy *) destruct (synproxy_loadable p).
    + destruct (synproxy_stops p);
        [ cbn [fst snd]; split; reflexivity | apply (IH e p nm Hrest) ].
    + cbn [fst snd]; split; reflexivity.
  - (* SDynset *) cbn [stmt_dynset_names] in Hhd.
    assert (Hne : nm <> name) by (intro; subst; apply Hhd; left; reflexivity).
    destruct dataf as [| d ds].
    + destruct (fields_loadable keyfs p).
      * destruct (IH (env_set_upd e op name
                        (List.concat (map (fun f => field_value f e p) keyfs)))
                     p nm Hrest) as [Hs Hm].
        rewrite Hs, Hm, (e_set_env_set_upd_other e op name _ nm Hne),
                e_map_env_set_upd.
        split; reflexivity.
      * cbn [fst snd]; split; reflexivity.
    + destruct (fields_loadable (keyfs ++ d :: ds) p).
      * destruct (IH (env_map_upd e op name
                        (List.concat (map (fun f => field_value f e p) keyfs))
                        (field_value d e p))
                     p nm Hrest) as [Hs Hm].
        rewrite Hs, Hm, e_set_env_map_upd,
                (e_map_env_map_upd_other e op name _ _ nm Hne).
        split; reflexivity.
      * cbn [fst snd]; split; reflexivity.
Qed.

Section WithHook.
Context (h : hook_id).

Lemma terminal_step_sm_stable : forall r e p nm,
  ~ In nm (flat_map stmt_dynset_names (r_after r)) ->
  e_set (fst (snd (terminal_step h r e p))) nm = e_set e nm
  /\ e_map (fst (snd (terminal_step h r e p))) nm = e_map e nm.
Proof.
  intros r e p nm Hnm. unfold terminal_step.
  destruct (has_effect_terminal r).
  - destruct (terminal_loadable r e p); [| split; reflexivity].
    destruct (nat_drops h r e p); [split; reflexivity|].
    cbn [fst snd].
    split; [rewrite e_set_apply_nat | rewrite e_map_apply_nat]; reflexivity.
  - destruct (r_verdict r); try (split; reflexivity).
    apply (after_step_sm_stable (r_after r) e p nm Hnm).
Qed.

Lemma end_step_sm_stable : forall r e p nm,
  ~ In nm (flat_map stmt_dynset_names (r_after r)) ->
  e_set (fst (snd (end_step h r e p))) nm = e_set e nm
  /\ e_map (fst (snd (end_step h r e p))) nm = e_map e nm.
Proof.
  intros r e p nm Hnm. unfold end_step.
  destruct (r_vmap r) as [vm|]; [| apply terminal_step_sm_stable; exact Hnm].
  destruct (vmap_loadable (Some vm) p); [| split; reflexivity]. cbv zeta.
  destruct (vm_keyf vm) as [[f ts]|];
    destruct (assoc_verdict _ (e_vmap e (vm_name vm)));
    solve [ split; reflexivity | apply terminal_step_sm_stable; exact Hnm ].
Qed.

(** THE stability fact: a rule's step preserves [e_set]/[e_map] at every name
    outside its dynset write targets. *)
Lemma rule_step_sm_stable : forall r e p nm,
  ~ In nm (rule_dynset_names r) ->
  e_set (fst (snd (rule_step h r e p))) nm = e_set e nm
  /\ e_map (fst (snd (rule_step h r e p))) nm = e_map e nm.
Proof.
  intros r e p nm Hnm. unfold rule_dynset_names in Hnm.
  assert (Hbody : ~ In nm (body_dynset_names (r_body r)))
    by (intro Hin; apply Hnm; apply in_or_app; left; exact Hin).
  assert (Hafter : ~ In nm (flat_map stmt_dynset_names (r_after r)))
    by (intro Hin; apply Hnm; apply in_or_app; right; exact Hin).
  unfold rule_step.
  pose proof (body_step_sm_stable (r_body r) e p nm Hbody) as [Hbs Hbm].
  destruct (body_step (r_body r) e p) as [e' p' | e' p' | e' p'] eqn:Hb;
    cbn [body_res_state fst] in Hbs, Hbm; cbn [fst snd].
  - split; assumption.
  - split; assumption.
  - destruct (end_step_sm_stable r e' p' nm Hafter) as [Hes Hem].
    split; [rewrite Hes; exact Hbs | rewrite Hem; exact Hbm].
Qed.

(** ** Part B: generic effect-level list lemmas. *)

(** On a mut-free rule the step leaves the state at [(e, p)]: the state half is
    pinned, read off [rule_step_state_mutfree] without naming any write-free verdict. *)
Lemma rule_step_mutfree_state : forall r e p,
  rule_mutfree r = true -> snd (rule_step h r e p) = (e, p).
Proof. intros r e p H. exact (rule_step_state_mutfree h r e p H). Qed.

(** A mut-free head steps the fold in the guarded shape, its tail continuing from
    the UNCHANGED [(e, p)] — the fold's own cons equation specialised to a
    write-free head, keyed on the step's own verdict [fst (rule_step h r e p)]. *)
Lemma eval_rules_mut_st_mutfree_cons : forall r tl e p,
  rule_mutfree r = true ->
  eval_rules_mut_st h (r :: tl) e p
  = match fst (rule_step h r e p) with
    | Some v => if terminal v then (Some v, (e, p)) else eval_rules_mut_st h tl e p
    | None => eval_rules_mut_st h tl e p
    end.
Proof.
  intros r tl e p H. rewrite eval_rules_mut_st_cons.
  pose proof (rule_step_mutfree_state r e p H) as Hpin.
  destruct (rule_step h r e p) as [v [e' p']]. cbn [fst snd] in Hpin |- *.
  injection Hpin as He Hp; subst.
  destruct v as [w |]; [destruct (terminal w) |]; reflexivity.
Qed.

(** Cons congruence on a mut-free head: since the head pins the state to [(e,p)],
    a tail equality AT [(e,p)] suffices — no arbitrary-state premise. *)
Lemma eval_rules_mut_st_mutfree_cons_cong : forall r rs1 rs2 e p,
  rule_mutfree r = true ->
  eval_rules_mut_st h rs1 e p = eval_rules_mut_st h rs2 e p ->
  eval_rules_mut_st h (r :: rs1) e p = eval_rules_mut_st h (r :: rs2) e p.
Proof.
  intros r rs1 rs2 e p Hmf Htl.
  rewrite (eval_rules_mut_st_mutfree_cons r rs1 e p Hmf),
          (eval_rules_mut_st_mutfree_cons r rs2 e p Hmf).
  destruct (fst (rule_step h r e p)) as [w |];
    [destruct (terminal w); [reflexivity | exact Htl] | exact Htl].
Qed.

(** A WRITE-FREE prefix's state fold walks the block leaving [(e, p)] fixed: it
    produces the block's own first-match verdict [fst (eval_rules_mut_st h b e p)]
    (a terminal-verdict early exit at the same pinned state), and on fall-through
    the tail continues from the ORIGINAL state.  This is what lets a guarded merge
    proved on the block itself be lifted to the whole run — entirely over the state
    fold, no pure-verdict detour. *)
Lemma eval_rules_mut_st_mutfree_prefix : forall b rest e p,
  forallb rule_mutfree b = true ->
  eval_rules_mut_st h (b ++ rest) e p
  = match fst (eval_rules_mut_st h b e p) with
    | Some v => (Some v, (e, p))
    | None => eval_rules_mut_st h rest e p
    end.
Proof.
  induction b as [| r b IH]; intros rest e p Hmf; [reflexivity|].
  cbn [forallb] in Hmf. apply Bool.andb_true_iff in Hmf as [Hr Hb].
  cbn [app].
  rewrite (eval_rules_mut_st_mutfree_cons r (b ++ rest) e p Hr).
  rewrite (eval_rules_mut_st_mutfree_cons r b e p Hr).
  destruct (fst (rule_step h r e p)) as [v|].
  - destruct (terminal v); [reflexivity | apply IH; exact Hb].
  - apply IH; exact Hb.
Qed.

(** Replace one write-free block by a state-fold-verdict-equivalent write-free
    block: the state fold leaves both blocks' state at [(e, p)], so agreement of
    their first-match verdicts transfers the whole run. *)
Lemma eval_rules_mut_st_mutfree_block : forall b1 b2 rest e p,
  forallb rule_mutfree b1 = true ->
  forallb rule_mutfree b2 = true ->
  fst (eval_rules_mut_st h b1 e p) = fst (eval_rules_mut_st h b2 e p) ->
  eval_rules_mut_st h (b1 ++ rest) e p = eval_rules_mut_st h (b2 ++ rest) e p.
Proof.
  intros b1 b2 rest e p H1 H2 Heq.
  rewrite (eval_rules_mut_st_mutfree_prefix b1 rest e p H1).
  rewrite (eval_rules_mut_st_mutfree_prefix b2 rest e p H2).
  rewrite Heq. reflexivity.
Qed.

(** Dropping a mut-free head [r1] that is SUBSUMED by the next rule [r2] (every
    terminal firing of [r1] is a terminal firing of [r2], at the SAME verdict)
    leaves the state fold unchanged: on the pinned state [r2], reached at [r1]'s
    old slot, decides identically anything [r1] would have. *)
Lemma eval_rules_mut_st_absorb_pair : forall r1 r2 rest e p,
  rule_mutfree r1 = true ->
  rule_mutfree r2 = true ->
  (forall v, fst (rule_step h r1 e p) = Some v -> fst (rule_step h r2 e p) = Some v) ->
  eval_rules_mut_st h (r1 :: r2 :: rest) e p = eval_rules_mut_st h (r2 :: rest) e p.
Proof.
  intros r1 r2 rest e p Hmf1 Hmf2 Hsub.
  rewrite (eval_rules_mut_st_mutfree_cons r1 (r2 :: rest) e p Hmf1).
  destruct (fst (rule_step h r1 e p)) as [v|] eqn:E1; [| reflexivity].
  destruct (terminal v) eqn:Et; [| reflexivity].
  rewrite (eval_rules_mut_st_mutfree_cons r2 rest e p Hmf2).
  rewrite (Hsub v eq_refl), Et. reflexivity.
Qed.

(** Stepping one shared head rule on both sides. *)
Lemma eval_rules_mut_st_cons_cong : forall r rs1 rs2 e p,
  (forall e' p', eval_rules_mut_st h rs1 e' p' = eval_rules_mut_st h rs2 e' p') ->
  eval_rules_mut_st h (r :: rs1) e p = eval_rules_mut_st h (r :: rs2) e p.
Proof.
  intros r rs1 rs2 e p Htail. rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
  destruct (rule_step h r e p) as [[v|] [e' p']];
    [ destruct (terminal v); [reflexivity | apply Htail] | apply Htail ].
Qed.

(** *** The first-match N-way merge over the state fold — abstract shell core.

    A nonempty run [map mk ms] of shells indexed by matchconds [ms], each
    stepping (on the pinned state [(e, p)]) to the guarded verdict [if
    (match_loadable m p && Lc) && (eval_matchcond m e p && Ac) then Oc else None],
    collapses to the ONE shell [mk m12] whose loadability agrees ([match_loadable
    m12 = ML]) and whose match realises the run's disjunction ([eval_matchcond m12
    = existsb ...]).  The conclusion is over the FULL observable of the fold —
    verdict AND resulting (env, packet).

    The shared loadability [Lc], body applicability [Ac] and fired verdict [Oc]
    are ABSTRACT: the caller supplies them (in [eval_rules_mut_st_run_merge_abs]
    via each shell's own [rule_step] under [rule_step_state_mutfree]), so the combinator
    reasons only over [rule_step]/[eval_rules_mut_st].  The [rule_mutfree]
    hypotheses are load-bearing: on the state fold a shell that does NOT fire can
    still advance the env (a limiter head consumes its bucket at its position),
    and a firing shell whose verdict falls through re-runs on the next shell — so
    an unconstrained merge would NOT preserve the threaded state.  Under
    mut-freeness [rule_step_mutfree_state] pins every shell's step to leave the
    state at [(e, p)]; the threaded state is then constant across the whole run,
    and the first-match/break argument runs directly over the fold's (verdict,
    state) pair. *)
Lemma shell_run_merge :
  forall (ms : list matchcond) (ML : packet -> bool) (Lc Ac : bool) (Oc : option verdict)
         (mk : matchcond -> rule) m12 rest e p,
  ms <> [] ->
  rule_mutfree (mk m12) = true ->
  (forall m, In m ms -> rule_mutfree (mk m) = true) ->
  (forall m, rule_mutfree (mk m) = true ->
     fst (rule_step h (mk m) e p)
     = (if (match_loadable m p && Lc) && (eval_matchcond m e p && Ac) then Oc else None)) ->
  (forall m, In m ms -> match_loadable m p = ML p) ->
  match_loadable m12 p = ML p ->
  eval_matchcond m12 e p = existsb (fun m => eval_matchcond m e p) ms ->
  eval_rules_mut_st h (mk m12 :: rest) e p
  = eval_rules_mut_st h (map mk ms ++ rest) e p.
Proof.
  intros ms ML Lc Ac Oc mk m12 rest e p Hne Hmf12 HmfEach Hverd HmlAll Hml Hev.
  (* Each mut-free shell steps in the guarded [if]-shape, its state pinned to
     [(e, p)]: the fold's [(verdict, state)] pair for one shell. *)
  assert (Hshell : forall m tl, rule_mutfree (mk m) = true ->
            eval_rules_mut_st h (mk m :: tl) e p
            = if (match_loadable m p && Lc) && (eval_matchcond m e p && Ac)
              then match Oc with
                   | Some w => if terminal w then (Some w, (e, p))
                               else eval_rules_mut_st h tl e p
                   | None => eval_rules_mut_st h tl e p
                   end
              else eval_rules_mut_st h tl e p).
  { intros m tl Hm.
    rewrite (eval_rules_mut_st_mutfree_cons (mk m) tl e p Hm), (Hverd m Hm).
    destruct ((match_loadable m p && Lc) && (eval_matchcond m e p && Ac)); reflexivity. }
  (* Characterise the whole run [run ++ rest] by first-match induction on [ms],
     with the threaded state pinned at [(e, p)] throughout. *)
  assert (Hrun :
    eval_rules_mut_st h (map mk ms ++ rest) e p
    = if ((ML p && Lc) && (existsb (fun m => eval_matchcond m e p) ms && Ac)) then
        match Oc with
        | Some v => if terminal v then (Some v, (e, p))
                    else eval_rules_mut_st h rest e p
        | None => eval_rules_mut_st h rest e p
        end
      else eval_rules_mut_st h rest e p).
  { clear Hev Hml Hmf12.
    assert (Hterm : (match Oc with Some v => terminal v | None => false end) = false
                    \/ (exists v, Oc = Some v /\ terminal v = true)).
    { destruct Oc as [v |]; [destruct (terminal v) eqn:Et;
        [right; eauto | left; reflexivity] | left; reflexivity]. }
    destruct Hterm as [Hnt | [v [EO Ev]]].
    - (* non-terminal / None fired verdict: the whole run falls through to [rest] *)
      assert (Htarget :
        match Oc with
        | Some w => if terminal w then (Some w, (e, p)) else eval_rules_mut_st h rest e p
        | None => eval_rules_mut_st h rest e p
        end = eval_rules_mut_st h rest e p).
      { destruct Oc as [w |]; [destruct (terminal w) eqn:Etw;
          [exfalso; clear -Hnt Etw; cbn in Hnt; congruence | reflexivity] | reflexivity]. }
      transitivity (eval_rules_mut_st h rest e p).
      2:{ rewrite Htarget. destruct ((ML p && Lc) && _); reflexivity. }
      clear Hne Hnt. revert HmlAll HmfEach.
      induction ms as [| m ms IH]; intros HmlAll HmfEach.
      + reflexivity.
      + cbn [map app]. rewrite (Hshell m _ (HmfEach m (or_introl eq_refl))).
        rewrite (IH (fun mm Hmm => HmlAll mm (or_intror Hmm))
                    (fun mm Hmm => HmfEach mm (or_intror Hmm))).
        destruct (match_loadable m p && Lc && (eval_matchcond m e p && Ac));
          [rewrite Htarget; reflexivity | reflexivity].
    - (* terminal [Some v]: first-match position matters *)
      rewrite EO. clear Hne. revert HmlAll HmfEach.
      induction ms as [| m ms IH]; intros HmlAll HmfEach.
      + cbn [map app existsb]. rewrite Bool.andb_false_r. reflexivity.
      + cbn [map app]. rewrite (Hshell m _ (HmfEach m (or_introl eq_refl))).
        rewrite (HmlAll m (or_introl eq_refl)). cbn [existsb].
        rewrite (IH (fun mm Hmm => HmlAll mm (or_intror Hmm))
                    (fun mm Hmm => HmfEach mm (or_intror Hmm))).
        rewrite EO, Ev.
        destruct (ML p && Lc); cbn [andb]; [| reflexivity].
        destruct Ac; [| rewrite !Bool.andb_false_r; reflexivity].
        rewrite !Bool.andb_true_r.
        destruct (eval_matchcond m e p); cbn [orb andb]; reflexivity. }
  (* Assemble: the merged shell's single step vs the run's characterisation. *)
  rewrite (Hshell m12 rest Hmf12), Hml, Hev, Hrun. reflexivity.
Qed.

(** *** The first-match N-way merge/absorption certificate over the state fold.

    A nonempty run [map (fun m => mk_head m body r1) ms] of shells that share the
    SAME tail body and SAME end record [r1], differing only in the head match,
    collapses to the ONE merged shell [mk_head m12 body r1] whose head realises
    the disjunction ([eval_matchcond m12 = existsb ...]).  The shared loadability,
    body applicability and fired verdict are read off each shell's own [rule_step]
    under [body_step_mutfree_synfree] — the guarded shell verdict [shell_run_merge]
    consumes — via the [mk_head] head/tail/end equations; the
    combinator supplies the first-match/break argument over the fold.  This is the
    substrate the optimizer's per-pass merge proofs apply directly (with
    [eval_rules_mut_st_mutfree_cons_cong] bridging the recursively-optimised
    tail). *)
Lemma eval_rules_mut_st_run_merge_abs :
  forall (ms : list matchcond) (ML : packet -> bool) body r1 m12 rest e p,
  ms <> [] ->
  rule_mutfree (mk_head m12 body r1) = true ->
  forallb rule_mutfree (map (fun m => mk_head m body r1) ms) = true ->
  (forall m, In m ms -> match_loadable m p = ML p) ->
  match_loadable m12 p = ML p ->
  eval_matchcond m12 e p = existsb (fun m => eval_matchcond m e p) ms ->
  eval_rules_mut_st h (mk_head m12 body r1 :: rest) e p
  = eval_rules_mut_st h (map (fun m => mk_head m body r1) ms ++ rest) e p.
Proof.
  intros ms ML body r1 m12 rest e p Hne Hmf12 HmfRun HmlAll Hml Hev.
  assert (HmfEach : forall m, In m ms -> rule_mutfree (mk_head m body r1) = true).
  { intros m Hm. rewrite forallb_forall in HmfRun.
    exact (HmfRun (mk_head m body r1) (in_map (fun m => mk_head m body r1) ms m Hm)). }
  refine (shell_run_merge ms ML true true
            (fst (rule_step h (mk_tail body r1) e p))
            (fun m => mk_head m body r1) m12 rest e p
            Hne Hmf12 HmfEach _ HmlAll Hml Hev).
  (* Each mut-free shell's step verdict, read off [rule_step_fst_mk_head]: the
     tail shell's verdict guarded by the (consume-free) head match — the abstract
     [Lc]/[Ac] collapse to [true], [Oc] to the shared tail step. *)
  intros m Hmfm.
  rewrite (rule_step_fst_mk_head h m body r1 e p (mk_head_mutfree_head m body r1 Hmfm)).
  rewrite !Bool.andb_true_r, eval_matchcond_loadable_absorb. reflexivity.
Qed.

(** *** The family-agnostic N-way run collapse over the state fold.

    A nonempty run [map mk xs] of write-free shells, each stepping (on the pinned
    state [(e, p)]) to the guarded verdict [if LL && mc x then O else None] — a
    SHARED loadability [LL] and fired verdict [O], differing only in the per-shell
    firing bit [mc x] — collapses to the ONE merged shell [rm] whose own step fires
    exactly the run's disjunction [if LL && existsb mc xs then O else None].  The
    conclusion is over the FULL observable of the fold — verdict AND resulting
    (env, packet).

    Everything is phrased over [rule_step]/[eval_rules_mut_st]: the per-shell
    firing shape [mc], the shared [LL]/[O] and the merged shell's disjunction are
    supplied by the caller (each read off the shell's own [rule_step] under
    [rule_step_state_mutfree] via the pass's structural certificates).  The [rule_mutfree]
    hypotheses are load-bearing: on the state fold a shell that does NOT fire can
    still advance the env at its position, so an unconstrained collapse would not
    preserve the threaded state.  Under mut-freeness [rule_step_mutfree_state] pins
    every step to leave the state at [(e, p)]; the threaded state is then constant
    across the whole run, and the first-match/break argument runs directly over the
    fold's (verdict, state) pair.  This is the substrate the value->set / concat-set
    N-way passes are certified on. *)
Lemma eval_rules_mut_st_run_collapse :
  forall {A : Type} (xs : list A) (mk : A -> rule) (mc : A -> bool)
         (LL : bool) (O : option verdict) rm rest e p,
  xs <> [] ->
  forallb rule_mutfree (map mk xs) = true ->
  rule_mutfree rm = true ->
  (forall x, In x xs ->
     fst (rule_step h (mk x) e p) = (if LL && mc x then O else None)) ->
  fst (rule_step h rm e p) = (if LL && existsb mc xs then O else None) ->
  eval_rules_mut_st h (rm :: rest) e p
  = eval_rules_mut_st h (map mk xs ++ rest) e p.
Proof.
  intros A xs mk mc LL O rm rest e p Hne HmfRun Hmfrm Hx Hrm.
  assert (HmfEach : forall x, In x xs -> rule_mutfree (mk x) = true).
  { intros x Hin. rewrite forallb_forall in HmfRun.
    exact (HmfRun (mk x) (in_map mk xs x Hin)). }
  (* Each mut-free shell steps in the guarded [if]-shape (its firing bit [mc x],
     the shared [LL]/[O]), state pinned to [(e, p)] — the fold's (verdict, state)
     pair for one shell, read off its own [rule_step] via [Hx]. *)
  assert (Hstep : forall x tl, In x xs ->
            eval_rules_mut_st h (mk x :: tl) e p
            = if LL && mc x
              then match O with
                   | Some w => if terminal w then (Some w, (e, p))
                               else eval_rules_mut_st h tl e p
                   | None => eval_rules_mut_st h tl e p
                   end
              else eval_rules_mut_st h tl e p).
  { intros x tl Hin.
    rewrite (eval_rules_mut_st_mutfree_cons (mk x) tl e p (HmfEach x Hin)).
    rewrite (Hx x Hin). destruct (LL && mc x); reflexivity. }
  (* The merged shell's own single step, same shape with the run's disjunction. *)
  assert (Hstepm : eval_rules_mut_st h (rm :: rest) e p
            = if LL && existsb mc xs
              then match O with
                   | Some w => if terminal w then (Some w, (e, p))
                               else eval_rules_mut_st h rest e p
                   | None => eval_rules_mut_st h rest e p
                   end
              else eval_rules_mut_st h rest e p).
  { rewrite (eval_rules_mut_st_mutfree_cons rm rest e p Hmfrm).
    rewrite Hrm. destruct (LL && existsb mc xs); reflexivity. }
  (* Characterise the whole run [map mk xs ++ rest] by first-match induction. *)
  assert (Hrun :
    eval_rules_mut_st h (map mk xs ++ rest) e p
    = if LL && existsb mc xs then
        match O with
        | Some v => if terminal v then (Some v, (e, p))
                    else eval_rules_mut_st h rest e p
        | None => eval_rules_mut_st h rest e p
        end
      else eval_rules_mut_st h rest e p).
  { clear Hrm Hmfrm HmfRun Hstepm.
    assert (Hterm : (match O with Some v => terminal v | None => false end) = false
                    \/ (exists v, O = Some v /\ terminal v = true)).
    { destruct O as [v |]; [destruct (terminal v) eqn:Et;
        [right; eauto | left; reflexivity] | left; reflexivity]. }
    destruct Hterm as [Hnt | [v [EO Ev]]].
    - (* non-terminal / None fired verdict: the whole run falls through to [rest] *)
      assert (Htarget :
        match O with
        | Some w => if terminal w then (Some w, (e, p)) else eval_rules_mut_st h rest e p
        | None => eval_rules_mut_st h rest e p
        end = eval_rules_mut_st h rest e p).
      { destruct O as [w |]; [destruct (terminal w) eqn:Etw;
          [exfalso; clear -Hnt Etw; cbn in Hnt; congruence | reflexivity] | reflexivity]. }
      transitivity (eval_rules_mut_st h rest e p).
      2:{ rewrite Htarget. destruct (LL && _); reflexivity. }
      clear Hne Hnt. revert Hx HmfEach Hstep.
      induction xs as [| x xs IH]; intros Hx HmfEach Hstep; [reflexivity|].
      cbn [map app]. rewrite (Hstep x _ (or_introl eq_refl)).
      rewrite (IH (fun x' Hx' => Hx x' (or_intror Hx'))
                  (fun x' Hx' => HmfEach x' (or_intror Hx'))
                  (fun x' tl Hx' => Hstep x' tl (or_intror Hx'))).
      destruct (LL && mc x); [rewrite Htarget; reflexivity | reflexivity].
    - (* terminal [Some v]: first-match position matters *)
      rewrite EO. clear Hne. revert Hx HmfEach Hstep.
      induction xs as [| x xs IH]; intros Hx HmfEach Hstep.
      + cbn [map app existsb]. rewrite Bool.andb_false_r. reflexivity.
      + cbn [map app]. rewrite (Hstep x _ (or_introl eq_refl)).
        rewrite (IH (fun x' Hx' => Hx x' (or_intror Hx'))
                    (fun x' Hx' => HmfEach x' (or_intror Hx'))
                    (fun x' tl Hx' => Hstep x' tl (or_intror Hx'))).
        cbn [existsb]. rewrite EO, Ev.
        destruct LL; cbn [andb]; [| reflexivity].
        destruct (mc x); cbn [orb]; reflexivity. }
  rewrite Hstepm, Hrun. reflexivity.
Qed.

End WithHook.

(** Pull the per-shell firing bit [c] to the outside of a shell's guard so the
    shared loadability/applicability factor [a && b] reads as the collapse's [LL].
    [reflexivity] on the reassociated form unifies [LL] and the per-shell [mc]
    against the [body_step_mutfree_synfree] shape at each merge site. *)
Lemma andb_swap_mid : forall a b c, a && (c && b) = (a && b) && c.
Proof. intros [] [] []; reflexivity. Qed.

(** The guarded shells carry a SHARED head guard [g] as well: pull the per-shell
    firing bit [c] out from under both [g] and the shared applicability [w]. *)
Lemma andb_pull3 : forall a g c w, a && (g && (c && w)) = (a && g && w) && c.
Proof. intros [] [] [] []; reflexivity. Qed.

(** The two-selector guarded shell nests the guard [g] between the two per-shell
    selectors; renormalise it to the [g && (c && w)] shape [andb_pull3] consumes. *)
Lemma andb_reassoc_g2 : forall c1 g c2 w, (c1 && g) && c2 && w = g && ((c1 && c2) && w).
Proof. intros [] [] [] []; reflexivity. Qed.

(** Push a mut-free rule's loadable/applicable guard [C] outside the fold's
    verdict [match]: the shape a per-rule [body_step_mutfree_synfree] rewrite lands the
    fold in, restated as the pure-strand [if]-guarded cons the merge inductions
    read.  [T] is the tail's fold, [ep] the pinned state. *)
Lemma match_if_push :
  forall (C : bool) (O : option verdict)
         (T : option verdict * (env * packet)) (ep : env * packet),
  match (if C then O else None) with
  | Some w => if terminal w then (Some w, ep) else T
  | None => T
  end
  = if C then match O with
              | Some w => if terminal w then (Some w, ep) else T
              | None => T
              end
         else T.
Proof. intros [] O T ep; reflexivity. Qed.

(** Replace a run [map mk1 l] by [map mk2 l] rule-for-rule when every shell steps
    to the SAME fold verdict on the pinned state (all mut-free): the state fold is
    determined position-by-position by each shell's [fst (rule_step ...)]. *)
Lemma eval_rules_mut_st_map_cong :
  forall (h : hook_id) {A : Type} (mk1 mk2 : A -> rule) l rest e p,
  (forall x, In x l -> rule_mutfree (mk1 x) = true) ->
  (forall x, In x l -> rule_mutfree (mk2 x) = true) ->
  (forall x, In x l -> fst (rule_step h (mk1 x) e p) = fst (rule_step h (mk2 x) e p)) ->
  eval_rules_mut_st h (map mk1 l ++ rest) e p
  = eval_rules_mut_st h (map mk2 l ++ rest) e p.
Proof.
  intros h A mk1 mk2 l rest e p.
  induction l as [| x l IH]; intros H1 H2 Hst; [reflexivity|].
  cbn [map app].
  rewrite (eval_rules_mut_st_mutfree_cons h (mk1 x) _ e p (H1 x (or_introl eq_refl))).
  rewrite (eval_rules_mut_st_mutfree_cons h (mk2 x) _ e p (H2 x (or_introl eq_refl))).
  rewrite (Hst x (or_introl eq_refl)).
  assert (IHtl : eval_rules_mut_st h (map mk1 l ++ rest) e p
                 = eval_rules_mut_st h (map mk2 l ++ rest) e p).
  { apply IH; intros y Hy; [apply H1 | apply H2 | apply Hst]; right; exact Hy. }
  destruct (fst (rule_step h (mk2 x) e p)) as [w|];
    [ destruct (terminal w); [reflexivity | exact IHtl] | exact IHtl ].
Qed.

(** [rule_mutfree] transfer along [mk_head] shells: mut-freedom is the tail
    body + after + natfree conjunction, with the head contributing only its
    [match_consumefree]. *)
Lemma rule_mutfree_mk_head : forall m body r,
  rule_mutfree (mk_head m body r)
  = match_consumefree m
    && (forallb body_item_mutfree body
        && forallb (fun s => negb (is_mut_stmt s)) (r_after r)
        && rule_natfree r).
Proof.
  intros m body r. unfold rule_mutfree, mk_head, rule_natfree, r_nat.
  cbn [r_body r_after r_outcome forallb body_item_mutfree].
  rewrite <- !Bool.andb_assoc. reflexivity.
Qed.

(** Swap the head of a mut-free shell for any consumption-free match. *)
Lemma rule_mutfree_mk_head_swap : forall m m' body r,
  match_consumefree m' = true ->
  rule_mutfree (mk_head m body r) = true ->
  rule_mutfree (mk_head m' body r) = true.
Proof.
  intros m m' body r Hm' H.
  rewrite rule_mutfree_mk_head in H |- *.
  apply Bool.andb_true_iff in H as [_ Htail].
  rewrite Hm'. cbn [andb]. exact Htail.
Qed.

(** A write-free rule has NO dynset target at all. *)
Lemma mutfree_body_dynset_nil : forall body,
  forallb body_item_mutfree body = true -> body_dynset_names body = [].
Proof.
  induction body as [| it body IH]; intro H; [reflexivity|].
  cbn [forallb] in H. apply Bool.andb_true_iff in H as [Hit Hrest].
  destruct it as [m | s]; unfold body_dynset_names in *; cbn [flat_map].
  - apply IH; exact Hrest.
  - destruct s; cbn [body_item_mutfree is_mut_stmt negb] in Hit; try discriminate Hit;
      cbn [stmt_dynset_names app]; apply IH; exact Hrest.
Qed.

Lemma mutfree_after_dynset_nil : forall ss,
  forallb (fun s => negb (is_mut_stmt s)) ss = true ->
  flat_map stmt_dynset_names ss = [].
Proof.
  induction ss as [| s ss IH]; intro H; [reflexivity|].
  cbn [forallb] in H. apply Bool.andb_true_iff in H as [Hs Hrest].
  destruct s; cbn [is_mut_stmt negb] in Hs; try discriminate Hs;
    cbn [flat_map stmt_dynset_names app]; apply IH; exact Hrest.
Qed.

Lemma rule_mutfree_dynset_nil : forall r,
  rule_mutfree r = true -> rule_dynset_names r = [].
Proof.
  intros r H. unfold rule_mutfree in H.
  apply Bool.andb_true_iff in H as [H _].
  apply Bool.andb_true_iff in H as [Hbody Hafter].
  unfold rule_dynset_names.
  rewrite (mutfree_body_dynset_nil _ Hbody), (mutfree_after_dynset_nil _ Hafter).
  reflexivity.
Qed.

(** ** Part C: write-target freshness ([Optimize_Uncond.rule_dynset_fresh],
    the dynset analogue of [rule_set_fresh]): a rule whose dynset targets avoid
    every minted [setname]/[mapname] at-or-above [n] cannot clobber a minted
    declaration; threaded through the fold via [rule_step_sm_stable] it keeps
    the minted lookups intact at every intermediate env. *)

Lemma rule_mutfree_dynset_fresh : forall n r,
  rule_mutfree r = true -> rule_dynset_fresh n r.
Proof.
  intros n r H k Hk. rewrite (rule_mutfree_dynset_nil r H).
  split; intros [].
Qed.

(** Stability of the two minted-name lookups across one rule step. *)
Lemma rule_step_setname_stable : forall h r e p k n,
  rule_dynset_fresh n r -> n <= k ->
  e_set (fst (snd (rule_step h r e p))) (setname k) = e_set e (setname k).
Proof.
  intros h r e p k n Hf Hk.
  destruct (Hf k Hk) as [Hs _].
  exact (proj1 (rule_step_sm_stable h r e p (setname k) Hs)).
Qed.

Lemma rule_step_mapname_stable : forall h r e p k n,
  rule_dynset_fresh n r -> n <= k ->
  e_map (fst (snd (rule_step h r e p))) (mapname k) = e_map e (mapname k).
Proof.
  intros h r e p k n Hf Hk.
  destruct (Hf k Hk) as [_ Hm].
  exact (proj2 (rule_step_sm_stable h r e p (mapname k) Hm)).
Qed.

(** All canonical shells over a shared write-free tail are write-free. *)
Lemma forallb_mutfree_shells : forall (A : Type) (g : A -> matchcond) l body r m0,
  (forall a : A, match_consumefree (g a) = true) ->
  rule_mutfree (mk_head m0 body r) = true ->
  forallb rule_mutfree (map (fun a => mk_head (g a) body r) l) = true.
Proof.
  intros A g l body r m0 Hg Hmf. apply forallb_forall.
  intros x Hx. apply in_map_iff in Hx as [a [Ha _]]. subst x.
  exact (rule_mutfree_mk_head_swap m0 (g a) body r (Hg a) Hmf).
Qed.

(** ** Part D: per-stage EFFECT-level correctness.

    Each stage lemma states: under the SAME environment [e] — constrained only
    to resolve the stage's own minted names as the output declarations do
    ([Hmint], pointwise, so it survives threading) — the output rules and the
    input rules produce the SAME (verdict, env) under the effect-observing fold.
    Unlike the verdict-level [_correct_uncond] family, both sides run under ONE
    env, so no cross-decl agreement machinery is needed; the write-target
    freshness [Forall (rule_dynset_fresh n)] keeps [Hmint] true at every
    intermediate env. *)

(** *** valueset. *)
Theorem optimize_rules_valueset_mut_st : forall h fuel rs n d n' d' rs' base e p,
  optimize_rules_valueset fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) rs ->
  eval_rules_mut_st h rs' e p = eval_rules_mut_st h rs e p.
Proof.
  intros h fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base e p H Hfresh Hmint Hwf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest]].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_valueset_consSS in H.
      inversion Hwf as [| ? ? Hwf1 Hwf_tail]; subst.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_value_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct (take_value_run_shape r1 f v1 body (r2 :: rest) vs rest' Ehd Erun)
          as [Hsplit Hwidth].
        destruct vs as [| v vs'].
        -- (* no eligible neighbour: keep r1, recurse at the stepped state *)
           remember (optimize_rules_valueset fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
           assert (Hst : forall k, n <= k ->
                     e_set (fst (snd (rule_step h r1 e p))) (setname k)
                     = e_set e (setname k))
             by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
           destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
           ++ destruct (terminal w); [reflexivity |].
              apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                       Hfresh); [| exact Hwf_tail].
              intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
           ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                       Hfresh); [| exact Hwf_tail].
              intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
        -- (* RUN of >= 2 rules: the guarded (write-free) merge *)
           cbv zeta in H.
           remember (optimize_rules_valueset fuel (S n)
                       {| sd_sets := (setname n, map (fun w => (w,w)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd'']rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (vals := v1 :: v :: vs') in *.
           set (dn := {| sd_sets := (setname n, map (fun w => (w,w)) vals) :: sd_sets d;
                         sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
           pose proof (optimize_rules_valueset_mono fuel (S n) dn rest' m'' dd'' rr''
                         (eq_sym Erec)) as Hmono.
           (* the fired first pair certifies r1 (hence every shell) write-free *)
           assert (Hmf1 : rule_mutfree r1 = true).
           { pose proof Erun as Erun2. cbn in Erun2.
             destruct (value_merge_pair r1 r2) as [[[[fa va] v2] bd]|] eqn:Evm.
             - exact (value_merge_pair_mutfree r1 r2 _ Evm).
             - inversion Erun2. }
           assert (Hr1shell : r1 = mk_head (MCmp f CEq v1) body r1)
             by (apply head_value_canon; exact Ehd).
           assert (Hmf1' : rule_mutfree (mk_head (MCmp f CEq v1) body r1) = true)
             by (rewrite <- Hr1shell; exact Hmf1).
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun w => mk_head (MCmp f CEq w) body r1) vals ++ rest').
           { subst vals. cbn [map app]. f_equal; [exact Hr1shell | exact Hsplit]. }
           (* the CURRENT env resolves the minted set to its point elements *)
           assert (Hlook : e_set e (setname n) = map (fun w => (w,w)) vals).
           { rewrite (Hmint n (le_n n) ltac:(lia)).
             rewrite e_set_declared.
             erewrite (optimize_rules_valueset_assoc_stable fuel (S n) dn rest'
                         m'' dd'' rr'' (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           assert (Hcert : eval_matchcond (MConcatSet [f] false (setname n)) e p
                   = existsb (fun w => eval_matchcond (MCmp f CEq w) e p) vals).
           { apply (concat_set_existsb f vals (setname n) e p).
             - exact Hlook.
             - intros w Hw Hld.
               assert (Hfxw : field_fixed_len f = Some (Datatypes.length w)).
               { subst vals. destruct Hw as [Hw | Hw].
                 - subst w. apply (take_value_run_head_width r1 f v1 body r2 rest
                                     (v :: vs') rest' Ehd Erun). discriminate.
                 - apply (Hwidth w Hw). }
               apply (field_fixed_len_loaded f (Datatypes.length w) e p Hfxw Hld). }
           assert (HmfM : forallb rule_mutfree
                     [mk_head (MConcatSet [f] false (setname n)) body r1] = true).
           { cbn [forallb].
             rewrite (rule_mutfree_mk_head_swap (MCmp f CEq v1)
                        (MConcatSet [f] false (setname n)) body r1 eq_refl Hmf1').
             reflexivity. }
           assert (HmfR : forallb rule_mutfree
                     (map (fun w => mk_head (MCmp f CEq w) body r1) vals) = true).
           { apply (forallb_mutfree_shells data (fun w => MCmp f CEq w) vals body r1
                      (MCmp f CEq v1)); [intro; reflexivity | exact Hmf1']. }
           assert (HmfMh : rule_mutfree
                     (mk_head (MConcatSet [f] false (setname n)) body r1) = true).
           { cbn [forallb] in HmfM. apply Bool.andb_true_iff in HmfM.
             exact (proj1 HmfM). }
           rewrite Hrun_eq.
           transitivity (eval_rules_mut_st h
                           (mk_head (MConcatSet [f] false (setname n)) body r1 :: rest') e p).
           ++ apply (eval_rules_mut_st_mutfree_cons_cong h _ rr'' rest' e p HmfMh).
              apply (IH rest' (S n) dn m'' dd'' rr'' base e p (eq_sym Erec)).
              --- intros k Hk Hin. subst dn; cbn [sd_sets map fst] in Hin.
                  destruct Hin as [Heq | Hin];
                    [ apply setname_inj in Heq; lia
                    | apply (Hfresh k); [lia | exact Hin] ].
              --- intros k Hk Hk'. apply Hmint; lia.
              --- eapply Forall_impl;
                    [ intros r Hr; apply (rule_dynset_fresh_mono n (S n) r); [lia | exact Hr] |].
                  rewrite Hsplit in Hwf_tail. apply Forall_app in Hwf_tail.
                  exact (proj2 Hwf_tail).
           ++ pose proof (eval_rules_mut_st_run_merge_abs h
                            (map (fun w => MCmp f CEq w) vals)
                            (fun q => fields_loadable [f] q) body r1
                            (MConcatSet [f] false (setname n)) rest' e p) as Hmerge.
              rewrite List.map_map in Hmerge.
              apply Hmerge; clear Hmerge.
              --- subst vals. cbn [map]. discriminate.
              --- exact HmfMh.
              --- exact HmfR.
              --- intros m Hm. apply (match_loadable_run f vals p m Hm).
              --- apply match_loadable_mconcat1.
              --- rewrite Hcert. rewrite existsb_map_eq. reflexivity.
      * (* unrecognised head: keep r1, recurse at the stepped state *)
        remember (optimize_rules_valueset fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
        assert (Hst : forall k, n <= k ->
                  e_set (fst (snd (rule_step h r1 e p))) (setname k)
                  = e_set e (setname k))
          by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
        destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
        ++ destruct (terminal w); [reflexivity |].
           apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                    Hfresh); [| exact Hwf_tail].
           intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
        ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                    Hfresh); [| exact Hwf_tail].
           intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
Qed.

(** *** dscp (masked-value -> transformed-set). *)
Theorem optimize_rules_dscp_mut_st : forall h fuel rs n d n' d' rs' base e p,
  optimize_rules_dscp fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) rs ->
  eval_rules_mut_st h rs' e p = eval_rules_mut_st h rs e p.
Proof.
  intros h fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base e p H Hfresh Hmint Hwf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest]].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_dscp_consSS in H.
      inversion Hwf as [| ? ? Hwf1 Hwf_tail]; subst.
      destruct (head_dscp r1) as [[[[[f mask] xor] v1] body] |] eqn:Ehd.
      * destruct (take_dscp_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct (take_dscp_run_shape r1 f mask xor v1 body (r2 :: rest) vs rest' Ehd Erun)
          as [Hsplit Hwidth].
        destruct vs as [| v vs'].
        -- remember (optimize_rules_dscp fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
           assert (Hst : forall k, n <= k ->
                     e_set (fst (snd (rule_step h r1 e p))) (setname k)
                     = e_set e (setname k))
             by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
           destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
           ++ destruct (terminal w); [reflexivity |].
              apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                       Hfresh); [| exact Hwf_tail].
              intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
           ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                       Hfresh); [| exact Hwf_tail].
              intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
        -- cbv zeta in H.
           remember (optimize_rules_dscp fuel (S n)
                       {| sd_sets := (setname n, map (fun w => (w,w)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (vals := v1 :: v :: vs') in *.
           set (dn := {| sd_sets := (setname n, map (fun w => (w,w)) vals) :: sd_sets d;
                         sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
           pose proof (optimize_rules_dscp_mono fuel (S n) dn rest' m'' dd'' rr''
                         (eq_sym Erec)) as Hmono.
           assert (Hmf1 : rule_mutfree r1 = true).
           { pose proof Erun as Erun2. cbn in Erun2.
             destruct (dscp_merge_pair r1 r2) as [[[[[[fa ma] xa] va] v2] bd]|] eqn:Evm.
             - exact (dscp_merge_pair_mutfree r1 r2 _ Evm).
             - inversion Erun2. }
           assert (Hr1shell : r1 = mk_head (MMasked f CEq mask xor v1) body r1)
             by (apply head_dscp_canon; exact Ehd).
           assert (Hmf1' : rule_mutfree (mk_head (MMasked f CEq mask xor v1) body r1) = true)
             by (rewrite <- Hr1shell; exact Hmf1).
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun w => mk_head (MMasked f CEq mask xor w) body r1) vals ++ rest').
           { subst vals. cbn [map app]. f_equal; [exact Hr1shell | exact Hsplit]. }
           assert (Hlook : e_set e (setname n) = map (fun w => (w,w)) vals).
           { rewrite (Hmint n (le_n n) ltac:(lia)).
             rewrite e_set_declared.
             erewrite (optimize_rules_dscp_assoc_stable fuel (S n) dn rest'
                         m'' dd'' rr'' (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           assert (Hfx1 : field_fixed_len f = Some (Datatypes.length v1))
             by (apply (take_dscp_run_head_width r1 f mask xor v1 body r2 rest
                          (v :: vs') rest' Ehd Erun); discriminate).
           assert (Hmxw : Datatypes.length mask = Datatypes.length v1
                          /\ Datatypes.length xor = Datatypes.length v1)
             by (apply (take_dscp_run_head_widths r1 f mask xor v1 body r2 rest
                          (v :: vs') rest' Ehd Erun); discriminate).
           destruct Hmxw as [Hlmask Hlxor].
           assert (Hallw : forall w, In w vals -> field_fixed_len f = Some (Datatypes.length w)).
           { subst vals. intros w [Hw | Hw]; [ subst w; exact Hfx1 | apply (Hwidth w Hw) ]. }
           assert (Hcert : eval_matchcond (MSetT f [TBitAnd mask xor] false (setname n)) e p
                   = existsb (fun w => eval_matchcond (MMasked f CEq mask xor w) e p) vals).
           { apply (mmasked_set_existsb f mask xor vals (setname n) e p).
             - exact Hlook.
             - intros w Hw Hld.
               assert (Hfxw : field_fixed_len f = Some (Datatypes.length w)) by (apply (Hallw w Hw)).
               assert (Hfl : Datatypes.length (field_value f e p) = Datatypes.length w)
                 by (apply (field_fixed_len_loaded f (Datatypes.length w) e p Hfxw Hld)).
               assert (Hww1 : Datatypes.length w = Datatypes.length v1)
                 by (assert (Some (Datatypes.length w) = Some (Datatypes.length v1)) as Hs
                       by (rewrite <- Hfxw; exact Hfx1); injection Hs; auto).
               rewrite (data_bitops_length_eq (field_value f e p) mask xor).
               + exact Hfl.
               + lia.
               + lia. }
           assert (HmfM : forallb rule_mutfree
                     [mk_head (MSetT f [TBitAnd mask xor] false (setname n)) body r1] = true).
           { cbn [forallb].
             rewrite (rule_mutfree_mk_head_swap (MMasked f CEq mask xor v1)
                        (MSetT f [TBitAnd mask xor] false (setname n)) body r1 eq_refl Hmf1').
             reflexivity. }
           assert (HmfR : forallb rule_mutfree
                     (map (fun w => mk_head (MMasked f CEq mask xor w) body r1) vals) = true).
           { apply (forallb_mutfree_shells data (fun w => MMasked f CEq mask xor w) vals body r1
                      (MMasked f CEq mask xor v1)); [intro; reflexivity | exact Hmf1']. }
           assert (HmfMh : rule_mutfree
                     (mk_head (MSetT f [TBitAnd mask xor] false (setname n)) body r1) = true).
           { cbn [forallb] in HmfM. apply Bool.andb_true_iff in HmfM.
             exact (proj1 HmfM). }
           rewrite Hrun_eq.
           transitivity (eval_rules_mut_st h
                           (mk_head (MSetT f [TBitAnd mask xor] false (setname n)) body r1
                              :: rest') e p).
           ++ apply (eval_rules_mut_st_mutfree_cons_cong h _ rr'' rest' e p HmfMh).
              apply (IH rest' (S n) dn m'' dd'' rr'' base e p (eq_sym Erec)).
              --- intros k Hk Hin. subst dn; cbn [sd_sets map fst] in Hin.
                  destruct Hin as [Heq | Hin];
                    [ apply setname_inj in Heq; lia
                    | apply (Hfresh k); [lia | exact Hin] ].
              --- intros k Hk Hk'. apply Hmint; lia.
              --- eapply Forall_impl;
                    [ intros r Hr; apply (rule_dynset_fresh_mono n (S n) r); [lia | exact Hr] |].
                  rewrite Hsplit in Hwf_tail. apply Forall_app in Hwf_tail.
                  exact (proj2 Hwf_tail).
           ++ pose proof (eval_rules_mut_st_run_merge_abs h
                            (map (fun w => MMasked f CEq mask xor w) vals)
                            (fun q => field_loadable f q) body r1
                            (MSetT f [TBitAnd mask xor] false (setname n)) rest' e p) as Hmerge.
              rewrite List.map_map in Hmerge.
              apply Hmerge; clear Hmerge.
              --- subst vals. cbn [map]. discriminate.
              --- exact HmfMh.
              --- exact HmfR.
              --- intros m Hm. apply (match_loadable_dscp_run f mask xor vals p m Hm).
              --- apply match_loadable_msett_bitand.
              --- rewrite Hcert. rewrite existsb_map_eq. reflexivity.
      * remember (optimize_rules_dscp fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
        assert (Hst : forall k, n <= k ->
                  e_set (fst (snd (rule_step h r1 e p))) (setname k)
                  = e_set e (setname k))
          by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
        destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
        ++ destruct (terminal w); [reflexivity |].
           apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                    Hfresh); [| exact Hwf_tail].
           intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
        ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                    Hfresh); [| exact Hwf_tail].
           intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
Qed.

(** *** intervalset (range-run -> interval set). *)
Theorem optimize_rules_intervalset_mut_st : forall h fuel rs n d n' d' rs' base e p,
  optimize_rules_intervalset fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) rs ->
  eval_rules_mut_st h rs' e p = eval_rules_mut_st h rs e p.
Proof.
  intros h fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base e p H Hfresh Hmint Hwf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest]].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_intervalset_consSS in H.
      inversion Hwf as [| ? ? Hwf1 Hwf_tail]; subst.
      destruct (head_range r1) as [[[[f lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_range_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        pose proof (take_range_run_shape r1 f lo1 hi1 body (r2 :: rest) ivs rest' Ehd Erun)
          as Hsplit.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
           assert (Hst : forall k, n <= k ->
                     e_set (fst (snd (rule_step h r1 e p))) (setname k)
                     = e_set e (setname k))
             by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
           destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
           ++ destruct (terminal w); [reflexivity |].
              apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                       Hfresh); [| exact Hwf_tail].
              intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
           ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                       Hfresh); [| exact Hwf_tail].
              intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
        -- cbv zeta in H.
           remember (optimize_rules_intervalset fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (ivsAll := (lo1, hi1) :: iv :: ivs') in *.
           set (dn := {| sd_sets := (setname n, ivsAll) :: sd_sets d;
                         sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
           pose proof (optimize_rules_intervalset_mono fuel (S n) dn rest' m'' dd'' rr''
                         (eq_sym Erec)) as Hmono.
           assert (Hmf1 : rule_mutfree r1 = true).
           { pose proof Erun as Erun2. cbn in Erun2.
             destruct (range_merge_pair r1 r2) as [[[[fa iva] ivb] bd]|] eqn:Evm.
             - exact (range_merge_pair_mutfree r1 r2 _ Evm).
             - inversion Erun2. }
           assert (Hr1shell : r1 = mk_head (MRange f false lo1 hi1) body r1)
             by (apply head_range_canon; exact Ehd).
           assert (Hmf1' : rule_mutfree (mk_head (MRange f false lo1 hi1) body r1) = true)
             by (rewrite <- Hr1shell; exact Hmf1).
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun iv0 => mk_head (MRange f false (fst iv0) (snd iv0)) body r1)
                       ivsAll ++ rest').
           { subst ivsAll. cbn [map app fst snd]. f_equal; [exact Hr1shell | exact Hsplit]. }
           assert (Hlook : e_set e (setname n) = ivsAll).
           { rewrite (Hmint n (le_n n) ltac:(lia)).
             rewrite e_set_declared.
             erewrite (optimize_rules_intervalset_assoc_stable fuel (S n) dn rest'
                         m'' dd'' rr'' (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           assert (Hcert : eval_matchcond (MConcatSet [f] false (setname n)) e p
                   = existsb (fun iv0 =>
                                eval_matchcond (MRange f false (fst iv0) (snd iv0)) e p)
                       ivsAll).
           { apply (concat_set_ivs_existsb f ivsAll (setname n) e p). exact Hlook. }
           assert (HmfM : forallb rule_mutfree
                     [mk_head (MConcatSet [f] false (setname n)) body r1] = true).
           { cbn [forallb].
             rewrite (rule_mutfree_mk_head_swap (MRange f false lo1 hi1)
                        (MConcatSet [f] false (setname n)) body r1 eq_refl Hmf1').
             reflexivity. }
           assert (HmfR : forallb rule_mutfree
                     (map (fun iv0 => mk_head (MRange f false (fst iv0) (snd iv0)) body r1)
                        ivsAll) = true).
           { apply (forallb_mutfree_shells (data * data)
                      (fun iv0 => MRange f false (fst iv0) (snd iv0)) ivsAll body r1
                      (MRange f false lo1 hi1)); [intro; reflexivity | exact Hmf1']. }
           assert (HmfMh : rule_mutfree
                     (mk_head (MConcatSet [f] false (setname n)) body r1) = true).
           { cbn [forallb] in HmfM. apply Bool.andb_true_iff in HmfM.
             exact (proj1 HmfM). }
           rewrite Hrun_eq.
           transitivity (eval_rules_mut_st h
                           (mk_head (MConcatSet [f] false (setname n)) body r1 :: rest') e p).
           ++ apply (eval_rules_mut_st_mutfree_cons_cong h _ rr'' rest' e p HmfMh).
              apply (IH rest' (S n) dn m'' dd'' rr'' base e p (eq_sym Erec)).
              --- intros k Hk Hin. subst dn; cbn [sd_sets map fst] in Hin.
                  destruct Hin as [Heq | Hin];
                    [ apply setname_inj in Heq; lia
                    | apply (Hfresh k); [lia | exact Hin] ].
              --- intros k Hk Hk'. apply Hmint; lia.
              --- eapply Forall_impl;
                    [ intros r Hr; apply (rule_dynset_fresh_mono n (S n) r); [lia | exact Hr] |].
                  rewrite Hsplit in Hwf_tail. apply Forall_app in Hwf_tail.
                  exact (proj2 Hwf_tail).
           ++ pose proof (eval_rules_mut_st_run_merge_abs h
                            (map (fun iv0 => MRange f false (fst iv0) (snd iv0)) ivsAll)
                            (fun q => fields_loadable [f] q) body r1
                            (MConcatSet [f] false (setname n)) rest' e p) as Hmerge.
              rewrite List.map_map in Hmerge.
              apply Hmerge; clear Hmerge.
              --- subst ivsAll. cbn [map]. discriminate.
              --- exact HmfMh.
              --- exact HmfR.
              --- intros m Hm. apply (match_loadable_range_run f ivsAll p m Hm).
              --- apply match_loadable_mconcat1.
              --- rewrite Hcert. rewrite existsb_map_eq. reflexivity.
      * remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
        assert (Hst : forall k, n <= k ->
                  e_set (fst (snd (rule_step h r1 e p))) (setname k)
                  = e_set e (setname k))
          by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
        destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
        ++ destruct (terminal w); [reflexivity |].
           apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                    Hfresh); [| exact Hwf_tail].
           intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
        ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                    Hfresh); [| exact Hwf_tail].
           intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
Qed.

(** *** intervalsethostorder (transformed-range-run -> host-order interval set). *)
Theorem optimize_rules_intervalsethostorder_mut_st : forall h fuel rs n d n' d' rs' base e p,
  optimize_rules_intervalsethostorder fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) rs ->
  eval_rules_mut_st h rs' e p = eval_rules_mut_st h rs e p.
Proof.
  intros h fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base e p H Hfresh Hmint Hwf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest]].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_intervalsethostorder_consSS in H.
      inversion Hwf as [| ? ? Hwf1 Hwf_tail]; subst.
      destruct (head_ivsett r1) as [[[[[f ts] lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_ivsett_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        pose proof (take_ivsett_run_shape r1 f ts lo1 hi1 body (r2 :: rest) ivs rest'
                      Ehd Erun) as Hsplit.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
           assert (Hst : forall k, n <= k ->
                     e_set (fst (snd (rule_step h r1 e p))) (setname k)
                     = e_set e (setname k))
             by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
           destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
           ++ destruct (terminal w); [reflexivity |].
              apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                       Hfresh); [| exact Hwf_tail].
              intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
           ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                       Hfresh); [| exact Hwf_tail].
              intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
        -- cbv zeta in H.
           remember (optimize_rules_intervalsethostorder fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (ivsAll := (lo1, hi1) :: iv :: ivs') in *.
           set (dn := {| sd_sets := (setname n, ivsAll) :: sd_sets d;
                         sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
           pose proof (optimize_rules_intervalsethostorder_mono fuel (S n) dn rest'
                         m'' dd'' rr'' (eq_sym Erec)) as Hmono.
           assert (Hmf1 : rule_mutfree r1 = true).
           { pose proof Erun as Erun2. unfold take_ivsett_run in Erun2.
             rewrite Ehd in Erun2.
             destruct (take_ivsett_run_raw r1 (r2 :: rest)) as [ivs0 rest0] eqn:Eraw.
             destruct (all_disjoint ((lo1, hi1) :: ivs0)); [| inversion Erun2].
             inversion Erun2; subst ivs0 rest0.
             cbn in Eraw.
             destruct (ivsett_merge_pair r1 r2) as [[[[[fa tsa] iva] ivb] bd]|] eqn:Evm.
             - exact (ivsett_merge_pair_mutfree r1 r2 _ Evm).
             - inversion Eraw. }
           assert (Hr1shell : r1 = mk_head (MRangeT f ts false lo1 hi1) body r1)
             by (apply head_ivsett_canon; exact Ehd).
           assert (Hmf1' : rule_mutfree (mk_head (MRangeT f ts false lo1 hi1) body r1) = true)
             by (rewrite <- Hr1shell; exact Hmf1).
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun iv0 => mk_head (MRangeT f ts false (fst iv0) (snd iv0)) body r1)
                       ivsAll ++ rest').
           { subst ivsAll. cbn [map app fst snd]. f_equal; [exact Hr1shell | exact Hsplit]. }
           assert (Hlook : e_set e (setname n) = ivsAll).
           { rewrite (Hmint n (le_n n) ltac:(lia)).
             rewrite e_set_declared.
             erewrite (optimize_rules_intervalsethostorder_assoc_stable fuel (S n) dn rest'
                         m'' dd'' rr'' (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           assert (Hcert : eval_matchcond (MSetT f ts false (setname n)) e p
                   = existsb (fun iv0 =>
                                eval_matchcond (MRangeT f ts false (fst iv0) (snd iv0)) e p)
                       ivsAll).
           { apply (msett_ivs_existsb f ts ivsAll (setname n) e p). exact Hlook. }
           assert (HmfM : forallb rule_mutfree
                     [mk_head (MSetT f ts false (setname n)) body r1] = true).
           { cbn [forallb].
             rewrite (rule_mutfree_mk_head_swap (MRangeT f ts false lo1 hi1)
                        (MSetT f ts false (setname n)) body r1 eq_refl Hmf1').
             reflexivity. }
           assert (HmfR : forallb rule_mutfree
                     (map (fun iv0 => mk_head (MRangeT f ts false (fst iv0) (snd iv0)) body r1)
                        ivsAll) = true).
           { apply (forallb_mutfree_shells (data * data)
                      (fun iv0 => MRangeT f ts false (fst iv0) (snd iv0)) ivsAll body r1
                      (MRangeT f ts false lo1 hi1)); [intro; reflexivity | exact Hmf1']. }
           assert (HmfMh : rule_mutfree
                     (mk_head (MSetT f ts false (setname n)) body r1) = true).
           { cbn [forallb] in HmfM. apply Bool.andb_true_iff in HmfM.
             exact (proj1 HmfM). }
           rewrite Hrun_eq.
           transitivity (eval_rules_mut_st h
                           (mk_head (MSetT f ts false (setname n)) body r1 :: rest') e p).
           ++ apply (eval_rules_mut_st_mutfree_cons_cong h _ rr'' rest' e p HmfMh).
              apply (IH rest' (S n) dn m'' dd'' rr'' base e p (eq_sym Erec)).
              --- intros k Hk Hin. subst dn; cbn [sd_sets map fst] in Hin.
                  destruct Hin as [Heq | Hin];
                    [ apply setname_inj in Heq; lia
                    | apply (Hfresh k); [lia | exact Hin] ].
              --- intros k Hk Hk'. apply Hmint; lia.
              --- eapply Forall_impl;
                    [ intros r Hr; apply (rule_dynset_fresh_mono n (S n) r); [lia | exact Hr] |].
                  rewrite Hsplit in Hwf_tail. apply Forall_app in Hwf_tail.
                  exact (proj2 Hwf_tail).
           ++ pose proof (eval_rules_mut_st_run_merge_abs h
                            (map (fun iv0 => MRangeT f ts false (fst iv0) (snd iv0)) ivsAll)
                            (fun q => field_loadable f q) body r1
                            (MSetT f ts false (setname n)) rest' e p) as Hmerge.
              rewrite List.map_map in Hmerge.
              apply Hmerge; clear Hmerge.
              --- subst ivsAll. cbn [map]. discriminate.
              --- exact HmfMh.
              --- exact HmfR.
              --- intros m Hm. apply (match_loadable_ranget_run f ts ivsAll p m Hm).
              --- apply match_loadable_msett.
              --- rewrite Hcert. rewrite existsb_map_eq. reflexivity.
      * remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
        assert (Hst : forall k, n <= k ->
                  e_set (fst (snd (rule_step h r1 e p))) (setname k)
                  = e_set e (setname k))
          by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
        destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
        ++ destruct (terminal w); [reflexivity |].
           apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                    Hfresh); [| exact Hwf_tail].
           intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
        ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                    Hfresh); [| exact Hwf_tail].
           intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
Qed.

(** Two-level shells (guarded families): swap the INNER head of a
    [mk_head gm (BMatch m :: body) r] shell for any consumption-free match. *)
Lemma rule_mutfree_mk_head2_swap : forall gm m m' body r,
  match_consumefree m' = true ->
  rule_mutfree (mk_head gm (BMatch m :: body) r) = true ->
  rule_mutfree (mk_head gm (BMatch m' :: body) r) = true.
Proof.
  intros gm m m' body r Hm' H.
  rewrite rule_mutfree_mk_head in H |- *.
  cbn [forallb body_item_mutfree] in H |- *.
  apply Bool.andb_true_iff in H as [Hgm Htl].
  apply Bool.andb_true_iff in Htl as [Htl Hnat].
  apply Bool.andb_true_iff in Htl as [Htl Hafter].
  apply Bool.andb_true_iff in Htl as [_ Hbody].
  rewrite Hgm, Hm', Hbody, Hafter, Hnat. reflexivity.
Qed.

Lemma forallb_mutfree_shells2 : forall (A : Type) (g : A -> matchcond) gm l body r m0,
  (forall a : A, match_consumefree (g a) = true) ->
  rule_mutfree (mk_head gm (BMatch m0 :: body) r) = true ->
  forallb rule_mutfree (map (fun a => mk_head gm (BMatch (g a) :: body) r) l) = true.
Proof.
  intros A g gm l body r m0 Hg Hmf. apply forallb_forall.
  intros x Hx. apply in_map_iff in Hx as [a [Ha _]]. subst x.
  exact (rule_mutfree_mk_head2_swap gm m0 (g a) body r (Hg a) Hmf).
Qed.

(** *** intervalsetguarded (guarded range-run -> interval set). *)
Theorem optimize_rules_intervalsetguarded_mut_st : forall h fuel rs n d n' d' rs' base e p,
  optimize_rules_intervalsetguarded fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) rs ->
  eval_rules_mut_st h rs' e p = eval_rules_mut_st h rs e p.
Proof.
  intros h fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base e p H Hfresh Hmint Hwf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest]].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_intervalsetguarded_consSS in H.
      inversion Hwf as [| ? ? Hwf1 Hwf_tail]; subst.
      destruct (head_rangeGr r1) as [[[[[gm f] lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_rangeg_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        pose proof (take_rangeg_run_shape r1 gm f lo1 hi1 body (r2 :: rest) ivs rest'
                      Ehd Erun) as Hsplit.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
           assert (Hst : forall k, n <= k ->
                     e_set (fst (snd (rule_step h r1 e p))) (setname k)
                     = e_set e (setname k))
             by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
           destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
           ++ destruct (terminal w); [reflexivity |].
              apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                       Hfresh); [| exact Hwf_tail].
              intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
           ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                       Hfresh); [| exact Hwf_tail].
              intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
        -- cbv zeta in H.
           remember (optimize_rules_intervalsetguarded fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (ivsAll := (lo1, hi1) :: iv :: ivs') in *.
           set (dn := {| sd_sets := (setname n, ivsAll) :: sd_sets d;
                         sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
           pose proof (optimize_rules_intervalsetguarded_mono fuel (S n) dn rest'
                         m'' dd'' rr'' (eq_sym Erec)) as Hmono.
           assert (Hmf1 : rule_mutfree r1 = true).
           { pose proof Erun as Erun2. unfold take_rangeg_run in Erun2.
             rewrite Ehd in Erun2.
             destruct (take_rangeg_run_raw r1 (r2 :: rest)) as [ivs0 rest0] eqn:Eraw.
             destruct (all_disjoint ((lo1, hi1) :: ivs0)); [| inversion Erun2].
             inversion Erun2; subst ivs0 rest0.
             cbn in Eraw.
             destruct (range_mergeGr_pair r1 r2) as [[[[[gma fa] iva] ivb] bd]|] eqn:Evm.
             - exact (range_mergeGr_pair_mutfree r1 r2 _ Evm).
             - inversion Eraw. }
           assert (Hr1shell : r1 = orig_ruleGr f gm lo1 hi1 body r1)
             by (apply head_rangeGr_canon; exact Ehd).
           assert (Hmf1' : rule_mutfree (orig_ruleGr f gm lo1 hi1 body r1) = true)
             by (rewrite <- Hr1shell; exact Hmf1).
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun iv0 => orig_ruleGr f gm (fst iv0) (snd iv0) body r1) ivsAll
                     ++ rest').
           { subst ivsAll. cbn [map app fst snd]. f_equal; [exact Hr1shell | exact Hsplit]. }
           assert (Hlook : e_set e (setname n) = ivsAll).
           { rewrite (Hmint n (le_n n) ltac:(lia)).
             rewrite e_set_declared.
             erewrite (optimize_rules_intervalsetguarded_assoc_stable fuel (S n) dn rest'
                         m'' dd'' rr'' (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           assert (Hcert : eval_matchcond (MConcatSet [f] false (setname n)) e p
                   = existsb (fun iv0 =>
                                eval_matchcond (MRange f false (fst iv0) (snd iv0)) e p)
                       ivsAll).
           { apply (concat_set_ivs_existsb f ivsAll (setname n) e p). exact Hlook. }
           assert (HmfM : forallb rule_mutfree
                     [merged_ruleGs f gm (setname n) body r1] = true).
           { cbn [forallb]. unfold merged_ruleGs.
             unfold orig_ruleGr in Hmf1'.
             rewrite (rule_mutfree_mk_head2_swap gm (MRange f false lo1 hi1)
                        (MConcatSet [f] false (setname n)) body r1 eq_refl Hmf1').
             reflexivity. }
           assert (HmfR : forallb rule_mutfree
                     (map (fun iv0 => orig_ruleGr f gm (fst iv0) (snd iv0) body r1)
                        ivsAll) = true).
           { unfold orig_ruleGr in *.
             apply (forallb_mutfree_shells2 (data * data)
                      (fun iv0 => MRange f false (fst iv0) (snd iv0)) gm ivsAll body r1
                      (MRange f false lo1 hi1)); [intro; reflexivity | exact Hmf1']. }
           assert (HmfMh : rule_mutfree (merged_ruleGs f gm (setname n) body r1) = true).
           { exact (proj1 (forallb_forall rule_mutfree
                      [merged_ruleGs f gm (setname n) body r1]) HmfM
                      (merged_ruleGs f gm (setname n) body r1) (or_introl eq_refl)). }
           rewrite Hrun_eq.
           transitivity (eval_rules_mut_st h
                           (merged_ruleGs f gm (setname n) body r1 :: rest') e p).
           ++ apply (eval_rules_mut_st_mutfree_cons_cong h _ rr'' rest' e p HmfMh).
              apply (IH rest' (S n) dn m'' dd'' rr'' base e p (eq_sym Erec)).
              --- intros k Hk Hin. subst dn; cbn [sd_sets map fst] in Hin.
                  destruct Hin as [Heq | Hin];
                    [ apply setname_inj in Heq; lia
                    | apply (Hfresh k); [lia | exact Hin] ].
              --- intros k Hk Hk'. apply Hmint; lia.
              --- eapply Forall_impl;
                    [ intros r Hr; apply (rule_dynset_fresh_mono n (S n) r); [lia | exact Hr] |].
                  rewrite Hsplit in Hwf_tail. apply Forall_app in Hwf_tail.
                  exact (proj2 Hwf_tail).
           ++ assert (Hgm : match_consumefree gm = true).
              { apply (mk_head_mutfree_head gm
                         (BMatch (MConcatSet [f] false (setname n)) :: body) r1). exact HmfMh. }
              refine (eval_rules_mut_st_run_collapse h
                        ivsAll
                        (fun iv0 => orig_ruleGr f gm (fst iv0) (snd iv0) body r1)
                        (fun iv0 => eval_matchcond (MRange f false (fst iv0) (snd iv0)) e p)
                        (eval_matchcond gm e p) (fst (rule_step h (mk_tail body r1) e p))
                        (merged_ruleGs f gm (setname n) body r1) rest' e p
                        _ HmfR HmfMh _ _).
              --- subst ivsAll. cbn [map]. discriminate.
              --- intros iv0 Hin. unfold orig_ruleGr.
                  rewrite (rule_step_fst_mk_head h gm _ r1 e p Hgm), mk_tail_cons.
                  rewrite (rule_step_fst_mk_head h (MRange f false (fst iv0) (snd iv0))
                             body r1 e p eq_refl).
                  rewrite if_and_nest. reflexivity.
              --- unfold merged_ruleGs.
                  rewrite (rule_step_fst_mk_head h gm _ r1 e p Hgm), mk_tail_cons.
                  rewrite (rule_step_fst_mk_head h (MConcatSet [f] false (setname n))
                             body r1 e p eq_refl).
                  rewrite if_and_nest, Hcert. reflexivity.
      * remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
        assert (Hst : forall k, n <= k ->
                  e_set (fst (snd (rule_step h r1 e p))) (setname k)
                  = e_set e (setname k))
          by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
        destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
        ++ destruct (terminal w); [reflexivity |].
           apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                    Hfresh); [| exact Hwf_tail].
           intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
        ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                    Hfresh); [| exact Hwf_tail].
           intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
Qed.

(** *** mixedpointrangeguarded (guarded point+range run -> interval set). *)
Theorem optimize_rules_mixedpointrangeguarded_mut_st : forall h fuel rs n d n' d' rs' base e p,
  optimize_rules_mixedpointrangeguarded fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) rs ->
  eval_rules_mut_st h rs' e p = eval_rules_mut_st h rs e p.
Proof.
  intros h fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base e p H Hfresh Hmint Hwf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest]].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_mixedpointrangeguarded_consSS in H.
      inversion Hwf as [| ? ? Hwf1 Hwf_tail]; subst.
      destruct (head_mixGm r1) as [[[[gm f] e1] body] |] eqn:Ehd.
      * destruct (take_mix_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        pose proof (take_mix_run_shape r1 gm f e1 body (r2 :: rest) es rest' Ehd Erun)
          as Hsplit.
        destruct es as [| el es'].
        -- remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
           assert (Hst : forall k, n <= k ->
                     e_set (fst (snd (rule_step h r1 e p))) (setname k)
                     = e_set e (setname k))
             by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
           destruct (rule_step h r1 e p) as [[w|] [e1' p1]]; cbn [fst snd] in Hst.
           ++ destruct (terminal w); [reflexivity |].
              apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1' p1 (eq_sym Erec)
                       Hfresh); [| exact Hwf_tail].
              intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
           ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1' p1 (eq_sym Erec)
                       Hfresh); [| exact Hwf_tail].
              intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
        -- cbv zeta in H.
           remember (optimize_rules_mixedpointrangeguarded fuel (S n)
                       {| sd_sets := (setname n, map melem_iv (e1 :: el :: es')) :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (esAll := e1 :: el :: es') in *.
           set (dn := {| sd_sets := (setname n, map melem_iv esAll) :: sd_sets d;
                         sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
           pose proof (optimize_rules_mixedpointrangeguarded_mono fuel (S n) dn rest'
                         m'' dd'' rr'' (eq_sym Erec)) as Hmono.
           assert (Hok_all : forall e0, In e0 esAll -> melem_ok f e0 = true).
           { intros e0 He0.
             pose proof (take_mix_run_melem_ok r1 gm f e1 body (r2 :: rest)
                           (el :: es') rest' Ehd Erun ltac:(discriminate)) as Hforall.
             rewrite forallb_forall in Hforall. apply (Hforall e0). exact He0. }
           assert (Hmf1 : rule_mutfree r1 = true).
           { pose proof Erun as Erun2. unfold take_mix_run in Erun2.
             rewrite Ehd in Erun2.
             destruct (take_mix_run_raw r1 (r2 :: rest)) as [es0 rest0] eqn:Eraw.
             destruct (forallb (melem_ok f) (e1 :: es0)
                       && all_disjoint (map melem_iv (e1 :: es0))); [| inversion Erun2].
             inversion Erun2; subst es0 rest0.
             cbn in Eraw.
             destruct (mix_mergeGm_pair r1 r2) as [[[[[gma fa] ea] eb] bd]|] eqn:Evm.
             - exact (mix_mergeGm_pair_mutfree r1 r2 _ Evm).
             - inversion Eraw. }
           assert (Hr1shell : r1 = orig_ruleGm f gm e1 body r1)
             by (apply head_mixGm_canon; exact Ehd).
           assert (Hmf1' : rule_mutfree (orig_ruleGm f gm e1 body r1) = true)
             by (rewrite <- Hr1shell; exact Hmf1).
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun e0 => orig_ruleGm f gm e0 body r1) esAll ++ rest').
           { subst esAll. cbn [map app]. f_equal; [exact Hr1shell | exact Hsplit]. }
           assert (Hlook : e_set e (setname n) = map melem_iv esAll).
           { rewrite (Hmint n (le_n n) ltac:(lia)).
             rewrite e_set_declared.
             erewrite (optimize_rules_mixedpointrangeguarded_assoc_stable fuel (S n) dn rest'
                         m'' dd'' rr'' (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           assert (Hcert : eval_matchcond (MConcatSet [f] false (setname n)) e p
                   = existsb (fun iv0 =>
                                eval_matchcond (MRange f false (fst iv0) (snd iv0)) e p)
                       (map melem_iv esAll)).
           { apply (concat_set_ivs_existsb f (map melem_iv esAll) (setname n) e p).
             exact Hlook. }
           assert (HmfM : forallb rule_mutfree
                     [merged_ruleGs f gm (setname n) body r1] = true).
           { cbn [forallb]. unfold merged_ruleGs.
             unfold orig_ruleGm in Hmf1'. cbn [melem_mc] in Hmf1'.
             rewrite (rule_mutfree_mk_head2_swap gm (melem_mc f e1)
                        (MConcatSet [f] false (setname n)) body r1 eq_refl
                        ltac:(destruct e1; exact Hmf1')).
             reflexivity. }
           assert (HmfR : forallb rule_mutfree
                     (map (fun e0 => orig_ruleGm f gm e0 body r1) esAll) = true).
           { unfold orig_ruleGm in *.
             apply (forallb_mutfree_shells2 melem
                      (fun e0 => melem_mc f e0) gm esAll body r1 (melem_mc f e1));
               [intro a; destruct a; reflexivity | destruct e1; exact Hmf1']. }
           assert (HmfMh : rule_mutfree (merged_ruleGs f gm (setname n) body r1) = true).
           { exact (proj1 (forallb_forall rule_mutfree
                      [merged_ruleGs f gm (setname n) body r1]) HmfM
                      (merged_ruleGs f gm (setname n) body r1) (or_introl eq_refl)). }
           rewrite Hrun_eq.
           transitivity (eval_rules_mut_st h
                           (merged_ruleGs f gm (setname n) body r1 :: rest') e p).
           ++ apply (eval_rules_mut_st_mutfree_cons_cong h _ rr'' rest' e p HmfMh).
              apply (IH rest' (S n) dn m'' dd'' rr'' base e p (eq_sym Erec)).
              --- intros k Hk Hin. subst dn; cbn [sd_sets map fst] in Hin.
                  destruct Hin as [Heq | Hin];
                    [ apply setname_inj in Heq; lia
                    | apply (Hfresh k); [lia | exact Hin] ].
              --- intros k Hk Hk'. apply Hmint; lia.
              --- eapply Forall_impl;
                    [ intros r Hr; apply (rule_dynset_fresh_mono n (S n) r); [lia | exact Hr] |].
                  rewrite Hsplit in Hwf_tail. apply Forall_app in Hwf_tail.
                  exact (proj2 Hwf_tail).
           ++ assert (Hgm : match_consumefree gm = true).
              { apply (mk_head_mutfree_head gm
                         (BMatch (MConcatSet [f] false (setname n)) :: body) r1). exact HmfMh. }
              refine (eval_rules_mut_st_run_collapse h
                        esAll
                        (fun e0 => orig_ruleGm f gm e0 body r1)
                        (fun e0 => eval_matchcond (melem_mc f e0) e p)
                        (eval_matchcond gm e p) (fst (rule_step h (mk_tail body r1) e p))
                        (merged_ruleGs f gm (setname n) body r1) rest' e p
                        _ HmfR HmfMh _ _).
              --- subst esAll. cbn [map]. discriminate.
              --- intros e0 Hin. unfold orig_ruleGm.
                  assert (Hmm : match_consumefree (melem_mc f e0) = true)
                    by (destruct e0; reflexivity).
                  rewrite (rule_step_fst_mk_head h gm _ r1 e p Hgm), mk_tail_cons.
                  rewrite (rule_step_fst_mk_head h (melem_mc f e0) body r1 e p Hmm).
                  rewrite if_and_nest. reflexivity.
              --- unfold merged_ruleGs.
                  rewrite (rule_step_fst_mk_head h gm _ r1 e p Hgm), mk_tail_cons.
                  rewrite (rule_step_fst_mk_head h (MConcatSet [f] false (setname n))
                             body r1 e p eq_refl).
                  rewrite if_and_nest, Hcert, existsb_map_eq.
                  rewrite (existsb_ext _
                             (fun e0 => eval_matchcond
                                          (MRange f false (fst (melem_iv e0)) (snd (melem_iv e0))) e p)
                             (fun e0 => eval_matchcond (melem_mc f e0) e p) esAll
                             (fun e0 He0 => eq_sym (eval_melem_mrange f e0 e p (Hok_all e0 He0)))).
                  reflexivity.
      * remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
        assert (Hst : forall k, n <= k ->
                  e_set (fst (snd (rule_step h r1 e p))) (setname k)
                  = e_set e (setname k))
          by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
        destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
        ++ destruct (terminal w); [reflexivity |].
           apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                    Hfresh); [| exact Hwf_tail].
           intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
        ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                    Hfresh); [| exact Hwf_tail].
           intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
Qed.

(** Compositional [rule_mutfree] intro/elim for arbitrary shell shapes. *)
Lemma rule_mutfree_mk_head_intro : forall m body r,
  match_consumefree m = true ->
  forallb body_item_mutfree body = true ->
  forallb (fun s => negb (is_mut_stmt s)) (r_after r) = true ->
  rule_natfree r = true ->
  rule_mutfree (mk_head m body r) = true.
Proof.
  intros m body r Hm Hb Ha Hn. rewrite rule_mutfree_mk_head.
  rewrite Hm, Hb, Ha, Hn. reflexivity.
Qed.

Lemma rule_mutfree_mk_head_elim : forall m body r,
  rule_mutfree (mk_head m body r) = true ->
  forallb body_item_mutfree body = true
  /\ forallb (fun s => negb (is_mut_stmt s)) (r_after r) = true
  /\ rule_natfree r = true.
Proof.
  intros m body r H. rewrite rule_mutfree_mk_head in H.
  apply Bool.andb_true_iff in H as [_ H].
  apply Bool.andb_true_iff in H as [H Hn].
  apply Bool.andb_true_iff in H as [Hb Ha].
  auto.
Qed.

Lemma forallb_bim_cons_bmatch : forall m body,
  forallb body_item_mutfree (BMatch m :: body)
  = match_consumefree m && forallb body_item_mutfree body.
Proof. reflexivity. Qed.

(** *** concat (two-selector tuple-run -> concat set). *)
Theorem optimize_rules_concat_mut_st : forall h fuel rs n d n' d' rs' base e p,
  optimize_rules_concat fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) rs ->
  eval_rules_mut_st h rs' e p = eval_rules_mut_st h rs e p.
Proof.
  intros h fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base e p H Hfresh Hmint Hwf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest]].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_concat_consSS in H.
      inversion Hwf as [| ? ? Hwf1 Hwf_tail]; subst.
      destruct (head_value2 r1) as [[[[[f1 a1] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concat_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct (take_concat_run_shape r1 f1 a1 f2 b1 body (r2 :: rest) ts rest' Ehd Erun)
          as [Hsplit [HwA HwB]].
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concat fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
           assert (Hst : forall k, n <= k ->
                     e_set (fst (snd (rule_step h r1 e p))) (setname k)
                     = e_set e (setname k))
             by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
           destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
           ++ destruct (terminal w); [reflexivity |].
              apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                       Hfresh); [| exact Hwf_tail].
              intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
           ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                       Hfresh); [| exact Hwf_tail].
              intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
        -- cbv zeta in H.
           remember (optimize_rules_concat fuel (S n)
                       {| sd_sets := (setname n, map pack_tuple ((a1,b1) :: t :: ts'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (tuples := (a1, b1) :: t :: ts') in *.
           set (dn := {| sd_sets := (setname n, map pack_tuple tuples) :: sd_sets d;
                         sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
           pose proof (optimize_rules_concat_mono fuel (S n) dn rest' m'' dd'' rr''
                         (eq_sym Erec)) as Hmono.
           assert (Hmf1 : rule_mutfree r1 = true).
           { pose proof Erun as Erun2. cbn in Erun2.
             destruct (concat_merge_pair r1 r2)
               as [[[[[[[fa ga] aa] ba] a2] b2] bd]|] eqn:Evm.
             - exact (concat_merge_pair_mutfree r1 r2 _ Evm).
             - inversion Erun2. }
           assert (Hr1shell : r1 = orig_rule2 f1 f2 a1 b1 body r1)
             by (apply head_value2_canon; exact Ehd).
           (* decompose the shared tail's mut-freedom *)
           assert (Hparts : forallb body_item_mutfree body = true
                            /\ forallb (fun s => negb (is_mut_stmt s)) (r_after r1) = true
                            /\ rule_natfree r1 = true).
           { rewrite Hr1shell in Hmf1. unfold orig_rule2 in Hmf1.
             destruct (rule_mutfree_mk_head_elim _ _ _ Hmf1) as [Hb [Ha Hn2]].
             rewrite forallb_bim_cons_bmatch in Hb.
             apply Bool.andb_true_iff in Hb as [_ Hb].
             unfold mk_head in Ha, Hn2; cbn [r_after] in Ha;
               unfold rule_natfree, r_nat in Hn2 |- *; cbn [r_outcome] in Hn2.
             auto. }
           destruct Hparts as [Hbody_mf [Hafter_mf Hnat_mf]].
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun ab => orig_rule2 f1 f2 (fst ab) (snd ab) body r1) tuples
                     ++ rest').
           { subst tuples. cbn [map app fst snd]. f_equal; [exact Hr1shell | exact Hsplit]. }
           assert (Hlook : e_set e (setname n) = map pack_tuple tuples).
           { rewrite (Hmint n (le_n n) ltac:(lia)).
             rewrite e_set_declared.
             erewrite (optimize_rules_concat_assoc_stable fuel (S n) dn rest'
                         m'' dd'' rr'' (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           assert (Hcert : eval_matchcond (MConcatSet [f1; f2] false (setname n)) e p
                   = existsb (fun ab => andb (eval_matchcond (MCmp f1 CEq (fst ab)) e p)
                                             (eval_matchcond (MCmp f2 CEq (snd ab)) e p))
                             tuples).
           { apply (concat_two_fields_certificate_N f1 f2 tuples (setname n) e p).
             - exact Hlook.
             - intros a b Hin Hld.
               assert (Hfx : field_fixed_len f1 = Some (Datatypes.length a)).
               { destruct (take_concat_run_head_width r1 f1 a1 f2 b1 body r2 rest
                             (t :: ts') rest' Ehd Erun ltac:(discriminate)) as [Hh1 _].
                 subst tuples. destruct Hin as [Hab | Hin].
                 - injection Hab as -> ->. exact Hh1.
                 - apply (HwA a b Hin). }
               apply (field_fixed_len_loaded f1 (Datatypes.length a) e p Hfx Hld).
             - intros a b Hin Hld.
               assert (Hfx : field_fixed_len f2 = Some (Datatypes.length b)).
               { destruct (take_concat_run_head_width r1 f1 a1 f2 b1 body r2 rest
                             (t :: ts') rest' Ehd Erun ltac:(discriminate)) as [_ Hh2].
                 subst tuples. destruct Hin as [Hab | Hin].
                 - injection Hab as -> ->. exact Hh2.
                 - apply (HwB a b Hin). }
               apply (field_fixed_len_loaded f2 (Datatypes.length b) e p Hfx Hld). }
           assert (HmfM : forallb rule_mutfree
                     [merged_rule2 f1 f2 (setname n) body r1] = true).
           { cbn [forallb]. unfold merged_rule2.
             rewrite (rule_mutfree_mk_head_intro (MConcatSet [f1; f2] false (setname n))
                        body r1 eq_refl Hbody_mf Hafter_mf Hnat_mf).
             reflexivity. }
           assert (HmfR : forallb rule_mutfree
                     (map (fun ab => orig_rule2 f1 f2 (fst ab) (snd ab) body r1)
                        tuples) = true).
           { apply forallb_forall. intros x Hx.
             apply in_map_iff in Hx as [ab [Hab _]]. subst x. unfold orig_rule2.
             apply rule_mutfree_mk_head_intro;
               [ reflexivity
               | rewrite forallb_bim_cons_bmatch; cbn [match_consumefree];
                 exact Hbody_mf
               | exact Hafter_mf | exact Hnat_mf ]. }
           assert (HmfMh : rule_mutfree (merged_rule2 f1 f2 (setname n) body r1) = true).
           { exact (proj1 (forallb_forall rule_mutfree
                      [merged_rule2 f1 f2 (setname n) body r1]) HmfM
                      (merged_rule2 f1 f2 (setname n) body r1) (or_introl eq_refl)). }
           rewrite Hrun_eq.
           transitivity (eval_rules_mut_st h
                           (merged_rule2 f1 f2 (setname n) body r1 :: rest') e p).
           ++ apply (eval_rules_mut_st_mutfree_cons_cong h _ rr'' rest' e p HmfMh).
              apply (IH rest' (S n) dn m'' dd'' rr'' base e p (eq_sym Erec)).
              --- intros k Hk Hin. subst dn; cbn [sd_sets map fst] in Hin.
                  destruct Hin as [Heq | Hin];
                    [ apply setname_inj in Heq; lia
                    | apply (Hfresh k); [lia | exact Hin] ].
              --- intros k Hk Hk'. apply Hmint; lia.
              --- eapply Forall_impl;
                    [ intros r Hr; apply (rule_dynset_fresh_mono n (S n) r); [lia | exact Hr] |].
                  rewrite Hsplit in Hwf_tail. apply Forall_app in Hwf_tail.
                  exact (proj2 Hwf_tail).
           ++ refine (eval_rules_mut_st_run_collapse h
                        tuples
                        (fun ab => orig_rule2 f1 f2 (fst ab) (snd ab) body r1)
                        (fun ab => eval_matchcond (MCmp f1 CEq (fst ab)) e p
                                   && eval_matchcond (MCmp f2 CEq (snd ab)) e p)
                        true (fst (rule_step h (mk_tail body r1) e p))
                        (merged_rule2 f1 f2 (setname n) body r1) rest' e p
                        _ HmfR HmfMh _ _).
              --- subst tuples. cbn [map]. discriminate.
              --- intros ab Hin. unfold orig_rule2.
                  rewrite (rule_step_fst_mk_head h (MCmp f1 CEq (fst ab)) _ r1 e p eq_refl).
                  rewrite mk_tail_cons.
                  rewrite (rule_step_fst_mk_head h (MCmp f2 CEq (snd ab)) body r1 e p eq_refl).
                  rewrite if_and_nest, Bool.andb_true_l. reflexivity.
              --- unfold merged_rule2.
                  rewrite (rule_step_fst_mk_head h (MConcatSet [f1; f2] false (setname n))
                             body r1 e p eq_refl).
                  rewrite Hcert, Bool.andb_true_l. reflexivity.
      * remember (optimize_rules_concat fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
        assert (Hst : forall k, n <= k ->
                  e_set (fst (snd (rule_step h r1 e p))) (setname k)
                  = e_set e (setname k))
          by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
        destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
        ++ destruct (terminal w); [reflexivity |].
           apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                    Hfresh); [| exact Hwf_tail].
           intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
        ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                    Hfresh); [| exact Hwf_tail].
           intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
Qed.

(** *** concatguarded (guarded two-selector tuple-run -> concat set). *)
Theorem optimize_rules_concatguarded_mut_st : forall h fuel rs n d n' d' rs' base e p,
  optimize_rules_concatguarded fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) rs ->
  eval_rules_mut_st h rs' e p = eval_rules_mut_st h rs e p.
Proof.
  intros h fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base e p H Hfresh Hmint Hwf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest]].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_concatguarded_consSS in H.
      inversion Hwf as [| ? ? Hwf1 Hwf_tail]; subst.
      destruct (head_value2g r1) as [[[[[[f1 a1] gm] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concatg_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct (take_concatg_run_shape r1 f1 a1 gm f2 b1 body (r2 :: rest) ts rest'
                    Ehd Erun) as [Hsplit [HwA HwB]].
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concatguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
           assert (Hst : forall k, n <= k ->
                     e_set (fst (snd (rule_step h r1 e p))) (setname k)
                     = e_set e (setname k))
             by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
           destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
           ++ destruct (terminal w); [reflexivity |].
              apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                       Hfresh); [| exact Hwf_tail].
              intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
           ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                       Hfresh); [| exact Hwf_tail].
              intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
        -- cbv zeta in H.
           remember (optimize_rules_concatguarded fuel (S n)
                       {| sd_sets := (setname n, map pack_tuple ((a1,b1) :: t :: ts'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (tuples := (a1, b1) :: t :: ts') in *.
           set (dn := {| sd_sets := (setname n, map pack_tuple tuples) :: sd_sets d;
                         sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
           pose proof (optimize_rules_concatguarded_mono fuel (S n) dn rest' m'' dd'' rr''
                         (eq_sym Erec)) as Hmono.
           assert (Hmf1 : rule_mutfree r1 = true).
           { pose proof Erun as Erun2. cbn in Erun2.
             destruct (concat_mergeg_pair r1 r2)
               as [[[[[[[[fa ga] gma] aa] ba] a2] b2] bd]|] eqn:Evm.
             - exact (concat_mergeg_pair_mutfree r1 r2 _ Evm).
             - inversion Erun2. }
           assert (Hr1shell : r1 = orig_rule2g f1 f2 gm a1 b1 body r1)
             by (apply head_value2g_canon; exact Ehd).
           assert (Hparts : match_consumefree gm = true
                            /\ forallb body_item_mutfree body = true
                            /\ forallb (fun s => negb (is_mut_stmt s)) (r_after r1) = true
                            /\ rule_natfree r1 = true).
           { rewrite Hr1shell in Hmf1. unfold orig_rule2g in Hmf1.
             destruct (rule_mutfree_mk_head_elim _ _ _ Hmf1) as [Hb [Ha Hn2]].
             rewrite forallb_bim_cons_bmatch in Hb.
             apply Bool.andb_true_iff in Hb as [Hgm Hb].
             rewrite forallb_bim_cons_bmatch in Hb.
             apply Bool.andb_true_iff in Hb as [_ Hb].
             unfold mk_head in Ha, Hn2; cbn [r_after] in Ha;
               unfold rule_natfree, r_nat in Hn2 |- *; cbn [r_outcome] in Hn2.
             auto. }
           destruct Hparts as [Hgm_cf [Hbody_mf [Hafter_mf Hnat_mf]]].
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun ab => orig_rule2g f1 f2 gm (fst ab) (snd ab) body r1) tuples
                     ++ rest').
           { subst tuples. cbn [map app fst snd]. f_equal; [exact Hr1shell | exact Hsplit]. }
           assert (Hlook : e_set e (setname n) = map pack_tuple tuples).
           { rewrite (Hmint n (le_n n) ltac:(lia)).
             rewrite e_set_declared.
             erewrite (optimize_rules_concatguarded_assoc_stable fuel (S n) dn rest'
                         m'' dd'' rr'' (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           assert (Hcert : eval_matchcond (MConcatSet [f1; f2] false (setname n)) e p
                   = existsb (fun ab => andb (eval_matchcond (MCmp f1 CEq (fst ab)) e p)
                                             (eval_matchcond (MCmp f2 CEq (snd ab)) e p))
                             tuples).
           { apply (concat_two_fields_certificate_N f1 f2 tuples (setname n) e p).
             - exact Hlook.
             - intros a b Hin Hld.
               assert (Hfx : field_fixed_len f1 = Some (Datatypes.length a)).
               { destruct (take_concatg_run_head_width r1 f1 a1 gm f2 b1 body r2 rest
                             (t :: ts') rest' Ehd Erun ltac:(discriminate)) as [Hh1 _].
                 subst tuples. destruct Hin as [Hab | Hin].
                 - injection Hab as -> ->. exact Hh1.
                 - apply (HwA a b Hin). }
               apply (field_fixed_len_loaded f1 (Datatypes.length a) e p Hfx Hld).
             - intros a b Hin Hld.
               assert (Hfx : field_fixed_len f2 = Some (Datatypes.length b)).
               { destruct (take_concatg_run_head_width r1 f1 a1 gm f2 b1 body r2 rest
                             (t :: ts') rest' Ehd Erun ltac:(discriminate)) as [_ Hh2].
                 subst tuples. destruct Hin as [Hab | Hin].
                 - injection Hab as -> ->. exact Hh2.
                 - apply (HwB a b Hin). }
               apply (field_fixed_len_loaded f2 (Datatypes.length b) e p Hfx Hld). }
           assert (HmfM : forallb rule_mutfree
                     [merged_rule2g f1 f2 gm (setname n) body r1] = true).
           { cbn [forallb]. unfold merged_rule2g.
             rewrite (rule_mutfree_mk_head_intro gm
                        (BMatch (MConcatSet [f1; f2] false (setname n)) :: body) r1 Hgm_cf
                        ltac:(rewrite forallb_bim_cons_bmatch; cbn [match_consumefree];
                              exact Hbody_mf)
                        Hafter_mf Hnat_mf).
             reflexivity. }
           assert (HmfR : forallb rule_mutfree
                     (map (fun ab => orig_rule2g f1 f2 gm (fst ab) (snd ab) body r1)
                        tuples) = true).
           { apply forallb_forall. intros x Hx.
             apply in_map_iff in Hx as [ab [Hab _]]. subst x. unfold orig_rule2g.
             apply rule_mutfree_mk_head_intro;
               [ reflexivity
               | rewrite forallb_bim_cons_bmatch; rewrite Hgm_cf;
                 rewrite forallb_bim_cons_bmatch; cbn [match_consumefree];
                 exact Hbody_mf
               | exact Hafter_mf | exact Hnat_mf ]. }
           assert (HmfMh : rule_mutfree (merged_rule2g f1 f2 gm (setname n) body r1) = true).
           { exact (proj1 (forallb_forall rule_mutfree
                      [merged_rule2g f1 f2 gm (setname n) body r1]) HmfM
                      (merged_rule2g f1 f2 gm (setname n) body r1) (or_introl eq_refl)). }
           rewrite Hrun_eq.
           transitivity (eval_rules_mut_st h
                           (merged_rule2g f1 f2 gm (setname n) body r1 :: rest') e p).
           ++ apply (eval_rules_mut_st_mutfree_cons_cong h _ rr'' rest' e p HmfMh).
              apply (IH rest' (S n) dn m'' dd'' rr'' base e p (eq_sym Erec)).
              --- intros k Hk Hin. subst dn; cbn [sd_sets map fst] in Hin.
                  destruct Hin as [Heq | Hin];
                    [ apply setname_inj in Heq; lia
                    | apply (Hfresh k); [lia | exact Hin] ].
              --- intros k Hk Hk'. apply Hmint; lia.
              --- eapply Forall_impl;
                    [ intros r Hr; apply (rule_dynset_fresh_mono n (S n) r); [lia | exact Hr] |].
                  rewrite Hsplit in Hwf_tail. apply Forall_app in Hwf_tail.
                  exact (proj2 Hwf_tail).
           ++ assert (Hgm : match_consumefree gm = true).
              { apply (mk_head_mutfree_head gm
                         (BMatch (MConcatSet [f1; f2] false (setname n)) :: body) r1).
                exact HmfMh. }
              refine (eval_rules_mut_st_run_collapse h
                        tuples
                        (fun ab => orig_rule2g f1 f2 gm (fst ab) (snd ab) body r1)
                        (fun ab => eval_matchcond (MCmp f1 CEq (fst ab)) e p
                                   && eval_matchcond (MCmp f2 CEq (snd ab)) e p)
                        (eval_matchcond gm e p) (fst (rule_step h (mk_tail body r1) e p))
                        (merged_rule2g f1 f2 gm (setname n) body r1) rest' e p
                        _ HmfR HmfMh _ _).
              --- subst tuples. cbn [map]. discriminate.
              --- intros ab Hin. unfold orig_rule2g.
                  rewrite (rule_step_fst_mk_head h (MCmp f1 CEq (fst ab)) _ r1 e p eq_refl),
                          mk_tail_cons.
                  rewrite (rule_step_fst_mk_head h gm _ r1 e p Hgm), mk_tail_cons.
                  rewrite (rule_step_fst_mk_head h (MCmp f2 CEq (snd ab)) body r1 e p eq_refl).
                  destruct (eval_matchcond (MCmp f1 CEq (fst ab)) e p);
                    destruct (eval_matchcond gm e p);
                    destruct (eval_matchcond (MCmp f2 CEq (snd ab)) e p); reflexivity.
              --- unfold merged_rule2g.
                  rewrite (rule_step_fst_mk_head h gm _ r1 e p Hgm), mk_tail_cons.
                  rewrite (rule_step_fst_mk_head h (MConcatSet [f1; f2] false (setname n))
                             body r1 e p eq_refl).
                  rewrite if_and_nest, Hcert. reflexivity.
      * remember (optimize_rules_concatguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
        assert (Hst : forall k, n <= k ->
                  e_set (fst (snd (rule_step h r1 e p))) (setname k)
                  = e_set e (setname k))
          by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
        destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
        ++ destruct (terminal w); [reflexivity |].
           apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                    Hfresh); [| exact Hwf_tail].
           intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
        ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                    Hfresh); [| exact Hwf_tail].
           intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
Qed.

(** *** setguarded (guarded single-field value-run -> set). *)
Theorem optimize_rules_setguarded_mut_st : forall h fuel rs n d n' d' rs' base e p,
  optimize_rules_setguarded fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) rs ->
  eval_rules_mut_st h rs' e p = eval_rules_mut_st h rs e p.
Proof.
  intros h fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base e p H Hfresh Hmint Hwf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest]].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_setguarded_consSS in H.
      inversion Hwf as [| ? ? Hwf1 Hwf_tail]; subst.
      destruct (head_valueGs r1) as [[[[gm f] v1] body] |] eqn:Ehd.
      * destruct (take_setg_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct (take_setg_run_shape r1 gm f v1 body (r2 :: rest) vs rest' Ehd Erun)
          as [Hsplit Hall].
        destruct vs as [| v0 vs'].
        -- remember (optimize_rules_setguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
           assert (Hst : forall k, n <= k ->
                     e_set (fst (snd (rule_step h r1 e p))) (setname k)
                     = e_set e (setname k))
             by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
           destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
           ++ destruct (terminal w); [reflexivity |].
              apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                       Hfresh); [| exact Hwf_tail].
              intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
           ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                       Hfresh); [| exact Hwf_tail].
              intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
        -- cbv zeta in H.
           remember (optimize_rules_setguarded fuel (S n)
                       {| sd_sets := (setname n, map (fun v => (v, v)) (v1 :: v0 :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (vals := v1 :: v0 :: vs') in *.
           set (dn := {| sd_sets := (setname n, map (fun v => (v, v)) vals) :: sd_sets d;
                         sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
           pose proof (optimize_rules_setguarded_mono fuel (S n) dn rest' m'' dd'' rr''
                         (eq_sym Erec)) as Hmono.
           assert (Hmf1 : rule_mutfree r1 = true).
           { pose proof Erun as Erun2. cbn in Erun2.
             destruct (value_mergeGs_pair r1 r2)
               as [[[[[gma fa] va] v2] bd]|] eqn:Evm.
             - exact (value_mergeGs_pair_mutfree r1 r2 _ Evm).
             - inversion Erun2. }
           assert (Hr1shell : r1 = orig_ruleGs f gm v1 body r1)
             by (apply head_valueGs_canon; exact Ehd).
           assert (Hmf1' : rule_mutfree (orig_ruleGs f gm v1 body r1) = true)
             by (rewrite <- Hr1shell; exact Hmf1).
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun v => orig_ruleGs f gm v body r1) vals ++ rest').
           { subst vals. cbn [map app]. f_equal; [exact Hr1shell | exact Hsplit]. }
           assert (Hlook : e_set e (setname n) = map (fun v => (v, v)) vals).
           { rewrite (Hmint n (le_n n) ltac:(lia)).
             rewrite e_set_declared.
             erewrite (optimize_rules_setguarded_assoc_stable fuel (S n) dn rest'
                         m'' dd'' rr'' (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           assert (Hcert : eval_matchcond (MConcatSet [f] false (setname n)) e p
                   = existsb (fun v => eval_matchcond (MCmp f CEq v) e p) vals).
           { apply (concat_set_existsb f vals (setname n) e p).
             - exact Hlook.
             - intros v Hin Hld.
               assert (Hfx : field_fixed_len f = Some (Datatypes.length v)).
               { subst vals. destruct Hin as [Hv | Hin].
                 - subst v. apply (take_setg_run_head_width r1 gm f v1 body r2 rest
                                     (v0 :: vs') rest' Ehd Erun ltac:(discriminate)).
                 - apply (Hall v Hin). }
               apply (field_fixed_len_loaded f (Datatypes.length v) e p Hfx Hld). }
           assert (HmfM : forallb rule_mutfree
                     [merged_ruleGs f gm (setname n) body r1] = true).
           { cbn [forallb]. unfold merged_ruleGs.
             unfold orig_ruleGs in Hmf1'.
             rewrite (rule_mutfree_mk_head2_swap gm (MCmp f CEq v1)
                        (MConcatSet [f] false (setname n)) body r1 eq_refl Hmf1').
             reflexivity. }
           assert (HmfR : forallb rule_mutfree
                     (map (fun v => orig_ruleGs f gm v body r1) vals) = true).
           { unfold orig_ruleGs in *.
             apply (forallb_mutfree_shells2 data
                      (fun v => MCmp f CEq v) gm vals body r1 (MCmp f CEq v1));
               [intro; reflexivity | exact Hmf1']. }
           assert (HmfMh : rule_mutfree (merged_ruleGs f gm (setname n) body r1) = true).
           { exact (proj1 (forallb_forall rule_mutfree
                      [merged_ruleGs f gm (setname n) body r1]) HmfM
                      (merged_ruleGs f gm (setname n) body r1) (or_introl eq_refl)). }
           rewrite Hrun_eq.
           transitivity (eval_rules_mut_st h
                           (merged_ruleGs f gm (setname n) body r1 :: rest') e p).
           ++ apply (eval_rules_mut_st_mutfree_cons_cong h _ rr'' rest' e p HmfMh).
              apply (IH rest' (S n) dn m'' dd'' rr'' base e p (eq_sym Erec)).
              --- intros k Hk Hin. subst dn; cbn [sd_sets map fst] in Hin.
                  destruct Hin as [Heq | Hin];
                    [ apply setname_inj in Heq; lia
                    | apply (Hfresh k); [lia | exact Hin] ].
              --- intros k Hk Hk'. apply Hmint; lia.
              --- eapply Forall_impl;
                    [ intros r Hr; apply (rule_dynset_fresh_mono n (S n) r); [lia | exact Hr] |].
                  rewrite Hsplit in Hwf_tail. apply Forall_app in Hwf_tail.
                  exact (proj2 Hwf_tail).
           ++ assert (Hgm : match_consumefree gm = true).
              { apply (mk_head_mutfree_head gm
                         (BMatch (MConcatSet [f] false (setname n)) :: body) r1). exact HmfMh. }
              refine (eval_rules_mut_st_run_collapse h
                        vals
                        (fun v => orig_ruleGs f gm v body r1)
                        (fun v => eval_matchcond (MCmp f CEq v) e p)
                        (eval_matchcond gm e p) (fst (rule_step h (mk_tail body r1) e p))
                        (merged_ruleGs f gm (setname n) body r1) rest' e p
                        _ HmfR HmfMh _ _).
              --- subst vals. cbn [map]. discriminate.
              --- intros v Hin. unfold orig_ruleGs.
                  rewrite (rule_step_fst_mk_head h gm _ r1 e p Hgm), mk_tail_cons.
                  rewrite (rule_step_fst_mk_head h (MCmp f CEq v) body r1 e p eq_refl).
                  rewrite if_and_nest. reflexivity.
              --- unfold merged_ruleGs.
                  rewrite (rule_step_fst_mk_head h gm _ r1 e p Hgm), mk_tail_cons.
                  rewrite (rule_step_fst_mk_head h (MConcatSet [f] false (setname n))
                             body r1 e p eq_refl).
                  rewrite if_and_nest, Hcert. reflexivity.
      * remember (optimize_rules_setguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
        assert (Hst : forall k, n <= k ->
                  e_set (fst (snd (rule_step h r1 e p))) (setname k)
                  = e_set e (setname k))
          by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
        destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
        ++ destruct (terminal w); [reflexivity |].
           apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                    Hfresh); [| exact Hwf_tail].
           intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
        ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec)
                    Hfresh); [| exact Hwf_tail].
           intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
Qed.

(** K-field shells: the [kmatches] prefix is all pure [MCmp] heads. *)
Lemma forallb_bim_kmatches : forall fields row,
  forallb body_item_mutfree (kmatches fields row) = true.
Proof.
  intros fields row. unfold kmatches. apply forallb_forall.
  intros x Hx. apply in_map_iff in Hx as [fa [Hfa _]]. subst x. reflexivity.
Qed.

Lemma rule_mutfree_orig_ruleK_intro : forall fields row body r1,
  forallb body_item_mutfree body = true ->
  forallb (fun s => negb (is_mut_stmt s)) (r_after r1) = true ->
  rule_natfree r1 = true ->
  rule_mutfree (orig_ruleK fields row body r1) = true.
Proof.
  intros fields row body r1 Hb Ha Hn.
  unfold rule_mutfree, orig_ruleK, rule_natfree, r_nat in *.
  cbn [r_body r_after r_outcome].
  rewrite forallb_app, forallb_bim_kmatches, Hb, Ha. cbn [andb].
  destruct (r_outcome r1); cbn in Hn |- *; congruence.
Qed.

Lemma rule_mutfree_orig_ruleK_elim : forall fields row body r1,
  rule_mutfree (orig_ruleK fields row body r1) = true ->
  forallb body_item_mutfree body = true
  /\ forallb (fun s => negb (is_mut_stmt s)) (r_after r1) = true
  /\ rule_natfree r1 = true.
Proof.
  intros fields row body r1 H.
  unfold rule_mutfree, orig_ruleK, rule_natfree, r_nat in *.
  cbn [r_body r_after r_outcome] in H.
  rewrite forallb_app in H.
  apply Bool.andb_true_iff in H as [H Hn].
  apply Bool.andb_true_iff in H as [H Ha].
  apply Bool.andb_true_iff in H as [_ Hb].
  auto.
Qed.

(** The K-field concat merge over the state fold: the merged [MConcatSet] rule
    replaces the whole write-free run of per-row shells (sharing loadability and
    fired verdict, differing only in their per-row key match).  The [MConcatSet]
    membership certificate [concat_fields_certificate_N] supplies the [existsb]
    the collapse's merged-shell disjunction consumes. *)
Lemma eval_rules_concat_mergeK : forall (h : hook_id) fields rows name body r1 rest e p,
  fields <> [] -> rows <> [] ->
  e_set e name = map pack_row rows ->
  (forall row, In row rows ->
     Forall2 (fun f a => field_fixed_len f = Some (Datatypes.length a)) fields row) ->
  forallb rule_mutfree (map (fun row => orig_ruleK fields row body r1) rows) = true ->
  rule_mutfree (merged_ruleK fields name body r1) = true ->
  eval_rules_mut_st h (merged_ruleK fields name body r1 :: rest) e p
  = eval_rules_mut_st h (map (fun row => orig_ruleK fields row body r1) rows ++ rest) e p.
Proof.
  intros h fields rows name body r1 rest e p Hfne Hrne Hset Hwf Hmfrun Hmfm.
  assert (Hlenrow : forall row, In row rows ->
                    Datatypes.length fields = Datatypes.length row)
    by (intros row Hin; apply (Forall2_length (Hwf row Hin))).
  refine (eval_rules_mut_st_run_collapse h
            rows
            (fun row => orig_ruleK fields row body r1)
            (fun row => forallb (fun fa => eval_matchcond (MCmp (fst fa) CEq (snd fa)) e p)
                                (combine fields row))
            true (fst (rule_step h (mk_tail body r1) e p))
            (merged_ruleK fields name body r1) rest e p
            Hrne Hmfrun Hmfm _ _).
  - intros row Hin.
    rewrite rule_step_fst_kmatches, Bool.andb_true_l. reflexivity.
  - unfold merged_ruleK.
    rewrite (rule_step_fst_mk_head h (MConcatSet fields false name) body r1 e p eq_refl).
    rewrite (concat_fields_certificate_N fields rows name e p Hfne Hset Hwf), Bool.andb_true_l.
    reflexivity.
Qed.

(** *** concatmulti (K>=3-field pairwise concat merge). *)
Theorem optimize_rules_concatmulti_mut_st : forall h rs n d n' d' rs' base e p,
  optimize_rules_concatmulti n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) rs ->
  eval_rules_mut_st h rs' e p = eval_rules_mut_st h rs e p.
Proof.
  intros h rs.
  induction rs as [rs IHrs] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' base e p H Hfresh Hmint Hwf.
  destruct rs as [| r1 [| r2 rest]].
  - cbn in H. inversion H; subst; reflexivity.
  - cbn in H. inversion H; subst; reflexivity.
  - rewrite optimize_rules_concatmulti_cons2 in H.
    inversion Hwf as [| ? ? Hwf1 Hwf2]; subst.
    inversion Hwf2 as [| ? ? Hwf2' Hwf_rest]; subst.
    destruct (concat_mergeK_pair r1 r2) as [[[[fields row1] row2] body] |] eqn:Em.
    + cbv zeta in H.
      destruct (concat_mergeK_pair_shape r1 r2 fields row1 row2 body Em)
        as [Hr1eq [Hr2eq [Hwk1 [Hwk2 [Hfne _]]]]].
      set (dn := {| sd_sets := (setname n, map pack_row [row1; row2]) :: sd_sets d;
                    sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
      remember (optimize_rules_concatmulti (S n) dn rest) as tt eqn:Erec.
      destruct tt as [[m'' dd''] rr'']. injection H as Hn' Hd' Hr'. subst n' d' rs'.
      pose proof (optimize_rules_concatmulti_mono rest (S n) dn m'' dd'' rr''
                    (eq_sym Erec)) as Hmono.
      assert (Hmf1 : rule_mutfree r1 = true)
        by (exact (concat_mergeK_pair_mutfree r1 r2 _ Em)).
      assert (Hparts : forallb body_item_mutfree body = true
                       /\ forallb (fun s => negb (is_mut_stmt s)) (r_after r1) = true
                       /\ rule_natfree r1 = true).
      { rewrite Hr1eq in Hmf1. exact (rule_mutfree_orig_ruleK_elim _ _ _ _ Hmf1). }
      destruct Hparts as [Hbody_mf [Hafter_mf Hnat_mf]].
      assert (Hlook : e_set e (setname n) = map pack_row [row1; row2]).
      { rewrite (Hmint n (le_n n) ltac:(lia)).
        rewrite e_set_declared.
        erewrite (optimize_rules_concatmulti_assoc_stable rest (S n) dn m'' dd'' rr''
                    (setname n) _ (eq_sym Erec)).
        - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
        - intros k Hk Heq. apply setname_inj in Heq. lia. }
      assert (HmfM : forallb rule_mutfree
                [merged_ruleK fields (setname n) body r1] = true).
      { cbn [forallb]. unfold merged_ruleK.
        rewrite (rule_mutfree_mk_head_intro (MConcatSet fields false (setname n))
                   body r1 eq_refl Hbody_mf Hafter_mf Hnat_mf).
        reflexivity. }
      assert (HmfR : forallb rule_mutfree [r1; r2] = true).
      { cbn [forallb]. rewrite Hr1eq at 1. rewrite Hr2eq.
        rewrite (rule_mutfree_orig_ruleK_intro fields row1 body r1
                   Hbody_mf Hafter_mf Hnat_mf).
        rewrite (rule_mutfree_orig_ruleK_intro fields row2 body r1
                   Hbody_mf Hafter_mf Hnat_mf).
        reflexivity. }
      assert (HmfMh : rule_mutfree (merged_ruleK fields (setname n) body r1) = true).
      { exact (proj1 (forallb_forall rule_mutfree
                 [merged_ruleK fields (setname n) body r1]) HmfM
                 (merged_ruleK fields (setname n) body r1) (or_introl eq_refl)). }
      transitivity (eval_rules_mut_st h
                      (merged_ruleK fields (setname n) body r1 :: rest) e p).
      * apply (eval_rules_mut_st_mutfree_cons_cong h _ rr'' rest e p HmfMh).
        apply (IHrs rest ltac:(unfold ltof; cbn; lia) (S n) dn m'' dd'' rr'' base e p
                 (eq_sym Erec)).
        -- intros k Hk Hin. subst dn; cbn [sd_sets map fst] in Hin.
           destruct Hin as [Heq | Hin];
             [ apply setname_inj in Heq; lia
             | apply (Hfresh k); [lia | exact Hin] ].
        -- intros k Hk Hk'. apply Hmint; lia.
        -- eapply Forall_impl;
             [ intros r Hr; apply (rule_dynset_fresh_mono n (S n) r); [lia | exact Hr]
             | exact Hwf_rest ].
      * rewrite (eval_rules_concat_mergeK h fields [row1; row2] (setname n) body r1 rest e p
                   Hfne ltac:(discriminate) Hlook
                   ltac:(intros row Hin; destruct Hin as [<-|[<-|[]]]; assumption)
                   ltac:(cbn [map]; rewrite <- Hr1eq, <- Hr2eq; exact HmfR) HmfMh).
        cbn [map]. rewrite <- Hr1eq, <- Hr2eq. reflexivity.
    + remember (optimize_rules_concatmulti n d (r2 :: rest)) as tt eqn:Erec.
      destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as Hn' Hd' Hr'. subst n' d' rs'.
      rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
      assert (Hst : forall k, n <= k ->
                e_set (fst (snd (rule_step h r1 e p))) (setname k)
                = e_set e (setname k))
        by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
      destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
      * destruct (terminal w); [reflexivity |].
        apply (IHrs (r2 :: rest) ltac:(unfold ltof; cbn; lia) n d m'' dd'' rr''
                 base e1 p1 (eq_sym Erec) Hfresh);
          [| constructor; assumption].
        intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
      * apply (IHrs (r2 :: rest) ltac:(unfold ltof; cbn; lia) n d m'' dd'' rr''
                 base e1 p1 (eq_sym Erec) Hfresh);
          [| constructor; assumption].
        intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
Qed.

(** vmap-family shells. *)
Lemma rule_mutfree_orig_rule_intro : forall f v body w,
  forallb body_item_mutfree body = true ->
  rule_mutfree (orig_rule f v body w) = true.
Proof.
  intros f v body w Hb. unfold orig_rule.
  apply rule_mutfree_mk_head_intro; [reflexivity | exact Hb | reflexivity | reflexivity].
Qed.

Lemma rule_mutfree_orig_rule_elim : forall f v body w,
  rule_mutfree (orig_rule f v body w) = true ->
  forallb body_item_mutfree body = true.
Proof.
  intros f v body w H. unfold orig_rule in H.
  exact (proj1 (rule_mutfree_mk_head_elim _ _ _ H)).
Qed.

Lemma rule_mutfree_mk_vmap_rule : forall f nm body,
  forallb body_item_mutfree body = true ->
  rule_mutfree (mk_vmap_rule f nm body) = true.
Proof.
  intros f nm body Hb.
  unfold rule_mutfree, mk_vmap_rule, rule_natfree, r_nat.
  cbn [r_body r_after r_outcome forallb]. rewrite Hb. reflexivity.
Qed.

(** The vmap driver's counter is monotone (the only stage missing this lemma). *)
Lemma optimize_rules_vmap_mono : forall fuel n d rs n' d' rs',
  optimize_rules_vmap fuel n d rs = (n', d', rs') -> n <= n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst. lia.
  - destruct rs as [| r1 [| r2 rest]]; try (cbn in H; inversion H; subst; lia).
    rewrite optimize_rules_vmap_consSS in H.
    destruct (head_value r1) as [[[f v1] body]|].
    + destruct (take_vmap_run r1 (r2 :: rest)) as [es rest'].
      destruct es as [| e0 es'].
      * destruct (optimize_rules_vmap fuel n d (r2 :: rest))
          as [[m'' dd''] rr''] eqn:Erec.
        cbv zeta in H. inversion H; subst. exact (IH _ _ _ _ _ _ Erec).
      * destruct (has_distinct_verdict (r_verdict r1) (e0 :: es') && body_vmap_safe body).
        -- cbv zeta in H.
           destruct (optimize_rules_vmap fuel (S n) _ rest')
             as [[m'' dd''] rr''] eqn:Erec.
           inversion H; subst.
           pose proof (IH _ _ _ _ _ _ Erec). lia.
        -- destruct (optimize_rules_vmap fuel n d (r2 :: rest))
             as [[m'' dd''] rr''] eqn:Erec.
           cbv zeta in H. inversion H; subst. exact (IH _ _ _ _ _ _ Erec).
    + destruct (optimize_rules_vmap fuel n d (r2 :: rest))
        as [[m'' dd''] rr''] eqn:Erec.
      cbv zeta in H. inversion H; subst. exact (IH _ _ _ _ _ _ Erec).
Qed.

(** The merged vmap rule's step, read off the fold's own [body_step]/[end_step]
    (no pure-strand detour): the body walk decides whether the rule is reached, and
    on a completed walk the vmap-keyed [end_step] returns the point map's
    [first_match] (or nothing when the key field does not load).  On a mut-free
    synproxy-free body the walk is [BRdone e p] or [BRbreak e p]. *)
Lemma fst_step_vmap_merged : forall (h : hook_id) f nm es body e p,
  e_vmap e nm = map vmap_pt es ->
  (forall v w, In (v, w) es -> field_fixed_len f = Some (Datatypes.length v)) ->
  body_has_synproxy body = false ->
  forallb body_item_mutfree body = true ->
  fst (rule_step h (mk_vmap_rule f nm body) e p)
  = match body_step body e p with
    | BRdone _ _ => if field_loadable f p then first_match f e p es else None
    | _ => None
    end.
Proof.
  intros h f nm es body e p Hvm Hfx Hns Hbody_mf.
  pose proof (body_has_synproxy_false_stops body p Hns) as Hsp.
  unfold rule_step, mk_vmap_rule. cbn [r_body].
  pose proof (body_step_mutfree_synfree body e p Hsp Hbody_mf) as HBS.
  destruct (body_step body e p) as [eb pb | eb pb | eb pb] eqn:EBS; cbn [fst].
  - reflexivity.
  -     destruct HBS as [HB | HB]; discriminate HB.
  -     destruct HBS as [HB | HB]; [discriminate HB |].
    injection HB as Heb Hpb. subst eb pb.
    unfold end_step. cbn [r_vmap vm_keyf vm_name vm_fields r_outcome].
    cbn [vmap_loadable vm_keyf].
    destruct (field_loadable f p) eqn:Hfld; cbn [fst]; [| reflexivity].
    cbn [apply_transforms fold_left]. rewrite Hvm.
    rewrite (assoc_verdict_points es f e p
               ltac:(intros v w Hin Hld;
                     apply (field_fixed_len_loaded f (Datatypes.length v) e p
                              (Hfx v w Hin) Hld)) Hfld).
    destruct (first_match f e p es) eqn:Efm; cbn [fst]; [reflexivity |].
    unfold terminal_step.
    cbn [has_effect_terminal r_nat r_tproxy r_fwd r_queue r_verdict r_after r_outcome].
    reflexivity.
Qed.

(** Each original vmap shell's step: the head [MCmp f CEq v] gates the SAME body
    walk, which on completion yields the terminal verdict [w]. *)
Lemma fst_step_vmap_orig : forall (h : hook_id) f v body w e p,
  body_has_synproxy body = false ->
  forallb body_item_mutfree body = true ->
  terminal w = true ->
  fst (rule_step h (orig_rule f v body w) e p)
  = if eval_matchcond (MCmp f CEq v) e p
    then match body_step body e p with BRdone _ _ => Some w | _ => None end
    else None.
Proof.
  intros h f v body w e p Hns Hbody_mf Hw.
  pose proof (body_has_synproxy_false_stops body p Hns) as Hsp.
  unfold rule_step, orig_rule, mk_head. cbn [r_body].
  cbn [body_step].
  rewrite (match_consume_free_id (MCmp f CEq v) e p eq_refl).
  destruct (eval_matchcond (MCmp f CEq v) e p) eqn:Ev; [| reflexivity].
  pose proof (body_step_mutfree_synfree body e p Hsp Hbody_mf) as HBS.
  destruct (body_step body e p) as [eb pb | eb pb | eb pb] eqn:EBS; cbn [fst].
  - reflexivity.
  -     destruct HBS as [HB | HB]; discriminate HB.
  -     destruct HBS as [HB | HB]; [discriminate HB |].
    injection HB as Heb Hpb. subst eb pb.
    unfold end_step, mk_vmap_base. cbn [r_vmap r_outcome].
    unfold terminal_step.
    cbn [has_effect_terminal r_nat r_tproxy r_fwd r_queue r_verdict r_after r_outcome].
    destruct w; cbn [terminal] in Hw; try discriminate Hw; reflexivity.
Qed.

(** The N-way vmap collapse over the STATE fold: a run of same-field, same-body
    shells with DISTINCT terminal verdicts and keys — whose merged vmap [nm]
    carries the N point entries — collapses to ONE [mk_vmap_rule].  Because the
    per-entry verdicts DIFFER this is not a shared-[O] merge; it is the vmap's own
    first-match scan, replayed rule-by-rule over the pinned state (the state fold
    and the vmap lookup scan the same keys in the same order).  All shells are
    mut-free, so the state stays at [(e, p)]. *)
Lemma eval_rules_mut_st_vmap_mergeN : forall (h : hook_id) f nm es body rest e p,
  e_vmap e nm = map vmap_pt es ->
  (forall v w, In (v, w) es -> field_fixed_len f = Some (Datatypes.length v)) ->
  (forall v w, In (v, w) es -> terminal w = true) ->
  body_has_synproxy body = false ->
  body_has_notrack body = false ->
  forallb body_item_mutfree body = true ->
  eval_rules_mut_st h (mk_vmap_rule f nm body :: rest) e p
  = eval_rules_mut_st h (map (fun vw => orig_rule f (fst vw) body (snd vw)) es ++ rest) e p.
Proof.
  intros h f nm es body rest e p Hvm Hfx Hterm Hns Hnt Hbody_mf.
  assert (Hmfo : forall v w, rule_mutfree (orig_rule f v body w) = true)
    by (intros; apply rule_mutfree_orig_rule_intro; exact Hbody_mf).
  rewrite (eval_rules_mut_st_mutfree_cons h (mk_vmap_rule f nm body) rest e p
             (rule_mutfree_mk_vmap_rule f nm body Hbody_mf)).
  rewrite (fst_step_vmap_merged h f nm es body e p Hvm Hfx Hns Hbody_mf). clear Hvm Hnt.
  destruct (body_step body e p) as [eb pb | eb pb | eb pb] eqn:EBS.
  1,2: (* body walk BREAKs / STEALs: the merged step is [None], and every shell
          (its head gates the SAME broken walk) also steps to [None] — so both the
          merged rule and the run fall through to [rest]. *)
      revert Hfx Hterm;
      induction es as [| [v w] es IH]; intros Hfx Hterm; cbn [map app];
        [reflexivity |];
      rewrite (eval_rules_mut_st_mutfree_cons h (orig_rule f v body w) _ e p (Hmfo v w)),
              (fst_step_vmap_orig h f v body w e p Hns Hbody_mf (Hterm v w (or_introl eq_refl))),
              EBS;
      destruct (eval_matchcond (MCmp f CEq v) e p);
        (apply IH; [ intros v' w' Hin; apply (Hfx v' w'); right; exact Hin
                   | intros v' w' Hin; apply (Hterm v' w'); right; exact Hin ]).
  - (* body walk completes: the merged rule's step is the vmap key scan
       ([first_match]); the run scans the SAME keys in the same order. *)
    destruct (field_loadable f p) eqn:Hfld.
    + revert Hfx Hterm.
      induction es as [| [v w] es IH]; intros Hfx Hterm;
        cbn [map app first_match]; [reflexivity |].
      rewrite (eval_rules_mut_st_mutfree_cons h (orig_rule f v body w) _ e p (Hmfo v w)),
              (fst_step_vmap_orig h f v body w e p Hns Hbody_mf
                 (Hterm v w (or_introl eq_refl))), EBS.
      assert (Hm : eval_matchcond (MCmp f CEq v) e p = eval_cmp CEq (field_value f e p) v).
      { unfold eval_matchcond, eval_matchcond_body. cbn [match_loadable].
        rewrite Hfld. reflexivity. }
      rewrite Hm.
      destruct (eval_cmp CEq (field_value f e p) v) eqn:Ev.
      * rewrite (Hterm v w (or_introl eq_refl)). reflexivity.
      * apply IH; [ intros v' w' Hin; apply (Hfx v' w'); right; exact Hin
                  | intros v' w' Hin; apply (Hterm v' w'); right; exact Hin ].
    + revert Hfx Hterm.
      induction es as [| [v w] es IH]; intros Hfx Hterm; cbn [map app]; [reflexivity |].
      rewrite (eval_rules_mut_st_mutfree_cons h (orig_rule f v body w) _ e p (Hmfo v w)),
              (fst_step_vmap_orig h f v body w e p Hns Hbody_mf
                 (Hterm v w (or_introl eq_refl))), EBS.
      assert (Hm : eval_matchcond (MCmp f CEq v) e p = false).
      { unfold eval_matchcond. cbn [match_loadable]. rewrite Hfld. reflexivity. }
      rewrite Hm.
      apply IH; [ intros v' w' Hin; apply (Hfx v' w'); right; exact Hin
                | intros v' w' Hin; apply (Hterm v' w'); right; exact Hin ].
Qed.

(** *** vmap (value+verdict run -> verdict map).  The minted namespace is
    [e_vmap], which NO evaluator write ever touches ([Semantics.rule_step_vmap])
    — so no write-freshness side condition is needed at all. *)
Theorem optimize_rules_vmap_mut_st : forall h fuel rs n d n' d' rs' base e p,
  optimize_rules_vmap fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  (forall k, n <= k -> k < n' ->
     e_vmap e (vmapname k) = e_vmap (env_with_sets base d') (vmapname k)) ->
  eval_rules_mut_st h rs' e p = eval_rules_mut_st h rs e p.
Proof.
  intros h fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base e p H Hfresh Hmint.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest]].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_vmap_consSS in H.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_vmap_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct (take_vmap_run_shape r1 f v1 body (r2 :: rest) es rest' Ehd Erun)
          as [Hsplit [HwK HwT]].
        destruct es as [| e0 es'].
        -- remember (optimize_rules_vmap fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
           pose proof (rule_step_vmap h r1 e p) as Hst.
           destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
           ++ destruct (terminal w); [reflexivity |].
              apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec) Hfresh).
              intros k Hk Hk'. rewrite Hst. apply Hmint; assumption.
           ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec) Hfresh).
              intros k Hk Hk'. rewrite Hst. apply Hmint; assumption.
        -- destruct (take_vmap_run_head r1 f v1 body r2 rest (e0 :: es') rest' Ehd Erun
                       ltac:(discriminate)) as [Hr1eq [HwK1 HwT1]].
           destruct (has_distinct_verdict (r_verdict r1) (e0 :: es') && body_vmap_safe body)
             eqn:Hdv.
           2:{ remember (optimize_rules_vmap fuel n d (r2 :: rest)) as tt eqn:Erec.
               destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
               injection H as Hn' Hd' Hr'. subst n' d' rs'.
               rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
               pose proof (rule_step_vmap h r1 e p) as Hst.
               destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
               - destruct (terminal w); [reflexivity |].
                 apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec) Hfresh).
                 intros k Hk Hk'. rewrite Hst. apply Hmint; assumption.
               - apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec) Hfresh).
                 intros k Hk Hk'. rewrite Hst. apply Hmint; assumption. }
           apply Bool.andb_true_iff in Hdv as [_ Hsafe].
           apply Bool.andb_true_iff in Hsafe as [Hns Hnt].
           apply Bool.negb_true_iff in Hns. apply Bool.negb_true_iff in Hnt.
           cbv zeta in H.
           remember (optimize_rules_vmap fuel (S n)
                       {| sd_sets := sd_sets d;
                          sd_vmaps := (vmapname n,
                            map vmap_pt ((v1, r_verdict r1) :: e0 :: es')) :: sd_vmaps d;
                          sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (entries := (v1, r_verdict r1) :: e0 :: es') in *.
           set (dn := {| sd_sets := sd_sets d;
                         sd_vmaps := (vmapname n, map vmap_pt entries) :: sd_vmaps d;
                         sd_maps := sd_maps d |}) in *.
           pose proof (optimize_rules_vmap_mono fuel (S n) dn rest' m'' dd'' rr''
                         (eq_sym Erec)) as Hmono.
           assert (Hmf1 : rule_mutfree r1 = true).
           { pose proof Erun as Erun2. cbn in Erun2.
             destruct (vmap_run_pair r1 r2) as [[[[fa v2] w2] bd]|] eqn:Evm.
             - exact (vmap_run_pair_mutfree r1 r2 _ Evm).
             - inversion Erun2. }
           assert (Hbody_mf : forallb body_item_mutfree body = true).
           { rewrite Hr1eq in Hmf1. exact (rule_mutfree_orig_rule_elim _ _ _ _ Hmf1). }
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun vw => orig_rule f (fst vw) body (snd vw)) entries ++ rest').
           { subst entries. cbn [map app fst snd]. f_equal; [exact Hr1eq | exact Hsplit]. }
           assert (Hlook : e_vmap e (vmapname n) = map vmap_pt entries).
           { rewrite (Hmint n (le_n n) ltac:(lia)).
             rewrite e_vmap_env_with_sets.
             erewrite (optimize_rules_vmap_assoc_stable fuel (S n) dn rest'
                         m'' dd'' rr'' (vmapname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_vmaps assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply vmapname_inj in Heq. lia. }
           assert (Hmfm : rule_mutfree (mk_vmap_rule f (vmapname n) body) = true)
             by (apply rule_mutfree_mk_vmap_rule; exact Hbody_mf).
           rewrite Hrun_eq.
           transitivity (eval_rules_mut_st h
                           (mk_vmap_rule f (vmapname n) body :: rest') e p).
           ++ apply (eval_rules_mut_st_mutfree_cons_cong h _ rr'' rest' e p Hmfm).
              apply (IH rest' (S n) dn m'' dd'' rr'' base e p (eq_sym Erec)).
              --- intros k Hk Hin. subst dn; cbn [sd_vmaps map fst] in Hin.
                  destruct Hin as [Heq | Hin];
                    [ apply vmapname_inj in Heq; lia
                    | apply (Hfresh k); [lia | exact Hin] ].
              --- intros k Hk Hk'. apply Hmint; lia.
           ++ apply (eval_rules_mut_st_vmap_mergeN h f (vmapname n) entries body rest' e p
                       Hlook
                       ltac:(intros v w Hin; subst entries;
                             destruct Hin as [Hvw | Hin];
                             [ inversion Hvw; subst; exact HwK1 | apply (HwK v w Hin) ])
                       ltac:(intros v w Hin; subst entries;
                             destruct Hin as [Hvw | Hin];
                             [ inversion Hvw; subst; exact HwT1 | apply (HwT v w Hin) ])
                       Hns Hnt Hbody_mf).
      * remember (optimize_rules_vmap fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
        pose proof (rule_step_vmap h r1 e p) as Hst.
        destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
        ++ destruct (terminal w); [reflexivity |].
           apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec) Hfresh).
           intros k Hk Hk'. rewrite Hst. apply Hmint; assumption.
        ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec) Hfresh).
           intros k Hk Hk'. rewrite Hst. apply Hmint; assumption.
Qed.

(** The guarded N-way vmap collapse over the state fold: identical to the plain
    one but with a SHARED head guard [gm].  A guarded shell is the plain shell over
    the guard-prepended body [BMatch gm :: body] ([orig_ruleGv_eq_swap] at the
    step level), so the guarded merge is the plain merge on that body, its run
    swapped rule-for-rule via [eval_rules_mut_st_map_cong]. *)
Lemma eval_rules_mut_st_vmap_mergeNg : forall (h : hook_id) f gm nm es body rest e p,
  e_vmap e nm = map vmap_pt es ->
  (forall v w, In (v, w) es -> field_fixed_len f = Some (Datatypes.length v)) ->
  (forall v w, In (v, w) es -> terminal w = true) ->
  body_has_synproxy body = false ->
  body_has_notrack body = false ->
  match_consumefree gm = true ->
  forallb body_item_mutfree body = true ->
  eval_rules_mut_st h (merged_ruleGv f gm nm body :: rest) e p
  = eval_rules_mut_st h (map (fun vw => orig_ruleGv f gm (fst vw) body (snd vw)) es ++ rest) e p.
Proof.
  intros h f gm nm es body rest e p Hvm Hfx Hterm Hns Hnt Hgm Hbody_mf.
  assert (HbodyG : forallb body_item_mutfree (BMatch gm :: body) = true)
    by (cbn [forallb body_item_mutfree]; rewrite Hgm; exact Hbody_mf).
  assert (HmfGv : forall v w, rule_mutfree (orig_ruleGv f gm v body w) = true).
  { intros v w. unfold orig_ruleGv, orig_ruleGs.
    apply rule_mutfree_mk_head_intro;
      [ exact Hgm
      | rewrite forallb_bim_cons_bmatch; cbn [match_consumefree]; exact Hbody_mf
      | reflexivity | reflexivity ]. }
  assert (HmfSw : forall v w, rule_mutfree (orig_rule f v (BMatch gm :: body) w) = true)
    by (intros; apply rule_mutfree_orig_rule_intro; exact HbodyG).
  unfold merged_ruleGv.
  rewrite (eval_rules_mut_st_map_cong h
             (fun vw => orig_ruleGv f gm (fst vw) body (snd vw))
             (fun vw => orig_rule f (fst vw) (BMatch gm :: body) (snd vw))
             es rest e p
             (fun vw _ => HmfGv (fst vw) (snd vw))
             (fun vw _ => HmfSw (fst vw) (snd vw))).
  - apply (eval_rules_mut_st_vmap_mergeN h f nm es (BMatch gm :: body) rest e p Hvm Hfx Hterm
             ltac:(unfold body_has_synproxy; cbn [existsb]; exact Hns)
             ltac:(unfold body_has_notrack; cbn [existsb]; exact Hnt)
             HbodyG).
  - intros vw _.
    assert (Hgmsw : match_consumefree gm = true).
    { apply (mk_head_mutfree_head gm (BMatch (MCmp f CEq (fst vw)) :: body)
               (mk_vmap_base (snd vw))). exact (HmfGv (fst vw) (snd vw)). }
    unfold orig_ruleGv, orig_ruleGs, orig_rule.
    exact (rule_step_fst_swap_head h gm (MCmp f CEq (fst vw)) body
             (mk_vmap_base (snd vw)) e p Hgmsw eq_refl).
Qed.

(** *** vmapguarded (guarded value+verdict run -> verdict map). *)
Theorem optimize_rules_vmapguarded_mut_st : forall h fuel rs n d n' d' rs' base e p,
  optimize_rules_vmapguarded fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  (forall k, n <= k -> k < n' ->
     e_vmap e (vmapname k) = e_vmap (env_with_sets base d') (vmapname k)) ->
  eval_rules_mut_st h rs' e p = eval_rules_mut_st h rs e p.
Proof.
  intros h fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base e p H Hfresh Hmint.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest]].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_vmapguarded_consSS in H.
      destruct (head_valueGs r1) as [[[[gm f] v1] body] |] eqn:Ehd.
      * destruct (take_vmapG_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct (take_vmapG_run_shape r1 gm f v1 body (r2 :: rest) es rest' Ehd Erun)
          as [Hsplit [HwK HwT]].
        destruct es as [| e0 es'].
        -- remember (optimize_rules_vmapguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
           pose proof (rule_step_vmap h r1 e p) as Hst.
           destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
           ++ destruct (terminal w); [reflexivity |].
              apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec) Hfresh).
              intros k Hk Hk'. rewrite Hst. apply Hmint; assumption.
           ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec) Hfresh).
              intros k Hk Hk'. rewrite Hst. apply Hmint; assumption.
        -- destruct (take_vmapG_run_head r1 gm f v1 body r2 rest (e0 :: es') rest' Ehd Erun
                       ltac:(discriminate)) as [Hr1eq [HwK1 HwT1]].
           destruct (has_distinct_verdict (r_verdict r1) (e0 :: es') && body_vmap_safe body)
             eqn:Hdv.
           2:{ remember (optimize_rules_vmapguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
               destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
               injection H as Hn' Hd' Hr'. subst n' d' rs'.
               rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
               pose proof (rule_step_vmap h r1 e p) as Hst.
               destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
               - destruct (terminal w); [reflexivity |].
                 apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec) Hfresh).
                 intros k Hk Hk'. rewrite Hst. apply Hmint; assumption.
               - apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec) Hfresh).
                 intros k Hk Hk'. rewrite Hst. apply Hmint; assumption. }
           apply Bool.andb_true_iff in Hdv as [_ Hsafe].
           apply Bool.andb_true_iff in Hsafe as [Hns Hnt].
           apply Bool.negb_true_iff in Hns. apply Bool.negb_true_iff in Hnt.
           cbv zeta in H.
           remember (optimize_rules_vmapguarded fuel (S n)
                       {| sd_sets := sd_sets d;
                          sd_vmaps := (vmapname n,
                            map vmap_pt ((v1, r_verdict r1) :: e0 :: es')) :: sd_vmaps d;
                          sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (entries := (v1, r_verdict r1) :: e0 :: es') in *.
           set (dn := {| sd_sets := sd_sets d;
                         sd_vmaps := (vmapname n, map vmap_pt entries) :: sd_vmaps d;
                         sd_maps := sd_maps d |}) in *.
           pose proof (optimize_rules_vmapguarded_mono fuel (S n) dn rest' m'' dd'' rr''
                         (eq_sym Erec)) as Hmono.
           assert (Hmf1 : rule_mutfree r1 = true).
           { pose proof Erun as Erun2. cbn in Erun2.
             destruct (vmap_run_pairG r1 r2) as [[[[[gma fa] v2] w2] bd]|] eqn:Evm.
             - exact (vmap_run_pairG_mutfree r1 r2 _ Evm).
             - inversion Erun2. }
           assert (Hparts : match_consumefree gm = true
                            /\ forallb body_item_mutfree body = true).
           { rewrite Hr1eq in Hmf1. unfold orig_ruleGv, orig_ruleGs in Hmf1.
             rewrite rule_mutfree_mk_head in Hmf1.
             apply Bool.andb_true_iff in Hmf1 as [Hgm Htl].
             apply Bool.andb_true_iff in Htl as [Htl _].
             apply Bool.andb_true_iff in Htl as [Htl _].
             rewrite forallb_bim_cons_bmatch in Htl.
             apply Bool.andb_true_iff in Htl as [_ Hb].
             auto. }
           destruct Hparts as [Hgm_cf Hbody_mf].
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun vw => orig_ruleGv f gm (fst vw) body (snd vw)) entries
                     ++ rest').
           { subst entries. cbn [map app fst snd]. f_equal; [exact Hr1eq | exact Hsplit]. }
           assert (Hlook : e_vmap e (vmapname n) = map vmap_pt entries).
           { rewrite (Hmint n (le_n n) ltac:(lia)).
             rewrite e_vmap_env_with_sets.
             erewrite (optimize_rules_vmapguarded_assoc_stable fuel (S n) dn rest'
                         m'' dd'' rr'' (vmapname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_vmaps assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply vmapname_inj in Heq. lia. }
           assert (Hmfm : rule_mutfree (merged_ruleGv f gm (vmapname n) body) = true).
           { unfold merged_ruleGv. apply rule_mutfree_mk_vmap_rule.
             rewrite forallb_bim_cons_bmatch, Hgm_cf. exact Hbody_mf. }
           rewrite Hrun_eq.
           transitivity (eval_rules_mut_st h
                           (merged_ruleGv f gm (vmapname n) body :: rest') e p).
           ++ apply (eval_rules_mut_st_mutfree_cons_cong h _ rr'' rest' e p Hmfm).
              apply (IH rest' (S n) dn m'' dd'' rr'' base e p (eq_sym Erec)).
              --- intros k Hk Hin. subst dn; cbn [sd_vmaps map fst] in Hin.
                  destruct Hin as [Heq | Hin];
                    [ apply vmapname_inj in Heq; lia
                    | apply (Hfresh k); [lia | exact Hin] ].
              --- intros k Hk Hk'. apply Hmint; lia.
           ++ apply (eval_rules_mut_st_vmap_mergeNg h f gm (vmapname n) entries body rest' e p
                       Hlook
                       ltac:(intros v w Hin; subst entries;
                             destruct Hin as [Hvw | Hin];
                             [ inversion Hvw; subst; exact HwK1 | apply (HwK v w Hin) ])
                       ltac:(intros v w Hin; subst entries;
                             destruct Hin as [Hvw | Hin];
                             [ inversion Hvw; subst; exact HwT1 | apply (HwT v w Hin) ])
                       Hns Hnt Hgm_cf Hbody_mf).
      * remember (optimize_rules_vmapguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
        pose proof (rule_step_vmap h r1 e p) as Hst.
        destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
        ++ destruct (terminal w); [reflexivity |].
           apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec) Hfresh).
           intros k Hk Hk'. rewrite Hst. apply Hmint; assumption.
        ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec) Hfresh).
           intros k Hk Hk'. rewrite Hst. apply Hmint; assumption.
Qed.

(** The masked merged rule's step (via [body_step]/[end_step]): the transform-keyed
    [end_step] returns the point map's [first_match_m] on a completed walk. *)
Lemma fst_step_dscpv_merged : forall (h : hook_id) f mask xor nm es body e p,
  e_vmap e nm = map vmap_pt es ->
  (forall v w, In (v, w) es -> field_fixed_len f = Some (Datatypes.length v)) ->
  (forall v w, In (v, w) es -> Datatypes.length mask = Datatypes.length v) ->
  (forall v w, In (v, w) es -> Datatypes.length xor = Datatypes.length v) ->
  body_has_synproxy body = false ->
  forallb body_item_mutfree body = true ->
  fst (rule_step h (mk_vmap_rule_t f [TBitAnd mask xor] nm body) e p)
  = match body_step body e p with
    | BRdone _ _ => if field_loadable f p then first_match_m f mask xor e p es else None
    | _ => None
    end.
Proof.
  intros h f mask xor nm es body e p Hvm Hfx Hmw Hxw Hns Hbody_mf.
  pose proof (body_has_synproxy_false_stops body p Hns) as Hsp.
  unfold rule_step, mk_vmap_rule_t. cbn [r_body].
  pose proof (body_step_mutfree_synfree body e p Hsp Hbody_mf) as HBS.
  destruct (body_step body e p) as [eb pb | eb pb | eb pb] eqn:EBS; cbn [fst].
  - reflexivity.
  - destruct HBS as [HB | HB]; discriminate HB.
  - destruct HBS as [HB | HB]; [discriminate HB |].
    injection HB as Heb Hpb. subst eb pb.
    unfold end_step. cbn [r_vmap vm_keyf vm_name vm_fields r_outcome].
    cbn [vmap_loadable vm_keyf].
    destruct (field_loadable f p) eqn:Hfld; cbn [fst]; [| reflexivity].
    cbn [apply_transforms fold_left apply_transform]. rewrite Hvm.
    rewrite (assoc_verdict_points_m es f mask xor e p
               ltac:(intros v w Hin Hld;
                     apply (dscpv_key_width f mask xor v e p
                              (Hfx v w Hin) (Hmw v w Hin) (Hxw v w Hin) Hld)) Hfld).
    destruct (first_match_m f mask xor e p es) eqn:Efm; cbn [fst]; [reflexivity |].
    unfold terminal_step.
    cbn [has_effect_terminal r_nat r_tproxy r_fwd r_queue r_verdict r_after r_outcome].
    reflexivity.
Qed.

(** Each masked original shell's step: its [MMasked] head gates the SAME body walk,
    which on completion yields the terminal verdict [w]. *)
Lemma fst_step_dscpv_orig : forall (h : hook_id) f mask xor v body w e p,
  body_has_synproxy body = false ->
  forallb body_item_mutfree body = true ->
  terminal w = true ->
  fst (rule_step h (orig_rule_m f mask xor v body w) e p)
  = if eval_matchcond (MMasked f CEq mask xor v) e p
    then match body_step body e p with BRdone _ _ => Some w | _ => None end
    else None.
Proof.
  intros h f mask xor v body w e p Hns Hbody_mf Hw.
  pose proof (body_has_synproxy_false_stops body p Hns) as Hsp.
  unfold rule_step, orig_rule_m, mk_head. cbn [r_body].
  cbn [body_step].
  rewrite (match_consume_free_id (MMasked f CEq mask xor v) e p eq_refl).
  destruct (eval_matchcond (MMasked f CEq mask xor v) e p) eqn:Ev; [| reflexivity].
  pose proof (body_step_mutfree_synfree body e p Hsp Hbody_mf) as HBS.
  destruct (body_step body e p) as [eb pb | eb pb | eb pb] eqn:EBS; cbn [fst].
  - reflexivity.
  - destruct HBS as [HB | HB]; discriminate HB.
  - destruct HBS as [HB | HB]; [discriminate HB |].
    injection HB as Heb Hpb. subst eb pb.
    unfold end_step, mk_vmap_base. cbn [r_vmap r_outcome].
    unfold terminal_step.
    cbn [has_effect_terminal r_nat r_tproxy r_fwd r_queue r_verdict r_after r_outcome].
    destruct w; cbn [terminal] in Hw; try discriminate Hw; reflexivity.
Qed.

(** The masked N-way vmap collapse over the state fold: like the plain vmap merge
    but the merged rule's key is [field & mask ^ xor] (a [TBitAnd] transform) and
    each shell matches [MMasked f CEq mask xor v].  The transformed-key lookup scan
    ([first_match_m]) is replayed rule-by-rule over the pinned state. *)
Lemma eval_rules_mut_st_dscpv_mergeN : forall (h : hook_id) f mask xor nm es body rest e p,
  e_vmap e nm = map vmap_pt es ->
  (forall v w, In (v, w) es -> field_fixed_len f = Some (Datatypes.length v)) ->
  (forall v w, In (v, w) es -> Datatypes.length mask = Datatypes.length v) ->
  (forall v w, In (v, w) es -> Datatypes.length xor = Datatypes.length v) ->
  (forall v w, In (v, w) es -> terminal w = true) ->
  body_has_synproxy body = false ->
  body_has_notrack body = false ->
  forallb body_item_mutfree body = true ->
  eval_rules_mut_st h (mk_vmap_rule_t f [TBitAnd mask xor] nm body :: rest) e p
  = eval_rules_mut_st h
      (map (fun vw => orig_rule_m f mask xor (fst vw) body (snd vw)) es ++ rest) e p.
Proof.
  intros h f mask xor nm es body rest e p Hvm Hfx Hmw Hxw Hterm Hns Hnt Hbody_mf.
  assert (Hmfo : forall v w, rule_mutfree (orig_rule_m f mask xor v body w) = true).
  { intros. unfold orig_rule_m. apply rule_mutfree_mk_head_intro;
      [ reflexivity | exact Hbody_mf | reflexivity | reflexivity ]. }
  assert (Hmfm : rule_mutfree (mk_vmap_rule_t f [TBitAnd mask xor] nm body) = true).
  { unfold rule_mutfree, mk_vmap_rule_t, rule_natfree, r_nat.
    cbn [r_body r_after r_outcome forallb]. rewrite Hbody_mf. reflexivity. }
  rewrite (eval_rules_mut_st_mutfree_cons h
             (mk_vmap_rule_t f [TBitAnd mask xor] nm body) rest e p Hmfm).
  rewrite (fst_step_dscpv_merged h f mask xor nm es body e p Hvm Hfx Hmw Hxw Hns Hbody_mf).
  clear Hvm Hnt.
  destruct (body_step body e p) as [eb pb | eb pb | eb pb] eqn:EBS.
  1,2: revert Hfx Hmw Hxw Hterm;
      induction es as [| [v w] es IH]; intros Hfx Hmw Hxw Hterm; cbn [map app];
        [reflexivity |];
      rewrite (eval_rules_mut_st_mutfree_cons h (orig_rule_m f mask xor v body w) _ e p
                 (Hmfo v w)),
              (fst_step_dscpv_orig h f mask xor v body w e p Hns Hbody_mf
                 (Hterm v w (or_introl eq_refl))), EBS;
      destruct (eval_matchcond (MMasked f CEq mask xor v) e p);
        (apply IH; [ intros v' w' Hin; apply (Hfx v' w'); right; exact Hin
                   | intros v' w' Hin; apply (Hmw v' w'); right; exact Hin
                   | intros v' w' Hin; apply (Hxw v' w'); right; exact Hin
                   | intros v' w' Hin; apply (Hterm v' w'); right; exact Hin ]).
  - destruct (field_loadable f p) eqn:Hfld.
    + revert Hfx Hmw Hxw Hterm.
      induction es as [| [v w] es IH]; intros Hfx Hmw Hxw Hterm;
        cbn [map app first_match_m]; [reflexivity |].
      rewrite (eval_rules_mut_st_mutfree_cons h (orig_rule_m f mask xor v body w) _ e p
                 (Hmfo v w)),
              (fst_step_dscpv_orig h f mask xor v body w e p Hns Hbody_mf
                 (Hterm v w (or_introl eq_refl))), EBS.
      destruct (eval_matchcond (MMasked f CEq mask xor v) e p) eqn:Ev.
      * rewrite (Hterm v w (or_introl eq_refl)). reflexivity.
      * apply IH; [ intros v' w' Hin; apply (Hfx v' w'); right; exact Hin
                  | intros v' w' Hin; apply (Hmw v' w'); right; exact Hin
                  | intros v' w' Hin; apply (Hxw v' w'); right; exact Hin
                  | intros v' w' Hin; apply (Hterm v' w'); right; exact Hin ].
    + revert Hfx Hmw Hxw Hterm.
      induction es as [| [v w] es IH]; intros Hfx Hmw Hxw Hterm; cbn [map app];
        [reflexivity |].
      rewrite (eval_rules_mut_st_mutfree_cons h (orig_rule_m f mask xor v body w) _ e p
                 (Hmfo v w)),
              (fst_step_dscpv_orig h f mask xor v body w e p Hns Hbody_mf
                 (Hterm v w (or_introl eq_refl))), EBS.
      assert (Hm : eval_matchcond (MMasked f CEq mask xor v) e p = false).
      { unfold eval_matchcond. cbn [match_loadable]. rewrite Hfld. reflexivity. }
      rewrite Hm.
      apply IH; [ intros v' w' Hin; apply (Hfx v' w'); right; exact Hin
                | intros v' w' Hin; apply (Hmw v' w'); right; exact Hin
                | intros v' w' Hin; apply (Hxw v' w'); right; exact Hin
                | intros v' w' Hin; apply (Hterm v' w'); right; exact Hin ].
Qed.

(** *** dscpvmap (masked value+verdict run -> transformed verdict map). *)
Theorem optimize_rules_dscpvmap_mut_st : forall h fuel rs n d n' d' rs' base e p,
  optimize_rules_dscpvmap fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  (forall k, n <= k -> k < n' ->
     e_vmap e (vmapname k) = e_vmap (env_with_sets base d') (vmapname k)) ->
  eval_rules_mut_st h rs' e p = eval_rules_mut_st h rs e p.
Proof.
  intros h fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base e p H Hfresh Hmint.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest]].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_dscpvmap_consSS in H.
      destruct (head_dscp r1) as [[[[[f mask] xor] v1] body] |] eqn:Ehd.
      * destruct (take_dscpv_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct (take_dscpv_run_shape r1 f mask xor v1 body (r2 :: rest) es rest' Ehd Erun)
          as [Hsplit [HwK [HwM [HwX HwT]]]].
        destruct es as [| e0 es'].
        -- remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
           pose proof (rule_step_vmap h r1 e p) as Hst.
           destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
           ++ destruct (terminal w); [reflexivity |].
              apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec) Hfresh).
              intros k Hk Hk'. rewrite Hst. apply Hmint; assumption.
           ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec) Hfresh).
              intros k Hk Hk'. rewrite Hst. apply Hmint; assumption.
        -- destruct (take_dscpv_run_head r1 f mask xor v1 body r2 rest (e0 :: es') rest'
                       Ehd Erun ltac:(discriminate))
             as [Hr1eq [HwK1 [HwM1 [HwX1 HwT1]]]].
           destruct (has_distinct_verdict (r_verdict r1) (e0 :: es') && body_vmap_safe body)
             eqn:Hdv.
           2:{ remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
               destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
               injection H as Hn' Hd' Hr'. subst n' d' rs'.
               rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
               pose proof (rule_step_vmap h r1 e p) as Hst.
               destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
               - destruct (terminal w); [reflexivity |].
                 apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec) Hfresh).
                 intros k Hk Hk'. rewrite Hst. apply Hmint; assumption.
               - apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec) Hfresh).
                 intros k Hk Hk'. rewrite Hst. apply Hmint; assumption. }
           apply Bool.andb_true_iff in Hdv as [_ Hsafe].
           apply Bool.andb_true_iff in Hsafe as [Hns Hnt].
           apply Bool.negb_true_iff in Hns. apply Bool.negb_true_iff in Hnt.
           cbv zeta in H.
           remember (optimize_rules_dscpvmap fuel (S n)
                       {| sd_sets := sd_sets d;
                          sd_vmaps := (vmapname n,
                            map vmap_pt ((v1, r_verdict r1) :: e0 :: es')) :: sd_vmaps d;
                          sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (entries := (v1, r_verdict r1) :: e0 :: es') in *.
           set (dn := {| sd_sets := sd_sets d;
                         sd_vmaps := (vmapname n, map vmap_pt entries) :: sd_vmaps d;
                         sd_maps := sd_maps d |}) in *.
           pose proof (optimize_rules_dscpvmap_mono fuel (S n) dn rest' m'' dd'' rr''
                         (eq_sym Erec)) as Hmono.
           assert (Hmf1 : rule_mutfree r1 = true).
           { pose proof Erun as Erun2. cbn in Erun2.
             destruct (dscpv_run_pair r1 r2) as [[[[[[fa ma] xa] v2] w2] bd]|] eqn:Evm.
             - exact (dscpv_run_pair_mutfree r1 r2 _ Evm).
             - inversion Erun2. }
           assert (Hbody_mf : forallb body_item_mutfree body = true).
           { rewrite Hr1eq in Hmf1. unfold orig_rule_m in Hmf1.
             exact (proj1 (rule_mutfree_mk_head_elim _ _ _ Hmf1)). }
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun vw => orig_rule_m f mask xor (fst vw) body (snd vw)) entries
                     ++ rest').
           { subst entries. cbn [map app fst snd]. f_equal; [exact Hr1eq | exact Hsplit]. }
           assert (Hlook : e_vmap e (vmapname n) = map vmap_pt entries).
           { rewrite (Hmint n (le_n n) ltac:(lia)).
             rewrite e_vmap_env_with_sets.
             erewrite (optimize_rules_dscpvmap_assoc_stable fuel (S n) dn rest'
                         m'' dd'' rr'' (vmapname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_vmaps assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply vmapname_inj in Heq. lia. }
           assert (Hmfm : rule_mutfree (mk_vmap_rule_t f [TBitAnd mask xor]
                                          (vmapname n) body) = true).
           { unfold rule_mutfree, mk_vmap_rule_t, rule_natfree, r_nat.
             cbn [r_body r_after r_outcome forallb]. rewrite Hbody_mf. reflexivity. }
           rewrite Hrun_eq.
           transitivity (eval_rules_mut_st h
                           (mk_vmap_rule_t f [TBitAnd mask xor] (vmapname n) body :: rest') e p).
           ++ apply (eval_rules_mut_st_mutfree_cons_cong h _ rr'' rest' e p Hmfm).
              apply (IH rest' (S n) dn m'' dd'' rr'' base e p (eq_sym Erec)).
              --- intros k Hk Hin. subst dn; cbn [sd_vmaps map fst] in Hin.
                  destruct Hin as [Heq | Hin];
                    [ apply vmapname_inj in Heq; lia
                    | apply (Hfresh k); [lia | exact Hin] ].
              --- intros k Hk Hk'. apply Hmint; lia.
           ++ apply (eval_rules_mut_st_dscpv_mergeN h f mask xor (vmapname n) entries body
                       rest' e p Hlook
                       ltac:(intros v w Hin; subst entries;
                             destruct Hin as [Hvw | Hin];
                             [ inversion Hvw; subst; exact HwK1 | apply (HwK v w Hin) ])
                       ltac:(intros v w Hin; subst entries;
                             destruct Hin as [Hvw | Hin];
                             [ inversion Hvw; subst; exact HwM1 | apply (HwM v w Hin) ])
                       ltac:(intros v w Hin; subst entries;
                             destruct Hin as [Hvw | Hin];
                             [ inversion Hvw; subst; exact HwX1 | apply (HwX v w Hin) ])
                       ltac:(intros v w Hin; subst entries;
                             destruct Hin as [Hvw | Hin];
                             [ inversion Hvw; subst; exact HwT1 | apply (HwT v w Hin) ])
                       Hns Hnt Hbody_mf).
      * remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
        pose proof (rule_step_vmap h r1 e p) as Hst.
        destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
        ++ destruct (terminal w); [reflexivity |].
           apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec) Hfresh).
           intros k Hk Hk'. rewrite Hst. apply Hmint; assumption.
        ++ apply (IH (r2 :: rest) n d m'' dd'' rr'' base e1 p1 (eq_sym Erec) Hfresh).
           intros k Hk Hk'. rewrite Hst. apply Hmint; assumption.
Qed.

(** ** The three EFFECT-REWRITING stages: fold-level per-shape certificates.

    dnat/snat fold whole NAT terminals and datamap folds `meta mark set` runs —
    their merged rules are NOT write-free, so the block lemma does not apply;
    instead each merge shape carries a fold-level certificate: the merged rule's
    [rule_step] equals the step sequence of the originals (same verdict, same
    (env, packet) out), built on the M3 data-plane equalities
    ([apply_nat_dnat_eq]/[apply_nat_snat_eq]/[dsl_step_map_merge]). *)

(** The fold on a dnat shell: fire (drop-or-translate) on a head hit, fall
    through state-unchanged otherwise. *)
Lemma rule_step_orig_dnat : forall h f v T e p,
  rule_step h (orig_dnat_rule f v T) e p
  = if eval_matchcond (MCmp f CEq v) e p
    then (if nat_drops h (orig_dnat_rule f v T) e p
          then (Some Drop, (e, p))
          else (Some Accept, apply_nat h (orig_dnat_rule f v T) e p))
    else (None, (e, p)).
Proof.
  intros h f v T e p.
  unfold rule_step. cbn [orig_dnat_rule r_body body_step match_consume].
  destruct (eval_matchcond (MCmp f CEq v) e p); [| reflexivity].
  unfold end_step. cbn [r_vmap r_outcome].
  unfold terminal_step, has_effect_terminal.
  cbn [r_nat r_tproxy r_fwd r_queue r_outcome].
  unfold terminal_loadable.
  cbn [r_nat r_outcome nat_src nat_map nat_field dnat_imm_spec].
  reflexivity.
Qed.

(** The fold on the bare merged map rule: translate on a map HIT, NFT_BREAK
    (fall through, state unchanged) on a miss or unloadable field. *)
Lemma rule_step_mk_dnat : forall h f m e p,
  rule_step h (mk_dnat_rule f m) e p
  = if field_loadable f p && map_has_key (field_value f e p) (e_map e m)
    then (if nat_drops h (mk_dnat_rule f m) e p
          then (Some Drop, (e, p))
          else (Some Accept, apply_nat h (mk_dnat_rule f m) e p))
    else (None, (e, p)).
Proof.
  intros h f m e p.
  unfold rule_step. cbn [mk_dnat_rule r_body body_step].
  unfold end_step, terminal_step, has_effect_terminal, terminal_loadable.
  cbn [mk_dnat_rule r_vmap r_nat r_tproxy r_fwd r_queue r_outcome
       nat_src nat_map nat_field dnat_map_spec fields_loadable forallb].
  rewrite nat_map_key_single. rewrite Bool.andb_true_r.
  reflexivity.
Qed.

Lemma nat_drops_dnat_eq : forall h f m v T e p,
  nat_drops h (mk_dnat_rule f m) e p = nat_drops h (orig_dnat_rule f v T) e p.
Proof. reflexivity. Qed.

Corollary apply_nat_dnat_merge2 : forall h f v1 v2 T1 T2 m e p,
  e_map e m = dmap2 v1 v2 T1 T2 ->
  data_eqb (field_value f e p) v1 = false ->
  data_eqb (field_value f e p) v2 = true ->
  apply_nat h (mk_dnat_rule f m) e p = apply_nat h (orig_dnat_rule f v2 T2) e p.
Proof.
  intros h f v1 v2 T1 T2 m e p Hmap Hv1 Hv2.
  transitivity (apply_nat h (orig_dnat_rule f [] T2) e p).
  - apply apply_nat_dnat_eq.
    rewrite Hmap. unfold dmap2. cbn [map_lookup_data]. rewrite Hv1, Hv2. reflexivity.
  - unfold apply_nat, orig_dnat_rule. cbn [r_nat r_outcome]. reflexivity.
Qed.

(** THE dnat pair certificate at the EFFECT level: verdict AND (env, packet). *)
Lemma eval_rules_mut_st_dnat_merge : forall h f v1 v2 T1 T2 m rest e p,
  e_map e m = dmap2 v1 v2 T1 T2 ->
  field_fixed_len f = Some (List.length v1) ->
  field_fixed_len f = Some (List.length v2) ->
  eval_rules_mut_st h (mk_dnat_rule f m :: rest) e p
  = eval_rules_mut_st h (orig_dnat_rule f v1 T1 :: orig_dnat_rule f v2 T2 :: rest) e p.
Proof.
  intros h f v1 v2 T1 T2 m rest e p Hmap Hfx1 Hfx2.
  rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
  rewrite rule_step_mk_dnat.
  rewrite (rule_step_orig_dnat h f v1 T1 e p).
  rewrite Hmap, map_has_key_dmap2.
  destruct (field_loadable f p) eqn:Hld.
  2:{ cbn [andb].
      rewrite (eval_mcmp_point_unload f v1 e p Hld).
      cbv beta iota. rewrite ?eval_rules_mut_st_cons.
      rewrite (rule_step_orig_dnat h f v2 T2 e p).
      rewrite (eval_mcmp_point_unload f v2 e p Hld).
      reflexivity. }
  rewrite (eval_mcmp_point f v1 e p Hld
             (field_fixed_len_loaded f (List.length v1) e p Hfx1 Hld)).
  cbn [andb].
  destruct (data_eqb (field_value f e p) v1) eqn:Hv1; cbn [orb].
  - (* key v1 hits: the merged translation IS the first original's *)
    rewrite (nat_drops_dnat_eq h f m v1 T1 e p).
    destruct (nat_drops h (orig_dnat_rule f v1 T1) e p); cbn [terminal];
      [reflexivity |].
    rewrite (apply_nat_dnat_merge1 h f v1 v2 T1 T2 m e p Hmap Hv1).
    destruct (apply_nat h (orig_dnat_rule f v1 T1) e p) as [e2 p2].
    reflexivity.
  - (* first original's head fails, state unchanged *)
    cbv beta iota. rewrite ?eval_rules_mut_st_cons.
    rewrite (rule_step_orig_dnat h f v2 T2 e p).
    rewrite (eval_mcmp_point f v2 e p Hld
               (field_fixed_len_loaded f (List.length v2) e p Hfx2 Hld)).
    destruct (data_eqb (field_value f e p) v2) eqn:Hv2.
    + (* key v2 hits *)
      rewrite (nat_drops_dnat_eq h f m v2 T2 e p).
      destruct (nat_drops h (orig_dnat_rule f v2 T2) e p); cbn [terminal];
        [reflexivity |].
      rewrite (apply_nat_dnat_merge2 h f v1 v2 T1 T2 m e p Hmap Hv1 Hv2).
      destruct (apply_nat h (orig_dnat_rule f v2 T2) e p) as [e2 p2].
      reflexivity.
    + (* miss: NFT_BREAK on the map = both originals' failing heads *)
      reflexivity.
Qed.

(** *** dnat (pairwise NAT-map fold) — effect-level stage lemma. *)
Theorem optimize_rules_dnat_mut_st : forall h rs n d n' d' rs' base e p,
  optimize_rules_dnat n d rs = (n', d', rs') ->
  (forall k, n <= k -> k < n' ->
     e_map e (mapname k) = e_map (env_with_sets base d') (mapname k)) ->
  Forall (rule_dynset_fresh n) rs ->
  eval_rules_mut_st h rs' e p = eval_rules_mut_st h rs e p.
Proof.
  intros h rs.
  induction rs as [rs IHrs] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' base e p H Hmint Hwf.
  destruct rs as [| r1 [| r2 rest]].
  - cbn in H. inversion H; subst; reflexivity.
  - cbn in H. inversion H; subst; reflexivity.
  - rewrite optimize_rules_dnat_cons2 in H.
    inversion Hwf as [| ? ? Hwf1 Hwf2]; subst.
    inversion Hwf2 as [| ? ? Hwf2' Hwf_rest]; subst.
    destruct (dnat_merge_pair r1 r2) as [[[[[f v1] v2] T1] T2]|] eqn:Em; cbv zeta in H.
    + destruct (dnat_merge_pair_shape r1 r2 f v1 v2 T1 T2 Em)
        as [Hr1eq [Hr2eq [Hfx1 [Hfx2 Hne]]]].
      set (dn := {| sd_sets := sd_sets d; sd_vmaps := sd_vmaps d;
                    sd_maps := (mapname n, dmap2 v1 v2 T1 T2) :: sd_maps d |}) in *.
      remember (optimize_rules_dnat (S n) dn rest) as tt eqn:Erec.
      destruct tt as [[m'' dd''] rr'']. injection H as Hn' Hd' Hr'. subst n' d' rs'.
      pose proof (optimize_rules_dnat_mono rest (S n) dn m'' dd'' rr''
                    (eq_sym Erec)) as Hmono.
      assert (Hlook : e_map e (mapname n) = dmap2 v1 v2 T1 T2).
      { rewrite (Hmint n (le_n n) ltac:(lia)).
        rewrite e_map_env_with_sets.
        erewrite (optimize_rules_dnat_maps_assoc_stable rest (S n) dn m'' dd'' rr''
                    (mapname n) _ (eq_sym Erec)).
        - subst dn; cbn [sd_maps assoc_str]. rewrite String.eqb_refl. reflexivity.
        - intros k Hk Heq. apply mapname_inj in Heq. lia. }
      rewrite Hr1eq, Hr2eq.
      rewrite <- (eval_rules_mut_st_dnat_merge h f v1 v2 T1 T2 (mapname n) rest e p
                    Hlook Hfx1 Hfx2).
      rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
      assert (Hst : forall nm, e_map (fst (snd (rule_step h (mk_dnat_rule f (mapname n))
                                                  e p))) nm
                    = e_map e nm).
      { intro nm.
        exact (proj2 (rule_step_sm_stable h (mk_dnat_rule f (mapname n)) e p nm
                        (fun F => F))). }
      destruct (rule_step h (mk_dnat_rule f (mapname n)) e p) as [[w|] [e1 p1]];
        cbn [fst snd] in Hst.
      * destruct (terminal w); [reflexivity |].
        apply (IHrs rest ltac:(unfold ltof; cbn; lia) (S n) dn m'' dd'' rr'' base e1 p1
                 (eq_sym Erec)).
        -- intros k Hk Hk'. rewrite (Hst (mapname k)). apply Hmint; lia.
        -- eapply Forall_impl;
             [ intros r Hr; apply (rule_dynset_fresh_mono n (S n) r); [lia | exact Hr]
             | exact Hwf_rest ].
      * apply (IHrs rest ltac:(unfold ltof; cbn; lia) (S n) dn m'' dd'' rr'' base e1 p1
                 (eq_sym Erec)).
        -- intros k Hk Hk'. rewrite (Hst (mapname k)). apply Hmint; lia.
        -- eapply Forall_impl;
             [ intros r Hr; apply (rule_dynset_fresh_mono n (S n) r); [lia | exact Hr]
             | exact Hwf_rest ].
    + remember (optimize_rules_dnat n d (r2 :: rest)) as tt eqn:Erec.
      destruct tt as [[m'' dd''] rr'']. injection H as Hn' Hd' Hr'. subst n' d' rs'.
      rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
      assert (Hst : forall k, n <= k ->
                e_map (fst (snd (rule_step h r1 e p))) (mapname k)
                = e_map e (mapname k))
        by (intros k Hk; exact (rule_step_mapname_stable h r1 e p k n Hwf1 Hk)).
      destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
      * destruct (terminal w); [reflexivity |].
        apply (IHrs (r2 :: rest) ltac:(unfold ltof; cbn; lia) n d m'' dd'' rr''
                 base e1 p1 (eq_sym Erec));
          [| constructor; assumption].
        intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
      * apply (IHrs (r2 :: rest) ltac:(unfold ltof; cbn; lia) n d m'' dd'' rr''
                 base e1 p1 (eq_sym Erec));
          [| constructor; assumption].
        intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
Qed.

(** Mirror fold characterisations for snat. *)
Lemma rule_step_orig_snat : forall h f v T e p,
  rule_step h (orig_snat_rule f v T) e p
  = if eval_matchcond (MCmp f CEq v) e p
    then (if nat_drops h (orig_snat_rule f v T) e p
          then (Some Drop, (e, p))
          else (Some Accept, apply_nat h (orig_snat_rule f v T) e p))
    else (None, (e, p)).
Proof.
  intros h f v T e p.
  unfold rule_step. cbn [orig_snat_rule r_body body_step match_consume].
  destruct (eval_matchcond (MCmp f CEq v) e p); [| reflexivity].
  unfold end_step, terminal_step, has_effect_terminal, terminal_loadable.
  cbn [orig_snat_rule r_vmap r_nat r_tproxy r_fwd r_queue r_outcome
       nat_src nat_map nat_field snat_imm_spec].
  reflexivity.
Qed.

Lemma rule_step_mk_snat : forall h f m e p,
  rule_step h (mk_snat_rule f m) e p
  = if field_loadable f p && map_has_key (field_value f e p) (e_map e m)
    then (if nat_drops h (mk_snat_rule f m) e p
          then (Some Drop, (e, p))
          else (Some Accept, apply_nat h (mk_snat_rule f m) e p))
    else (None, (e, p)).
Proof.
  intros h f m e p.
  unfold rule_step. cbn [mk_snat_rule r_body body_step].
  unfold end_step, terminal_step, has_effect_terminal, terminal_loadable.
  cbn [mk_snat_rule r_vmap r_nat r_tproxy r_fwd r_queue r_outcome
       nat_src nat_map nat_field snat_map_spec fields_loadable forallb].
  rewrite nat_map_key_single. rewrite Bool.andb_true_r.
  reflexivity.
Qed.

Lemma nat_drops_snat_eq : forall h f m v T e p,
  nat_drops h (mk_snat_rule f m) e p = nat_drops h (orig_snat_rule f v T) e p.
Proof. reflexivity. Qed.

Corollary apply_nat_snat_merge2 : forall h f v1 v2 T1 T2 m e p,
  e_map e m = dmap2 v1 v2 T1 T2 ->
  data_eqb (field_value f e p) v1 = false ->
  data_eqb (field_value f e p) v2 = true ->
  apply_nat h (mk_snat_rule f m) e p = apply_nat h (orig_snat_rule f v2 T2) e p.
Proof.
  intros h f v1 v2 T1 T2 m e p Hmap Hv1 Hv2.
  transitivity (apply_nat h (orig_snat_rule f [] T2) e p).
  - apply apply_nat_snat_eq.
    rewrite Hmap. unfold dmap2. cbn [map_lookup_data]. rewrite Hv1, Hv2. reflexivity.
  - unfold apply_nat, orig_snat_rule. cbn [r_nat r_outcome]. reflexivity.
Qed.

Lemma eval_rules_mut_st_snat_merge : forall h f v1 v2 T1 T2 m rest e p,
  e_map e m = dmap2 v1 v2 T1 T2 ->
  field_fixed_len f = Some (List.length v1) ->
  field_fixed_len f = Some (List.length v2) ->
  eval_rules_mut_st h (mk_snat_rule f m :: rest) e p
  = eval_rules_mut_st h (orig_snat_rule f v1 T1 :: orig_snat_rule f v2 T2 :: rest) e p.
Proof.
  intros h f v1 v2 T1 T2 m rest e p Hmap Hfx1 Hfx2.
  rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
  rewrite rule_step_mk_snat.
  rewrite (rule_step_orig_snat h f v1 T1 e p).
  rewrite Hmap, map_has_key_dmap2.
  destruct (field_loadable f p) eqn:Hld.
  2:{ cbn [andb].
      rewrite (eval_mcmp_point_unload f v1 e p Hld).
      cbv beta iota. rewrite ?eval_rules_mut_st_cons.
      rewrite (rule_step_orig_snat h f v2 T2 e p).
      rewrite (eval_mcmp_point_unload f v2 e p Hld).
      reflexivity. }
  rewrite (eval_mcmp_point f v1 e p Hld
             (field_fixed_len_loaded f (List.length v1) e p Hfx1 Hld)).
  cbn [andb].
  destruct (data_eqb (field_value f e p) v1) eqn:Hv1; cbn [orb].
  - rewrite (nat_drops_snat_eq h f m v1 T1 e p).
    destruct (nat_drops h (orig_snat_rule f v1 T1) e p); cbn [terminal];
      [reflexivity |].
    rewrite (apply_nat_snat_merge1 h f v1 v2 T1 T2 m e p Hmap Hv1).
    destruct (apply_nat h (orig_snat_rule f v1 T1) e p) as [e2 p2].
    reflexivity.
  - cbv beta iota. rewrite ?eval_rules_mut_st_cons.
    rewrite (rule_step_orig_snat h f v2 T2 e p).
    rewrite (eval_mcmp_point f v2 e p Hld
               (field_fixed_len_loaded f (List.length v2) e p Hfx2 Hld)).
    destruct (data_eqb (field_value f e p) v2) eqn:Hv2.
    + rewrite (nat_drops_snat_eq h f m v2 T2 e p).
      destruct (nat_drops h (orig_snat_rule f v2 T2) e p); cbn [terminal];
        [reflexivity |].
      rewrite (apply_nat_snat_merge2 h f v1 v2 T1 T2 m e p Hmap Hv1 Hv2).
      destruct (apply_nat h (orig_snat_rule f v2 T2) e p) as [e2 p2].
      reflexivity.
    + reflexivity.
Qed.

(** *** snat (pairwise NAT-map fold) — effect-level stage lemma. *)
Theorem optimize_rules_snat_mut_st : forall h rs n d n' d' rs' base e p,
  optimize_rules_snat n d rs = (n', d', rs') ->
  (forall k, n <= k -> k < n' ->
     e_map e (mapname k) = e_map (env_with_sets base d') (mapname k)) ->
  Forall (rule_dynset_fresh n) rs ->
  eval_rules_mut_st h rs' e p = eval_rules_mut_st h rs e p.
Proof.
  intros h rs.
  induction rs as [rs IHrs] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' base e p H Hmint Hwf.
  destruct rs as [| r1 [| r2 rest]].
  - cbn in H. inversion H; subst; reflexivity.
  - cbn in H. inversion H; subst; reflexivity.
  - rewrite optimize_rules_snat_cons2 in H.
    inversion Hwf as [| ? ? Hwf1 Hwf2]; subst.
    inversion Hwf2 as [| ? ? Hwf2' Hwf_rest]; subst.
    destruct (snat_merge_pair r1 r2) as [[[[[f v1] v2] T1] T2]|] eqn:Em; cbv zeta in H.
    + destruct (snat_merge_pair_shape r1 r2 f v1 v2 T1 T2 Em)
        as [Hr1eq [Hr2eq [Hfx1 [Hfx2 Hne]]]].
      set (dn := {| sd_sets := sd_sets d; sd_vmaps := sd_vmaps d;
                    sd_maps := (mapname n, dmap2 v1 v2 T1 T2) :: sd_maps d |}) in *.
      remember (optimize_rules_snat (S n) dn rest) as tt eqn:Erec.
      destruct tt as [[m'' dd''] rr'']. injection H as Hn' Hd' Hr'. subst n' d' rs'.
      pose proof (optimize_rules_snat_mono rest (S n) dn m'' dd'' rr''
                    (eq_sym Erec)) as Hmono.
      assert (Hlook : e_map e (mapname n) = dmap2 v1 v2 T1 T2).
      { rewrite (Hmint n (le_n n) ltac:(lia)).
        rewrite e_map_env_with_sets.
        erewrite (optimize_rules_snat_maps_assoc_stable rest (S n) dn m'' dd'' rr''
                    (mapname n) _ (eq_sym Erec)).
        - subst dn; cbn [sd_maps assoc_str]. rewrite String.eqb_refl. reflexivity.
        - intros k Hk Heq. apply mapname_inj in Heq. lia. }
      rewrite Hr1eq, Hr2eq.
      rewrite <- (eval_rules_mut_st_snat_merge h f v1 v2 T1 T2 (mapname n) rest e p
                    Hlook Hfx1 Hfx2).
      rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
      assert (Hst : forall nm, e_map (fst (snd (rule_step h (mk_snat_rule f (mapname n))
                                                  e p))) nm
                    = e_map e nm).
      { intro nm.
        exact (proj2 (rule_step_sm_stable h (mk_snat_rule f (mapname n)) e p nm
                        (fun F => F))). }
      destruct (rule_step h (mk_snat_rule f (mapname n)) e p) as [[w|] [e1 p1]];
        cbn [fst snd] in Hst.
      * destruct (terminal w); [reflexivity |].
        apply (IHrs rest ltac:(unfold ltof; cbn; lia) (S n) dn m'' dd'' rr'' base e1 p1
                 (eq_sym Erec)).
        -- intros k Hk Hk'. rewrite (Hst (mapname k)). apply Hmint; lia.
        -- eapply Forall_impl;
             [ intros r Hr; apply (rule_dynset_fresh_mono n (S n) r); [lia | exact Hr]
             | exact Hwf_rest ].
      * apply (IHrs rest ltac:(unfold ltof; cbn; lia) (S n) dn m'' dd'' rr'' base e1 p1
                 (eq_sym Erec)).
        -- intros k Hk Hk'. rewrite (Hst (mapname k)). apply Hmint; lia.
        -- eapply Forall_impl;
             [ intros r Hr; apply (rule_dynset_fresh_mono n (S n) r); [lia | exact Hr]
             | exact Hwf_rest ].
    + remember (optimize_rules_snat n d (r2 :: rest)) as tt eqn:Erec.
      destruct tt as [[m'' dd''] rr'']. injection H as Hn' Hd' Hr'. subst n' d' rs'.
      rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
      assert (Hst : forall k, n <= k ->
                e_map (fst (snd (rule_step h r1 e p))) (mapname k)
                = e_map e (mapname k))
        by (intros k Hk; exact (rule_step_mapname_stable h r1 e p k n Hwf1 Hk)).
      destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
      * destruct (terminal w); [reflexivity |].
        apply (IHrs (r2 :: rest) ltac:(unfold ltof; cbn; lia) n d m'' dd'' rr''
                 base e1 p1 (eq_sym Erec));
          [| constructor; assumption].
        intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
      * apply (IHrs (r2 :: rest) ltac:(unfold ltof; cbn; lia) n d m'' dd'' rr''
                 base e1 p1 (eq_sym Erec));
          [| constructor; assumption].
        intros k Hk Hk'. rewrite (Hst k Hk). apply Hmint; assumption.
Qed.

(** *** datamap (guarded `meta set` value-map fold) — effect-level. *)
Lemma eval_rules_mut_st_continue : forall h r rest e p,
  fst (rule_step h r e p) = None ->
  eval_rules_mut_st h (r :: rest) e p
  = (let '(e', p') := dsl_step h r e p in eval_rules_mut_st h rest e' p').
Proof.
  intros h r rest e p Ho. rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil. unfold dsl_step.
  destruct (rule_step h r e p) as [v [e' p']]. cbn [fst snd] in Ho |- *.
  subst v. reflexivity.
Qed.

(** THE datamap pair certificate at the EFFECT level (env-returning analogue of
    [Optimize_DataMap.eval_rules_mut_map_merge]). *)
Lemma eval_rules_mut_st_map_merge : forall h f v1 v2 M1 M2 sn mn k rest e p,
  is_payload_load f = true ->
  e_set e sn = map2_set v1 v2 ->
  e_map e mn = map2_map v1 v2 M1 M2 ->
  field_fixed_len f = Some (List.length v1) ->
  field_fixed_len f = Some (List.length v2) ->
  data_eqb v1 v2 = false ->
  eval_rules_mut_st h (mk_map_rule f sn mn k :: rest) e p
  = eval_rules_mut_st h (orig_map_rule f v1 M1 k :: orig_map_rule f v2 M2 k :: rest) e p.
Proof.
  intros h f v1 v2 M1 M2 sn mn k rest e p Hpl Hset Hmap Hfx1 Hfx2 Hne.
  rewrite (eval_rules_mut_st_continue h _ rest e p (step_mk_map_none h f sn mn k e p)).
  rewrite (eval_rules_mut_st_continue h _ _ e p (step_orig_map_none h f v1 M1 k e p)).
  rewrite (dsl_step_map_merge h f v1 v2 M1 M2 sn mn k e p Hpl Hset Hmap Hfx1 Hfx2 Hne).
  destruct (dsl_step h (orig_map_rule f v1 M1 k) e p) as [e1 p1].
  rewrite (eval_rules_mut_st_continue h _ rest e1 p1 (step_orig_map_none h f v2 M2 k e1 p1)).
  reflexivity.
Qed.

Theorem optimize_rules_datamap_mut_st : forall h rs n d n' d' rs' base e p,
  optimize_rules_datamap n d rs = (n', d', rs') ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  (forall k, n <= k -> k < n' ->
     e_map e (mapname k) = e_map (env_with_sets base d') (mapname k)) ->
  Forall (rule_dynset_fresh n) rs ->
  eval_rules_mut_st h rs' e p = eval_rules_mut_st h rs e p.
Proof.
  intros h rs.
  induction rs as [rs IHrs] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' base e p H Hmints Hmintm Hwf.
  destruct rs as [| r1 [| r2 rest]].
  - cbn in H. inversion H; subst; reflexivity.
  - cbn in H. inversion H; subst; reflexivity.
  - rewrite optimize_rules_datamap_cons2 in H.
    inversion Hwf as [| ? ? Hwf1 Hwf2]; subst.
    inversion Hwf2 as [| ? ? Hwf2' Hwf_rest]; subst.
    destruct (map_merge_pair r1 r2) as [[[[[[f v1] v2] M1] M2] k0]|] eqn:Em; cbv zeta in H.
    + destruct (map_merge_pair_shape r1 r2 f v1 v2 M1 M2 k0 Em)
        as [Hr1eq [Hr2eq [Hfx1 [Hfx2 Hne]]]].
      pose proof (map_merge_pair_payload r1 r2 f v1 v2 M1 M2 k0 Em) as Hpl.
      set (dn := {| sd_sets := (setname n, map2_set v1 v2) :: sd_sets d;
                    sd_vmaps := sd_vmaps d;
                    sd_maps := (mapname n, map2_map v1 v2 M1 M2) :: sd_maps d |}) in *.
      remember (optimize_rules_datamap (S n) dn rest) as tt eqn:Erec.
      destruct tt as [[m'' dd''] rr'']. injection H as Hn' Hd' Hr'. subst n' d' rs'.
      pose proof (optimize_rules_datamap_mono rest (S n) dn m'' dd'' rr''
                    (eq_sym Erec)) as Hmono.
      assert (Hlooks : e_set e (setname n) = map2_set v1 v2).
      { rewrite (Hmints n (le_n n) ltac:(lia)).
        rewrite e_set_declared.
        erewrite (optimize_rules_datamap_assoc_stable rest (S n) dn m'' dd'' rr''
                    (setname n) _ (eq_sym Erec)).
        - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
        - intros k Hk Heq. apply setname_inj in Heq. lia. }
      assert (Hlookm : e_map e (mapname n) = map2_map v1 v2 M1 M2).
      { rewrite (Hmintm n (le_n n) ltac:(lia)).
        rewrite e_map_env_with_sets.
        erewrite (optimize_rules_datamap_maps_assoc_stable rest (S n) dn m'' dd'' rr''
                    (mapname n) _ (eq_sym Erec)).
        - subst dn; cbn [sd_maps assoc_str]. rewrite String.eqb_refl. reflexivity.
        - intros k Hk Heq. apply mapname_inj in Heq. lia. }
      rewrite Hr1eq, Hr2eq.
      rewrite <- (eval_rules_mut_st_map_merge h f v1 v2 M1 M2 (setname n) (mapname n) k0
                    rest e p Hpl Hlooks Hlookm Hfx1 Hfx2 Hne).
      rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
      assert (Hst : forall nm, e_set (fst (snd (rule_step h
                        (mk_map_rule f (setname n) (mapname n) k0) e p))) nm
                      = e_set e nm
                    /\ e_map (fst (snd (rule_step h
                        (mk_map_rule f (setname n) (mapname n) k0) e p))) nm
                      = e_map e nm).
      { intro nm.
        exact (rule_step_sm_stable h (mk_map_rule f (setname n) (mapname n) k0) e p nm
                 (fun F => F)). }
      destruct (rule_step h (mk_map_rule f (setname n) (mapname n) k0) e p)
        as [[w|] [e1 p1]]; cbn [fst snd] in Hst.
      * destruct (terminal w); [reflexivity |].
        apply (IHrs rest ltac:(unfold ltof; cbn; lia) (S n) dn m'' dd'' rr'' base e1 p1
                 (eq_sym Erec)).
        -- intros k Hk Hk'. rewrite (proj1 (Hst (setname k))). apply Hmints; lia.
        -- intros k Hk Hk'. rewrite (proj2 (Hst (mapname k))). apply Hmintm; lia.
        -- eapply Forall_impl;
             [ intros r Hr; apply (rule_dynset_fresh_mono n (S n) r); [lia | exact Hr]
             | exact Hwf_rest ].
      * apply (IHrs rest ltac:(unfold ltof; cbn; lia) (S n) dn m'' dd'' rr'' base e1 p1
                 (eq_sym Erec)).
        -- intros k Hk Hk'. rewrite (proj1 (Hst (setname k))). apply Hmints; lia.
        -- intros k Hk Hk'. rewrite (proj2 (Hst (mapname k))). apply Hmintm; lia.
        -- eapply Forall_impl;
             [ intros r Hr; apply (rule_dynset_fresh_mono n (S n) r); [lia | exact Hr]
             | exact Hwf_rest ].
    + remember (optimize_rules_datamap n d (r2 :: rest)) as tt eqn:Erec.
      destruct tt as [[m'' dd''] rr'']. injection H as Hn' Hd' Hr'. subst n' d' rs'.
      rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
      assert (Hsts : forall k, n <= k ->
                e_set (fst (snd (rule_step h r1 e p))) (setname k)
                = e_set e (setname k))
        by (intros k Hk; exact (rule_step_setname_stable h r1 e p k n Hwf1 Hk)).
      assert (Hstm : forall k, n <= k ->
                e_map (fst (snd (rule_step h r1 e p))) (mapname k)
                = e_map e (mapname k))
        by (intros k Hk; exact (rule_step_mapname_stable h r1 e p k n Hwf1 Hk)).
      destruct (rule_step h r1 e p) as [[w|] [e1 p1]]; cbn [fst snd] in Hsts, Hstm.
      * destruct (terminal w); [reflexivity |].
        apply (IHrs (r2 :: rest) ltac:(unfold ltof; cbn; lia) n d m'' dd'' rr''
                 base e1 p1 (eq_sym Erec));
          [ | | constructor; assumption].
        -- intros k Hk Hk'. rewrite (Hsts k Hk). apply Hmints; assumption.
        -- intros k Hk Hk'. rewrite (Hstm k Hk). apply Hmintm; assumption.
      * apply (IHrs (r2 :: rest) ltac:(unfold ltof; cbn; lia) n d m'' dd'' rr''
                 base e1 p1 (eq_sym Erec));
          [ | | constructor; assumption].
        -- intros k Hk Hk'. rewrite (Hsts k Hk). apply Hmints; assumption.
        -- intros k Hk Hk'. rewrite (Hstm k Hk). apply Hmintm; assumption.
Qed.

(** Two [mk_head] shells over a COMMON base rule collapse under head subsumption:
    when [m1] loadable/matching implies [m2] loadable/matching, dropping the [m1]
    shell before the [m2] shell preserves the state fold.  Every terminal firing of
    the [m1] shell is a firing of the [m2] shell at the SAME verdict (the shells
    share body / end, so their fired verdict is head-independent), so
    [eval_rules_mut_st_absorb_pair]'s subsumption holds. *)
Lemma eval_rules_mut_st_absorb_mk : forall (h : hook_id) m1 m2 body rbase rest e p,
  rule_mutfree (mk_head m1 body rbase) = true ->
  rule_mutfree (mk_head m2 body rbase) = true ->
  (match_loadable m1 p = true -> match_loadable m2 p = true) ->
  (eval_matchcond m1 e p = true -> eval_matchcond m2 e p = true) ->
  eval_rules_mut_st h (mk_head m1 body rbase :: mk_head m2 body rbase :: rest) e p
  = eval_rules_mut_st h (mk_head m2 body rbase :: rest) e p.
Proof.
  intros h m1 m2 body rbase rest e p Hmf1 Hmf2 Pload Peval.
  apply (eval_rules_mut_st_absorb_pair h (mk_head m1 body rbase)
           (mk_head m2 body rbase) rest e p Hmf1 Hmf2).
  intros v Hfire.
  rewrite (rule_step_fst_mk_head h m1 body rbase e p
             (mk_head_mutfree_head m1 body rbase Hmf1)) in Hfire.
  rewrite (rule_step_fst_mk_head h m2 body rbase e p
             (mk_head_mutfree_head m2 body rbase Hmf2)).
  destruct (eval_matchcond m1 e p) eqn:E1; [| discriminate Hfire].
  rewrite (Peval eq_refl). exact Hfire.
Qed.

(** *** absorb (prefix-subsumed rule deletion) — effect-level. *)
Theorem optimize_rules_absorb_mut_st : forall h fuel rs e p,
  eval_rules_mut_st h (optimize_rules_absorb fuel rs) e p
  = eval_rules_mut_st h rs e p.
Proof.
  induction fuel as [| fuel IH]; intros rs e p; [reflexivity |].
  destruct rs as [| r1 [| r2 rest]]; try reflexivity.
  cbn [optimize_rules_absorb].
  destruct (absorb_pair r1 r2) as [tup |] eqn:Eap.
  - (* r1 deleted: both r1 and the surviving r2 are write-free shells *)
    rewrite (IH (r2 :: rest) e p).
    assert (Hmf1 : rule_mutfree r1 = true) by (exact (absorb_pair_mutfree r1 r2 _ Eap)).
    destruct tup as [[[[[[b off] w1] w2] v1] v2] body].
    destruct (absorb_pair_facts r1 r2 b off w1 w2 v1 v2 body Eap)
      as [Hr1 [Hr2 [Hle [Hlv1 [Hlv2 Hfn]]]]].
    set (m1 := MCmp (FPayload b off w1) CEq v1) in *.
    set (m2 := MCmp (FPayload b off w2) CEq v2) in *.
    assert (Hmf1' : rule_mutfree (mk_head m1 body r1) = true)
      by (rewrite <- Hr1; exact Hmf1).
    assert (Hmf2' : rule_mutfree (mk_head m2 body r1) = true)
      by (exact (rule_mutfree_mk_head_swap m1 m2 body r1 eq_refl Hmf1')).
    rewrite Hr1, Hr2. symmetry.
    apply (eval_rules_mut_st_absorb_mk h m1 m2 body r1 rest e p Hmf1' Hmf2').
    + unfold m1, m2. cbn [match_loadable field_loadable field_load load_ok].
      apply read_payload_ok_mono. exact Hle.
    + unfold eval_matchcond, m1, m2, eval_matchcond_body.
      cbn [match_loadable field_loadable field_load load_ok].
      intro Hm1. apply andb_true_iff in Hm1 as [Hl1 Hb1].
      apply andb_true_iff. split.
      * apply (read_payload_ok_mono b off w2 w1 p Hle Hl1).
      * cbn [eval_cmp field_value field_load do_load] in Hb1 |- *.
        rewrite read_payload_slice in Hb1. rewrite read_payload_slice.
        apply data_eqb_true_iff in Hb1. apply data_eqb_true_iff.
        rewrite Hlv1 in Hb1. rewrite firstn_len_slice in Hb1.
        rewrite Hlv2. rewrite firstn_len_slice.
        rewrite (slice_prefix (base_bytes b p) off w2 w1 Hle), Hb1. exact Hfn.
  - rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
    destruct (rule_step h r1 e p) as [[w|] [e1 p1]];
      [ destruct (terminal w); [reflexivity | apply IH] | apply IH ].
Qed.

(** *** ctmask (bitmask-union pair merge) — effect-level. *)
Theorem optimize_rules_ctmask_mut_st : forall h fuel rs e p,
  eval_rules_mut_st h (optimize_rules_ctmask fuel rs) e p
  = eval_rules_mut_st h rs e p.
Proof.
  induction fuel as [| fuel IH]; intros rs e p; [reflexivity |].
  destruct rs as [| r1 [| r2 rest]]; try reflexivity.
  cbn [optimize_rules_ctmask].
  destruct (ctmask_pair r1 r2) as [[[[[f m1] m2] z] body] |] eqn:Ep.
  - rewrite (IH (ctmask_merged f m1 m2 z body r1 :: rest) e p).
    assert (Hmf1 : rule_mutfree r1 = true) by (exact (ctmask_pair_mutfree r1 r2 _ Ep)).
    destruct (ctmask_pair_facts r1 r2 f m1 m2 z body Ep) as [Hr1 [Hr2 [Hl1 [Hl2 Hz]]]].
    assert (Hmf1' : rule_mutfree (mk_head (MMasked f CNe m1 z z) body r1) = true)
      by (rewrite <- Hr1; exact Hmf1).
    assert (Hmfg : forall m, rule_mutfree (mk_head (MMasked f CNe m z z) body r1) = true)
      by (intro m; exact (rule_mutfree_mk_head_swap (MMasked f CNe m1 z z)
             (MMasked f CNe m z z) body r1 eq_refl Hmf1')).
    assert (Hrun_eq : r1 :: r2 :: rest
              = map (fun m => mk_head (MMasked f CNe m z z) body r1) [m1; m2] ++ rest).
    { cbn [map app]. f_equal; [exact Hr1 | f_equal; exact Hr2]. }
    rewrite Hrun_eq. unfold ctmask_merged.
    refine (eval_rules_mut_st_run_collapse h [m1; m2]
              (fun m => mk_head (MMasked f CNe m z z) body r1)
              (fun m => eval_matchcond (MMasked f CNe m z z) e p)
              true (fst (rule_step h (mk_tail body r1) e p))
              (mk_head (MMasked f CNe (data_or m1 m2) z z) body r1) rest e p
              ltac:(discriminate) _ (Hmfg (data_or m1 m2)) _ _).
    + cbn [map forallb]. rewrite !Hmfg. reflexivity.
    + intros m Hin.
      rewrite (rule_step_fst_mk_head h (MMasked f CNe m z z) body r1 e p eq_refl).
      rewrite Bool.andb_true_l. reflexivity.
    + rewrite (rule_step_fst_mk_head h (MMasked f CNe (data_or m1 m2) z z)
                 body r1 e p eq_refl).
      rewrite (mmasked_ctmask_disjunction f m1 m2 z e p Hl1 Hl2 Hz).
      cbn [existsb]. rewrite Bool.orb_false_r, Bool.andb_true_l. reflexivity.
  - rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
    destruct (rule_step h r1 e p) as [[w|] [e1 p1]];
      [ destruct (terminal w); [reflexivity | apply IH] | apply IH ].
Qed.

(** ** Part E: the BASE pass ([Optimize.optimize_chain]) and [normalize_chain]
    at the effect level. *)

(** dce: everything after an unconditionally-terminal EMPTY rule is dead in the
    fold too — the shadowing rule's step is ([Some v], (e,p)) with [v] terminal. *)
Lemma eval_rules_mut_st_dce : forall h rs e p,
  eval_rules_mut_st h (dce rs) e p = eval_rules_mut_st h rs e p.
Proof.
  intros h rs. induction rs as [| r rs IH]; intros e p; [reflexivity |].
  cbn [dce]. destruct (shadows r) eqn:Hs.
  - unfold shadows in Hs.
    apply andb_true_iff in Hs. destruct Hs as [Hs1 Hq].
    apply andb_true_iff in Hs1. destruct Hs1 as [Hs2 Hfwd].
    apply andb_true_iff in Hs2. destruct Hs2 as [Hs3 Htp].
    apply andb_true_iff in Hs3. destruct Hs3 as [Hs4 Hnat].
    apply andb_true_iff in Hs4. destruct Hs4 as [Hs5 Hvm].
    apply andb_true_iff in Hs5. destruct Hs5 as [Hm Hv].
    rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
    unfold rule_step.
    destruct (r_body r) as [| it body] eqn:Eb; [| discriminate Hm].
    cbn [body_step].
    unfold end_step.
    destruct (r_vmap r) as [vm |] eqn:Evm; [discriminate Hvm |].
    unfold terminal_step, has_effect_terminal.
    destruct (r_nat r) as [ns |] eqn:Enat; [discriminate Hnat |].
    destruct (r_tproxy r) as [t |] eqn:Etp; [discriminate Htp |].
    destruct (r_fwd r) as [w |] eqn:Efwd; [discriminate Hfwd |].
    destruct (r_queue r) as [q |] eqn:Eq; [discriminate Hq |].
    destruct (r_verdict r) eqn:Ev; cbn in Hv |- *; try discriminate Hv; reflexivity.
  - rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
    destruct (rule_step h r e p) as [[w|] [e1 p1]];
      [ destruct (terminal w); [reflexivity | apply IH] | apply IH ].
Qed.

(** prune_noops: a no-op rule's step is the identity ([None], (e,p)). *)
Lemma eval_rules_mut_st_prune_noops : forall h rs e p,
  eval_rules_mut_st h (prune_noops rs) e p = eval_rules_mut_st h rs e p.
Proof.
  intros h rs. induction rs as [| r rs IH]; intros e p; [reflexivity |].
  unfold prune_noops in *. cbn [filter]. destruct (is_noop r) eqn:Hn; cbn [negb].
  - rewrite IH. symmetry.
    unfold is_noop in Hn.
    apply andb_true_iff in Hn as [Hn Hq].
    apply andb_true_iff in Hn as [Hn Hfwd].
    apply andb_true_iff in Hn as [Hn Htp].
    apply andb_true_iff in Hn as [Hn Hnat].
    apply andb_true_iff in Hn as [Hn Hvm].
    apply andb_true_iff in Hn as [Hba Hv].
    apply andb_true_iff in Hba as [Hb Hra].
    rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
    unfold rule_step.
    destruct (r_body r) as [| it b] eqn:Eb; [| discriminate Hb].
    cbn [body_step].
    unfold end_step.
    destruct (r_vmap r); [discriminate Hvm |].
    unfold terminal_step, has_effect_terminal.
    destruct (r_nat r); [discriminate Hnat |].
    destruct (r_tproxy r); [discriminate Htp |].
    destruct (r_fwd r); [discriminate Hfwd |].
    destruct (r_queue r); [discriminate Hq |].
    destruct (r_verdict r) eqn:Ev; cbn in Hv |- *; try discriminate Hv.
    destruct (r_after r) as [| sa ra] eqn:Era; [| discriminate Hra].
    cbn [after_step]. reflexivity.
  - rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
    destruct (rule_step h r e p) as [[w|] [e1 p1]];
      [ destruct (terminal w); [reflexivity | apply IH] | apply IH ].
Qed.

(** dedup: the pass fires ONLY on [rule_mutfree] rules (the new guard), where
    both sides' steps are the state-invariant pure projections and the historical
    verdict equalities apply. *)
Lemma forallb_bim_map_bmatch : forall l,
  forallb body_item_mutfree (map BMatch l) = forallb match_consumefree l.
Proof.
  induction l as [| m l IH]; [reflexivity |].
  cbn [map forallb body_item_mutfree]. rewrite IH. reflexivity.
Qed.

Lemma forallb_bim_map_bstmt : forall l,
  forallb body_item_mutfree (map BStmt l)
  = forallb (fun s => negb (is_mut_stmt s)) l.
Proof.
  induction l as [| s l IH]; [reflexivity |].
  cbn [map forallb body_item_mutfree]. rewrite IH. reflexivity.
Qed.

Lemma forallb_bim_matches : forall body,
  forallb body_item_mutfree body = true ->
  forallb match_consumefree (body_matches body) = true.
Proof.
  induction body as [| it body IH]; intro H; [reflexivity |].
  cbn [forallb] in H. apply andb_true_iff in H as [Hit Hrest].
  destruct it as [m | s]; unfold body_matches in *; cbn.
  - cbn [body_item_mutfree] in Hit. rewrite Hit. cbn [andb].
    apply IH; exact Hrest.
  - apply IH; exact Hrest.
Qed.

Lemma forallb_bim_stmts : forall body,
  forallb body_item_mutfree body = true ->
  forallb (fun s => negb (is_mut_stmt s)) (body_stmts body) = true.
Proof.
  induction body as [| it body IH]; intro H; [reflexivity |].
  cbn [forallb] in H. apply andb_true_iff in H as [Hit Hrest].
  destruct it as [m | s]; unfold body_stmts in *; cbn.
  - apply IH; exact Hrest.
  - cbn [body_item_mutfree] in Hit. rewrite Hit. cbn [andb].
    apply IH; exact Hrest.
Qed.

Lemma dedup_rule_mutfree : forall r,
  rule_mutfree r = true -> rule_mutfree (dedup_rule r) = true.
Proof.
  intros r Hmf. unfold dedup_rule.
  destruct (body_has_synproxy (r_body r) || body_has_notrack (r_body r)
            || negb (rule_mutfree r)) eqn:Hg; [exact Hmf |].
  unfold rule_mutfree in Hmf |- *.
  cbn [r_body r_after r_outcome].
  apply andb_true_iff in Hmf as [Hmf Hnat].
  apply andb_true_iff in Hmf as [Hbody Hafter].
  rewrite forallb_app, forallb_bim_map_bmatch, forallb_bim_map_bstmt.
  rewrite (forallb_nodup _ matchcond_eq_dec).
  rewrite (forallb_bim_matches _ Hbody), (forallb_bim_stmts _ Hbody).
  unfold rule_natfree, r_nat in Hnat |- *. cbn [r_outcome].
  rewrite Hafter, Hnat. reflexivity.
Qed.

(** The per-rule verdict certificate for dedup: on a mut-free rule the match
    reordering / de-duplication leaves the fold's verdict unchanged.  Read
    directly off [rule_step] — the body's break/completion classification is
    dedup-invariant ([body_step_done_class] over the preserved match- and
    load-sets), and the shared end fields give the same [end_step]. *)
Lemma fst_rule_step_dedup : forall h r e p,
  rule_mutfree r = true ->
  fst (rule_step h (dedup_rule r) e p) = fst (rule_step h r e p).
Proof.
  intros h r e p Hmf.
  destruct (body_has_synproxy (r_body r)) eqn:Hsp.
  { unfold dedup_rule; rewrite Hsp; reflexivity. }
  destruct (body_has_notrack (r_body r)) eqn:Hnt.
  { unfold dedup_rule; rewrite Hsp, Hnt; reflexivity. }
  assert (Hmfd := dedup_rule_mutfree r Hmf).
  assert (Hbody : forallb body_item_mutfree (r_body r) = true).
  { unfold rule_mutfree in Hmf. apply andb_true_iff in Hmf as [Hmf' _].
    apply andb_true_iff in Hmf' as [Hb _]. exact Hb. }
  assert (Hbody' : forallb body_item_mutfree (r_body (dedup_rule r)) = true).
  { unfold rule_mutfree in Hmfd. apply andb_true_iff in Hmfd as [Hmfd' _].
    apply andb_true_iff in Hmfd' as [Hb _]. exact Hb. }
  assert (Hnt' : body_has_notrack (r_body (dedup_rule r)) = false)
    by (apply dedup_body_no_notrack_rule; [exact Hsp | exact Hnt]).
  assert (Hsps : body_synproxy_stops (r_body r) p = false)
    by (apply body_has_synproxy_false_stops; exact Hsp).
  assert (Hsps' : body_synproxy_stops (r_body (dedup_rule r)) p = false).
  { unfold dedup_rule; rewrite Hsp, Hnt, Hmf; cbn [orb negb r_body].
    apply dedup_body_no_synproxy_stops; exact Hsp. }
  pose proof (body_step_done_class (r_body (dedup_rule r)) e p Hsps' Hnt' Hbody') as Hcl'.
  pose proof (body_step_done_class (r_body r) e p Hsps Hnt Hbody) as Hcl.
  assert (Hclass :
    (match body_step (r_body (dedup_rule r)) e p with BRdone _ _ => true | _ => false end)
    = (match body_step (r_body r) e p with BRdone _ _ => true | _ => false end)).
  { rewrite Hcl', Hcl. f_equal.
    - (* load-sets agree *)
      unfold dedup_rule; rewrite Hsp, Hnt, Hmf; cbn [orb negb r_body].
      rewrite (body_loadable_split
                 (map BMatch (nodup matchcond_eq_dec (body_matches (r_body r)))
                  ++ map BStmt (body_stmts (r_body r))) p).
      rewrite body_matches_app, body_matches_map_BMatch, body_matches_map_BStmt, app_nil_r.
      rewrite body_stmts_app, body_stmts_map_BMatch, body_stmts_map_BStmt. cbn [app].
      rewrite (forallb_nodup _ matchcond_eq_dec).
      symmetry. apply body_loadable_split.
    - (* match-sets agree *)
      unfold dedup_rule; rewrite Hsp, Hnt, Hmf; cbn [orb negb r_body].
      rewrite body_matches_app, body_matches_map_BMatch, body_matches_map_BStmt, app_nil_r.
      apply (forallb_nodup _ matchcond_eq_dec). }
  assert (Hend : forall e' p', end_step h (dedup_rule r) e' p' = end_step h r e' p').
  { intros e' p'. unfold dedup_rule; rewrite Hsp, Hnt, Hmf; cbn [orb negb]. reflexivity. }
  unfold rule_step.
  pose proof (body_step_mutfree_synfree (r_body (dedup_rule r)) e p Hsps' Hbody') as Hd'.
  pose proof (body_step_mutfree_synfree (r_body r) e p Hsps Hbody) as Hd.
  destruct Hd' as [Hd'|Hd']; destruct Hd as [Hd|Hd].
  - rewrite Hd', Hd. reflexivity.
  - rewrite Hd' in Hclass; rewrite Hd in Hclass; cbn in Hclass; discriminate Hclass.
  - rewrite Hd' in Hclass; rewrite Hd in Hclass; cbn in Hclass; discriminate Hclass.
  - rewrite Hd', Hd; cbn [fst]; rewrite (Hend e p); reflexivity.
Qed.

Lemma eval_rules_mut_st_map_dedup : forall h rs e p,
  eval_rules_mut_st h (map (fun r => simplify_rule (dedup_rule r)) rs) e p
  = eval_rules_mut_st h rs e p.
Proof.
  intros h rs.
  assert (Hsid : forall r, simplify_rule r = r).
  { intros [b o a]. unfold simplify_rule. cbn [r_body r_outcome r_after].
    rewrite map_simplify_item_id. reflexivity. }
  induction rs as [| r rs IH]; intros e p; [reflexivity |].
  cbn [map]. rewrite Hsid.
  destruct (body_has_synproxy (r_body r) || body_has_notrack (r_body r)
            || negb (rule_mutfree r)) eqn:Hg.
  - assert (Hid : dedup_rule r = r) by (unfold dedup_rule; rewrite Hg; reflexivity).
    rewrite Hid. rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil.
    destruct (rule_step h r e p) as [[w|] [e1 p1]];
      [ destruct (terminal w); [reflexivity | apply IH] | apply IH ].
  - assert (Hmf : rule_mutfree r = true).
    { destruct (rule_mutfree r); [reflexivity |].
      rewrite !Bool.orb_true_r in Hg. discriminate Hg. }
    assert (Hmfd : rule_mutfree (dedup_rule r) = true)
      by (apply dedup_rule_mutfree; exact Hmf).
    assert (Hstep : fst (rule_step h (dedup_rule r) e p) = fst (rule_step h r e p))
      by (apply fst_rule_step_dedup; exact Hmf).
    rewrite (eval_rules_mut_st_mutfree_cons h (dedup_rule r) _ e p Hmfd).
    rewrite (eval_rules_mut_st_mutfree_cons h r _ e p Hmf).
    rewrite Hstep.
    destruct (fst (rule_step h r e p)) as [w|];
      [ destruct (terminal w); [reflexivity | apply IH] | apply IH ].
Qed.

(** The whole base pass. *)
Theorem optimize_chain_mut_st : forall h c e p,
  eval_chain_mut_st h (optimize_chain c) e p = eval_chain_mut_st h c e p.
Proof.
  intros h c e p. unfold eval_chain_mut_st, optimize_chain. cbn [c_rules c_policy].
  rewrite eval_rules_mut_st_dce, eval_rules_mut_st_prune_noops.
  rewrite eval_rules_mut_st_map_dedup. reflexivity.
Qed.

(** normalize ([MEq] -> [MCmp CEq]): the rewritten match is extensionally the
    same PURE match, so the fold agrees step-for-step. *)
Lemma normalize_mc_consume : forall m e p,
  match_consume (normalize_mc m) e p = match_consume m e p.
Proof. intros [f v|f v|f neg lo hi|f neg msk xr v|f op v| | | | | | | | ] e p; reflexivity. Qed.

Lemma normalize_body_step : forall body e p,
  body_step (map normalize_bi body) e p = body_step body e p.
Proof.
  induction body as [| it body IH]; intros e p; [reflexivity |].
  destruct it as [m | s].
  - cbn [map normalize_bi body_step].
    rewrite normalize_mc_matchcond, normalize_mc_consume.
    destruct (eval_matchcond m e p); [apply IH | reflexivity].
  - destruct s; cbn [map normalize_bi body_step];
      repeat first
        [ match goal with
          | |- context [match ?l with nil => _ | cons _ _ => _ end] =>
              is_var l; destruct l
          end
        | match goal with
          | |- context [if ?b then _ else _] => destruct b
          end ];
      rewrite ?IH; reflexivity.
Qed.

Lemma normalize_rule_step : forall h r e p,
  rule_step h (normalize_rule r) e p = rule_step h r e p.
Proof.
  intros h r e p. unfold rule_step.
  rewrite normalize_r_body, normalize_body_step.
  destruct (body_step (r_body r) e p) as [e' p' | e' p' | e' p']; reflexivity.
Qed.

Lemma eval_rules_mut_st_normalize : forall h rs e p,
  eval_rules_mut_st h (map normalize_rule rs) e p = eval_rules_mut_st h rs e p.
Proof.
  intros h rs. induction rs as [| r rs IH]; intros e p; [reflexivity |].
  cbn [map]. rewrite ?eval_rules_mut_st_cons, ?eval_rules_mut_st_nil. rewrite normalize_rule_step.
  destruct (rule_step h r e p) as [[w|] [e1 p1]];
    [ destruct (terminal w); [reflexivity | apply IH] | apply IH ].
Qed.

Theorem normalize_chain_mut_st : forall h c e p,
  eval_chain_mut_st h (normalize_chain c) e p = eval_chain_mut_st h c e p.
Proof.
  intros h c e p. unfold eval_chain_mut_st, normalize_chain. cbn [c_rules c_policy].
  rewrite eval_rules_mut_st_normalize. reflexivity.
Qed.

(** ** Part F: dynset-target freshness is PRESERVED by every stage.

    A merged rule's dynset targets are exactly its base rule's (same shared tail
    body and end fields; the fresh head match contributes no statement), or
    empty (the exact-shape dnat/snat/datamap shells).  So the write-target
    freshness [rule_dynset_fresh n0] transfers from a stage's input to its
    output — at a FIXED bound [n0], no counter bookkeeping. *)

Lemma rule_dynset_names_mk_head : forall m body r,
  rule_dynset_names (mk_head m body r)
  = body_dynset_names body ++ flat_map stmt_dynset_names (r_after r).
Proof. reflexivity. Qed.

Lemma rule_dynset_names_bmatch_cons : forall m body,
  body_dynset_names (BMatch m :: body) = body_dynset_names body.
Proof. reflexivity. Qed.

(** Freshness transfer between two shells over the SAME tail body/end fields. *)
Lemma rule_dynset_fresh_mk_head_swap : forall n0 m m' body r,
  rule_dynset_fresh n0 (mk_head m body r) ->
  rule_dynset_fresh n0 (mk_head m' body r).
Proof.
  intros n0 m m' body r Hf k Hk.
  specialize (Hf k Hk). rewrite rule_dynset_names_mk_head in Hf |- *. exact Hf.
Qed.

Lemma rule_dynset_fresh_mk_head2_swap : forall n0 gm m m' body r,
  rule_dynset_fresh n0 (mk_head gm (BMatch m :: body) r) ->
  rule_dynset_fresh n0 (mk_head gm (BMatch m' :: body) r).
Proof.
  intros n0 gm m m' body r Hf k Hk.
  specialize (Hf k Hk).
  rewrite rule_dynset_names_mk_head, rule_dynset_names_bmatch_cons in Hf |- *.
  exact Hf.
Qed.

(** Head-hoisting transfer (guarded families / vmap shells): any two rules whose
    dynset-name LISTS agree share the freshness. *)
Lemma rule_dynset_fresh_names_eq : forall n0 r r',
  rule_dynset_names r' = rule_dynset_names r ->
  rule_dynset_fresh n0 r -> rule_dynset_fresh n0 r'.
Proof. intros n0 r r' Heq Hf k Hk. rewrite Heq. exact (Hf k Hk). Qed.

Lemma optimize_rules_valueset_dynset_fresh : forall n0 fuel rs n d n' d' rs',
  optimize_rules_valueset fuel n d rs = (n', d', rs') ->
  Forall (rule_dynset_fresh n0) rs -> Forall (rule_dynset_fresh n0) rs'.
Proof.
  intros n0 fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' H Hwf;
    [cbn in H; inversion H; subst; exact Hwf |].
  destruct rs as [| r1 [| r2 rest]]; try (cbn in H; inversion H; subst; exact Hwf).
  rewrite optimize_rules_valueset_consSS in H.
  inversion Hwf as [| ? ? Hw1 Hwtail]; subst.
  destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
  - destruct (take_value_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
    destruct (take_value_run_shape r1 f v1 body (r2 :: rest) vs rest' Ehd Erun)
      as [Hsplit _].
    destruct vs as [| v vs'].
    + remember (optimize_rules_valueset fuel n d (r2 :: rest)) as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as _ _ Hr'. subst rs'.
      constructor; [exact Hw1 | exact (IH _ _ _ _ _ _ (eq_sym Erec) Hwtail)].
    + cbv zeta in H.
      remember (optimize_rules_valueset fuel (S n)
                  {| sd_sets := (setname n, map (fun w => (w,w)) (v1 :: v :: vs'))
                                :: sd_sets d;
                     sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
        as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as _ _ Hr'. subst rs'.
      assert (Hf' : rule_dynset_fresh n0 (mk_head (MCmp f CEq v1) body r1))
        by (rewrite <- (head_value_canon r1 f v1 body Ehd); exact Hw1).
      constructor.
      * exact (rule_dynset_fresh_names_eq n0 _ _ eq_refl Hf').
      * apply (IH _ _ _ _ _ _ (eq_sym Erec)).
        rewrite Hsplit in Hwtail. apply Forall_app in Hwtail. exact (proj2 Hwtail).
  - remember (optimize_rules_valueset fuel n d (r2 :: rest)) as t eqn:Erec.
    destruct t as [[m'' dd''] rr'']. cbv zeta in H.
    injection H as _ _ Hr'. subst rs'.
    constructor; [exact Hw1 | exact (IH _ _ _ _ _ _ (eq_sym Erec) Hwtail)].
Qed.

Lemma optimize_rules_dscp_dynset_fresh : forall n0 fuel rs n d n' d' rs',
  optimize_rules_dscp fuel n d rs = (n', d', rs') ->
  Forall (rule_dynset_fresh n0) rs -> Forall (rule_dynset_fresh n0) rs'.
Proof.
  intros n0 fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' H Hwf;
    [cbn in H; inversion H; subst; exact Hwf |].
  destruct rs as [| r1 [| r2 rest]]; try (cbn in H; inversion H; subst; exact Hwf).
  rewrite optimize_rules_dscp_consSS in H.
  inversion Hwf as [| ? ? Hw1 Hwtail]; subst.
  destruct (head_dscp r1) as [[[[[f mask] xor] v1] body] |] eqn:Ehd.
  - destruct (take_dscp_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
    destruct (take_dscp_run_shape r1 f mask xor v1 body (r2 :: rest) vs rest' Ehd Erun)
      as [Hsplit _].
    destruct vs as [| v vs'].
    + remember (optimize_rules_dscp fuel n d (r2 :: rest)) as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as _ _ Hr'. subst rs'.
      constructor; [exact Hw1 | exact (IH _ _ _ _ _ _ (eq_sym Erec) Hwtail)].
    + cbv zeta in H.
      remember (optimize_rules_dscp fuel (S n)
                  {| sd_sets := (setname n, map (fun w => (w,w)) (v1 :: v :: vs'))
                                :: sd_sets d;
                     sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
        as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as _ _ Hr'. subst rs'.
      assert (Hf' : rule_dynset_fresh n0 (mk_head (MMasked f CEq mask xor v1) body r1))
        by (rewrite <- (head_dscp_canon r1 f mask xor v1 body Ehd); exact Hw1).
      constructor.
      * exact (rule_dynset_fresh_names_eq n0 _ _ eq_refl Hf').
      * apply (IH _ _ _ _ _ _ (eq_sym Erec)).
        rewrite Hsplit in Hwtail. apply Forall_app in Hwtail. exact (proj2 Hwtail).
  - remember (optimize_rules_dscp fuel n d (r2 :: rest)) as t eqn:Erec.
    destruct t as [[m'' dd''] rr'']. cbv zeta in H.
    injection H as _ _ Hr'. subst rs'.
    constructor; [exact Hw1 | exact (IH _ _ _ _ _ _ (eq_sym Erec) Hwtail)].
Qed.

Lemma optimize_rules_intervalset_dynset_fresh : forall n0 fuel rs n d n' d' rs',
  optimize_rules_intervalset fuel n d rs = (n', d', rs') ->
  Forall (rule_dynset_fresh n0) rs -> Forall (rule_dynset_fresh n0) rs'.
Proof.
  intros n0 fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' H Hwf;
    [cbn in H; inversion H; subst; exact Hwf |].
  destruct rs as [| r1 [| r2 rest]]; try (cbn in H; inversion H; subst; exact Hwf).
  rewrite optimize_rules_intervalset_consSS in H.
  inversion Hwf as [| ? ? Hw1 Hwtail]; subst.
  destruct (head_range r1) as [[[[f lo1] hi1] body] |] eqn:Ehd.
  - destruct (take_range_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
    pose proof (take_range_run_shape r1 f lo1 hi1 body (r2 :: rest) ivs rest' Ehd Erun)
      as Hsplit.
    destruct ivs as [| iv ivs'].
    + remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as _ _ Hr'. subst rs'.
      constructor; [exact Hw1 | exact (IH _ _ _ _ _ _ (eq_sym Erec) Hwtail)].
    + cbv zeta in H.
      remember (optimize_rules_intervalset fuel (S n)
                  {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                     sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
        as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as _ _ Hr'. subst rs'.
      assert (Hf' : rule_dynset_fresh n0 (mk_head (MRange f false lo1 hi1) body r1))
        by (rewrite <- (head_range_canon r1 f lo1 hi1 body Ehd); exact Hw1).
      constructor.
      * exact (rule_dynset_fresh_names_eq n0 _ _ eq_refl Hf').
      * apply (IH _ _ _ _ _ _ (eq_sym Erec)).
        rewrite Hsplit in Hwtail. apply Forall_app in Hwtail. exact (proj2 Hwtail).
  - remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as t eqn:Erec.
    destruct t as [[m'' dd''] rr'']. cbv zeta in H.
    injection H as _ _ Hr'. subst rs'.
    constructor; [exact Hw1 | exact (IH _ _ _ _ _ _ (eq_sym Erec) Hwtail)].
Qed.

Lemma optimize_rules_intervalsethostorder_dynset_fresh : forall n0 fuel rs n d n' d' rs',
  optimize_rules_intervalsethostorder fuel n d rs = (n', d', rs') ->
  Forall (rule_dynset_fresh n0) rs -> Forall (rule_dynset_fresh n0) rs'.
Proof.
  intros n0 fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' H Hwf;
    [cbn in H; inversion H; subst; exact Hwf |].
  destruct rs as [| r1 [| r2 rest]]; try (cbn in H; inversion H; subst; exact Hwf).
  rewrite optimize_rules_intervalsethostorder_consSS in H.
  inversion Hwf as [| ? ? Hw1 Hwtail]; subst.
  destruct (head_ivsett r1) as [[[[[f ts] lo1] hi1] body] |] eqn:Ehd.
  - destruct (take_ivsett_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
    pose proof (take_ivsett_run_shape r1 f ts lo1 hi1 body (r2 :: rest) ivs rest'
                  Ehd Erun) as Hsplit.
    destruct ivs as [| iv ivs'].
    + remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as _ _ Hr'. subst rs'.
      constructor; [exact Hw1 | exact (IH _ _ _ _ _ _ (eq_sym Erec) Hwtail)].
    + cbv zeta in H.
      remember (optimize_rules_intervalsethostorder fuel (S n)
                  {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                     sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
        as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as _ _ Hr'. subst rs'.
      assert (Hf' : rule_dynset_fresh n0 (mk_head (MRangeT f ts false lo1 hi1) body r1))
        by (rewrite <- (head_ivsett_canon r1 f ts lo1 hi1 body Ehd); exact Hw1).
      constructor.
      * exact (rule_dynset_fresh_names_eq n0 _ _ eq_refl Hf').
      * apply (IH _ _ _ _ _ _ (eq_sym Erec)).
        rewrite Hsplit in Hwtail. apply Forall_app in Hwtail. exact (proj2 Hwtail).
  - remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as t eqn:Erec.
    destruct t as [[m'' dd''] rr'']. cbv zeta in H.
    injection H as _ _ Hr'. subst rs'.
    constructor; [exact Hw1 | exact (IH _ _ _ _ _ _ (eq_sym Erec) Hwtail)].
Qed.

Lemma optimize_rules_intervalsetguarded_dynset_fresh : forall n0 fuel rs n d n' d' rs',
  optimize_rules_intervalsetguarded fuel n d rs = (n', d', rs') ->
  Forall (rule_dynset_fresh n0) rs -> Forall (rule_dynset_fresh n0) rs'.
Proof.
  intros n0 fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' H Hwf;
    [cbn in H; inversion H; subst; exact Hwf |].
  destruct rs as [| r1 [| r2 rest]]; try (cbn in H; inversion H; subst; exact Hwf).
  rewrite optimize_rules_intervalsetguarded_consSS in H.
  inversion Hwf as [| ? ? Hw1 Hwtail]; subst.
  destruct (head_rangeGr r1) as [[[[[gm f] lo1] hi1] body] |] eqn:Ehd.
  - destruct (take_rangeg_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
    pose proof (take_rangeg_run_shape r1 gm f lo1 hi1 body (r2 :: rest) ivs rest'
                  Ehd Erun) as Hsplit.
    destruct ivs as [| iv ivs'].
    + remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as _ _ Hr'. subst rs'.
      constructor; [exact Hw1 | exact (IH _ _ _ _ _ _ (eq_sym Erec) Hwtail)].
    + cbv zeta in H.
      remember (optimize_rules_intervalsetguarded fuel (S n)
                  {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                     sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
        as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as _ _ Hr'. subst rs'.
      assert (Hf' : rule_dynset_fresh n0 (orig_ruleGr f gm lo1 hi1 body r1))
        by (rewrite <- (head_rangeGr_canon r1 gm f lo1 hi1 body Ehd); exact Hw1).
      constructor.
      * unfold orig_ruleGr in Hf'.
        exact (rule_dynset_fresh_names_eq n0 _ _ eq_refl Hf').
      * apply (IH _ _ _ _ _ _ (eq_sym Erec)).
        rewrite Hsplit in Hwtail. apply Forall_app in Hwtail. exact (proj2 Hwtail).
  - remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as t eqn:Erec.
    destruct t as [[m'' dd''] rr'']. cbv zeta in H.
    injection H as _ _ Hr'. subst rs'.
    constructor; [exact Hw1 | exact (IH _ _ _ _ _ _ (eq_sym Erec) Hwtail)].
Qed.

Lemma optimize_rules_mixedpointrangeguarded_dynset_fresh : forall n0 fuel rs n d n' d' rs',
  optimize_rules_mixedpointrangeguarded fuel n d rs = (n', d', rs') ->
  Forall (rule_dynset_fresh n0) rs -> Forall (rule_dynset_fresh n0) rs'.
Proof.
  intros n0 fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' H Hwf;
    [cbn in H; inversion H; subst; exact Hwf |].
  destruct rs as [| r1 [| r2 rest]]; try (cbn in H; inversion H; subst; exact Hwf).
  rewrite optimize_rules_mixedpointrangeguarded_consSS in H.
  inversion Hwf as [| ? ? Hw1 Hwtail]; subst.
  destruct (head_mixGm r1) as [[[[gm f] e1] body] |] eqn:Ehd.
  - destruct (take_mix_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
    pose proof (take_mix_run_shape r1 gm f e1 body (r2 :: rest) es rest' Ehd Erun)
      as Hsplit.
    destruct es as [| el es'].
    + remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as _ _ Hr'. subst rs'.
      constructor; [exact Hw1 | exact (IH _ _ _ _ _ _ (eq_sym Erec) Hwtail)].
    + cbv zeta in H.
      remember (optimize_rules_mixedpointrangeguarded fuel (S n)
                  {| sd_sets := (setname n, map melem_iv (e1 :: el :: es')) :: sd_sets d;
                     sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
        as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as _ _ Hr'. subst rs'.
      assert (Hf' : rule_dynset_fresh n0 (orig_ruleGm f gm e1 body r1))
        by (rewrite <- (head_mixGm_canon r1 gm f e1 body Ehd); exact Hw1).
      constructor.
      * unfold orig_ruleGm in Hf'. unfold merged_ruleGs.
        exact (rule_dynset_fresh_names_eq n0 _ _ eq_refl Hf').
      * apply (IH _ _ _ _ _ _ (eq_sym Erec)).
        rewrite Hsplit in Hwtail. apply Forall_app in Hwtail. exact (proj2 Hwtail).
  - remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as t eqn:Erec.
    destruct t as [[m'' dd''] rr'']. cbv zeta in H.
    injection H as _ _ Hr'. subst rs'.
    constructor; [exact Hw1 | exact (IH _ _ _ _ _ _ (eq_sym Erec) Hwtail)].
Qed.

Lemma optimize_rules_concat_dynset_fresh : forall n0 fuel rs n d n' d' rs',
  optimize_rules_concat fuel n d rs = (n', d', rs') ->
  Forall (rule_dynset_fresh n0) rs -> Forall (rule_dynset_fresh n0) rs'.
Proof.
  intros n0 fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' H Hwf;
    [cbn in H; inversion H; subst; exact Hwf |].
  destruct rs as [| r1 [| r2 rest]]; try (cbn in H; inversion H; subst; exact Hwf).
  rewrite optimize_rules_concat_consSS in H.
  inversion Hwf as [| ? ? Hw1 Hwtail]; subst.
  destruct (head_value2 r1) as [[[[[f1 a1] f2] b1] body] |] eqn:Ehd.
  - destruct (take_concat_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
    destruct (take_concat_run_shape r1 f1 a1 f2 b1 body (r2 :: rest) ts rest' Ehd Erun)
      as [Hsplit _].
    destruct ts as [| t ts'].
    + remember (optimize_rules_concat fuel n d (r2 :: rest)) as tt eqn:Erec.
      destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as _ _ Hr'. subst rs'.
      constructor; [exact Hw1 | exact (IH _ _ _ _ _ _ (eq_sym Erec) Hwtail)].
    + cbv zeta in H.
      remember (optimize_rules_concat fuel (S n)
                  {| sd_sets := (setname n, map pack_tuple ((a1,b1) :: t :: ts'))
                                :: sd_sets d;
                     sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
        as tt eqn:Erec.
      destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as _ _ Hr'. subst rs'.
      assert (Hf' : rule_dynset_fresh n0 (orig_rule2 f1 f2 a1 b1 body r1))
        by (rewrite <- (head_value2_canon r1 f1 a1 f2 b1 body Ehd); exact Hw1).
      constructor.
      * unfold orig_rule2 in Hf'. unfold merged_rule2.
        exact (rule_dynset_fresh_names_eq n0 _ _ eq_refl Hf').
      * apply (IH _ _ _ _ _ _ (eq_sym Erec)).
        rewrite Hsplit in Hwtail. apply Forall_app in Hwtail. exact (proj2 Hwtail).
  - remember (optimize_rules_concat fuel n d (r2 :: rest)) as tt eqn:Erec.
    destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
    injection H as _ _ Hr'. subst rs'.
    constructor; [exact Hw1 | exact (IH _ _ _ _ _ _ (eq_sym Erec) Hwtail)].
Qed.

Lemma optimize_rules_concatguarded_dynset_fresh : forall n0 fuel rs n d n' d' rs',
  optimize_rules_concatguarded fuel n d rs = (n', d', rs') ->
  Forall (rule_dynset_fresh n0) rs -> Forall (rule_dynset_fresh n0) rs'.
Proof.
  intros n0 fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' H Hwf;
    [cbn in H; inversion H; subst; exact Hwf |].
  destruct rs as [| r1 [| r2 rest]]; try (cbn in H; inversion H; subst; exact Hwf).
  rewrite optimize_rules_concatguarded_consSS in H.
  inversion Hwf as [| ? ? Hw1 Hwtail]; subst.
  destruct (head_value2g r1) as [[[[[[f1 a1] gm] f2] b1] body] |] eqn:Ehd.
  - destruct (take_concatg_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
    destruct (take_concatg_run_shape r1 f1 a1 gm f2 b1 body (r2 :: rest) ts rest'
                Ehd Erun) as [Hsplit _].
    destruct ts as [| t ts'].
    + remember (optimize_rules_concatguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
      destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as _ _ Hr'. subst rs'.
      constructor; [exact Hw1 | exact (IH _ _ _ _ _ _ (eq_sym Erec) Hwtail)].
    + cbv zeta in H.
      remember (optimize_rules_concatguarded fuel (S n)
                  {| sd_sets := (setname n, map pack_tuple ((a1,b1) :: t :: ts'))
                                :: sd_sets d;
                     sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
        as tt eqn:Erec.
      destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as _ _ Hr'. subst rs'.
      assert (Hf' : rule_dynset_fresh n0 (orig_rule2g f1 f2 gm a1 b1 body r1))
        by (rewrite <- (head_value2g_canon r1 f1 a1 gm f2 b1 body Ehd); exact Hw1).
      constructor.
      * unfold orig_rule2g in Hf'. unfold merged_rule2g.
        exact (rule_dynset_fresh_names_eq n0 _ _ eq_refl Hf').
      * apply (IH _ _ _ _ _ _ (eq_sym Erec)).
        rewrite Hsplit in Hwtail. apply Forall_app in Hwtail. exact (proj2 Hwtail).
  - remember (optimize_rules_concatguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
    destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
    injection H as _ _ Hr'. subst rs'.
    constructor; [exact Hw1 | exact (IH _ _ _ _ _ _ (eq_sym Erec) Hwtail)].
Qed.

Lemma optimize_rules_setguarded_dynset_fresh : forall n0 fuel rs n d n' d' rs',
  optimize_rules_setguarded fuel n d rs = (n', d', rs') ->
  Forall (rule_dynset_fresh n0) rs -> Forall (rule_dynset_fresh n0) rs'.
Proof.
  intros n0 fuel.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' H Hwf;
    [cbn in H; inversion H; subst; exact Hwf |].
  destruct rs as [| r1 [| r2 rest]]; try (cbn in H; inversion H; subst; exact Hwf).
  rewrite optimize_rules_setguarded_consSS in H.
  inversion Hwf as [| ? ? Hw1 Hwtail]; subst.
  destruct (head_valueGs r1) as [[[[gm f] v1] body] |] eqn:Ehd.
  - destruct (take_setg_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
    destruct (take_setg_run_shape r1 gm f v1 body (r2 :: rest) vs rest' Ehd Erun)
      as [Hsplit _].
    destruct vs as [| v0 vs'].
    + remember (optimize_rules_setguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
      destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as _ _ Hr'. subst rs'.
      constructor; [exact Hw1 | exact (IH _ _ _ _ _ _ (eq_sym Erec) Hwtail)].
    + cbv zeta in H.
      remember (optimize_rules_setguarded fuel (S n)
                  {| sd_sets := (setname n, map (fun v => (v, v)) (v1 :: v0 :: vs'))
                                :: sd_sets d;
                     sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
        as tt eqn:Erec.
      destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as _ _ Hr'. subst rs'.
      assert (Hf' : rule_dynset_fresh n0 (orig_ruleGs f gm v1 body r1))
        by (rewrite <- (head_valueGs_canon r1 gm f v1 body Ehd); exact Hw1).
      constructor.
      * unfold orig_ruleGs in Hf'. unfold merged_ruleGs.
        exact (rule_dynset_fresh_names_eq n0 _ _ eq_refl Hf').
      * apply (IH _ _ _ _ _ _ (eq_sym Erec)).
        rewrite Hsplit in Hwtail. apply Forall_app in Hwtail. exact (proj2 Hwtail).
  - remember (optimize_rules_setguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
    destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
    injection H as _ _ Hr'. subst rs'.
    constructor; [exact Hw1 | exact (IH _ _ _ _ _ _ (eq_sym Erec) Hwtail)].
Qed.

Lemma optimize_rules_concatmulti_dynset_fresh : forall n0 rs n d n' d' rs',
  optimize_rules_concatmulti n d rs = (n', d', rs') ->
  Forall (rule_dynset_fresh n0) rs -> Forall (rule_dynset_fresh n0) rs'.
Proof.
  intros n0 rs.
  induction rs as [rs IHrs] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H Hwf.
  destruct rs as [| r1 [| r2 rest]]; try (cbn in H; inversion H; subst; exact Hwf).
  rewrite optimize_rules_concatmulti_cons2 in H.
  inversion Hwf as [| ? ? Hw1 Hwf2]; subst.
  inversion Hwf2 as [| ? ? Hw2 Hwrest]; subst.
  destruct (concat_mergeK_pair r1 r2) as [[[[fields row1] row2] body] |] eqn:Em;
    cbv zeta in H.
  - destruct (concat_mergeK_pair_shape r1 r2 fields row1 row2 body Em)
      as [Hr1eq [_ _]].
    remember (optimize_rules_concatmulti (S n)
                {| sd_sets := (setname n, map pack_row [row1; row2]) :: sd_sets d;
                   sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest) as tt eqn:Erec.
    destruct tt as [[m'' dd''] rr'']. injection H as _ _ Hr'. subst rs'.
    constructor.
    + (* merged_ruleK's dynset names = the shared tail's = r1's *)
      intros k Hk. specialize (Hw1 k Hk).
      rewrite Hr1eq in Hw1.
      unfold merged_ruleK, rule_dynset_names, orig_ruleK in Hw1 |- *.
      cbn [mk_head r_body r_after] in Hw1 |- *.
      unfold body_dynset_names in Hw1 |- *.
      rewrite flat_map_app in Hw1.
      assert (Hkm : flat_map
                      (fun it => match it with BStmt s => stmt_dynset_names s
                                 | BMatch _ => [] end) (kmatches fields row1) = []).
      { unfold kmatches. induction (combine fields row1) as [| fa l IHl];
          [reflexivity |]. cbn [map flat_map]. exact IHl. }
      rewrite Hkm in Hw1. cbn [app] in Hw1. exact Hw1.
    + apply (IHrs rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym Erec) Hwrest).
  - remember (optimize_rules_concatmulti n d (r2 :: rest)) as tt eqn:Erec.
    destruct tt as [[m'' dd''] rr'']. injection H as _ _ Hr'. subst rs'.
    constructor;
      [ exact Hw1
      | apply (IHrs (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym Erec));
        constructor; assumption ].
Qed.

Lemma rule_dynset_fresh_nil_names : forall n0 r,
  rule_dynset_names r = [] -> rule_dynset_fresh n0 r.
Proof. intros n0 r Hn k Hk. rewrite Hn. split; intros []. Qed.

Lemma optimize_rules_dnat_dynset_fresh : forall n0 rs n d n' d' rs',
  optimize_rules_dnat n d rs = (n', d', rs') ->
  Forall (rule_dynset_fresh n0) rs -> Forall (rule_dynset_fresh n0) rs'.
Proof.
  intros n0 rs.
  induction rs as [rs IHrs] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H Hwf.
  destruct rs as [| r1 [| r2 rest]]; try (cbn in H; inversion H; subst; exact Hwf).
  rewrite optimize_rules_dnat_cons2 in H.
  inversion Hwf as [| ? ? Hw1 Hwf2]; subst.
  inversion Hwf2 as [| ? ? Hw2 Hwrest]; subst.
  destruct (dnat_merge_pair r1 r2) as [[[[[f v1] v2] T1] T2]|] eqn:Em; cbv zeta in H.
  - remember (optimize_rules_dnat (S n)
                {| sd_sets := sd_sets d; sd_vmaps := sd_vmaps d;
                   sd_maps := (mapname n, dmap2 v1 v2 T1 T2) :: sd_maps d |} rest)
      as tt eqn:Erec.
    destruct tt as [[m'' dd''] rr'']. injection H as _ _ Hr'. subst rs'.
    constructor.
    + apply rule_dynset_fresh_nil_names. reflexivity.
    + apply (IHrs rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym Erec) Hwrest).
  - remember (optimize_rules_dnat n d (r2 :: rest)) as tt eqn:Erec.
    destruct tt as [[m'' dd''] rr'']. injection H as _ _ Hr'. subst rs'.
    constructor;
      [ exact Hw1
      | apply (IHrs (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym Erec));
        constructor; assumption ].
Qed.

Lemma optimize_rules_snat_dynset_fresh : forall n0 rs n d n' d' rs',
  optimize_rules_snat n d rs = (n', d', rs') ->
  Forall (rule_dynset_fresh n0) rs -> Forall (rule_dynset_fresh n0) rs'.
Proof.
  intros n0 rs.
  induction rs as [rs IHrs] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H Hwf.
  destruct rs as [| r1 [| r2 rest]]; try (cbn in H; inversion H; subst; exact Hwf).
  rewrite optimize_rules_snat_cons2 in H.
  inversion Hwf as [| ? ? Hw1 Hwf2]; subst.
  inversion Hwf2 as [| ? ? Hw2 Hwrest]; subst.
  destruct (snat_merge_pair r1 r2) as [[[[[f v1] v2] T1] T2]|] eqn:Em; cbv zeta in H.
  - remember (optimize_rules_snat (S n)
                {| sd_sets := sd_sets d; sd_vmaps := sd_vmaps d;
                   sd_maps := (mapname n, dmap2 v1 v2 T1 T2) :: sd_maps d |} rest)
      as tt eqn:Erec.
    destruct tt as [[m'' dd''] rr'']. injection H as _ _ Hr'. subst rs'.
    constructor.
    + apply rule_dynset_fresh_nil_names. reflexivity.
    + apply (IHrs rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym Erec) Hwrest).
  - remember (optimize_rules_snat n d (r2 :: rest)) as tt eqn:Erec.
    destruct tt as [[m'' dd''] rr'']. injection H as _ _ Hr'. subst rs'.
    constructor;
      [ exact Hw1
      | apply (IHrs (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym Erec));
        constructor; assumption ].
Qed.

Lemma optimize_rules_datamap_dynset_fresh : forall n0 rs n d n' d' rs',
  optimize_rules_datamap n d rs = (n', d', rs') ->
  Forall (rule_dynset_fresh n0) rs -> Forall (rule_dynset_fresh n0) rs'.
Proof.
  intros n0 rs.
  induction rs as [rs IHrs] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H Hwf.
  destruct rs as [| r1 [| r2 rest]]; try (cbn in H; inversion H; subst; exact Hwf).
  rewrite optimize_rules_datamap_cons2 in H.
  inversion Hwf as [| ? ? Hw1 Hwf2]; subst.
  inversion Hwf2 as [| ? ? Hw2 Hwrest]; subst.
  destruct (map_merge_pair r1 r2) as [[[[[[f v1] v2] M1] M2] k0]|] eqn:Em; cbv zeta in H.
  - remember (optimize_rules_datamap (S n)
                {| sd_sets := (setname n, map2_set v1 v2) :: sd_sets d;
                   sd_vmaps := sd_vmaps d;
                   sd_maps := (mapname n, map2_map v1 v2 M1 M2) :: sd_maps d |} rest)
      as tt eqn:Erec.
    destruct tt as [[m'' dd''] rr'']. injection H as _ _ Hr'. subst rs'.
    constructor.
    + apply rule_dynset_fresh_nil_names. reflexivity.
    + apply (IHrs rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym Erec) Hwrest).
  - remember (optimize_rules_datamap n d (r2 :: rest)) as tt eqn:Erec.
    destruct tt as [[m'' dd''] rr'']. injection H as _ _ Hr'. subst rs'.
    constructor;
      [ exact Hw1
      | apply (IHrs (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym Erec));
        constructor; assumption ].
Qed.

(** ctmask: the merged rule's dynset names are its base rule's. *)
Lemma optimize_rules_ctmask_dynset_fresh : forall n0 fuel rs,
  Forall (rule_dynset_fresh n0) rs ->
  Forall (rule_dynset_fresh n0) (optimize_rules_ctmask fuel rs).
Proof.
  intros n0 fuel rs Hwf.
  apply (optimize_rules_ctmask_Forall (rule_dynset_fresh n0) fuel rs); [| exact Hwf].
  intros r1 r2 f m1 m2 z body Hp Hf1.
  destruct (ctmask_pair_facts r1 r2 f m1 m2 z body Hp) as [Hr1 _].
  rewrite Hr1 in Hf1. unfold ctmask_merged.
  exact (rule_dynset_fresh_names_eq n0 _ _ eq_refl Hf1).
Qed.

Lemma optimize_chain_valueset_mut_st : forall h n d c n' d' c' base e p,
  optimize_chain_valueset n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) (c_rules c) ->
  eval_chain_mut_st h c' e p = eval_chain_mut_st h c e p.
Proof.
  intros h n d c n' d' c' base e p H Hfresh Hmint Hwf.
  unfold optimize_chain_valueset in H.
  destruct (optimize_rules_valueset (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain_mut_st. cbn [c_rules c_policy].
  rewrite (optimize_rules_valueset_mut_st h (Datatypes.length (c_rules c)) (c_rules c)
             n d m'' dd'' rr'' base e p E Hfresh Hmint Hwf). reflexivity.
Qed.

Lemma optimize_chain_valueset_sets_assoc_stable : forall n d c n' d' c' nm X0,
  optimize_chain_valueset n d c = (n', d', c') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X0 = assoc_str nm (sd_sets d) X0.
Proof.
  intros n d c n' d' c' nm X0 H Hnm.
  unfold optimize_chain_valueset in H.
  destruct (optimize_rules_valueset (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  exact (optimize_rules_valueset_assoc_stable (Datatypes.length (c_rules c)) n d
           (c_rules c) m'' dd'' rr'' nm X0 E Hnm).
Qed.

Lemma optimize_chain_valueset_dynset_fresh : forall n0 n d c n' d' c',
  optimize_chain_valueset n d c = (n', d', c') ->
  Forall (rule_dynset_fresh n0) (c_rules c) ->
  Forall (rule_dynset_fresh n0) (c_rules c').
Proof.
  intros n0 n d c n' d' c' H Hwf.
  unfold optimize_chain_valueset in H.
  destruct (optimize_rules_valueset (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. cbn [c_rules].
  exact (optimize_rules_valueset_dynset_fresh n0 (Datatypes.length (c_rules c))
           (c_rules c) n d m'' dd'' rr'' E Hwf).
Qed.

Lemma optimize_chain_concat_mut_st : forall h n d c n' d' c' base e p,
  optimize_chain_concat n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) (c_rules c) ->
  eval_chain_mut_st h c' e p = eval_chain_mut_st h c e p.
Proof.
  intros h n d c n' d' c' base e p H Hfresh Hmint Hwf.
  unfold optimize_chain_concat in H.
  destruct (optimize_rules_concat (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain_mut_st. cbn [c_rules c_policy].
  rewrite (optimize_rules_concat_mut_st h (Datatypes.length (c_rules c)) (c_rules c)
             n d m'' dd'' rr'' base e p E Hfresh Hmint Hwf). reflexivity.
Qed.

Lemma optimize_chain_concat_sets_assoc_stable : forall n d c n' d' c' nm X0,
  optimize_chain_concat n d c = (n', d', c') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X0 = assoc_str nm (sd_sets d) X0.
Proof.
  intros n d c n' d' c' nm X0 H Hnm.
  unfold optimize_chain_concat in H.
  destruct (optimize_rules_concat (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  exact (optimize_rules_concat_assoc_stable (Datatypes.length (c_rules c)) n d
           (c_rules c) m'' dd'' rr'' nm X0 E Hnm).
Qed.

Lemma optimize_chain_concat_dynset_fresh : forall n0 n d c n' d' c',
  optimize_chain_concat n d c = (n', d', c') ->
  Forall (rule_dynset_fresh n0) (c_rules c) ->
  Forall (rule_dynset_fresh n0) (c_rules c').
Proof.
  intros n0 n d c n' d' c' H Hwf.
  unfold optimize_chain_concat in H.
  destruct (optimize_rules_concat (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. cbn [c_rules].
  exact (optimize_rules_concat_dynset_fresh n0 (Datatypes.length (c_rules c))
           (c_rules c) n d m'' dd'' rr'' E Hwf).
Qed.

Lemma optimize_chain_concatguarded_mut_st : forall h n d c n' d' c' base e p,
  optimize_chain_concatguarded n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) (c_rules c) ->
  eval_chain_mut_st h c' e p = eval_chain_mut_st h c e p.
Proof.
  intros h n d c n' d' c' base e p H Hfresh Hmint Hwf.
  unfold optimize_chain_concatguarded in H.
  destruct (optimize_rules_concatguarded (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain_mut_st. cbn [c_rules c_policy].
  rewrite (optimize_rules_concatguarded_mut_st h (Datatypes.length (c_rules c)) (c_rules c)
             n d m'' dd'' rr'' base e p E Hfresh Hmint Hwf). reflexivity.
Qed.

Lemma optimize_chain_concatguarded_sets_assoc_stable : forall n d c n' d' c' nm X0,
  optimize_chain_concatguarded n d c = (n', d', c') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X0 = assoc_str nm (sd_sets d) X0.
Proof.
  intros n d c n' d' c' nm X0 H Hnm.
  unfold optimize_chain_concatguarded in H.
  destruct (optimize_rules_concatguarded (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  exact (optimize_rules_concatguarded_assoc_stable (Datatypes.length (c_rules c)) n d
           (c_rules c) m'' dd'' rr'' nm X0 E Hnm).
Qed.

Lemma optimize_chain_concatguarded_dynset_fresh : forall n0 n d c n' d' c',
  optimize_chain_concatguarded n d c = (n', d', c') ->
  Forall (rule_dynset_fresh n0) (c_rules c) ->
  Forall (rule_dynset_fresh n0) (c_rules c').
Proof.
  intros n0 n d c n' d' c' H Hwf.
  unfold optimize_chain_concatguarded in H.
  destruct (optimize_rules_concatguarded (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. cbn [c_rules].
  exact (optimize_rules_concatguarded_dynset_fresh n0 (Datatypes.length (c_rules c))
           (c_rules c) n d m'' dd'' rr'' E Hwf).
Qed.

Lemma optimize_chain_setguarded_mut_st : forall h n d c n' d' c' base e p,
  optimize_chain_setguarded n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) (c_rules c) ->
  eval_chain_mut_st h c' e p = eval_chain_mut_st h c e p.
Proof.
  intros h n d c n' d' c' base e p H Hfresh Hmint Hwf.
  unfold optimize_chain_setguarded in H.
  destruct (optimize_rules_setguarded (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain_mut_st. cbn [c_rules c_policy].
  rewrite (optimize_rules_setguarded_mut_st h (Datatypes.length (c_rules c)) (c_rules c)
             n d m'' dd'' rr'' base e p E Hfresh Hmint Hwf). reflexivity.
Qed.

Lemma optimize_chain_setguarded_sets_assoc_stable : forall n d c n' d' c' nm X0,
  optimize_chain_setguarded n d c = (n', d', c') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X0 = assoc_str nm (sd_sets d) X0.
Proof.
  intros n d c n' d' c' nm X0 H Hnm.
  unfold optimize_chain_setguarded in H.
  destruct (optimize_rules_setguarded (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  exact (optimize_rules_setguarded_assoc_stable (Datatypes.length (c_rules c)) n d
           (c_rules c) m'' dd'' rr'' nm X0 E Hnm).
Qed.

Lemma optimize_chain_setguarded_dynset_fresh : forall n0 n d c n' d' c',
  optimize_chain_setguarded n d c = (n', d', c') ->
  Forall (rule_dynset_fresh n0) (c_rules c) ->
  Forall (rule_dynset_fresh n0) (c_rules c').
Proof.
  intros n0 n d c n' d' c' H Hwf.
  unfold optimize_chain_setguarded in H.
  destruct (optimize_rules_setguarded (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. cbn [c_rules].
  exact (optimize_rules_setguarded_dynset_fresh n0 (Datatypes.length (c_rules c))
           (c_rules c) n d m'' dd'' rr'' E Hwf).
Qed.

Lemma optimize_chain_intervalset_mut_st : forall h n d c n' d' c' base e p,
  optimize_chain_intervalset n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) (c_rules c) ->
  eval_chain_mut_st h c' e p = eval_chain_mut_st h c e p.
Proof.
  intros h n d c n' d' c' base e p H Hfresh Hmint Hwf.
  unfold optimize_chain_intervalset in H.
  destruct (optimize_rules_intervalset (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain_mut_st. cbn [c_rules c_policy].
  rewrite (optimize_rules_intervalset_mut_st h (Datatypes.length (c_rules c)) (c_rules c)
             n d m'' dd'' rr'' base e p E Hfresh Hmint Hwf). reflexivity.
Qed.

Lemma optimize_chain_intervalset_sets_assoc_stable : forall n d c n' d' c' nm X0,
  optimize_chain_intervalset n d c = (n', d', c') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X0 = assoc_str nm (sd_sets d) X0.
Proof.
  intros n d c n' d' c' nm X0 H Hnm.
  unfold optimize_chain_intervalset in H.
  destruct (optimize_rules_intervalset (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  exact (optimize_rules_intervalset_assoc_stable (Datatypes.length (c_rules c)) n d
           (c_rules c) m'' dd'' rr'' nm X0 E Hnm).
Qed.

Lemma optimize_chain_intervalset_dynset_fresh : forall n0 n d c n' d' c',
  optimize_chain_intervalset n d c = (n', d', c') ->
  Forall (rule_dynset_fresh n0) (c_rules c) ->
  Forall (rule_dynset_fresh n0) (c_rules c').
Proof.
  intros n0 n d c n' d' c' H Hwf.
  unfold optimize_chain_intervalset in H.
  destruct (optimize_rules_intervalset (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. cbn [c_rules].
  exact (optimize_rules_intervalset_dynset_fresh n0 (Datatypes.length (c_rules c))
           (c_rules c) n d m'' dd'' rr'' E Hwf).
Qed.

Lemma optimize_chain_intervalsethostorder_mut_st : forall h n d c n' d' c' base e p,
  optimize_chain_intervalsethostorder n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) (c_rules c) ->
  eval_chain_mut_st h c' e p = eval_chain_mut_st h c e p.
Proof.
  intros h n d c n' d' c' base e p H Hfresh Hmint Hwf.
  unfold optimize_chain_intervalsethostorder in H.
  destruct (optimize_rules_intervalsethostorder (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain_mut_st. cbn [c_rules c_policy].
  rewrite (optimize_rules_intervalsethostorder_mut_st h (Datatypes.length (c_rules c)) (c_rules c)
             n d m'' dd'' rr'' base e p E Hfresh Hmint Hwf). reflexivity.
Qed.

Lemma optimize_chain_intervalsethostorder_sets_assoc_stable : forall n d c n' d' c' nm X0,
  optimize_chain_intervalsethostorder n d c = (n', d', c') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X0 = assoc_str nm (sd_sets d) X0.
Proof.
  intros n d c n' d' c' nm X0 H Hnm.
  unfold optimize_chain_intervalsethostorder in H.
  destruct (optimize_rules_intervalsethostorder (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  exact (optimize_rules_intervalsethostorder_assoc_stable (Datatypes.length (c_rules c)) n d
           (c_rules c) m'' dd'' rr'' nm X0 E Hnm).
Qed.

Lemma optimize_chain_intervalsethostorder_dynset_fresh : forall n0 n d c n' d' c',
  optimize_chain_intervalsethostorder n d c = (n', d', c') ->
  Forall (rule_dynset_fresh n0) (c_rules c) ->
  Forall (rule_dynset_fresh n0) (c_rules c').
Proof.
  intros n0 n d c n' d' c' H Hwf.
  unfold optimize_chain_intervalsethostorder in H.
  destruct (optimize_rules_intervalsethostorder (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. cbn [c_rules].
  exact (optimize_rules_intervalsethostorder_dynset_fresh n0 (Datatypes.length (c_rules c))
           (c_rules c) n d m'' dd'' rr'' E Hwf).
Qed.

Lemma optimize_chain_dscp_mut_st : forall h n d c n' d' c' base e p,
  optimize_chain_dscp n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) (c_rules c) ->
  eval_chain_mut_st h c' e p = eval_chain_mut_st h c e p.
Proof.
  intros h n d c n' d' c' base e p H Hfresh Hmint Hwf.
  unfold optimize_chain_dscp in H.
  destruct (optimize_rules_dscp (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain_mut_st. cbn [c_rules c_policy].
  rewrite (optimize_rules_dscp_mut_st h (Datatypes.length (c_rules c)) (c_rules c)
             n d m'' dd'' rr'' base e p E Hfresh Hmint Hwf). reflexivity.
Qed.

Lemma optimize_chain_dscp_sets_assoc_stable : forall n d c n' d' c' nm X0,
  optimize_chain_dscp n d c = (n', d', c') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X0 = assoc_str nm (sd_sets d) X0.
Proof.
  intros n d c n' d' c' nm X0 H Hnm.
  unfold optimize_chain_dscp in H.
  destruct (optimize_rules_dscp (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  exact (optimize_rules_dscp_assoc_stable (Datatypes.length (c_rules c)) n d
           (c_rules c) m'' dd'' rr'' nm X0 E Hnm).
Qed.

Lemma optimize_chain_dscp_dynset_fresh : forall n0 n d c n' d' c',
  optimize_chain_dscp n d c = (n', d', c') ->
  Forall (rule_dynset_fresh n0) (c_rules c) ->
  Forall (rule_dynset_fresh n0) (c_rules c').
Proof.
  intros n0 n d c n' d' c' H Hwf.
  unfold optimize_chain_dscp in H.
  destruct (optimize_rules_dscp (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. cbn [c_rules].
  exact (optimize_rules_dscp_dynset_fresh n0 (Datatypes.length (c_rules c))
           (c_rules c) n d m'' dd'' rr'' E Hwf).
Qed.

Lemma optimize_chain_intervalsetguarded_mut_st : forall h n d c n' d' c' base e p,
  optimize_chain_intervalsetguarded n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) (c_rules c) ->
  eval_chain_mut_st h c' e p = eval_chain_mut_st h c e p.
Proof.
  intros h n d c n' d' c' base e p H Hfresh Hmint Hwf.
  unfold optimize_chain_intervalsetguarded in H.
  destruct (optimize_rules_intervalsetguarded (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain_mut_st. cbn [c_rules c_policy].
  rewrite (optimize_rules_intervalsetguarded_mut_st h (Datatypes.length (c_rules c)) (c_rules c)
             n d m'' dd'' rr'' base e p E Hfresh Hmint Hwf). reflexivity.
Qed.

Lemma optimize_chain_intervalsetguarded_sets_assoc_stable : forall n d c n' d' c' nm X0,
  optimize_chain_intervalsetguarded n d c = (n', d', c') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X0 = assoc_str nm (sd_sets d) X0.
Proof.
  intros n d c n' d' c' nm X0 H Hnm.
  unfold optimize_chain_intervalsetguarded in H.
  destruct (optimize_rules_intervalsetguarded (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  exact (optimize_rules_intervalsetguarded_assoc_stable (Datatypes.length (c_rules c)) n d
           (c_rules c) m'' dd'' rr'' nm X0 E Hnm).
Qed.

Lemma optimize_chain_intervalsetguarded_dynset_fresh : forall n0 n d c n' d' c',
  optimize_chain_intervalsetguarded n d c = (n', d', c') ->
  Forall (rule_dynset_fresh n0) (c_rules c) ->
  Forall (rule_dynset_fresh n0) (c_rules c').
Proof.
  intros n0 n d c n' d' c' H Hwf.
  unfold optimize_chain_intervalsetguarded in H.
  destruct (optimize_rules_intervalsetguarded (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. cbn [c_rules].
  exact (optimize_rules_intervalsetguarded_dynset_fresh n0 (Datatypes.length (c_rules c))
           (c_rules c) n d m'' dd'' rr'' E Hwf).
Qed.

Lemma optimize_chain_mixedpointrangeguarded_mut_st : forall h n d c n' d' c' base e p,
  optimize_chain_mixedpointrangeguarded n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) (c_rules c) ->
  eval_chain_mut_st h c' e p = eval_chain_mut_st h c e p.
Proof.
  intros h n d c n' d' c' base e p H Hfresh Hmint Hwf.
  unfold optimize_chain_mixedpointrangeguarded in H.
  destruct (optimize_rules_mixedpointrangeguarded (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain_mut_st. cbn [c_rules c_policy].
  rewrite (optimize_rules_mixedpointrangeguarded_mut_st h (Datatypes.length (c_rules c)) (c_rules c)
             n d m'' dd'' rr'' base e p E Hfresh Hmint Hwf). reflexivity.
Qed.

Lemma optimize_chain_mixedpointrangeguarded_sets_assoc_stable : forall n d c n' d' c' nm X0,
  optimize_chain_mixedpointrangeguarded n d c = (n', d', c') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X0 = assoc_str nm (sd_sets d) X0.
Proof.
  intros n d c n' d' c' nm X0 H Hnm.
  unfold optimize_chain_mixedpointrangeguarded in H.
  destruct (optimize_rules_mixedpointrangeguarded (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  exact (optimize_rules_mixedpointrangeguarded_assoc_stable (Datatypes.length (c_rules c)) n d
           (c_rules c) m'' dd'' rr'' nm X0 E Hnm).
Qed.

Lemma optimize_chain_concatmulti_mut_st : forall h n d c n' d' c' base e p,
  optimize_chain_concatmulti n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  Forall (rule_dynset_fresh n) (c_rules c) ->
  eval_chain_mut_st h c' e p = eval_chain_mut_st h c e p.
Proof.
  intros h n d c n' d' c' base e p H Hfresh Hmint Hwf.
  unfold optimize_chain_concatmulti in H.
  destruct (optimize_rules_concatmulti n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain_mut_st. cbn [c_rules c_policy].
  rewrite (optimize_rules_concatmulti_mut_st h (c_rules c)
             n d m'' dd'' rr'' base e p E Hfresh Hmint Hwf). reflexivity.
Qed.

Lemma optimize_chain_concatmulti_sets_assoc_stable : forall n d c n' d' c' nm X0,
  optimize_chain_concatmulti n d c = (n', d', c') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X0 = assoc_str nm (sd_sets d) X0.
Proof.
  intros n d c n' d' c' nm X0 H Hnm.
  unfold optimize_chain_concatmulti in H.
  destruct (optimize_rules_concatmulti n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  exact (optimize_rules_concatmulti_assoc_stable (c_rules c) n d m'' dd'' rr'' nm X0
           E Hnm).
Qed.

Lemma optimize_chain_concatmulti_dynset_fresh : forall n0 n d c n' d' c',
  optimize_chain_concatmulti n d c = (n', d', c') ->
  Forall (rule_dynset_fresh n0) (c_rules c) ->
  Forall (rule_dynset_fresh n0) (c_rules c').
Proof.
  intros n0 n d c n' d' c' H Hwf.
  unfold optimize_chain_concatmulti in H.
  destruct (optimize_rules_concatmulti n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. cbn [c_rules].
  exact (optimize_rules_concatmulti_dynset_fresh n0 (c_rules c) n d m'' dd'' rr'' E Hwf).
Qed.

Lemma optimize_chain_datamap_mut_st : forall h n d c n' d' c' base e p,
  optimize_chain_datamap n d c = (n', d', c') ->
  (forall k, n <= k -> k < n' ->
     e_set e (setname k) = e_set (env_with_sets base d') (setname k)) ->
  (forall k, n <= k -> k < n' ->
     e_map e (mapname k) = e_map (env_with_sets base d') (mapname k)) ->
  Forall (rule_dynset_fresh n) (c_rules c) ->
  eval_chain_mut_st h c' e p = eval_chain_mut_st h c e p.
Proof.
  intros h n d c n' d' c' base e p H Hms Hmm Hwf.
  unfold optimize_chain_datamap in H.
  destruct (optimize_rules_datamap n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain_mut_st. cbn [c_rules c_policy].
  rewrite (optimize_rules_datamap_mut_st h (c_rules c)
             n d m'' dd'' rr'' base e p E Hms Hmm Hwf). reflexivity.
Qed.

Lemma optimize_chain_datamap_sets_assoc_stable : forall n d c n' d' c' nm X0,
  optimize_chain_datamap n d c = (n', d', c') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X0 = assoc_str nm (sd_sets d) X0.
Proof.
  intros n d c n' d' c' nm X0 H Hnm.
  unfold optimize_chain_datamap in H.
  destruct (optimize_rules_datamap n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  exact (optimize_rules_datamap_assoc_stable (c_rules c) n d m'' dd'' rr'' nm X0 E Hnm).
Qed.

Lemma optimize_chain_datamap_maps_assoc_stable : forall n d c n' d' c' nm X0,
  optimize_chain_datamap n d c = (n', d', c') ->
  (forall k, n <= k -> nm <> mapname k) ->
  assoc_str nm (sd_maps d') X0 = assoc_str nm (sd_maps d) X0.
Proof.
  intros n d c n' d' c' nm X0 H Hnm.
  unfold optimize_chain_datamap in H.
  destruct (optimize_rules_datamap n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  exact (optimize_rules_datamap_maps_assoc_stable (c_rules c) n d m'' dd'' rr'' nm X0
           E Hnm).
Qed.

Lemma optimize_chain_datamap_dynset_fresh : forall n0 n d c n' d' c',
  optimize_chain_datamap n d c = (n', d', c') ->
  Forall (rule_dynset_fresh n0) (c_rules c) ->
  Forall (rule_dynset_fresh n0) (c_rules c').
Proof.
  intros n0 n d c n' d' c' H Hwf.
  unfold optimize_chain_datamap in H.
  destruct (optimize_rules_datamap n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. cbn [c_rules].
  exact (optimize_rules_datamap_dynset_fresh n0 (c_rules c) n d m'' dd'' rr'' E Hwf).
Qed.

Lemma optimize_chain_dnat_mut_st : forall h n d c n' d' c' base e p,
  optimize_chain_dnat n d c = (n', d', c') ->
  (forall k, n <= k -> k < n' ->
     e_map e (mapname k) = e_map (env_with_sets base d') (mapname k)) ->
  Forall (rule_dynset_fresh n) (c_rules c) ->
  eval_chain_mut_st h c' e p = eval_chain_mut_st h c e p.
Proof.
  intros h n d c n' d' c' base e p H Hmint Hwf.
  unfold optimize_chain_dnat in H.
  destruct (optimize_rules_dnat n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain_mut_st. cbn [c_rules c_policy].
  rewrite (optimize_rules_dnat_mut_st h (c_rules c)
             n d m'' dd'' rr'' base e p E Hmint Hwf). reflexivity.
Qed.

Lemma optimize_chain_dnat_dynset_fresh : forall n0 n d c n' d' c',
  optimize_chain_dnat n d c = (n', d', c') ->
  Forall (rule_dynset_fresh n0) (c_rules c) ->
  Forall (rule_dynset_fresh n0) (c_rules c').
Proof.
  intros n0 n d c n' d' c' H Hwf.
  unfold optimize_chain_dnat in H.
  destruct (optimize_rules_dnat n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. cbn [c_rules].
  exact (optimize_rules_dnat_dynset_fresh n0 (c_rules c) n d m'' dd'' rr'' E Hwf).
Qed.

Lemma optimize_chain_snat_mut_st : forall h n d c n' d' c' base e p,
  optimize_chain_snat n d c = (n', d', c') ->
  (forall k, n <= k -> k < n' ->
     e_map e (mapname k) = e_map (env_with_sets base d') (mapname k)) ->
  Forall (rule_dynset_fresh n) (c_rules c) ->
  eval_chain_mut_st h c' e p = eval_chain_mut_st h c e p.
Proof.
  intros h n d c n' d' c' base e p H Hmint Hwf.
  unfold optimize_chain_snat in H.
  destruct (optimize_rules_snat n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain_mut_st. cbn [c_rules c_policy].
  rewrite (optimize_rules_snat_mut_st h (c_rules c)
             n d m'' dd'' rr'' base e p E Hmint Hwf). reflexivity.
Qed.

Lemma optimize_chain_snat_dynset_fresh : forall n0 n d c n' d' c',
  optimize_chain_snat n d c = (n', d', c') ->
  Forall (rule_dynset_fresh n0) (c_rules c) ->
  Forall (rule_dynset_fresh n0) (c_rules c').
Proof.
  intros n0 n d c n' d' c' H Hwf.
  unfold optimize_chain_snat in H.
  destruct (optimize_rules_snat n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. cbn [c_rules].
  exact (optimize_rules_snat_dynset_fresh n0 (c_rules c) n d m'' dd'' rr'' E Hwf).
Qed.

Lemma optimize_chain_vmapguarded_mut_st : forall h n d c n' d' c' base e p,
  optimize_chain_vmapguarded n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  (forall k, n <= k -> k < n' ->
     e_vmap e (vmapname k) = e_vmap (env_with_sets base d') (vmapname k)) ->
  eval_chain_mut_st h c' e p = eval_chain_mut_st h c e p.
Proof.
  intros h n d c n' d' c' base e p H Hfresh Hmint.
  unfold optimize_chain_vmapguarded in H.
  destruct (optimize_rules_vmapguarded (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain_mut_st. cbn [c_rules c_policy].
  rewrite (optimize_rules_vmapguarded_mut_st h (Datatypes.length (c_rules c)) (c_rules c)
             n d m'' dd'' rr'' base e p E Hfresh Hmint). reflexivity.
Qed.

Lemma optimize_chain_vmapguarded_vmaps_assoc_stable : forall n d c n' d' c' nm X0,
  optimize_chain_vmapguarded n d c = (n', d', c') ->
  (forall k, n <= k -> nm <> vmapname k) ->
  assoc_str nm (sd_vmaps d') X0 = assoc_str nm (sd_vmaps d) X0.
Proof.
  intros n d c n' d' c' nm X0 H Hnm.
  unfold optimize_chain_vmapguarded in H.
  destruct (optimize_rules_vmapguarded (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  exact (optimize_rules_vmapguarded_assoc_stable (Datatypes.length (c_rules c)) n d
           (c_rules c) m'' dd'' rr'' nm X0 E Hnm).
Qed.

Lemma optimize_chain_dscpvmap_mut_st : forall h n d c n' d' c' base e p,
  optimize_chain_dscpvmap n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  (forall k, n <= k -> k < n' ->
     e_vmap e (vmapname k) = e_vmap (env_with_sets base d') (vmapname k)) ->
  eval_chain_mut_st h c' e p = eval_chain_mut_st h c e p.
Proof.
  intros h n d c n' d' c' base e p H Hfresh Hmint.
  unfold optimize_chain_dscpvmap in H.
  destruct (optimize_rules_dscpvmap (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain_mut_st. cbn [c_rules c_policy].
  rewrite (optimize_rules_dscpvmap_mut_st h (Datatypes.length (c_rules c)) (c_rules c)
             n d m'' dd'' rr'' base e p E Hfresh Hmint). reflexivity.
Qed.

Lemma optimize_chain_dscpvmap_vmaps_assoc_stable : forall n d c n' d' c' nm X0,
  optimize_chain_dscpvmap n d c = (n', d', c') ->
  (forall k, n <= k -> nm <> vmapname k) ->
  assoc_str nm (sd_vmaps d') X0 = assoc_str nm (sd_vmaps d) X0.
Proof.
  intros n d c n' d' c' nm X0 H Hnm.
  unfold optimize_chain_dscpvmap in H.
  destruct (optimize_rules_dscpvmap (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  exact (optimize_rules_dscpvmap_assoc_stable (Datatypes.length (c_rules c)) n d
           (c_rules c) m'' dd'' rr'' nm X0 E Hnm).
Qed.

Lemma optimize_chain_vmap_mut_st : forall h n d c n' d' c' base e p,
  optimize_chain_vmap n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  (forall k, n <= k -> k < n' ->
     e_vmap e (vmapname k) = e_vmap (env_with_sets base d') (vmapname k)) ->
  eval_chain_mut_st h c' e p = eval_chain_mut_st h c e p.
Proof.
  intros h n d c n' d' c' base e p H Hfresh Hmint.
  unfold optimize_chain_vmap in H.
  destruct (optimize_rules_vmap (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain_mut_st. cbn [c_rules c_policy].
  rewrite (optimize_rules_vmap_mut_st h (Datatypes.length (c_rules c)) (c_rules c)
             n d m'' dd'' rr'' base e p E Hfresh Hmint). reflexivity.
Qed.

Lemma optimize_chain_vmap_vmaps_assoc_stable : forall n d c n' d' c' nm X0,
  optimize_chain_vmap n d c = (n', d', c') ->
  (forall k, n <= k -> nm <> vmapname k) ->
  assoc_str nm (sd_vmaps d') X0 = assoc_str nm (sd_vmaps d) X0.
Proof.
  intros n d c n' d' c' nm X0 H Hnm.
  unfold optimize_chain_vmap in H.
  destruct (optimize_rules_vmap (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  exact (optimize_rules_vmap_assoc_stable (Datatypes.length (c_rules c)) n d
           (c_rules c) m'' dd'' rr'' nm X0 E Hnm).
Qed.

Lemma optimize_chain_vmap_sets : forall n d c n' d' c',
  optimize_chain_vmap n d c = (n', d', c') -> sd_sets d' = sd_sets d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_vmap in H.
  destruct (optimize_rules_vmap (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  exact (optimize_rules_vmap_sets (Datatypes.length (c_rules c)) n d (c_rules c)
           m'' dd'' rr'' E).
Qed.

Lemma optimize_chain_vmap_maps : forall n d c n' d' c',
  optimize_chain_vmap n d c = (n', d', c') -> sd_maps d' = sd_maps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_vmap in H.
  destruct (optimize_rules_vmap (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  exact (optimize_rules_vmap_maps (Datatypes.length (c_rules c)) n d (c_rules c)
           m'' dd'' rr'' E).
Qed.

Lemma optimize_chain_vmap_mono : forall n d c n' d' c',
  optimize_chain_vmap n d c = (n', d', c') -> n <= n'.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_vmap in H.
  destruct (optimize_rules_vmap (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  injection H as Hn Hd Hc. subst m'' dd''.
  exact (optimize_rules_vmap_mono _ _ _ _ _ _ _ E).
Qed.

(** absorb / ctmask at the chain level. *)
Lemma absorb_chain_mut_st : forall h c e p,
  eval_chain_mut_st h (absorb_chain c) e p = eval_chain_mut_st h c e p.
Proof.
  intros h c e p. unfold eval_chain_mut_st, absorb_chain. cbn [c_rules c_policy].
  rewrite optimize_rules_absorb_mut_st. reflexivity.
Qed.

Lemma ctmask_chain_mut_st : forall h c e p,
  eval_chain_mut_st h (ctmask_chain c) e p = eval_chain_mut_st h c e p.
Proof.
  intros h c e p. unfold eval_chain_mut_st, ctmask_chain. cbn [c_rules c_policy].
  rewrite optimize_rules_ctmask_mut_st. reflexivity.
Qed.

Lemma ctmask_chain_dynset_fresh : forall n0 c,
  Forall (rule_dynset_fresh n0) (c_rules c) ->
  Forall (rule_dynset_fresh n0) (c_rules (ctmask_chain c)).
Proof.
  intros n0 c Hwf. unfold ctmask_chain. cbn [c_rules].
  exact (optimize_rules_ctmask_dynset_fresh n0 (Datatypes.length (c_rules c))
           (c_rules c) Hwf).
Qed.

(** ** Part G: the COMPOSED effect-level pipeline theorem.

    The 18-stage [Optimize_Table.optimize_table], certified against the
    FULL-STATE effect-observing [eval_chain_mut_st h]: under the deployed
    environment (the synthesised declarations in scope), the optimised chain
    and the input chain produce the SAME verdict AND the SAME resulting
    (env, packet) state, for every hook, base environment and packet. *)
Theorem optimize_table_mut_st_correct_uncond_gen : forall h n d c n' d' c' base p,
  optimize_table n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k)  (map fst (sd_sets  d))) ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  (forall k, n <= k -> ~ In (mapname k)  (map fst (sd_maps  d))) ->
  Forall (rule_dynset_fresh n) (c_rules (optimize_chain c)) ->
  eval_chain_mut_st h c' (env_with_sets base d') p
  = eval_chain_mut_st h c (env_with_sets base d') p.
Proof.
  intros h n d c n' d' c' base p H Hfs Hfv Hfm Hwf.
  unfold optimize_table in H.
  destruct (optimize_chain_absorb n d (optimize_chain c)) as [[nA dA] cA] eqn:EA.
  pose proof (optimize_chain_absorb_eq n d (optimize_chain c)) as Habs.
  rewrite EA in Habs. injection Habs as HnA HdA HcA. subst nA dA.
  destruct (optimize_chain_ctmask n d cA) as [[nT dT] cT] eqn:ET.
  pose proof (optimize_chain_ctmask_eq n d cA) as Hct.
  rewrite ET in Hct. injection Hct as HnT HdT HcT. subst nT dT.
  assert (HwfA : Forall (rule_dynset_fresh n) (c_rules cA))
    by (rewrite HcA; apply absorb_chain_Forall; exact Hwf).
  assert (HwfT : Forall (rule_dynset_fresh n) (c_rules cT))
    by (rewrite HcT; apply ctmask_chain_dynset_fresh; exact HwfA).
  destruct (optimize_chain_dnat n d cT) as [[nD dD] cD] eqn:ED.
  destruct (optimize_chain_snat nD dD cD) as [[nS dS] cS] eqn:ES.
  destruct (optimize_chain_valueset nS dS cS) as [[n1 d1] c1] eqn:E1.
  destruct (optimize_chain_concatmulti n1 d1 c1) as [[nK dK] cK] eqn:EK.
  destruct (optimize_chain_datamap nK dK cK) as [[nM dM] cM] eqn:EM.
  destruct (optimize_chain_concat nM dM cM) as [[n2 d2] c2] eqn:E2.
  destruct (optimize_chain_concatguarded n2 d2 c2) as [[nG dG] cG] eqn:EG.
  destruct (optimize_chain_setguarded nG dG cG) as [[nGs dGs] cGs] eqn:EGs.
  destruct (optimize_chain_intervalset nGs dGs cGs) as [[nI dI] cI] eqn:EI.
  destruct (optimize_chain_intervalsethostorder nI dI cI) as [[nIt dIt] cIt] eqn:EIt.
  destruct (optimize_chain_dscp nIt dIt cIt) as [[nDs dDs] cDs] eqn:EDs.
  destruct (optimize_chain_intervalsetguarded nDs dDs cDs) as [[nIg dIg] cIg] eqn:EIg.
  destruct (optimize_chain_mixedpointrangeguarded nIg dIg cIg) as [[nMx dMx] cMx] eqn:EMx.
  destruct (optimize_chain_vmapguarded nMx dMx cMx) as [[nVg dVg] cVg] eqn:EVg.
  destruct (optimize_chain_dscpvmap nVg dVg cVg) as [[nDv dDv] cDv] eqn:EDv.
  (* counter monotonicity chain *)
  pose proof (optimize_chain_dnat_mono n d cT nD dD cD ED) as HmnD.
  pose proof (optimize_chain_snat_mono nD dD cD nS dS cS ES) as HmnS.
  pose proof (optimize_chain_valueset_mono nS dS cS n1 d1 c1 E1) as Hmn1.
  pose proof (optimize_chain_concatmulti_mono n1 d1 c1 nK dK cK EK) as HmnK.
  pose proof (optimize_chain_datamap_mono nK dK cK nM dM cM EM) as HmnM.
  pose proof (optimize_chain_concat_mono nM dM cM n2 d2 c2 E2) as Hmn2.
  pose proof (optimize_chain_concatguarded_mono n2 d2 c2 nG dG cG EG) as HmnG.
  pose proof (optimize_chain_setguarded_mono nG dG cG nGs dGs cGs EGs) as HmnGs.
  pose proof (optimize_chain_intervalset_mono nGs dGs cGs nI dI cI EI) as HmnI.
  pose proof (optimize_chain_intervalsethostorder_mono nI dI cI nIt dIt cIt EIt) as HmnIt.
  pose proof (optimize_chain_dscp_mono nIt dIt cIt nDs dDs cDs EDs) as HmnDs.
  pose proof (optimize_chain_intervalsetguarded_mono nDs dDs cDs nIg dIg cIg EIg) as HmnIg.
  pose proof (optimize_chain_mixedpointrangeguarded_mono nIg dIg cIg nMx dMx cMx EMx) as HmnMx.
  pose proof (optimize_chain_vmapguarded_mono nMx dMx cMx nVg dVg cVg EVg) as HmnVg.
  pose proof (optimize_chain_dscpvmap_mono nVg dVg cVg nDv dDv cDv EDv) as HmnDv.
  pose proof (optimize_chain_vmap_mono nDv dDv cDv n' d' c' H) as Hmn'.
  (* setname decl-freshness threading (as in the verdict-level harness) *)
  assert (Hfs_D : forall k, nD <= k -> ~ In (setname k) (map fst (sd_sets dD))).
  { intros k Hk. rewrite (optimize_chain_dnat_sets n d cT nD dD cD ED).
    apply Hfs. lia. }
  assert (Hfs_S : forall k, nS <= k -> ~ In (setname k) (map fst (sd_sets dS))).
  { intros k Hk. rewrite (optimize_chain_snat_sets nD dD cD nS dS cS ES).
    apply Hfs_D. lia. }
  pose proof (optimize_chain_valueset_fresh_setname nS dS cS n1 d1 c1 E1 Hfs_S) as Hfs1.
  pose proof (optimize_chain_concatmulti_fresh_setname n1 d1 c1 nK dK cK EK Hfs1) as HfsK.
  pose proof (optimize_chain_datamap_fresh_setname nK dK cK nM dM cM EM HfsK) as HfsM.
  pose proof (optimize_chain_concat_fresh_setname nM dM cM n2 d2 c2 E2 HfsM) as Hfs2.
  pose proof (optimize_chain_concatguarded_fresh_setname n2 d2 c2 nG dG cG EG Hfs2) as HfsG.
  pose proof (optimize_chain_setguarded_fresh_setname nG dG cG nGs dGs cGs EGs HfsG) as HfsGs.
  pose proof (optimize_chain_intervalset_fresh_setname nGs dGs cGs nI dI cI EI HfsGs) as HfsI.
  pose proof (optimize_chain_intervalsethostorder_fresh_setname nI dI cI nIt dIt cIt EIt HfsI) as HfsIt.
  pose proof (optimize_chain_dscp_fresh_setname nIt dIt cIt nDs dDs cDs EDs HfsIt) as HfsDs.
  pose proof (optimize_chain_intervalsetguarded_fresh_setname nDs dDs cDs nIg dIg cIg EIg HfsDs) as HfsIg.
  (* vmapname decl-freshness threading *)
  assert (Hfv_D : forall k, nD <= k -> ~ In (vmapname k) (map fst (sd_vmaps dD))).
  { intros k Hk. rewrite (optimize_chain_dnat_vmaps n d cT nD dD cD ED).
    apply Hfv. lia. }
  assert (Hfv_S : forall k, nS <= k -> ~ In (vmapname k) (map fst (sd_vmaps dS))).
  { intros k Hk. rewrite (optimize_chain_snat_vmaps nD dD cD nS dS cS ES).
    apply Hfv_D. lia. }
  assert (HvmG : sd_vmaps dG = sd_vmaps dS).
  { rewrite (optimize_chain_concatguarded_vmaps n2 d2 c2 nG dG cG EG).
    rewrite (optimize_chain_concat_vmaps nM dM cM n2 d2 c2 E2).
    rewrite (optimize_chain_datamap_vmaps nK dK cK nM dM cM EM).
    rewrite (optimize_chain_concatmulti_vmaps n1 d1 c1 nK dK cK EK).
    apply (optimize_chain_valueset_vmaps nS dS cS n1 d1 c1 E1). }
  assert (HvmMx : sd_vmaps dMx = sd_vmaps dS).
  { rewrite (optimize_chain_mixedpointrangeguarded_vmaps nIg dIg cIg nMx dMx cMx EMx).
    rewrite (optimize_chain_intervalsetguarded_vmaps nDs dDs cDs nIg dIg cIg EIg).
    rewrite (optimize_chain_dscp_vmaps nIt dIt cIt nDs dDs cDs EDs).
    rewrite (optimize_chain_intervalsethostorder_vmaps nI dI cI nIt dIt cIt EIt).
    rewrite (optimize_chain_intervalset_vmaps nGs dGs cGs nI dI cI EI).
    rewrite (optimize_chain_setguarded_vmaps nG dG cG nGs dGs cGs EGs).
    exact HvmG. }
  assert (HfvMx : forall k, nMx <= k -> ~ In (vmapname k) (map fst (sd_vmaps dMx))).
  { intros k Hk. rewrite HvmMx. apply Hfv_S. lia. }
  pose proof (optimize_chain_vmapguarded_fresh_vmapname nMx dMx cMx nVg dVg cVg EVg HfvMx) as HfvVg.
  pose proof (optimize_chain_dscpvmap_fresh_vmapname nVg dVg cVg nDv dDv cDv EDv HfvVg) as HfvDv.
  (* dynset write-target freshness threading (all at the fixed seed [n]) *)
  assert (HwfD : Forall (rule_dynset_fresh n) (c_rules cD))
    by (exact (optimize_chain_dnat_dynset_fresh n n d cT nD dD cD ED HwfT)).
  assert (HwfS : Forall (rule_dynset_fresh n) (c_rules cS))
    by (exact (optimize_chain_snat_dynset_fresh n nD dD cD nS dS cS ES HwfD)).
  assert (Hwf1 : Forall (rule_dynset_fresh n) (c_rules c1))
    by (exact (optimize_chain_valueset_dynset_fresh n nS dS cS n1 d1 c1 E1 HwfS)).
  assert (HwfK : Forall (rule_dynset_fresh n) (c_rules cK))
    by (exact (optimize_chain_concatmulti_dynset_fresh n n1 d1 c1 nK dK cK EK Hwf1)).
  assert (HwfM : Forall (rule_dynset_fresh n) (c_rules cM))
    by (exact (optimize_chain_datamap_dynset_fresh n nK dK cK nM dM cM EM HwfK)).
  assert (Hwf2 : Forall (rule_dynset_fresh n) (c_rules c2))
    by (exact (optimize_chain_concat_dynset_fresh n nM dM cM n2 d2 c2 E2 HwfM)).
  assert (HwfG : Forall (rule_dynset_fresh n) (c_rules cG))
    by (exact (optimize_chain_concatguarded_dynset_fresh n n2 d2 c2 nG dG cG EG Hwf2)).
  assert (HwfGs : Forall (rule_dynset_fresh n) (c_rules cGs))
    by (exact (optimize_chain_setguarded_dynset_fresh n nG dG cG nGs dGs cGs EGs HwfG)).
  assert (HwfI : Forall (rule_dynset_fresh n) (c_rules cI))
    by (exact (optimize_chain_intervalset_dynset_fresh n nGs dGs cGs nI dI cI EI HwfGs)).
  assert (HwfIt : Forall (rule_dynset_fresh n) (c_rules cIt))
    by (exact (optimize_chain_intervalsethostorder_dynset_fresh n nI dI cI nIt dIt cIt EIt HwfI)).
  assert (HwfDs : Forall (rule_dynset_fresh n) (c_rules cDs))
    by (exact (optimize_chain_dscp_dynset_fresh n nIt dIt cIt nDs dDs cDs EDs HwfIt)).
  assert (HwfIg : Forall (rule_dynset_fresh n) (c_rules cIg))
    by (exact (optimize_chain_intervalsetguarded_dynset_fresh n nDs dDs cDs nIg dIg cIg EIg HwfDs)).
  (* per-stage weakening of the write-target freshness to the stage counter *)
  assert (Wk : forall m rs, n <= m -> Forall (rule_dynset_fresh n) rs ->
                Forall (rule_dynset_fresh m) rs).
  { intros m rs Hle Hf. eapply Forall_impl; [| exact Hf].
    intros r Hr. exact (rule_dynset_fresh_mono n m r Hle Hr). }
  (* the SETS declaration ladder: the vmap family leaves sd_sets untouched, and
     each set-minting stage preserves the lookup of every EARLIER-minted name *)
  assert (HsetsTop : sd_sets d' = sd_sets dMx).
  { rewrite (optimize_chain_vmap_sets nDv dDv cDv n' d' c' H).
    rewrite (optimize_chain_dscpvmap_sets nVg dVg cVg nDv dDv cDv EDv).
    apply (optimize_chain_vmapguarded_sets nMx dMx cMx nVg dVg cVg EVg). }
  (* the MAPS declaration ladder *)
  assert (HmapsTop : sd_maps d' = sd_maps dM).
  { rewrite (optimize_chain_vmap_maps nDv dDv cDv n' d' c' H).
    rewrite (optimize_chain_dscpvmap_maps nVg dVg cVg nDv dDv cDv EDv).
    rewrite (optimize_chain_vmapguarded_maps nMx dMx cMx nVg dVg cVg EVg).
    rewrite (optimize_chain_mixedpointrangeguarded_maps nIg dIg cIg nMx dMx cMx EMx).
    rewrite (optimize_chain_intervalsetguarded_maps nDs dDs cDs nIg dIg cIg EIg).
    rewrite (optimize_chain_dscp_maps nIt dIt cIt nDs dDs cDs EDs).
    rewrite (optimize_chain_intervalsethostorder_maps nI dI cI nIt dIt cIt EIt).
    rewrite (optimize_chain_intervalset_maps nGs dGs cGs nI dI cI EI).
    rewrite (optimize_chain_setguarded_maps nG dG cG nGs dGs cGs EGs).
    rewrite (optimize_chain_concatguarded_maps n2 d2 c2 nG dG cG EG).
    apply (optimize_chain_concat_maps nM dM cM n2 d2 c2 E2). }
  set (E := env_with_sets base d') in *.
  (* rewrite the pipeline right-to-left, discharging each stage's minted-name
     resolution from the declaration ladders *)
  rewrite (optimize_chain_vmap_mut_st h nDv dDv cDv n' d' c' base E p H HfvDv
             ltac:(intros k Hk Hk'; reflexivity)).
  rewrite (optimize_chain_dscpvmap_mut_st h nVg dVg cVg nDv dDv cDv base E p EDv HfvVg
             ltac:(intros k Hk Hk'; unfold E; rewrite !e_vmap_env_with_sets;
                   rewrite (optimize_chain_vmap_vmaps_assoc_stable nDv dDv cDv n' d' c'
                              (vmapname k) _ H
                              ltac:(intros j Hj Heq; apply vmapname_inj in Heq; lia));
                   reflexivity)).
  rewrite (optimize_chain_vmapguarded_mut_st h nMx dMx cMx nVg dVg cVg base E p EVg HfvMx
             ltac:(intros k Hk Hk'; unfold E; rewrite !e_vmap_env_with_sets;
                   rewrite (optimize_chain_vmap_vmaps_assoc_stable nDv dDv cDv n' d' c'
                              (vmapname k) _ H
                              ltac:(intros j Hj Heq; apply vmapname_inj in Heq; lia));
                   rewrite (optimize_chain_dscpvmap_vmaps_assoc_stable nVg dVg cVg nDv dDv cDv
                              (vmapname k) _ EDv
                              ltac:(intros j Hj Heq; apply vmapname_inj in Heq; lia));
                   reflexivity)).
  rewrite (optimize_chain_mixedpointrangeguarded_mut_st h nIg dIg cIg nMx dMx cMx base E p
             EMx HfsIg
             ltac:(intros k Hk Hk'; unfold E; rewrite !e_set_declared;
                   rewrite HsetsTop; reflexivity)
             (Wk nIg (c_rules cIg) ltac:(lia) HwfIg)).
  rewrite (optimize_chain_intervalsetguarded_mut_st h nDs dDs cDs nIg dIg cIg base E p
             EIg HfsDs
             ltac:(intros k Hk Hk'; unfold E; rewrite !e_set_declared;
                   rewrite HsetsTop;
                   rewrite (optimize_chain_mixedpointrangeguarded_sets_assoc_stable
                              nIg dIg cIg nMx dMx cMx (setname k) _ EMx
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   reflexivity)
             (Wk nDs (c_rules cDs) ltac:(lia) HwfDs)).
  rewrite (optimize_chain_dscp_mut_st h nIt dIt cIt nDs dDs cDs base E p EDs HfsIt
             ltac:(intros k Hk Hk'; unfold E; rewrite !e_set_declared;
                   rewrite HsetsTop;
                   rewrite (optimize_chain_mixedpointrangeguarded_sets_assoc_stable
                              nIg dIg cIg nMx dMx cMx (setname k) _ EMx
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalsetguarded_sets_assoc_stable
                              nDs dDs cDs nIg dIg cIg (setname k) _ EIg
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   reflexivity)
             (Wk nIt (c_rules cIt) ltac:(lia) HwfIt)).
  rewrite (optimize_chain_intervalsethostorder_mut_st h nI dI cI nIt dIt cIt base E p
             EIt HfsI
             ltac:(intros k Hk Hk'; unfold E; rewrite !e_set_declared;
                   rewrite HsetsTop;
                   rewrite (optimize_chain_mixedpointrangeguarded_sets_assoc_stable
                              nIg dIg cIg nMx dMx cMx (setname k) _ EMx
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalsetguarded_sets_assoc_stable
                              nDs dDs cDs nIg dIg cIg (setname k) _ EIg
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_dscp_sets_assoc_stable
                              nIt dIt cIt nDs dDs cDs (setname k) _ EDs
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   reflexivity)
             (Wk nI (c_rules cI) ltac:(lia) HwfI)).
  rewrite (optimize_chain_intervalset_mut_st h nGs dGs cGs nI dI cI base E p EI HfsGs
             ltac:(intros k Hk Hk'; unfold E; rewrite !e_set_declared;
                   rewrite HsetsTop;
                   rewrite (optimize_chain_mixedpointrangeguarded_sets_assoc_stable
                              nIg dIg cIg nMx dMx cMx (setname k) _ EMx
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalsetguarded_sets_assoc_stable
                              nDs dDs cDs nIg dIg cIg (setname k) _ EIg
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_dscp_sets_assoc_stable
                              nIt dIt cIt nDs dDs cDs (setname k) _ EDs
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalsethostorder_sets_assoc_stable
                              nI dI cI nIt dIt cIt (setname k) _ EIt
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   reflexivity)
             (Wk nGs (c_rules cGs) ltac:(lia) HwfGs)).
  rewrite (optimize_chain_setguarded_mut_st h nG dG cG nGs dGs cGs base E p EGs HfsG
             ltac:(intros k Hk Hk'; unfold E; rewrite !e_set_declared;
                   rewrite HsetsTop;
                   rewrite (optimize_chain_mixedpointrangeguarded_sets_assoc_stable
                              nIg dIg cIg nMx dMx cMx (setname k) _ EMx
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalsetguarded_sets_assoc_stable
                              nDs dDs cDs nIg dIg cIg (setname k) _ EIg
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_dscp_sets_assoc_stable
                              nIt dIt cIt nDs dDs cDs (setname k) _ EDs
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalsethostorder_sets_assoc_stable
                              nI dI cI nIt dIt cIt (setname k) _ EIt
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalset_sets_assoc_stable
                              nGs dGs cGs nI dI cI (setname k) _ EI
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   reflexivity)
             (Wk nG (c_rules cG) ltac:(lia) HwfG)).
  rewrite (optimize_chain_concatguarded_mut_st h n2 d2 c2 nG dG cG base E p EG Hfs2
             ltac:(intros k Hk Hk'; unfold E; rewrite !e_set_declared;
                   rewrite HsetsTop;
                   rewrite (optimize_chain_mixedpointrangeguarded_sets_assoc_stable
                              nIg dIg cIg nMx dMx cMx (setname k) _ EMx
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalsetguarded_sets_assoc_stable
                              nDs dDs cDs nIg dIg cIg (setname k) _ EIg
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_dscp_sets_assoc_stable
                              nIt dIt cIt nDs dDs cDs (setname k) _ EDs
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalsethostorder_sets_assoc_stable
                              nI dI cI nIt dIt cIt (setname k) _ EIt
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalset_sets_assoc_stable
                              nGs dGs cGs nI dI cI (setname k) _ EI
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_setguarded_sets_assoc_stable
                              nG dG cG nGs dGs cGs (setname k) _ EGs
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   reflexivity)
             (Wk n2 (c_rules c2) ltac:(lia) Hwf2)).
  rewrite (optimize_chain_concat_mut_st h nM dM cM n2 d2 c2 base E p E2 HfsM
             ltac:(intros k Hk Hk'; unfold E; rewrite !e_set_declared;
                   rewrite HsetsTop;
                   rewrite (optimize_chain_mixedpointrangeguarded_sets_assoc_stable
                              nIg dIg cIg nMx dMx cMx (setname k) _ EMx
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalsetguarded_sets_assoc_stable
                              nDs dDs cDs nIg dIg cIg (setname k) _ EIg
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_dscp_sets_assoc_stable
                              nIt dIt cIt nDs dDs cDs (setname k) _ EDs
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalsethostorder_sets_assoc_stable
                              nI dI cI nIt dIt cIt (setname k) _ EIt
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalset_sets_assoc_stable
                              nGs dGs cGs nI dI cI (setname k) _ EI
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_setguarded_sets_assoc_stable
                              nG dG cG nGs dGs cGs (setname k) _ EGs
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_concatguarded_sets_assoc_stable
                              n2 d2 c2 nG dG cG (setname k) _ EG
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   reflexivity)
             (Wk nM (c_rules cM) ltac:(lia) HwfM)).
  rewrite (optimize_chain_datamap_mut_st h nK dK cK nM dM cM base E p EM
             ltac:(intros k Hk Hk'; unfold E; rewrite !e_set_declared;
                   rewrite HsetsTop;
                   rewrite (optimize_chain_mixedpointrangeguarded_sets_assoc_stable
                              nIg dIg cIg nMx dMx cMx (setname k) _ EMx
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalsetguarded_sets_assoc_stable
                              nDs dDs cDs nIg dIg cIg (setname k) _ EIg
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_dscp_sets_assoc_stable
                              nIt dIt cIt nDs dDs cDs (setname k) _ EDs
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalsethostorder_sets_assoc_stable
                              nI dI cI nIt dIt cIt (setname k) _ EIt
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalset_sets_assoc_stable
                              nGs dGs cGs nI dI cI (setname k) _ EI
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_setguarded_sets_assoc_stable
                              nG dG cG nGs dGs cGs (setname k) _ EGs
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_concatguarded_sets_assoc_stable
                              n2 d2 c2 nG dG cG (setname k) _ EG
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_concat_sets_assoc_stable
                              nM dM cM n2 d2 c2 (setname k) _ E2
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   reflexivity)
             ltac:(intros k Hk Hk'; unfold E; rewrite !e_map_env_with_sets;
                   rewrite HmapsTop; reflexivity)
             (Wk nK (c_rules cK) ltac:(lia) HwfK)).
  rewrite (optimize_chain_concatmulti_mut_st h n1 d1 c1 nK dK cK base E p EK Hfs1
             ltac:(intros k Hk Hk'; unfold E; rewrite !e_set_declared;
                   rewrite HsetsTop;
                   rewrite (optimize_chain_mixedpointrangeguarded_sets_assoc_stable
                              nIg dIg cIg nMx dMx cMx (setname k) _ EMx
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalsetguarded_sets_assoc_stable
                              nDs dDs cDs nIg dIg cIg (setname k) _ EIg
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_dscp_sets_assoc_stable
                              nIt dIt cIt nDs dDs cDs (setname k) _ EDs
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalsethostorder_sets_assoc_stable
                              nI dI cI nIt dIt cIt (setname k) _ EIt
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalset_sets_assoc_stable
                              nGs dGs cGs nI dI cI (setname k) _ EI
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_setguarded_sets_assoc_stable
                              nG dG cG nGs dGs cGs (setname k) _ EGs
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_concatguarded_sets_assoc_stable
                              n2 d2 c2 nG dG cG (setname k) _ EG
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_concat_sets_assoc_stable
                              nM dM cM n2 d2 c2 (setname k) _ E2
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_datamap_sets_assoc_stable
                              nK dK cK nM dM cM (setname k) _ EM
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   reflexivity)
             (Wk n1 (c_rules c1) ltac:(lia) Hwf1)).
  rewrite (optimize_chain_valueset_mut_st h nS dS cS n1 d1 c1 base E p E1 Hfs_S
             ltac:(intros k Hk Hk'; unfold E; rewrite !e_set_declared;
                   rewrite HsetsTop;
                   rewrite (optimize_chain_mixedpointrangeguarded_sets_assoc_stable
                              nIg dIg cIg nMx dMx cMx (setname k) _ EMx
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalsetguarded_sets_assoc_stable
                              nDs dDs cDs nIg dIg cIg (setname k) _ EIg
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_dscp_sets_assoc_stable
                              nIt dIt cIt nDs dDs cDs (setname k) _ EDs
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalsethostorder_sets_assoc_stable
                              nI dI cI nIt dIt cIt (setname k) _ EIt
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_intervalset_sets_assoc_stable
                              nGs dGs cGs nI dI cI (setname k) _ EI
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_setguarded_sets_assoc_stable
                              nG dG cG nGs dGs cGs (setname k) _ EGs
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_concatguarded_sets_assoc_stable
                              n2 d2 c2 nG dG cG (setname k) _ EG
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_concat_sets_assoc_stable
                              nM dM cM n2 d2 c2 (setname k) _ E2
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_datamap_sets_assoc_stable
                              nK dK cK nM dM cM (setname k) _ EM
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   rewrite (optimize_chain_concatmulti_sets_assoc_stable
                              n1 d1 c1 nK dK cK (setname k) _ EK
                              ltac:(intros j Hj Heq; apply setname_inj in Heq; lia));
                   reflexivity)
             (Wk nS (c_rules cS) ltac:(lia) HwfS)).
  rewrite (optimize_chain_snat_mut_st h nD dD cD nS dS cS base E p ES
             ltac:(intros k Hk Hk'; unfold E; rewrite !e_map_env_with_sets;
                   rewrite HmapsTop;
                   rewrite (optimize_chain_datamap_maps_assoc_stable
                              nK dK cK nM dM cM (mapname k) _ EM
                              ltac:(intros j Hj Heq; apply mapname_inj in Heq; lia));
                   rewrite (optimize_chain_concatmulti_maps n1 d1 c1 nK dK cK EK);
                   rewrite (optimize_chain_valueset_maps nS dS cS n1 d1 c1 E1);
                   reflexivity)
             (Wk nD (c_rules cD) ltac:(lia) HwfD)).
  rewrite (optimize_chain_dnat_mut_st h n d cT nD dD cD base E p ED
             ltac:(intros k Hk Hk'; unfold E; rewrite !e_map_env_with_sets;
                   rewrite HmapsTop;
                   rewrite (optimize_chain_datamap_maps_assoc_stable
                              nK dK cK nM dM cM (mapname k) _ EM
                              ltac:(intros j Hj Heq; apply mapname_inj in Heq; lia));
                   rewrite (optimize_chain_concatmulti_maps n1 d1 c1 nK dK cK EK);
                   rewrite (optimize_chain_valueset_maps nS dS cS n1 d1 c1 E1);
                   rewrite (optimize_chain_snat_maps_assoc_stable nD dD cD nS dS cS
                              (mapname k) _ ES
                              ltac:(intros j Hj Heq; apply mapname_inj in Heq; lia));
                   reflexivity)
             HwfT).
  rewrite HcT, (ctmask_chain_mut_st h cA E p).
  rewrite HcA, (absorb_chain_mut_st h (optimize_chain c) E p).
  apply optimize_chain_mut_st.
Qed.

(** ** HEADLINE (optimizer EFFECT axis; see proof/THEOREMS.md).

    THE effect-level pipeline guarantee, with NO hypothesis on the input chain:
    running the SHIPPED unconditional optimizer [optimize_table_uncond] and
    evaluating its output in the deployed environment (the synthesised
    declarations [d'] in scope) yields, at EVERY netfilter hook, for EVERY base
    environment and EVERY packet, EXACTLY the original chain's verdict AND
    resulting (env, packet) state under the FULL-STATE effect-observing chain
    semantics [eval_chain_mut_st h] — the single per-rule fold that threads
    packet meta/ct writes, dynset env writes, the notrack latch, limiter/
    quota/connlimit consumption and the NAT data plane at their own body
    positions, with nothing of the threaded state dropped from the observable.

    A pipeline stage can therefore no longer preserve every verdict while
    altering a write a later hook observes: BOTH halves of the state ARE the
    theorem's observable — the env half is what [seq_eval_env] carries to the
    next packet, the packet half (e.g. a `meta mark set`) is what
    [eval_ruleset_u]'s priority dispatch hands to the next base chain at the
    same hook.  (Freshness is discharged BY CONSTRUCTION: [seed_start] mints
    past every name the chain reads AND every dynset write target, so no rule
    can shadow or clobber a minted declaration.  Jump scope: see the header —
    the flat fold skips callees, so this composes with multi-chain dispatch on
    the transfer-free license.) *)
Theorem optimize_table_uncond_mut_st_correct : forall h c base p n' d' c',
  optimize_table_uncond c = (n', d', c') ->
  eval_chain_mut_st h c' (env_with_sets base d') p
  = eval_chain_mut_st h c (env_with_sets base d') p.
Proof.
  intros h c base p n' d' c' H. unfold optimize_table_uncond in H.
  transitivity (eval_chain_mut_st h (normalize_chain c) (env_with_sets base d') p);
    [| apply normalize_chain_mut_st].
  apply (optimize_table_mut_st_correct_uncond_gen h
           (seed_start (optimize_chain (normalize_chain c))) empty_decls
           (normalize_chain c) n' d' c' base p H).
  - intros k _ Hin; cbn in Hin; exact Hin.
  - intros k _ Hin; cbn in Hin; exact Hin.
  - intros k _ Hin; cbn in Hin; exact Hin.
  - apply seed_start_dynset_fresh.
Qed.

(** The (verdict, env) view of the same guarantee — the historical M5
    statement, now a PROJECTION corollary of the full-state headline via
    [Semantics.eval_chain_mut_env_st] (NOT an independent proof: whatever the
    full-state theorem equates, its projections are equal too). *)
Theorem optimize_table_uncond_mut_env_correct : forall h c base p n' d' c',
  optimize_table_uncond c = (n', d', c') ->
  eval_chain_mut_env h c' (env_with_sets base d') p
  = eval_chain_mut_env h c (env_with_sets base d') p.
Proof.
  intros h c base p n' d' c' H.
  rewrite !eval_chain_mut_env_st.
  rewrite (optimize_table_uncond_mut_st_correct h c base p n' d' c' H).
  reflexivity.
Qed.

(** ** Part H: PRECISION PIN — why the observable must carry the packet half.

    Regression witness (from the M5 adversarial challenge): the chain
    [`meta mark set 0x1`] (fall-through) and the EMPTY chain are IDENTIFIED by
    the (verdict, env) observable [eval_chain_mut_env] — at every hook, env and
    packet — because a mark write lands in the PACKET half of the state.  Yet
    the model's own priority dispatch reads that mark in a later base chain at
    the same hook, so a pipeline certified only at (verdict, env) could
    rewrite one chain into the other and flip a later chain's verdict.  The
    full-state observable [eval_chain_mut_st] the headline uses distinguishes
    the pair; these pins keep it that way. *)
Definition mutst_pin_mark_rule : rule :=
  {| r_body := [ BStmt (SMetaSet MKmark (VImm [0;0;0;1])) ];
     r_outcome := ONone; r_after := [] |}.
Definition mutst_pin_c_marks : chain :=
  {| c_policy := Accept; c_rules := [mutst_pin_mark_rule] |}.
Definition mutst_pin_c_empty : chain :=
  {| c_policy := Accept; c_rules := [] |}.

(** The env-only observable is BLIND to the pair (both components, everywhere). *)
Lemma mutst_pin_mut_env_blind : forall h e p,
  eval_chain_mut_env h mutst_pin_c_marks e p
  = eval_chain_mut_env h mutst_pin_c_empty e p.
Proof. intros h e p. reflexivity. Qed.

(** The full-state observable is NOT: the exported packet carries the mark. *)
Definition mutst_pin_pkt : packet :=
  {| pkt_meta := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := true;
     pkt_fragoff := 0; pkt_flow := [1;1]; pkt_untracked := false;
     pkt_ctdir_orig := true; pkt_ct_present := true |}.
Definition mutst_pin_env : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => [];
     e_limit := fun _ => 0; e_quota := fun _ => 0;
     e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => []; e_nat := fun _ => None;
     e_numgen := fun _ => 0 |}.

Lemma mutst_pin_mark_observed :
  pkt_meta (snd (snd (eval_chain_mut_st Hprerouting mutst_pin_c_marks
                        mutst_pin_env mutst_pin_pkt))) MKmark = [0;0;0;1]
  /\ pkt_meta (snd (snd (eval_chain_mut_st Hprerouting mutst_pin_c_empty
                        mutst_pin_env mutst_pin_pkt))) MKmark = [].
Proof. split; reflexivity. Qed.

Lemma mutst_pin_distinguishes :
  eval_chain_mut_st Hprerouting mutst_pin_c_marks mutst_pin_env mutst_pin_pkt
  <> eval_chain_mut_st Hprerouting mutst_pin_c_empty mutst_pin_env mutst_pin_pkt.
Proof.
  intro Hid.
  destruct mutst_pin_mark_observed as [H1 H2].
  rewrite Hid, H2 in H1. discriminate H1.
Qed.

(** ** Axiom-freedom audit (build-time guard; mirrors Optimize_Uncond).
    Prints "Closed under the global context". *)
Print Assumptions optimize_table_uncond_mut_st_correct.
Print Assumptions optimize_table_uncond_mut_env_correct.
