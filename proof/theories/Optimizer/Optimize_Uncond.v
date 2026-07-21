(** * Optimize_Uncond: UNCONDITIONAL correctness of the [nft -o] consolidation
    pipeline.

    The earlier per-pass [_correct] theorems (and the composed pipeline) required
    their INPUT chain to be [rules_clean].  That hypothesis was only ever used for
    ONE thing: the env-stability of a PASSED-THROUGH rule when a sibling merge
    prepends a fresh set/vmap declaration.  (The clean-input-only composed theorems
    have since been removed as strictly redundant: the unconditional results below
    subsume them, since [rules_clean] implies the read-freshness obligations.)
    The N-way run-merge lemmas
    themselves ([eval_rules_run_merge_abs], [eval_rules_run_collapse],
    [eval_rules_vmap_mergeN]) are body-agnostic — they collapse a run of
    [mk_head]/[orig_rule] shells with ANY shared body/end-fields, clean or not.

    This file removes [rules_clean] entirely, replacing it with a far weaker
    *read-freshness* side-condition that is DISCHARGEABLE BY CONSTRUCTION at the
    fresh-table entry point: the synthesised [setname]/[vmapname] names are minted
    from a counter chosen past the LENGTH of every name the input reads, so no
    passed-through rule can read a minted name.  A passed-through rule therefore
    evaluates identically with or without the fresh declaration — UNCONDITIONALLY,
    for an ARBITRARY (possibly unclean) input chain.

    Part 1: generalised env-AGREEMENT for an ARBITRARY rule (drop the
            [body_only_matches] restriction of [Optimize_Table_Inv]).
    Part 2: the length-based fresh-counter ([seed_bound]) + its two freshness lemmas.
    Part 3: unconditional per-pass correctness (valueset / concat / vmap).
    Part 4: unconditional [optimize_table] + END-TO-END compile theorems. *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import String.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Correct Optimize Optimize_ValueSet Optimize_Vmap Optimize_VmapGuarded Optimize_Concat Optimize_ConcatMulti
  Optimize_ConcatGuarded Optimize_SetGuarded Optimize_IntervalSet Optimize_IntervalSetGuarded Optimize_MixedPointRangeGuarded Optimize_Absorb Optimize_CtMask
  Optimize_Dscp Optimize_DscpVmap Optimize_IntervalSetHostOrder Optimize_DataMap Optimize_Dnat Optimize_Snat Optimize_Table_Inv Optimize_Table Optimize_Normalize.

Local Open Scope nat_scope.

(** ** Part 1: env-AGREEMENT for an ARBITRARY rule.

    A rule's verdict reads the set/vmap environment ONLY through the matchconds its
    body evaluates ([mc_set_name]) and the verdict map it carries ([rule_vmap_name]).
    We prove this WITHOUT the [body_only_matches] restriction, which means handling
    statement body items — [SSynproxy] and [SNotrack] (threads [set_untracked] into
    the rest of the walk).  Loadability predicates and [synproxy_stops]/
    [body_synproxy_stops] do not take the env at all, so their stability across two
    decls is a TYPING fact (no lemma needed); [set_untracked] acts on the packet
    alone, so it trivially preserves whichever env the walk carries. *)

(** [outcome_core] AGREES across two decls that agree on the rule's vmap name. *)
Lemma outcome_core_agree : forall r q base d1 d2,
  (forall nm, In nm (rule_vmap_name r) ->
     e_vmap (env_with_sets base d1) nm = e_vmap (env_with_sets base d2) nm) ->
  outcome_core r (env_with_sets base d1) q
  = outcome_core r (env_with_sets base d2) q.
Proof.
  intros r q base d1 d2 Hvmap. unfold outcome_core.
  destruct (r_vmap r) as [vm |] eqn:Ev; [| reflexivity].
  assert (Hk : match vm_keyf vm with
                 | Some (f, ts) => apply_transforms ts (field_value f (env_with_sets base d1) q)
                 | None => List.concat (map (fun f => field_value f (env_with_sets base d1) q) (vm_fields vm))
                 end
             = match vm_keyf vm with
                 | Some (f, ts) => apply_transforms ts (field_value f (env_with_sets base d2) q)
                 | None => List.concat (map (fun f => field_value f (env_with_sets base d2) q) (vm_fields vm))
                 end).
  { destruct (vm_keyf vm) as [[f ts] |].
    - rewrite (field_value_env_with_sets f q base d1 d2). reflexivity.
    - rewrite (map_ext _ _ (fun f => field_value_env_with_sets f q base d1 d2)). reflexivity. }
  rewrite Hk.
  rewrite (Hvmap (vm_name vm)) by (unfold rule_vmap_name; rewrite Ev; left; reflexivity).
  destruct (assoc_verdict _ (e_vmap (env_with_sets base d2) (vm_name vm))); reflexivity.
Qed.

(** *** Generalised whole-rule agreement: ARBITRARY body (no [body_only_matches]). *)

Lemma rule_applies_walk_agree_gen : forall body p base d1 d2,
  (forall nm, In nm (body_set_names body) ->
     e_set (env_with_sets base d1) nm = e_set (env_with_sets base d2) nm) ->
  rule_applies_walk body (env_with_sets base d1) p
  = rule_applies_walk body (env_with_sets base d2) p.
Proof.
  intros body. induction body as [| it body IH]; intros p base d1 d2 Hag; [reflexivity|].
  assert (Hsub : forall nm, In nm (body_set_names body) -> In nm (body_set_names (it :: body))).
  { intros nm Hnm. unfold body_set_names in *. cbn [body_matches flat_map].
    destruct it as [m | s]; cbn [flat_map].
    - apply in_or_app. right. exact Hnm.
    - exact Hnm. }
  destruct it as [m | s].
  - cbn [rule_applies_walk].
    rewrite (eval_matchcond_agree m p base d1 d2).
    + rewrite (IH p base d1 d2 (fun nm Hnm => Hag nm (Hsub nm Hnm))). reflexivity.
    + intros nm Hnm. apply Hag. apply (mc_in_body_read (BMatch m :: body) m nm);
        [ left; reflexivity | exact Hnm ].
  - cbn [rule_applies_walk]. destruct s;
      try (apply (IH p base d1 d2 (fun nm Hnm => Hag nm (Hsub nm Hnm)))).
    + (* SNotrack *)
      apply (IH (set_untracked p) base d1 d2 (fun nm Hnm => Hag nm (Hsub nm Hnm))).
    + (* SSynproxy *)
      destruct (synproxy_stops p);
        [reflexivity | apply (IH p base d1 d2 (fun nm Hnm => Hag nm (Hsub nm Hnm)))].
Qed.

Lemma rule_loadable_agree_gen : forall r p base d1 d2,
  decls_agree_rule base d1 d2 r ->
  rule_loadable r (env_with_sets base d1) p
  = rule_loadable r (env_with_sets base d2) p.
Proof.
  intros r p base d1 d2 [_ [Hvmap Hmap]]. unfold rule_loadable.
  f_equal.
  destruct (body_synproxy_stops (r_body r) p); [reflexivity |].
  apply (end_loadable_agree r (body_thread (r_body r) p) base d1 d2 Hvmap Hmap).
Qed.

Lemma rule_applies_agree_gen : forall r p base d1 d2,
  decls_agree_rule base d1 d2 r ->
  rule_applies r (env_with_sets base d1) p
  = rule_applies r (env_with_sets base d2) p.
Proof.
  intros r p base d1 d2 [Hset _]. unfold rule_applies.
  apply (rule_applies_walk_agree_gen (r_body r) p base d1 d2 Hset).
Qed.

Lemma outcome_agree_gen : forall r p base d1 d2,
  decls_agree_rule base d1 d2 r ->
  outcome r (env_with_sets base d1) p
  = outcome r (env_with_sets base d2) p.
Proof.
  intros r p base d1 d2 [_ [Hvmap _]]. unfold outcome.
  destruct (body_synproxy_stops (r_body r) p); [reflexivity |].
  apply (outcome_core_agree r (body_thread (r_body r) p) base d1 d2 Hvmap).
Qed.

(** [eval_rules] AGREES across two decls that agree (per-rule) on the names each
    rule reads — for an ARBITRARY rule list. *)
Lemma eval_rules_agree_gen : forall rs p base d1 d2,
  (forall r, In r rs -> decls_agree_rule base d1 d2 r) ->
  eval_rules rs (env_with_sets base d1) p
  = eval_rules rs (env_with_sets base d2) p.
Proof.
  induction rs as [| r rs IH]; intros p base d1 d2 Hag; [reflexivity|].
  pose proof (Hag r (or_introl eq_refl)) as Hda.
  cbn [eval_rules].
  rewrite (rule_loadable_agree_gen r p base d1 d2 Hda).
  rewrite (rule_applies_agree_gen r p base d1 d2 Hda).
  rewrite (outcome_agree_gen r p base d1 d2 Hda).
  rewrite (IH p base d1 d2 (fun r' Hr' => Hag r' (or_intror Hr'))). reflexivity.
Qed.

(** ** Part 2: the length-based fresh-counter and read-freshness predicates.

    To make the entry point's freshness side-conditions DISCHARGEABLE BY
    CONSTRUCTION, we mint synthesized names from a counter chosen STRICTLY ABOVE the
    LENGTH of every name the input chain reads.  Since [setname k]/[vmapname k] are
    each STRICTLY LONGER than [k], any [k] past that bound yields a name longer than
    every seed name — hence absent from the seed.  No string parsing, only a length
    argument; [setname]/[vmapname] keep their [nat]-counter shape. *)

Local Transparent setname vmapname.

Lemma string_of_nat_length : forall n, String.length (string_of_nat n) = n.
Proof. induction n as [| n IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma string_append_length : forall a b,
  String.length (a ++ b)%string = String.length a + String.length b.
Proof. induction a as [| c a IH]; intros b; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma setname_length : forall n, String.length (setname n) = 5 + n.
Proof.
  intros n. unfold setname. rewrite string_append_length, string_of_nat_length.
  reflexivity.
Qed.

Lemma mapname_length : forall n, String.length (mapname n) = 5 + n.
Proof.
  intros n. Transparent mapname. unfold mapname.
  rewrite string_append_length, string_of_nat_length. reflexivity.
Qed.
Global Opaque mapname.

Lemma vmapname_length : forall n, String.length (vmapname n) = 6 + n.
Proof.
  intros n. unfold vmapname. rewrite string_append_length, string_of_nat_length.
  reflexivity.
Qed.

Local Opaque setname vmapname.

(** Membership in a [nat] list is bounded by [list_max]. *)
Lemma in_le_list_max : forall x l, In x l -> x <= list_max l.
Proof.
  induction l as [| a l IH]; intros Hin; [destruct Hin|].
  cbn [list_max]. destruct Hin as [Heq | Hin].
  - subst. apply Nat.le_max_l.
  - apply Nat.max_le_iff. right. apply IH; exact Hin.
Qed.

(** A name strictly longer than every string in [seed] is absent from [seed]. *)
Lemma not_in_of_length_gt : forall (s : string) seed,
  list_max (map String.length seed) < String.length s -> ~ In s seed.
Proof.
  intros s seed Hlt Hin.
  assert (Hle : String.length s <= list_max (map String.length seed)).
  { apply in_le_list_max. apply in_map. exact Hin. }
  lia.
Qed.

(** *** Read-freshness predicates: a rule reads no minted name at-or-above [n]. *)
Definition rule_set_fresh (n : nat) (r : rule) : Prop :=
  forall k, n <= k -> ~ In (setname k) (body_set_names (r_body r)).

Definition rule_vmap_fresh (n : nat) (r : rule) : Prop :=
  forall k, n <= k -> ~ In (vmapname k) (rule_vmap_name r).

Lemma rule_set_fresh_mono : forall n m r,
  n <= m -> rule_set_fresh n r -> rule_set_fresh m r.
Proof. intros n m r Hnm Hf k Hk. apply Hf. lia. Qed.

Lemma rule_vmap_fresh_mono : forall n m r,
  n <= m -> rule_vmap_fresh n r -> rule_vmap_fresh m r.
Proof. intros n m r Hnm Hf k Hk. apply Hf. lia. Qed.

(** A rule reads no minted DATA-MAP name (`__mapN`) at-or-above [n] as a NAT
    operand.  Trivial for every non-[nat_map] rule (empty [rule_nat_map_name]). *)
Definition rule_nat_map_fresh (n : nat) (r : rule) : Prop :=
  forall k, n <= k -> ~ In (mapname k) (rule_nat_map_name r).

Lemma rule_nat_map_fresh_mono : forall n m r,
  n <= m -> rule_nat_map_fresh n r -> rule_nat_map_fresh m r.
Proof. intros n m r Hnm Hf k Hk. apply Hf. lia. Qed.

(** *** The two seam helpers: a passed-through rule that reads no minted name
    AGREES across the extended declarations. *)

(** valueset / concat seam: the pass adds only [setname] entries (and leaves
    [sd_vmaps] fixed); a [rule_set_fresh n] rule agrees. *)
Lemma decls_agree_rule_setseam : forall base d d' r n,
  sd_vmaps d' = sd_vmaps d ->
  sd_maps d' = sd_maps d ->
  (forall nm X, (forall k, n <= k -> nm <> setname k) ->
     assoc_str nm (sd_sets d') X = assoc_str nm (sd_sets d) X) ->
  rule_set_fresh n r ->
  decls_agree_rule base d' d r.
Proof.
  intros base d d' r n Hvm Hmaps Hassoc Hfresh. repeat split.
  - intros nm Hnm. rewrite !e_set_declared.
    apply Hassoc. intros k Hk Heq. subst nm. apply (Hfresh k Hk Hnm).
  - intros nm _. rewrite !e_vmap_env_with_sets. rewrite Hvm. reflexivity.
  - intros nm _. rewrite !e_map_env_with_sets. rewrite Hmaps. reflexivity.
Qed.

(** vmap seam: the pass adds only [vmapname] entries (and leaves [sd_sets]/
    [sd_maps] fixed); a [rule_vmap_fresh n] rule agrees. *)
Lemma decls_agree_rule_vmapseam : forall base d d' r n,
  sd_sets d' = sd_sets d ->
  sd_maps d' = sd_maps d ->
  (forall nm X, (forall k, n <= k -> nm <> vmapname k) ->
     assoc_str nm (sd_vmaps d') X = assoc_str nm (sd_vmaps d) X) ->
  rule_vmap_fresh n r ->
  decls_agree_rule base d' d r.
Proof.
  intros base d d' r n Hss Hmaps Hassoc Hfresh. repeat split.
  - intros nm _. rewrite !e_set_declared. rewrite Hss. reflexivity.
  - intros nm Hnm. rewrite !e_vmap_env_with_sets.
    apply Hassoc. intros k Hk Heq. subst nm. apply (Hfresh k Hk Hnm).
  - intros nm _. rewrite !e_map_env_with_sets. rewrite Hmaps. reflexivity.
Qed.

(** mapN seam: the pass adds [setname] (head guard) AND [mapname] (data map)
    entries (leaving [sd_vmaps] fixed); a rule that is both [rule_set_fresh] and
    [rule_nat_map_fresh] at [n] agrees. *)
Lemma decls_agree_rule_mapseam : forall base d d' r n,
  sd_vmaps d' = sd_vmaps d ->
  (forall nm X, (forall k, n <= k -> nm <> setname k) ->
     assoc_str nm (sd_sets d') X = assoc_str nm (sd_sets d) X) ->
  (forall nm X, (forall k, n <= k -> nm <> mapname k) ->
     assoc_str nm (sd_maps d') X = assoc_str nm (sd_maps d) X) ->
  rule_set_fresh n r ->
  rule_nat_map_fresh n r ->
  decls_agree_rule base d' d r.
Proof.
  intros base d d' r n Hvm Hassocs Hassocm Hsfresh Hmfresh. repeat split.
  - intros nm Hnm. rewrite !e_set_declared.
    apply Hassocs. intros k Hk Heq. subst nm. apply (Hsfresh k Hk Hnm).
  - intros nm _. rewrite !e_vmap_env_with_sets. rewrite Hvm. reflexivity.
  - intros nm Hnm. rewrite !e_map_env_with_sets.
    apply Hassocm. intros k Hk Heq. subst nm. apply (Hmfresh k Hk Hnm).
Qed.

(** A [decls_agree_rule] is symmetric in its two declaration sets. *)
Lemma decls_agree_rule_sym : forall base d1 d2 r,
  decls_agree_rule base d1 d2 r -> decls_agree_rule base d2 d1 r.
Proof.
  intros base d1 d2 r [Hset [Hvmap Hmap]]. repeat split.
  - intros nm Hnm. symmetry. apply Hset; exact Hnm.
  - intros nm Hnm. symmetry. apply Hvmap; exact Hnm.
  - intros nm Hnm. symmetry. apply Hmap; exact Hnm.
Qed.

(** A cons-step congruence for [eval_rules]: equal head behaviour (loadable /
    applies / outcome) AND equal tail evaluations give equal whole evaluations. *)
Lemma eval_rules_cons_cong : forall r X Y e1 e2 p,
  rule_loadable r e1 p = rule_loadable r e2 p ->
  rule_applies r e1 p = rule_applies r e2 p ->
  outcome r e1 p = outcome r e2 p ->
  eval_rules X e1 p = eval_rules Y e2 p ->
  eval_rules (r :: X) e1 p = eval_rules (r :: Y) e2 p.
Proof.
  intros r X Y e1 e2 p HL HA HO HXY. cbn [eval_rules]. rewrite HL, HA, HO, HXY. reflexivity.
Qed.

(** An [orig_dnat_rule] reads NO set/vmap/map name, so it AGREES across any decls. *)
Lemma decls_agree_orig_dnat : forall base d1 d2 f v T,
  decls_agree_rule base d1 d2 (orig_dnat_rule f v T).
Proof.
  intros. repeat split; intros nm Hin; cbn in Hin; contradiction.
Qed.

(** The dnat pass preserves [sd_sets]/[sd_vmaps] and only prepends [mapname]-keyed
    [sd_maps] entries, so a rule reading no minted mapname AGREES across the
    extended decls. *)
Lemma decls_agree_rule_dnatseam : forall base d d' r n,
  sd_sets d' = sd_sets d -> sd_vmaps d' = sd_vmaps d ->
  (forall nm X, (forall k, n <= k -> nm <> mapname k) ->
     assoc_str nm (sd_maps d') X = assoc_str nm (sd_maps d) X) ->
  rule_nat_map_fresh n r ->
  decls_agree_rule base d' d r.
Proof.
  intros base d d' r n Hss Hvm Hassocm Hmfresh. repeat split.
  - intros nm _. rewrite !e_set_declared. rewrite Hss. reflexivity.
  - intros nm _. rewrite !e_vmap_env_with_sets. rewrite Hvm. reflexivity.
  - intros nm Hnm. rewrite !e_map_env_with_sets. apply Hassocm.
    intros k Hk Heq. subst nm. apply (Hmfresh k Hk Hnm).
Qed.

(** *** dnat (bare-map): per-list VERDICT correctness, env-threaded.  The merged
    bare rule READS [e_map (mapname n)] = the freshly-prepended [dmap2], so this is
    NOT env-independent like the meta-mark mapN pass; it threads the agreement infra
    exactly as [valueset] does, plugging in [eval_rules_dnat_merge]. *)
(** STAGE — composed into [optimize_table_correct_uncond_gen]; not a standalone headline. *)
Theorem optimize_rules_dnat_eval : forall rs n d n' d' rs' base p,
  optimize_rules_dnat n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (mapname k) (map fst (sd_maps d))) ->
  Forall (rule_nat_map_fresh n) rs ->
  eval_rules rs' (env_with_sets base d') p
  = eval_rules rs  (env_with_sets base d) p.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' base p H Hfresh Hrf. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; reflexivity.
  - cbn in H; inversion H; subst; reflexivity.
  - rewrite optimize_rules_dnat_cons2 in H.
    inversion Hrf as [| ? ? Hf1 Hrf_t]; subst.
    inversion Hrf_t as [| ? ? Hf2 Hrf_r]; subst.
    destruct (dnat_merge_pair r1 r2) as [[[[[f v1] v2] T1] T2]|] eqn:Epair.
    + (* MERGE *)
      cbv zeta in H.
      destruct (dnat_merge_pair_shape r1 r2 f v1 v2 T1 T2 Epair)
        as [Hr1 [Hr2 [Hfx1 [Hfx2 Hne]]]].
      remember (optimize_rules_dnat (S n)
                  {| sd_sets := sd_sets d; sd_vmaps := sd_vmaps d;
                     sd_maps := (mapname n, dmap2 v1 v2 T1 T2) :: sd_maps d |} rest)
        as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. inversion H; subst n' d' rs'. clear H.
      set (dd := {| sd_sets := sd_sets d; sd_vmaps := sd_vmaps d;
                    sd_maps := (mapname n, dmap2 v1 v2 T1 T2) :: sd_maps d |}) in *.
      assert (Hfresh' : forall k, S n <= k -> ~ In (mapname k) (map fst (sd_maps dd))).
      { intros k Hk Hin. subst dd; cbn [sd_maps map fst] in Hin.
        destruct Hin as [Heq | Hin].
        - apply mapname_inj in Heq. lia.
        - apply (Hfresh k); [lia | exact Hin]. }
      assert (Hrf_r' : Forall (rule_nat_map_fresh (S n)) rest).
      { eapply Forall_impl; [| exact Hrf_r].
        intros r Hr. apply (rule_nat_map_fresh_mono n (S n) r); [lia | exact Hr]. }
      pose proof (IH rest ltac:(unfold ltof; cbn; lia) (S n) dd m'' dd'' rr'' base p
                    (eq_sym Erec) Hfresh' Hrf_r') as Htail0.
      assert (Hrest_dd_d : eval_rules rest (env_with_sets base dd) p
                         = eval_rules rest (env_with_sets base d) p).
      { apply eval_rules_agree_gen. intros r Hr.
        apply (decls_agree_rule_dnatseam base d dd r n).
        - subst dd; reflexivity.
        - subst dd; reflexivity.
        - intros nm X Hnm. subst dd; cbn [sd_maps assoc_str].
          destruct (String.eqb nm (mapname n)) eqn:Eq;
            [apply String.eqb_eq in Eq; exfalso; apply (Hnm n); [lia | exact Eq] | reflexivity].
        - rewrite Forall_forall in Hrf_r. apply Hrf_r; exact Hr. }
      assert (Hlook : e_map (env_with_sets base dd'') (mapname n)
                    = dmap2 v1 v2 T1 T2).
      { rewrite e_map_env_with_sets.
        rewrite (optimize_rules_dnat_maps_assoc_stable rest (S n) dd m'' dd'' rr''
                   (mapname n) (e_map base (mapname n)) (eq_sym Erec)
                   ltac:(intros j Hj Heq; apply mapname_inj in Heq; lia)).
        subst dd; cbn [sd_maps assoc_str]. rewrite String.eqb_refl. reflexivity. }
      subst r1 r2.
      rewrite (eval_rules_dnat_merge f v1 v2 T1 T2 (mapname n) rr''
                 (env_with_sets base dd'') p Hlook Hfx1 Hfx2).
      apply (eval_rules_cons_cong (orig_dnat_rule f v1 T1));
        [ apply (rule_loadable_agree_gen _ p base dd'' d (decls_agree_orig_dnat _ _ _ _ _ _))
        | apply (rule_applies_agree_gen _ p base dd'' d (decls_agree_orig_dnat _ _ _ _ _ _))
        | apply (outcome_agree_gen _ p base dd'' d (decls_agree_orig_dnat _ _ _ _ _ _)) | ].
      apply (eval_rules_cons_cong (orig_dnat_rule f v2 T2));
        [ apply (rule_loadable_agree_gen _ p base dd'' d (decls_agree_orig_dnat _ _ _ _ _ _))
        | apply (rule_applies_agree_gen _ p base dd'' d (decls_agree_orig_dnat _ _ _ _ _ _))
        | apply (outcome_agree_gen _ p base dd'' d (decls_agree_orig_dnat _ _ _ _ _ _)) | ].
      rewrite Htail0. exact Hrest_dd_d.
    + (* NO MERGE: keep r1, recurse on (r2 :: rest) *)
      cbv zeta in H.
      remember (optimize_rules_dnat n d (r2 :: rest)) as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. inversion H; subst n' d' rs'. clear H.
      pose proof (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) n d m'' dd'' rr'' base p
                    (eq_sym Erec) Hfresh Hrf_t) as Htail.
      assert (Hda1 : decls_agree_rule base dd'' d r1).
      { apply (decls_agree_rule_dnatseam base d dd'' r1 n).
        - apply (optimize_rules_dnat_sets (r2 :: rest) n d m'' dd'' rr'' (eq_sym Erec)).
        - apply (optimize_rules_dnat_vmaps (r2 :: rest) n d m'' dd'' rr'' (eq_sym Erec)).
        - intros nm X Hnm. apply (optimize_rules_dnat_maps_assoc_stable (r2 :: rest) n d
                                    m'' dd'' rr'' nm X (eq_sym Erec) Hnm).
        - exact Hf1. }
      apply (eval_rules_cons_cong r1);
        [ apply (rule_loadable_agree_gen r1 p base dd'' d Hda1)
        | apply (rule_applies_agree_gen r1 p base dd'' d Hda1)
        | apply (outcome_agree_gen r1 p base dd'' d Hda1)
        | exact Htail ].
Qed.

(** The chain-level lift: the dnat pass preserves [eval_chain] on every packet. *)
Lemma optimize_chain_dnat_eval : forall n d c n' d' c' base p,
  optimize_chain_dnat n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (mapname k) (map fst (sd_maps d))) ->
  Forall (rule_nat_map_fresh n) (c_rules c) ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c  (env_with_sets base d) p.
Proof.
  intros n d c n' d' c' base p H Hfresh Hrf. unfold optimize_chain_dnat in H.
  destruct (optimize_rules_dnat n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_dnat_eval (c_rules c) n d m'' dd'' rr'' base p E Hfresh Hrf).
  reflexivity.
Qed.

(** The dnat pass preserves set-/vmap-read freshness: the merged [mk_dnat_rule]
    has an empty body and no verdict map, so it reads NO setname/vmapname. *)
Lemma optimize_rules_dnat_output_set_fresh : forall rs n d n' d' rs',
  optimize_rules_dnat n d rs = (n', d', rs') ->
  Forall (rule_set_fresh n) rs -> Forall (rule_set_fresh n') rs'.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H Hrf. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; exact Hrf.
  - cbn in H; inversion H; subst; exact Hrf.
  - rewrite optimize_rules_dnat_cons2 in H.
    inversion Hrf as [| ? ? Hf1 Hrf2]; subst.
    inversion Hrf2 as [| ? ? Hf2 Hrf_rest]; subst.
    destruct (dnat_merge_pair r1 r2) as [[[[[f v1] v2] T1] T2]|] eqn:Ep; cbv zeta in H.
    + remember (optimize_rules_dnat (S n)
                  {| sd_sets := sd_sets d; sd_vmaps := sd_vmaps d;
                     sd_maps := (mapname n, dmap2 v1 v2 T1 T2) :: sd_maps d |} rest)
        as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst n' d' rs'. clear H. constructor.
      * intros j Hj Hin. cbn [mk_dnat_rule r_body body_set_names body_matches flat_map] in Hin.
        contradiction.
      * apply (IH rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E)).
        eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia|exact Hr]
                            |exact Hrf_rest].
    + remember (optimize_rules_dnat n d (r2 :: rest)) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst n' d' rs'. clear H.
      pose proof (optimize_rules_dnat_mono (r2 :: rest) n d _ _ _ (eq_sym E)) as Hmono.
      constructor;
        [apply (rule_set_fresh_mono n m'' r1 Hmono Hf1)
        |apply (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E));
           constructor; assumption].
Qed.

Lemma optimize_rules_dnat_output_vmap_fresh : forall rs n d n' d' rs',
  optimize_rules_dnat n d rs = (n', d', rs') ->
  Forall (rule_vmap_fresh n) rs -> Forall (rule_vmap_fresh n') rs'.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H Hrf. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; exact Hrf.
  - cbn in H; inversion H; subst; exact Hrf.
  - rewrite optimize_rules_dnat_cons2 in H.
    inversion Hrf as [| ? ? Hf1 Hrf2]; subst.
    inversion Hrf2 as [| ? ? Hf2 Hrf_rest]; subst.
    destruct (dnat_merge_pair r1 r2) as [[[[[f v1] v2] T1] T2]|] eqn:Ep; cbv zeta in H.
    + remember (optimize_rules_dnat (S n)
                  {| sd_sets := sd_sets d; sd_vmaps := sd_vmaps d;
                     sd_maps := (mapname n, dmap2 v1 v2 T1 T2) :: sd_maps d |} rest)
        as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst n' d' rs'. clear H. constructor.
      * intros j Hj Hin. cbn [mk_dnat_rule rule_vmap_name r_vmap r_outcome] in Hin. contradiction.
      * apply (IH rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E)).
        eapply Forall_impl; [intros r Hr; apply (rule_vmap_fresh_mono n (S n) r); [lia|exact Hr]
                            |exact Hrf_rest].
    + remember (optimize_rules_dnat n d (r2 :: rest)) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst n' d' rs'. clear H.
      pose proof (optimize_rules_dnat_mono (r2 :: rest) n d _ _ _ (eq_sym E)) as Hmono.
      constructor;
        [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
        |apply (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E));
           constructor; assumption].
Qed.

Lemma optimize_chain_dnat_output_set_fresh : forall n d c n' d' c',
  optimize_chain_dnat n d c = (n', d', c') ->
  Forall (rule_set_fresh n) (c_rules c) -> Forall (rule_set_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_dnat in H.
  destruct (optimize_rules_dnat n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. cbn [c_rules].
  apply (optimize_rules_dnat_output_set_fresh _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_dnat_output_vmap_fresh : forall n d c n' d' c',
  optimize_chain_dnat n d c = (n', d', c') ->
  Forall (rule_vmap_fresh n) (c_rules c) -> Forall (rule_vmap_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_dnat in H.
  destruct (optimize_rules_dnat n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. cbn [c_rules].
  apply (optimize_rules_dnat_output_vmap_fresh _ _ _ _ _ _ E Hrf).
Qed.

(** dnat preserves nat-map read-freshness: the ONLY nat-map name the merged rule
    reads is [mapname n], which is BELOW the output counter [n'] (>= S n). *)
Lemma optimize_rules_dnat_output_nat_map_fresh : forall rs n d n' d' rs',
  optimize_rules_dnat n d rs = (n', d', rs') ->
  Forall (rule_nat_map_fresh n) rs -> Forall (rule_nat_map_fresh n') rs'.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H Hrf. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; exact Hrf.
  - cbn in H; inversion H; subst; exact Hrf.
  - rewrite optimize_rules_dnat_cons2 in H.
    inversion Hrf as [| ? ? Hf1 Hrf2]; subst.
    inversion Hrf2 as [| ? ? Hf2 Hrf_rest]; subst.
    destruct (dnat_merge_pair r1 r2) as [[[[[f v1] v2] T1] T2]|] eqn:Ep; cbv zeta in H.
    + remember (optimize_rules_dnat (S n)
                  {| sd_sets := sd_sets d; sd_vmaps := sd_vmaps d;
                     sd_maps := (mapname n, dmap2 v1 v2 T1 T2) :: sd_maps d |} rest)
        as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst n' d' rs'. clear H.
      pose proof (optimize_rules_dnat_mono rest (S n) _ _ _ _ (eq_sym E)) as Hmono.
      constructor.
      * intros j Hj Hin.
        cbn [mk_dnat_rule rule_nat_map_name r_nat dnat_map_spec nat_map r_outcome] in Hin.
        destruct Hin as [Heq | []]. apply mapname_inj in Heq. lia.
      * apply (IH rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E)).
        eapply Forall_impl; [intros r Hr; apply (rule_nat_map_fresh_mono n (S n) r); [lia|exact Hr]
                            |exact Hrf_rest].
    + remember (optimize_rules_dnat n d (r2 :: rest)) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst n' d' rs'. clear H.
      pose proof (optimize_rules_dnat_mono (r2 :: rest) n d _ _ _ (eq_sym E)) as Hmono.
      constructor;
        [apply (rule_nat_map_fresh_mono n m'' r1 Hmono Hf1)
        |apply (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E));
           constructor; assumption].
Qed.

Lemma optimize_chain_dnat_output_nat_map_fresh : forall n d c n' d' c',
  optimize_chain_dnat n d c = (n', d', c') ->
  Forall (rule_nat_map_fresh n) (c_rules c) -> Forall (rule_nat_map_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_dnat in H.
  destruct (optimize_rules_dnat n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. cbn [c_rules].
  apply (optimize_rules_dnat_output_nat_map_fresh _ _ _ _ _ _ E Hrf).
Qed.
(** An [orig_snat_rule] reads NO set/vmap/map name, so it AGREES across any decls. *)
Lemma decls_agree_orig_snat : forall base d1 d2 f v T,
  decls_agree_rule base d1 d2 (orig_snat_rule f v T).
Proof.
  intros. repeat split; intros nm Hin; cbn in Hin; contradiction.
Qed.

(** The snat pass is structurally identical to the dnat pass (it preserves
    [sd_sets]/[sd_vmaps] and only prepends [mapname]-keyed [sd_maps] entries), so it
    reuses the kind-agnostic seam lemma [decls_agree_rule_dnatseam] verbatim. *)

(** *** snat (bare-map): per-list VERDICT correctness, env-threaded.  The merged
    bare rule READS [e_map (mapname n)] = the freshly-prepended [dmap2], so this is
    NOT env-independent like the meta-mark mapN pass; it threads the agreement infra
    exactly as [valueset] does, plugging in [eval_rules_snat_merge]. *)
(** STAGE — composed into [optimize_table_correct_uncond_gen]; not a standalone headline. *)
Theorem optimize_rules_snat_eval : forall rs n d n' d' rs' base p,
  optimize_rules_snat n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (mapname k) (map fst (sd_maps d))) ->
  Forall (rule_nat_map_fresh n) rs ->
  eval_rules rs' (env_with_sets base d') p
  = eval_rules rs  (env_with_sets base d) p.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' base p H Hfresh Hrf. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; reflexivity.
  - cbn in H; inversion H; subst; reflexivity.
  - rewrite optimize_rules_snat_cons2 in H.
    inversion Hrf as [| ? ? Hf1 Hrf_t]; subst.
    inversion Hrf_t as [| ? ? Hf2 Hrf_r]; subst.
    destruct (snat_merge_pair r1 r2) as [[[[[f v1] v2] T1] T2]|] eqn:Epair.
    + (* MERGE *)
      cbv zeta in H.
      destruct (snat_merge_pair_shape r1 r2 f v1 v2 T1 T2 Epair)
        as [Hr1 [Hr2 [Hfx1 [Hfx2 Hne]]]].
      remember (optimize_rules_snat (S n)
                  {| sd_sets := sd_sets d; sd_vmaps := sd_vmaps d;
                     sd_maps := (mapname n, dmap2 v1 v2 T1 T2) :: sd_maps d |} rest)
        as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. inversion H; subst n' d' rs'. clear H.
      set (dd := {| sd_sets := sd_sets d; sd_vmaps := sd_vmaps d;
                    sd_maps := (mapname n, dmap2 v1 v2 T1 T2) :: sd_maps d |}) in *.
      assert (Hfresh' : forall k, S n <= k -> ~ In (mapname k) (map fst (sd_maps dd))).
      { intros k Hk Hin. subst dd; cbn [sd_maps map fst] in Hin.
        destruct Hin as [Heq | Hin].
        - apply mapname_inj in Heq. lia.
        - apply (Hfresh k); [lia | exact Hin]. }
      assert (Hrf_r' : Forall (rule_nat_map_fresh (S n)) rest).
      { eapply Forall_impl; [| exact Hrf_r].
        intros r Hr. apply (rule_nat_map_fresh_mono n (S n) r); [lia | exact Hr]. }
      pose proof (IH rest ltac:(unfold ltof; cbn; lia) (S n) dd m'' dd'' rr'' base p
                    (eq_sym Erec) Hfresh' Hrf_r') as Htail0.
      assert (Hrest_dd_d : eval_rules rest (env_with_sets base dd) p
                         = eval_rules rest (env_with_sets base d) p).
      { apply eval_rules_agree_gen. intros r Hr.
        apply (decls_agree_rule_dnatseam base d dd r n).
        - subst dd; reflexivity.
        - subst dd; reflexivity.
        - intros nm X Hnm. subst dd; cbn [sd_maps assoc_str].
          destruct (String.eqb nm (mapname n)) eqn:Eq;
            [apply String.eqb_eq in Eq; exfalso; apply (Hnm n); [lia | exact Eq] | reflexivity].
        - rewrite Forall_forall in Hrf_r. apply Hrf_r; exact Hr. }
      assert (Hlook : e_map (env_with_sets base dd'') (mapname n)
                    = dmap2 v1 v2 T1 T2).
      { rewrite e_map_env_with_sets.
        rewrite (optimize_rules_snat_maps_assoc_stable rest (S n) dd m'' dd'' rr''
                   (mapname n) (e_map base (mapname n)) (eq_sym Erec)
                   ltac:(intros j Hj Heq; apply mapname_inj in Heq; lia)).
        subst dd; cbn [sd_maps assoc_str]. rewrite String.eqb_refl. reflexivity. }
      subst r1 r2.
      rewrite (eval_rules_snat_merge f v1 v2 T1 T2 (mapname n) rr''
                 (env_with_sets base dd'') p Hlook Hfx1 Hfx2).
      apply (eval_rules_cons_cong (orig_snat_rule f v1 T1));
        [ apply (rule_loadable_agree_gen _ p base dd'' d (decls_agree_orig_snat _ _ _ _ _ _))
        | apply (rule_applies_agree_gen _ p base dd'' d (decls_agree_orig_snat _ _ _ _ _ _))
        | apply (outcome_agree_gen _ p base dd'' d (decls_agree_orig_snat _ _ _ _ _ _)) | ].
      apply (eval_rules_cons_cong (orig_snat_rule f v2 T2));
        [ apply (rule_loadable_agree_gen _ p base dd'' d (decls_agree_orig_snat _ _ _ _ _ _))
        | apply (rule_applies_agree_gen _ p base dd'' d (decls_agree_orig_snat _ _ _ _ _ _))
        | apply (outcome_agree_gen _ p base dd'' d (decls_agree_orig_snat _ _ _ _ _ _)) | ].
      rewrite Htail0. exact Hrest_dd_d.
    + (* NO MERGE: keep r1, recurse on (r2 :: rest) *)
      cbv zeta in H.
      remember (optimize_rules_snat n d (r2 :: rest)) as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. inversion H; subst n' d' rs'. clear H.
      pose proof (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) n d m'' dd'' rr'' base p
                    (eq_sym Erec) Hfresh Hrf_t) as Htail.
      assert (Hda1 : decls_agree_rule base dd'' d r1).
      { apply (decls_agree_rule_dnatseam base d dd'' r1 n).
        - apply (optimize_rules_snat_sets (r2 :: rest) n d m'' dd'' rr'' (eq_sym Erec)).
        - apply (optimize_rules_snat_vmaps (r2 :: rest) n d m'' dd'' rr'' (eq_sym Erec)).
        - intros nm X Hnm. apply (optimize_rules_snat_maps_assoc_stable (r2 :: rest) n d
                                    m'' dd'' rr'' nm X (eq_sym Erec) Hnm).
        - exact Hf1. }
      apply (eval_rules_cons_cong r1);
        [ apply (rule_loadable_agree_gen r1 p base dd'' d Hda1)
        | apply (rule_applies_agree_gen r1 p base dd'' d Hda1)
        | apply (outcome_agree_gen r1 p base dd'' d Hda1)
        | exact Htail ].
Qed.

(** The chain-level lift: the snat pass preserves [eval_chain] on every packet. *)
Lemma optimize_chain_snat_eval : forall n d c n' d' c' base p,
  optimize_chain_snat n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (mapname k) (map fst (sd_maps d))) ->
  Forall (rule_nat_map_fresh n) (c_rules c) ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c  (env_with_sets base d) p.
Proof.
  intros n d c n' d' c' base p H Hfresh Hrf. unfold optimize_chain_snat in H.
  destruct (optimize_rules_snat n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_snat_eval (c_rules c) n d m'' dd'' rr'' base p E Hfresh Hrf).
  reflexivity.
Qed.

(** The snat pass preserves set-/vmap-read freshness: the merged [mk_snat_rule]
    has an empty body and no verdict map, so it reads NO setname/vmapname. *)
Lemma optimize_rules_snat_output_set_fresh : forall rs n d n' d' rs',
  optimize_rules_snat n d rs = (n', d', rs') ->
  Forall (rule_set_fresh n) rs -> Forall (rule_set_fresh n') rs'.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H Hrf. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; exact Hrf.
  - cbn in H; inversion H; subst; exact Hrf.
  - rewrite optimize_rules_snat_cons2 in H.
    inversion Hrf as [| ? ? Hf1 Hrf2]; subst.
    inversion Hrf2 as [| ? ? Hf2 Hrf_rest]; subst.
    destruct (snat_merge_pair r1 r2) as [[[[[f v1] v2] T1] T2]|] eqn:Ep; cbv zeta in H.
    + remember (optimize_rules_snat (S n)
                  {| sd_sets := sd_sets d; sd_vmaps := sd_vmaps d;
                     sd_maps := (mapname n, dmap2 v1 v2 T1 T2) :: sd_maps d |} rest)
        as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst n' d' rs'. clear H. constructor.
      * intros j Hj Hin. cbn [mk_snat_rule r_body body_set_names body_matches flat_map] in Hin.
        contradiction.
      * apply (IH rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E)).
        eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia|exact Hr]
                            |exact Hrf_rest].
    + remember (optimize_rules_snat n d (r2 :: rest)) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst n' d' rs'. clear H.
      pose proof (optimize_rules_snat_mono (r2 :: rest) n d _ _ _ (eq_sym E)) as Hmono.
      constructor;
        [apply (rule_set_fresh_mono n m'' r1 Hmono Hf1)
        |apply (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E));
           constructor; assumption].
Qed.

Lemma optimize_rules_snat_output_vmap_fresh : forall rs n d n' d' rs',
  optimize_rules_snat n d rs = (n', d', rs') ->
  Forall (rule_vmap_fresh n) rs -> Forall (rule_vmap_fresh n') rs'.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H Hrf. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; exact Hrf.
  - cbn in H; inversion H; subst; exact Hrf.
  - rewrite optimize_rules_snat_cons2 in H.
    inversion Hrf as [| ? ? Hf1 Hrf2]; subst.
    inversion Hrf2 as [| ? ? Hf2 Hrf_rest]; subst.
    destruct (snat_merge_pair r1 r2) as [[[[[f v1] v2] T1] T2]|] eqn:Ep; cbv zeta in H.
    + remember (optimize_rules_snat (S n)
                  {| sd_sets := sd_sets d; sd_vmaps := sd_vmaps d;
                     sd_maps := (mapname n, dmap2 v1 v2 T1 T2) :: sd_maps d |} rest)
        as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst n' d' rs'. clear H. constructor.
      * intros j Hj Hin. cbn [mk_snat_rule rule_vmap_name r_vmap r_outcome] in Hin. contradiction.
      * apply (IH rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E)).
        eapply Forall_impl; [intros r Hr; apply (rule_vmap_fresh_mono n (S n) r); [lia|exact Hr]
                            |exact Hrf_rest].
    + remember (optimize_rules_snat n d (r2 :: rest)) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst n' d' rs'. clear H.
      pose proof (optimize_rules_snat_mono (r2 :: rest) n d _ _ _ (eq_sym E)) as Hmono.
      constructor;
        [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
        |apply (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E));
           constructor; assumption].
Qed.

Lemma optimize_chain_snat_output_set_fresh : forall n d c n' d' c',
  optimize_chain_snat n d c = (n', d', c') ->
  Forall (rule_set_fresh n) (c_rules c) -> Forall (rule_set_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_snat in H.
  destruct (optimize_rules_snat n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. cbn [c_rules].
  apply (optimize_rules_snat_output_set_fresh _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_snat_output_vmap_fresh : forall n d c n' d' c',
  optimize_chain_snat n d c = (n', d', c') ->
  Forall (rule_vmap_fresh n) (c_rules c) -> Forall (rule_vmap_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_snat in H.
  destruct (optimize_rules_snat n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. cbn [c_rules].
  apply (optimize_rules_snat_output_vmap_fresh _ _ _ _ _ _ E Hrf).
Qed.

(** snat preserves nat-map read-freshness: the ONLY nat-map name the merged rule
    reads is [mapname n], which is BELOW the output counter [n'] (>= S n). *)
Lemma optimize_rules_snat_output_nat_map_fresh : forall rs n d n' d' rs',
  optimize_rules_snat n d rs = (n', d', rs') ->
  Forall (rule_nat_map_fresh n) rs -> Forall (rule_nat_map_fresh n') rs'.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H Hrf. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; exact Hrf.
  - cbn in H; inversion H; subst; exact Hrf.
  - rewrite optimize_rules_snat_cons2 in H.
    inversion Hrf as [| ? ? Hf1 Hrf2]; subst.
    inversion Hrf2 as [| ? ? Hf2 Hrf_rest]; subst.
    destruct (snat_merge_pair r1 r2) as [[[[[f v1] v2] T1] T2]|] eqn:Ep; cbv zeta in H.
    + remember (optimize_rules_snat (S n)
                  {| sd_sets := sd_sets d; sd_vmaps := sd_vmaps d;
                     sd_maps := (mapname n, dmap2 v1 v2 T1 T2) :: sd_maps d |} rest)
        as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst n' d' rs'. clear H.
      pose proof (optimize_rules_snat_mono rest (S n) _ _ _ _ (eq_sym E)) as Hmono.
      constructor.
      * intros j Hj Hin.
        cbn [mk_snat_rule rule_nat_map_name r_nat snat_map_spec nat_map r_outcome] in Hin.
        destruct Hin as [Heq | []]. apply mapname_inj in Heq. lia.
      * apply (IH rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E)).
        eapply Forall_impl; [intros r Hr; apply (rule_nat_map_fresh_mono n (S n) r); [lia|exact Hr]
                            |exact Hrf_rest].
    + remember (optimize_rules_snat n d (r2 :: rest)) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst n' d' rs'. clear H.
      pose proof (optimize_rules_snat_mono (r2 :: rest) n d _ _ _ (eq_sym E)) as Hmono.
      constructor;
        [apply (rule_nat_map_fresh_mono n m'' r1 Hmono Hf1)
        |apply (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E));
           constructor; assumption].
Qed.

Lemma optimize_chain_snat_output_nat_map_fresh : forall n d c n' d' c',
  optimize_chain_snat n d c = (n', d', c') ->
  Forall (rule_nat_map_fresh n) (c_rules c) -> Forall (rule_nat_map_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_snat in H.
  destruct (optimize_rules_snat n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. cbn [c_rules].
  apply (optimize_rules_snat_output_nat_map_fresh _ _ _ _ _ _ E Hrf).
Qed.


(** ** Part 3: unconditional per-pass correctness.

    Each theorem drops [rules_clean] in favour of [Forall (rule_set_fresh n)]
    (resp. [rule_vmap_fresh]).  The MERGE case needs no cleanliness: the run-merge
    lemmas are body-agnostic.  The PASS-THROUGH case uses read-freshness +
    [decls_agree_rule_*seam] to keep the passed rule env-stable. *)

(** *** valueset. *)
(** STAGE — composed into [optimize_table_correct_uncond_gen]; not a standalone headline. *)
Theorem optimize_rules_valueset_correct_uncond : forall fuel rs n d n' d' rs' base p,
  optimize_rules_valueset fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) rs ->
  eval_rules rs' (env_with_sets base d') p
  = eval_rules rs  (env_with_sets base d) p.
Proof.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base p H Hfresh Hrf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_valueset_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_value_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct (take_value_run_shape r1 f v1 body (r2 :: rest) vs rest' Ehd Erun)
          as [Hsplit Hwidth].
        destruct vs as [| v vs'].
        -- (* no eligible neighbour: keep r1, recurse *)
           remember (optimize_rules_valueset fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           cbn [eval_rules].
           rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
           assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_setseam base d dd'' r1 n).
             - apply (optimize_rules_valueset_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_valueset_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_valueset_assoc_stable fuel n d (r2 :: rest)
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
           rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
           rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
           rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
        -- (* RUN of >= 2 rules: fold them all into one __setN *)
           cbv zeta in H.
           remember (optimize_rules_valueset fuel (S n)
                       {| sd_sets := (setname n, map (fun w => (w,w)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (vals := v1 :: v :: vs') in *.
           set (elems := map (fun w => (w, w)) vals) in *.
           set (dn := {| sd_sets := (setname n, elems) :: sd_sets d;
                         sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun w => mk_head (MCmp f CEq w) body r1) vals ++ rest').
           { subst vals. cbn [map app]. f_equal.
             - apply (head_value_canon r1 f v1 body Ehd).
             - exact Hsplit. }
           (* read-freshness of rest' at S n (suffix of (r2::rest), monotone) *)
           assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia | exact Hr] |].
             assert (Hsub : Forall (rule_set_fresh n) rest').
             { rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
             exact Hsub. }
           assert (Htail : eval_rules rr'' (env_with_sets base dd'') p
                           = eval_rules rest' (env_with_sets base dn) p).
           { eapply (IH rest' (S n) dn m'' dd'' rr'' base p (eq_sym Erec)); [| exact Hrf_rest'].
             intros k Hk Hin. subst dn; cbn [sd_sets map] in Hin.
             destruct Hin as [Heq | Hin].
             - apply setname_inj in Heq. lia.
             - apply (Hfresh k); [lia | exact Hin]. }
           assert (Hlook : e_set (env_with_sets base dd'') (setname n)
                           = elems).
           { rewrite e_set_declared.
             erewrite (optimize_rules_valueset_assoc_stable fuel (S n) dn _ _ _ _
                         (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           set (ed := env_with_sets base dd'') in *.
           assert (Hcert : eval_matchcond (MConcatSet [f] false (setname n)) ed p
                   = existsb (fun w => eval_matchcond (MCmp f CEq w) ed p) vals).
           { apply (concat_set_existsb f vals (setname n) ed p).
             - subst elems. exact Hlook.
             - intros w Hw Hld.
               assert (Hfxw : field_fixed_len f = Some (Datatypes.length w)).
               { subst vals. destruct Hw as [Hw | Hw].
                 - subst w. apply (take_value_run_head_width r1 f v1 body r2 rest
                                     (v :: vs') rest' Ehd Erun). discriminate.
                 - apply (Hwidth w Hw). }
               apply (field_fixed_len_loaded f (Datatypes.length w) ed p Hfxw Hld). }
           transitivity (eval_rules
             (map (fun m => mk_head m body r1) (map (fun w => MCmp f CEq w) vals)
              ++ rr'') ed p).
           { apply (eval_rules_run_merge_abs
                      (map (fun w => MCmp f CEq w) vals)
                      (fun q => fields_loadable [f] q) body r1
                      (MConcatSet [f] false (setname n)) rr'' ed p).
             - subst vals. discriminate.
             - intros m Hm. apply (match_loadable_run f vals p m Hm).
             - apply match_loadable_mconcat1.
             - rewrite Hcert. rewrite existsb_map_eq. reflexivity. }
           rewrite List.map_map.
           assert (Htail' : eval_rules rr'' ed p = eval_rules rest' ed p).
           { rewrite Htail. unfold ed.
             apply (eval_rules_agree_gen rest' p base dn dd'').
             intros r Hr. apply decls_agree_rule_sym.
             apply (decls_agree_rule_setseam base dn dd'' r (S n)).
             - apply (optimize_rules_valueset_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_valueset_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_valueset_assoc_stable fuel (S n) dn rest'
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - rewrite Forall_forall in Hrf_rest'. apply Hrf_rest'; exact Hr. }
           rewrite (eval_rules_app_cong
                      (map (fun w => mk_head (MCmp f CEq w) body r1) vals)
                      rr'' rest' ed p Htail').
           rewrite <- Hrun_eq.
           (* whole input list at dd'' equals at d (read-fresh + assoc-stable) *)
           assert (Hvm_dd : sd_vmaps dd'' = sd_vmaps d).
           { rewrite (optimize_rules_valueset_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hmaps_dd : sd_maps dd'' = sd_maps d).
           { rewrite (optimize_rules_valueset_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hassoc_dd : forall nm X, (forall k, n <= k -> nm <> setname k) ->
                     assoc_str nm (sd_sets dd'') X = assoc_str nm (sd_sets d) X).
           { intros nm X Hf.
             rewrite (optimize_rules_valueset_assoc_stable fuel (S n) dn rest' m'' dd'' rr'' nm X
                        (eq_sym Erec) (fun k Hk => Hf k ltac:(lia))).
             subst dn; cbn [sd_sets assoc_str].
             destruct (String.eqb nm (setname n)) eqn:Eq.
             - apply String.eqb_eq in Eq. exfalso. apply (Hf n (Nat.le_refl n) Eq).
             - reflexivity. }
           unfold ed. apply (eval_rules_agree_gen (r1 :: r2 :: rest) p base dd'' d).
           intros r Hr. apply (decls_agree_rule_setseam base d dd'' r n Hvm_dd Hmaps_dd Hassoc_dd).
           rewrite Forall_forall in Hrf. apply Hrf; exact Hr.
      * (* head not value-eligible: keep r1, recurse *)
        remember (optimize_rules_valueset fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        cbn [eval_rules].
        rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
        assert (Hda1 : decls_agree_rule base dd'' d r1).
        { apply (decls_agree_rule_setseam base d dd'' r1 n).
          - apply (optimize_rules_valueset_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - apply (optimize_rules_valueset_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - intros nm X Hf. apply (optimize_rules_valueset_assoc_stable fuel n d (r2 :: rest)
                                    m'' dd'' rr'' nm X (eq_sym Erec) Hf).
          - exact Hf1. }
        rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
        rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
        rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
Qed.

(** *** dscp (masked-payload value->set consolidation, Optimize_Dscp).  Structurally
    identical to [valueset], but the run's heads are masked equalities [MMasked f CEq
    mask xor v] and the merged head is a masked-lookup [MSetT f [TBitAnd mask xor]
    false __setN] over the N point values; [mmasked_set_existsb] is the membership
    certificate (with the [data_bitops] width discharged from the fixed-width side
    condition), and [eval_rules_run_merge_abs] collapses the run (both merged and run
    heads share [match_loadable = field_loadable f]). *)
(** STAGE — composed into [optimize_table_correct_uncond_gen]; not a standalone headline. *)
Theorem optimize_rules_dscp_correct_uncond : forall fuel rs n d n' d' rs' base p,
  optimize_rules_dscp fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) rs ->
  eval_rules rs' (env_with_sets base d') p
  = eval_rules rs  (env_with_sets base d) p.
Proof.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base p H Hfresh Hrf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_dscp_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_dscp r1) as [[[[[f mask] xor] v1] body] |] eqn:Ehd.
      * destruct (take_dscp_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct (take_dscp_run_shape r1 f mask xor v1 body (r2 :: rest) vs rest' Ehd Erun)
          as [Hsplit Hwidth].
        destruct vs as [| v vs'].
        -- remember (optimize_rules_dscp fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           cbn [eval_rules].
           rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
           assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_setseam base d dd'' r1 n).
             - apply (optimize_rules_dscp_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_dscp_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_dscp_assoc_stable fuel n d (r2 :: rest)
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
           rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
           rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
           rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
        -- cbv zeta in H.
           remember (optimize_rules_dscp fuel (S n)
                       {| sd_sets := (setname n, map (fun w => (w,w)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (vals := v1 :: v :: vs') in *.
           set (elems := map (fun w => (w, w)) vals) in *.
           set (dn := {| sd_sets := (setname n, elems) :: sd_sets d;
                         sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun w => mk_head (MMasked f CEq mask xor w) body r1) vals ++ rest').
           { subst vals. cbn [map app]. f_equal.
             - apply (head_dscp_canon r1 f mask xor v1 body Ehd).
             - exact Hsplit. }
           assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia | exact Hr] |].
             assert (Hsub : Forall (rule_set_fresh n) rest').
             { rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
             exact Hsub. }
           assert (Htail : eval_rules rr'' (env_with_sets base dd'') p
                           = eval_rules rest' (env_with_sets base dn) p).
           { eapply (IH rest' (S n) dn m'' dd'' rr'' base p (eq_sym Erec)); [| exact Hrf_rest'].
             intros k Hk Hin. subst dn; cbn [sd_sets map] in Hin.
             destruct Hin as [Heq | Hin].
             - apply setname_inj in Heq. lia.
             - apply (Hfresh k); [lia | exact Hin]. }
           assert (Hlook : e_set (env_with_sets base dd'') (setname n)
                           = elems).
           { rewrite e_set_declared.
             erewrite (optimize_rules_dscp_assoc_stable fuel (S n) dn _ _ _ _
                         (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           set (ed := env_with_sets base dd'') in *.
           (* every value in the run has the field's fixed width, and r1's mask/xor
              have that width too *)
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
           assert (Hcert : eval_matchcond (MSetT f [TBitAnd mask xor] false (setname n)) ed p
                   = existsb (fun w => eval_matchcond (MMasked f CEq mask xor w) ed p) vals).
           { apply (mmasked_set_existsb f mask xor vals (setname n) ed p).
             - subst elems. exact Hlook.
             - intros w Hw Hld.
               assert (Hfxw : field_fixed_len f = Some (Datatypes.length w)) by (apply (Hallw w Hw)).
               assert (Hfl : Datatypes.length (field_value f ed p) = Datatypes.length w)
                 by (apply (field_fixed_len_loaded f (Datatypes.length w) ed p Hfxw Hld)).
               assert (Hww1 : Datatypes.length w = Datatypes.length v1)
                 by (assert (Some (Datatypes.length w) = Some (Datatypes.length v1)) as Hs
                       by (rewrite <- Hfxw; exact Hfx1); injection Hs; auto).
               rewrite (data_bitops_length_eq (field_value f ed p) mask xor).
               + exact Hfl.
               + lia.
               + lia. }
           transitivity (eval_rules
             (map (fun m => mk_head m body r1)
                  (map (fun w => MMasked f CEq mask xor w) vals)
              ++ rr'') ed p).
           { apply (eval_rules_run_merge_abs
                      (map (fun w => MMasked f CEq mask xor w) vals)
                      (fun q => field_loadable f q) body r1
                      (MSetT f [TBitAnd mask xor] false (setname n)) rr'' ed p).
             - subst vals. discriminate.
             - intros m Hm. apply (match_loadable_dscp_run f mask xor vals p m Hm).
             - apply match_loadable_msett_bitand.
             - rewrite Hcert. rewrite existsb_map_eq. reflexivity. }
           rewrite List.map_map.
           assert (Htail' : eval_rules rr'' ed p = eval_rules rest' ed p).
           { rewrite Htail. unfold ed.
             apply (eval_rules_agree_gen rest' p base dn dd'').
             intros r Hr. apply decls_agree_rule_sym.
             apply (decls_agree_rule_setseam base dn dd'' r (S n)).
             - apply (optimize_rules_dscp_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_dscp_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_dscp_assoc_stable fuel (S n) dn rest'
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - rewrite Forall_forall in Hrf_rest'. apply Hrf_rest'; exact Hr. }
           rewrite (eval_rules_app_cong
                      (map (fun w => mk_head (MMasked f CEq mask xor w) body r1) vals)
                      rr'' rest' ed p Htail').
           rewrite <- Hrun_eq.
           assert (Hvm_dd : sd_vmaps dd'' = sd_vmaps d).
           { rewrite (optimize_rules_dscp_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hmaps_dd : sd_maps dd'' = sd_maps d).
           { rewrite (optimize_rules_dscp_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hassoc_dd : forall nm X, (forall k, n <= k -> nm <> setname k) ->
                     assoc_str nm (sd_sets dd'') X = assoc_str nm (sd_sets d) X).
           { intros nm X Hf.
             rewrite (optimize_rules_dscp_assoc_stable fuel (S n) dn rest' m'' dd'' rr'' nm X
                        (eq_sym Erec) (fun k Hk => Hf k ltac:(lia))).
             subst dn; cbn [sd_sets assoc_str].
             destruct (String.eqb nm (setname n)) eqn:Eq.
             - apply String.eqb_eq in Eq. exfalso. apply (Hf n (Nat.le_refl n) Eq).
             - reflexivity. }
           unfold ed. apply (eval_rules_agree_gen (r1 :: r2 :: rest) p base dd'' d).
           intros r Hr. apply (decls_agree_rule_setseam base d dd'' r n Hvm_dd Hmaps_dd Hassoc_dd).
           rewrite Forall_forall in Hrf. apply Hrf; exact Hr.
      * remember (optimize_rules_dscp fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        cbn [eval_rules].
        rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
        assert (Hda1 : decls_agree_rule base dd'' d r1).
        { apply (decls_agree_rule_setseam base d dd'' r1 n).
          - apply (optimize_rules_dscp_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - apply (optimize_rules_dscp_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - intros nm X Hf. apply (optimize_rules_dscp_assoc_stable fuel n d (r2 :: rest)
                                    m'' dd'' rr'' nm X (eq_sym Erec) Hf).
          - exact Hf1. }
        rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
        rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
        rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
Qed.

(** *** intervalsethostorder (host-order interval / range set consolidation, Optimize_IntervalSetHostOrder).
    Structurally identical to [intervalset], but the run's heads are transformed ranges
    [MRangeT f ts false lo hi] and the synthesised set head is [MSetT f ts false __setN]
    — the byteorder transform [ts] is carried IDENTICALLY on both, and the membership
    certificate ([msett_ivs_existsb]) collapses the [MSetT] to the run's [existsb]. *)
(** STAGE — composed into [optimize_table_correct_uncond_gen]; not a standalone headline. *)
Theorem optimize_rules_intervalsethostorder_correct_uncond : forall fuel rs n d n' d' rs' base p,
  optimize_rules_intervalsethostorder fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) rs ->
  eval_rules rs' (env_with_sets base d') p
  = eval_rules rs  (env_with_sets base d) p.
Proof.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base p H Hfresh Hrf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_intervalsethostorder_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_ivsett r1) as [[[[[f ts] lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_ivsett_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        pose proof (take_ivsett_run_shape r1 f ts lo1 hi1 body (r2 :: rest) ivs rest' Ehd Erun) as Hsplit.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           cbn [eval_rules].
           rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
           assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_setseam base d dd'' r1 n).
             - apply (optimize_rules_intervalsethostorder_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_intervalsethostorder_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_intervalsethostorder_assoc_stable fuel n d (r2 :: rest)
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
           rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
           rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
           rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
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
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun iv0 => mk_head (MRangeT f ts false (fst iv0) (snd iv0)) body r1) ivsAll
                     ++ rest').
           { subst ivsAll. cbn [map app fst snd]. f_equal.
             - apply (head_ivsett_canon r1 f ts lo1 hi1 body Ehd).
             - exact Hsplit. }
           assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia | exact Hr] |].
             assert (Hsub : Forall (rule_set_fresh n) rest').
             { rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
             exact Hsub. }
           assert (Htail : eval_rules rr'' (env_with_sets base dd'') p
                           = eval_rules rest' (env_with_sets base dn) p).
           { eapply (IH rest' (S n) dn m'' dd'' rr'' base p (eq_sym Erec)); [| exact Hrf_rest'].
             intros k Hk Hin. subst dn; cbn [sd_sets map] in Hin.
             destruct Hin as [Heq | Hin].
             - apply setname_inj in Heq. lia.
             - apply (Hfresh k); [lia | exact Hin]. }
           assert (Hlook : e_set (env_with_sets base dd'') (setname n)
                           = ivsAll).
           { rewrite e_set_declared.
             erewrite (optimize_rules_intervalsethostorder_assoc_stable fuel (S n) dn _ _ _ _
                         (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           set (ed := env_with_sets base dd'') in *.
           assert (Hcert : eval_matchcond (MSetT f ts false (setname n)) ed p
                   = existsb (fun iv0 => eval_matchcond (MRangeT f ts false (fst iv0) (snd iv0)) ed p) ivsAll).
           { apply (msett_ivs_existsb f ts ivsAll (setname n) ed p). exact Hlook. }
           transitivity (eval_rules
             (map (fun m => mk_head m body r1)
                  (map (fun iv0 => MRangeT f ts false (fst iv0) (snd iv0)) ivsAll)
              ++ rr'') ed p).
           { apply (eval_rules_run_merge_abs
                      (map (fun iv0 => MRangeT f ts false (fst iv0) (snd iv0)) ivsAll)
                      (fun q => field_loadable f q) body r1
                      (MSetT f ts false (setname n)) rr'' ed p).
             - subst ivsAll. discriminate.
             - intros m Hm. apply (match_loadable_ranget_run f ts ivsAll p m Hm).
             - apply match_loadable_msett.
             - rewrite Hcert. rewrite existsb_map_eq. reflexivity. }
           rewrite List.map_map.
           assert (Htail' : eval_rules rr'' ed p = eval_rules rest' ed p).
           { rewrite Htail. unfold ed.
             apply (eval_rules_agree_gen rest' p base dn dd'').
             intros r Hr. apply decls_agree_rule_sym.
             apply (decls_agree_rule_setseam base dn dd'' r (S n)).
             - apply (optimize_rules_intervalsethostorder_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_intervalsethostorder_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_intervalsethostorder_assoc_stable fuel (S n) dn rest'
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - rewrite Forall_forall in Hrf_rest'. apply Hrf_rest'; exact Hr. }
           rewrite (eval_rules_app_cong
                      (map (fun iv0 => mk_head (MRangeT f ts false (fst iv0) (snd iv0)) body r1) ivsAll)
                      rr'' rest' ed p Htail').
           rewrite <- Hrun_eq.
           assert (Hvm_dd : sd_vmaps dd'' = sd_vmaps d).
           { rewrite (optimize_rules_intervalsethostorder_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hmaps_dd : sd_maps dd'' = sd_maps d).
           { rewrite (optimize_rules_intervalsethostorder_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hassoc_dd : forall nm X, (forall k, n <= k -> nm <> setname k) ->
                     assoc_str nm (sd_sets dd'') X = assoc_str nm (sd_sets d) X).
           { intros nm X Hf.
             rewrite (optimize_rules_intervalsethostorder_assoc_stable fuel (S n) dn rest' m'' dd'' rr'' nm X
                        (eq_sym Erec) (fun k Hk => Hf k ltac:(lia))).
             subst dn; cbn [sd_sets assoc_str].
             destruct (String.eqb nm (setname n)) eqn:Eq.
             - apply String.eqb_eq in Eq. exfalso. apply (Hf n (Nat.le_refl n) Eq).
             - reflexivity. }
           unfold ed. apply (eval_rules_agree_gen (r1 :: r2 :: rest) p base dd'' d).
           intros r Hr. apply (decls_agree_rule_setseam base d dd'' r n Hvm_dd Hmaps_dd Hassoc_dd).
           rewrite Forall_forall in Hrf. apply Hrf; exact Hr.
      * remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        cbn [eval_rules].
        rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
        assert (Hda1 : decls_agree_rule base dd'' d r1).
        { apply (decls_agree_rule_setseam base d dd'' r1 n).
          - apply (optimize_rules_intervalsethostorder_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - apply (optimize_rules_intervalsethostorder_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - intros nm X Hf. apply (optimize_rules_intervalsethostorder_assoc_stable fuel n d (r2 :: rest)
                                    m'' dd'' rr'' nm X (eq_sym Erec) Hf).
          - exact Hf1. }
        rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
        rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
        rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
Qed.

(** *** intervalset (interval / range set consolidation, Optimize_IntervalSet).  Structurally a
    single-field set merge like valueset, but the run's heads are [MRange]s and the
    synthesised set carries the intervals directly — NO fixed-width side-condition
    (range membership uses [data_le], which does not truncate). *)

(** An [MRange] head contributes NO set name, so a range-head shell's set names are
    exactly its tail's. *)
Lemma body_set_names_cons_mrange : forall f lo hi body,
  body_set_names (BMatch (MRange f false lo hi) :: body) = body_set_names body.
Proof. reflexivity. Qed.

(** STAGE — composed into [optimize_table_correct_uncond_gen]; not a standalone headline. *)
Theorem optimize_rules_intervalset_correct_uncond : forall fuel rs n d n' d' rs' base p,
  optimize_rules_intervalset fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) rs ->
  eval_rules rs' (env_with_sets base d') p
  = eval_rules rs  (env_with_sets base d) p.
Proof.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base p H Hfresh Hrf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_intervalset_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_range r1) as [[[[f lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_range_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        pose proof (take_range_run_shape r1 f lo1 hi1 body (r2 :: rest) ivs rest' Ehd Erun) as Hsplit.
        destruct ivs as [| iv ivs'].
        -- (* no eligible neighbour: keep r1, recurse *)
           remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           cbn [eval_rules].
           rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
           assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_setseam base d dd'' r1 n).
             - apply (optimize_rules_intervalset_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_intervalset_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_intervalset_assoc_stable fuel n d (r2 :: rest)
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
           rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
           rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
           rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
        -- (* RUN of >= 2 rules: fold into one interval __setN *)
           cbv zeta in H.
           remember (optimize_rules_intervalset fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (ivsAll := (lo1, hi1) :: iv :: ivs') in *.
           set (dn := {| sd_sets := (setname n, ivsAll) :: sd_sets d;
                         sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun iv0 => mk_head (MRange f false (fst iv0) (snd iv0)) body r1) ivsAll
                     ++ rest').
           { subst ivsAll. cbn [map app fst snd]. f_equal.
             - apply (head_range_canon r1 f lo1 hi1 body Ehd).
             - exact Hsplit. }
           assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia | exact Hr] |].
             assert (Hsub : Forall (rule_set_fresh n) rest').
             { rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
             exact Hsub. }
           assert (Htail : eval_rules rr'' (env_with_sets base dd'') p
                           = eval_rules rest' (env_with_sets base dn) p).
           { eapply (IH rest' (S n) dn m'' dd'' rr'' base p (eq_sym Erec)); [| exact Hrf_rest'].
             intros k Hk Hin. subst dn; cbn [sd_sets map] in Hin.
             destruct Hin as [Heq | Hin].
             - apply setname_inj in Heq. lia.
             - apply (Hfresh k); [lia | exact Hin]. }
           assert (Hlook : e_set (env_with_sets base dd'') (setname n)
                           = ivsAll).
           { rewrite e_set_declared.
             erewrite (optimize_rules_intervalset_assoc_stable fuel (S n) dn _ _ _ _
                         (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           set (ed := env_with_sets base dd'') in *.
           assert (Hcert : eval_matchcond (MConcatSet [f] false (setname n)) ed p
                   = existsb (fun iv0 => eval_matchcond (MRange f false (fst iv0) (snd iv0)) ed p) ivsAll).
           { apply (concat_set_ivs_existsb f ivsAll (setname n) ed p). exact Hlook. }
           transitivity (eval_rules
             (map (fun m => mk_head m body r1)
                  (map (fun iv0 => MRange f false (fst iv0) (snd iv0)) ivsAll)
              ++ rr'') ed p).
           { apply (eval_rules_run_merge_abs
                      (map (fun iv0 => MRange f false (fst iv0) (snd iv0)) ivsAll)
                      (fun q => fields_loadable [f] q) body r1
                      (MConcatSet [f] false (setname n)) rr'' ed p).
             - subst ivsAll. discriminate.
             - intros m Hm. apply (match_loadable_range_run f ivsAll p m Hm).
             - apply match_loadable_mconcat1.
             - rewrite Hcert. rewrite existsb_map_eq. reflexivity. }
           rewrite List.map_map.
           assert (Htail' : eval_rules rr'' ed p = eval_rules rest' ed p).
           { rewrite Htail. unfold ed.
             apply (eval_rules_agree_gen rest' p base dn dd'').
             intros r Hr. apply decls_agree_rule_sym.
             apply (decls_agree_rule_setseam base dn dd'' r (S n)).
             - apply (optimize_rules_intervalset_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_intervalset_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_intervalset_assoc_stable fuel (S n) dn rest'
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - rewrite Forall_forall in Hrf_rest'. apply Hrf_rest'; exact Hr. }
           rewrite (eval_rules_app_cong
                      (map (fun iv0 => mk_head (MRange f false (fst iv0) (snd iv0)) body r1) ivsAll)
                      rr'' rest' ed p Htail').
           rewrite <- Hrun_eq.
           assert (Hvm_dd : sd_vmaps dd'' = sd_vmaps d).
           { rewrite (optimize_rules_intervalset_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hmaps_dd : sd_maps dd'' = sd_maps d).
           { rewrite (optimize_rules_intervalset_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hassoc_dd : forall nm X, (forall k, n <= k -> nm <> setname k) ->
                     assoc_str nm (sd_sets dd'') X = assoc_str nm (sd_sets d) X).
           { intros nm X Hf.
             rewrite (optimize_rules_intervalset_assoc_stable fuel (S n) dn rest' m'' dd'' rr'' nm X
                        (eq_sym Erec) (fun k Hk => Hf k ltac:(lia))).
             subst dn; cbn [sd_sets assoc_str].
             destruct (String.eqb nm (setname n)) eqn:Eq.
             - apply String.eqb_eq in Eq. exfalso. apply (Hf n (Nat.le_refl n) Eq).
             - reflexivity. }
           unfold ed. apply (eval_rules_agree_gen (r1 :: r2 :: rest) p base dd'' d).
           intros r Hr. apply (decls_agree_rule_setseam base d dd'' r n Hvm_dd Hmaps_dd Hassoc_dd).
           rewrite Forall_forall in Hrf. apply Hrf; exact Hr.
      * (* head not range-eligible: keep r1, recurse *)
        remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        cbn [eval_rules].
        rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
        assert (Hda1 : decls_agree_rule base dd'' d r1).
        { apply (decls_agree_rule_setseam base d dd'' r1 n).
          - apply (optimize_rules_intervalset_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - apply (optimize_rules_intervalset_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - intros nm X Hf. apply (optimize_rules_intervalset_assoc_stable fuel n d (r2 :: rest)
                                    m'' dd'' rr'' nm X (eq_sym Erec) Hf).
          - exact Hf1. }
        rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
        rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
        rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
Qed.

(** *** intervalsetguarded (GUARDED interval / range set consolidation, Optimize_IntervalSetGuarded).
    Combines the guarded run-collapse of [setguarded] ([existsb_guardhead_factor] factors
    the head l4proto/nfproto guard out of the [existsb]) with the interval membership
    certificate of [intervalset] ([concat_set_ivs_existsb]): a single-field [MConcatSet]
    over an interval set is EXACTLY the [existsb] disjunction of the [MRange] matches.
    No fixed-width side-condition. *)
(** STAGE — composed into [optimize_table_correct_uncond_gen]; not a standalone headline. *)
Theorem optimize_rules_intervalsetguarded_correct_uncond : forall fuel rs n d n' d' rs' base p,
  optimize_rules_intervalsetguarded fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) rs ->
  eval_rules rs' (env_with_sets base d') p
  = eval_rules rs  (env_with_sets base d) p.
Proof.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base p H Hfresh Hrf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_intervalsetguarded_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_rangeGr r1) as [[[[[gm f] lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_rangeg_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        pose proof (take_rangeg_run_shape r1 gm f lo1 hi1 body (r2 :: rest) ivs rest' Ehd Erun) as Hsplit.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           cbn [eval_rules].
           rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
           assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_setseam base d dd'' r1 n).
             - apply (optimize_rules_intervalsetguarded_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_intervalsetguarded_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_intervalsetguarded_assoc_stable fuel n d (r2 :: rest)
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
           rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
           rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
           rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
        -- cbv zeta in H.
           remember (optimize_rules_intervalsetguarded fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (ivsAll := (lo1, hi1) :: iv :: ivs') in *.
           set (dn := {| sd_sets := (setname n, ivsAll) :: sd_sets d;
                         sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun iv0 => orig_ruleGr f gm (fst iv0) (snd iv0) body r1) ivsAll
                     ++ rest').
           { subst ivsAll. cbn [map app fst snd]. f_equal.
             - apply (head_rangeGr_canon r1 gm f lo1 hi1 body Ehd).
             - exact Hsplit. }
           assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia | exact Hr] |].
             assert (Hsub : Forall (rule_set_fresh n) rest').
             { rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
             exact Hsub. }
           assert (Hvm_dd : sd_vmaps dd'' = sd_vmaps d).
           { rewrite (optimize_rules_intervalsetguarded_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hmaps_dd : sd_maps dd'' = sd_maps d).
           { rewrite (optimize_rules_intervalsetguarded_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hassoc_dd : forall nm X, (forall k, n <= k -> nm <> setname k) ->
                     assoc_str nm (sd_sets dd'') X = assoc_str nm (sd_sets d) X).
           { intros nm X Hf.
             rewrite (optimize_rules_intervalsetguarded_assoc_stable fuel (S n) dn rest' m'' dd'' rr'' nm X
                        (eq_sym Erec) (fun k Hk => Hf k ltac:(lia))).
             subst dn; cbn [sd_sets assoc_str].
             destruct (String.eqb nm (setname n)) eqn:Eq.
             - apply String.eqb_eq in Eq. exfalso. apply (Hf n (Nat.le_refl n) Eq).
             - reflexivity. }
           assert (Htail : eval_rules rr'' (env_with_sets base dd'') p
                           = eval_rules rest' (env_with_sets base dn) p).
           { eapply (IH rest' (S n) dn m'' dd'' rr'' base p (eq_sym Erec)); [| exact Hrf_rest'].
             intros k Hk Hin. subst dn; cbn [sd_sets map] in Hin.
             destruct Hin as [Heq | Hin].
             - apply setname_inj in Heq. lia.
             - apply (Hfresh k); [lia | exact Hin]. }
           assert (Hlook : e_set (env_with_sets base dd'') (setname n)
                           = ivsAll).
           { rewrite e_set_declared.
             erewrite (optimize_rules_intervalsetguarded_assoc_stable fuel (S n) dn _ _ _ _
                         (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           set (ed := env_with_sets base dd'') in *.
           assert (Hcert : eval_matchcond (MConcatSet [f] false (setname n)) ed p
                   = existsb (fun iv0 => eval_matchcond (MRange f false (fst iv0) (snd iv0)) ed p) ivsAll).
           { apply (concat_set_ivs_existsb f ivsAll (setname n) ed p). exact Hlook. }
           transitivity (eval_rules
             (map (fun iv0 => orig_ruleGr f gm (fst iv0) (snd iv0) body r1) ivsAll ++ rr'') ed p).
           { apply (eval_rules_run_collapse
                      (map (fun iv0 => orig_ruleGr f gm (fst iv0) (snd iv0) body r1) ivsAll)
                      (rule_loadable (merged_ruleGs f gm (setname n) body r1) ed p)
                      (outcome (merged_ruleGs f gm (setname n) body r1) ed p)
                      (merged_ruleGs f gm (setname n) body r1) rr'' ed p).
             - subst ivsAll. discriminate.
             - intros r Hr. apply in_map_iff in Hr as [iv0 [Hiv _]]. subst r.
               symmetry. apply merged_ruleGs_loadable_eq_origr.
             - intros r Hr. apply in_map_iff in Hr as [iv0 [Hiv _]]. subst r.
               symmetry. apply merged_ruleGs_outcome_eq_origr.
             - reflexivity.
             - reflexivity.
             - rewrite merged_ruleGs_applies. rewrite Hcert.
               rewrite existsb_map_eq.
               rewrite (existsb_ext _ _ _ ivsAll
                          (fun iv0 (_ : In iv0 ivsAll) =>
                             orig_ruleGr_applies f gm (fst iv0) (snd iv0) body r1 ed p)).
               symmetry. apply existsb_guardhead_factor. }
           assert (Htail' : eval_rules rr'' ed p = eval_rules rest' ed p).
           { rewrite Htail. unfold ed.
             apply (eval_rules_agree_gen rest' p base dn dd'').
             intros r Hr. apply decls_agree_rule_sym.
             apply (decls_agree_rule_setseam base dn dd'' r (S n)).
             - apply (optimize_rules_intervalsetguarded_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_intervalsetguarded_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_intervalsetguarded_assoc_stable fuel (S n) dn rest'
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - rewrite Forall_forall in Hrf_rest'. apply Hrf_rest'; exact Hr. }
           rewrite (eval_rules_app_cong
                      (map (fun iv0 => orig_ruleGr f gm (fst iv0) (snd iv0) body r1) ivsAll)
                      rr'' rest' ed p Htail').
           rewrite <- Hrun_eq.
           unfold ed. apply (eval_rules_agree_gen (r1 :: r2 :: rest) p base dd'' d).
           intros r Hr. apply (decls_agree_rule_setseam base d dd'' r n Hvm_dd Hmaps_dd Hassoc_dd).
           rewrite Forall_forall in Hrf. apply Hrf; exact Hr.
      * remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        cbn [eval_rules].
        rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
        assert (Hda1 : decls_agree_rule base dd'' d r1).
        { apply (decls_agree_rule_setseam base d dd'' r1 n).
          - apply (optimize_rules_intervalsetguarded_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - apply (optimize_rules_intervalsetguarded_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - intros nm X Hf. apply (optimize_rules_intervalsetguarded_assoc_stable fuel n d (r2 :: rest)
                                    m'' dd'' rr'' nm X (eq_sym Erec) Hf).
          - exact Hf1. }
        rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
        rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
        rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
Qed.

(** *** mixedpointrangeguarded (GUARDED MIXED point+range set consolidation, Optimize_MixedPointRangeGuarded).
    Structurally identical to [intervalsetguarded]; the only new content is the per-element
    verdict bridge [eval_melem_mrange] (a point head [MCmp f CEq v] equals the
    degenerate-interval [MRange f false v v] match under the field's FIXED-WIDTH
    guard), applied through the interval membership certificate. *)
(** STAGE — composed into [optimize_table_correct_uncond_gen]; not a standalone headline. *)
Theorem optimize_rules_mixedpointrangeguarded_correct_uncond : forall fuel rs n d n' d' rs' base p,
  optimize_rules_mixedpointrangeguarded fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) rs ->
  eval_rules rs' (env_with_sets base d') p
  = eval_rules rs  (env_with_sets base d) p.
Proof.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base p H Hfresh Hrf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_mixedpointrangeguarded_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_mixGm r1) as [[[[gm f] e1] body] |] eqn:Ehd.
      * destruct (take_mix_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        pose proof (take_mix_run_shape r1 gm f e1 body (r2 :: rest) es rest' Ehd Erun) as Hsplit.
        destruct es as [| e es'].
        -- remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           cbn [eval_rules].
           rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
           assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_setseam base d dd'' r1 n).
             - apply (optimize_rules_mixedpointrangeguarded_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_mixedpointrangeguarded_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_mixedpointrangeguarded_assoc_stable fuel n d (r2 :: rest)
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
           rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
           rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
           rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
        -- cbv zeta in H.
           remember (optimize_rules_mixedpointrangeguarded fuel (S n)
                       {| sd_sets := (setname n, map melem_iv (e1 :: e :: es')) :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (esAll := e1 :: e :: es') in *.
           set (dn := {| sd_sets := (setname n, map melem_iv esAll) :: sd_sets d;
                         sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
           assert (Hok_all : forall e0, In e0 esAll -> melem_ok f e0 = true).
           { intros e0 He0.
             pose proof (take_mix_run_melem_ok r1 gm f e1 body (r2 :: rest)
                           (e :: es') rest' Ehd Erun ltac:(discriminate)) as Hforall.
             rewrite forallb_forall in Hforall. apply (Hforall e0). exact He0. }
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun e0 => orig_ruleGm f gm e0 body r1) esAll ++ rest').
           { subst esAll. cbn [map app]. f_equal.
             - apply (head_mixGm_canon r1 gm f e1 body Ehd).
             - exact Hsplit. }
           assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia | exact Hr] |].
             assert (Hsub : Forall (rule_set_fresh n) rest').
             { rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
             exact Hsub. }
           assert (Hvm_dd : sd_vmaps dd'' = sd_vmaps d).
           { rewrite (optimize_rules_mixedpointrangeguarded_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hmaps_dd : sd_maps dd'' = sd_maps d).
           { rewrite (optimize_rules_mixedpointrangeguarded_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hassoc_dd : forall nm X, (forall k, n <= k -> nm <> setname k) ->
                     assoc_str nm (sd_sets dd'') X = assoc_str nm (sd_sets d) X).
           { intros nm X Hf.
             rewrite (optimize_rules_mixedpointrangeguarded_assoc_stable fuel (S n) dn rest' m'' dd'' rr'' nm X
                        (eq_sym Erec) (fun k Hk => Hf k ltac:(lia))).
             subst dn; cbn [sd_sets assoc_str].
             destruct (String.eqb nm (setname n)) eqn:Eq.
             - apply String.eqb_eq in Eq. exfalso. apply (Hf n (Nat.le_refl n) Eq).
             - reflexivity. }
           assert (Htail : eval_rules rr'' (env_with_sets base dd'') p
                           = eval_rules rest' (env_with_sets base dn) p).
           { eapply (IH rest' (S n) dn m'' dd'' rr'' base p (eq_sym Erec)); [| exact Hrf_rest'].
             intros k Hk Hin. subst dn; cbn [sd_sets map] in Hin.
             destruct Hin as [Heq | Hin].
             - apply setname_inj in Heq. lia.
             - apply (Hfresh k); [lia | exact Hin]. }
           assert (Hlook : e_set (env_with_sets base dd'') (setname n)
                           = map melem_iv esAll).
           { rewrite e_set_declared.
             erewrite (optimize_rules_mixedpointrangeguarded_assoc_stable fuel (S n) dn _ _ _ _
                         (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           set (ed := env_with_sets base dd'') in *.
           assert (Hcert : eval_matchcond (MConcatSet [f] false (setname n)) ed p
                   = existsb (fun iv0 => eval_matchcond (MRange f false (fst iv0) (snd iv0)) ed p)
                             (map melem_iv esAll)).
           { apply (concat_set_ivs_existsb f (map melem_iv esAll) (setname n) ed p). exact Hlook. }
           transitivity (eval_rules
             (map (fun e0 => orig_ruleGm f gm e0 body r1) esAll ++ rr'') ed p).
           { apply (eval_rules_run_collapse
                      (map (fun e0 => orig_ruleGm f gm e0 body r1) esAll)
                      (rule_loadable (merged_ruleGs f gm (setname n) body r1) ed p)
                      (outcome (merged_ruleGs f gm (setname n) body r1) ed p)
                      (merged_ruleGs f gm (setname n) body r1) rr'' ed p).
             - subst esAll. discriminate.
             - intros r Hr. apply in_map_iff in Hr as [e0 [He0 _]]. subst r.
               symmetry. apply merged_ruleGs_loadable_eq_origm.
             - intros r Hr. apply in_map_iff in Hr as [e0 [He0 _]]. subst r.
               symmetry. apply merged_ruleGs_outcome_eq_origm.
             - reflexivity.
             - reflexivity.
             - rewrite merged_ruleGs_applies. rewrite Hcert. rewrite existsb_map_eq.
               rewrite (existsb_ext _
                          (fun e0 => eval_matchcond
                                       (MRange f false (fst (melem_iv e0)) (snd (melem_iv e0))) ed p)
                          (fun e0 => eval_matchcond (melem_mc f e0) ed p) esAll
                          (fun e0 He0 => eq_sym (eval_melem_mrange f e0 ed p (Hok_all e0 He0)))).
               symmetry. rewrite existsb_map_eq.
               rewrite (existsb_ext _ _ _ esAll
                          (fun e0 (_ : In e0 esAll) =>
                             orig_ruleGm_applies f gm e0 body r1 ed p)).
               apply existsb_guardhead_factor. }
           assert (Htail' : eval_rules rr'' ed p = eval_rules rest' ed p).
           { rewrite Htail. unfold ed.
             apply (eval_rules_agree_gen rest' p base dn dd'').
             intros r Hr. apply decls_agree_rule_sym.
             apply (decls_agree_rule_setseam base dn dd'' r (S n)).
             - apply (optimize_rules_mixedpointrangeguarded_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_mixedpointrangeguarded_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_mixedpointrangeguarded_assoc_stable fuel (S n) dn rest'
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - rewrite Forall_forall in Hrf_rest'. apply Hrf_rest'; exact Hr. }
           rewrite (eval_rules_app_cong
                      (map (fun e0 => orig_ruleGm f gm e0 body r1) esAll)
                      rr'' rest' ed p Htail').
           rewrite <- Hrun_eq.
           unfold ed. apply (eval_rules_agree_gen (r1 :: r2 :: rest) p base dd'' d).
           intros r Hr. apply (decls_agree_rule_setseam base d dd'' r n Hvm_dd Hmaps_dd Hassoc_dd).
           rewrite Forall_forall in Hrf. apply Hrf; exact Hr.
      * remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        cbn [eval_rules].
        rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
        assert (Hda1 : decls_agree_rule base dd'' d r1).
        { apply (decls_agree_rule_setseam base d dd'' r1 n).
          - apply (optimize_rules_mixedpointrangeguarded_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - apply (optimize_rules_mixedpointrangeguarded_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - intros nm X Hf. apply (optimize_rules_mixedpointrangeguarded_assoc_stable fuel n d (r2 :: rest)
                                    m'' dd'' rr'' nm X (eq_sym Erec) Hf).
          - exact Hf1. }
        rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
        rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
        rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
Qed.

(** *** concat. *)
(** STAGE — composed into [optimize_table_correct_uncond_gen]; not a standalone headline. *)
Theorem optimize_rules_concat_correct_uncond : forall fuel rs n d n' d' rs' base p,
  optimize_rules_concat fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) rs ->
  eval_rules rs' (env_with_sets base d') p
  = eval_rules rs  (env_with_sets base d) p.
Proof.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base p H Hfresh Hrf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_concat_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_value2 r1) as [[[[[f1 a1] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concat_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct (take_concat_run_shape r1 f1 a1 f2 b1 body (r2 :: rest) ts rest' Ehd Erun)
          as [Hsplit [HwA HwB]].
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concat fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           cbn [eval_rules].
           rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
           assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_setseam base d dd'' r1 n).
             - apply (optimize_rules_concat_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_concat_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_concat_assoc_stable fuel n d (r2 :: rest)
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
           rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
           rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
           rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
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
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun ab => orig_rule2 f1 f2 (fst ab) (snd ab) body r1) tuples
                     ++ rest').
           { subst tuples. cbn [map app fst snd]. f_equal.
             - apply (head_value2_canon r1 f1 a1 f2 b1 body Ehd).
             - exact Hsplit. }
           assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia | exact Hr] |].
             assert (Hsub : Forall (rule_set_fresh n) rest').
             { rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
             exact Hsub. }
           assert (Hvm_dd : sd_vmaps dd'' = sd_vmaps d).
           { rewrite (optimize_rules_concat_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hmaps_dd : sd_maps dd'' = sd_maps d).
           { rewrite (optimize_rules_concat_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hassoc_dd : forall nm X, (forall k, n <= k -> nm <> setname k) ->
                     assoc_str nm (sd_sets dd'') X = assoc_str nm (sd_sets d) X).
           { intros nm X Hf.
             rewrite (optimize_rules_concat_assoc_stable fuel (S n) dn rest' m'' dd'' rr'' nm X
                        (eq_sym Erec) (fun k Hk => Hf k ltac:(lia))).
             subst dn; cbn [sd_sets assoc_str].
             destruct (String.eqb nm (setname n)) eqn:Eq.
             - apply String.eqb_eq in Eq. exfalso. apply (Hf n (Nat.le_refl n) Eq).
             - reflexivity. }
           assert (Htail : eval_rules rr'' (env_with_sets base dd'') p
                           = eval_rules rest' (env_with_sets base dn) p).
           { eapply (IH rest' (S n) dn m'' dd'' rr'' base p (eq_sym Erec)); [| exact Hrf_rest'].
             intros k Hk Hin. subst dn; cbn [sd_sets map] in Hin.
             destruct Hin as [Heq | Hin].
             - apply setname_inj in Heq. lia.
             - apply (Hfresh k); [lia | exact Hin]. }
           assert (Hlook : e_set (env_with_sets base dd'')
                             (setname n) = map pack_tuple tuples).
           { rewrite e_set_declared.
             erewrite (optimize_rules_concat_assoc_stable fuel (S n) dn rest' _ _ _
                         (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           set (ed := env_with_sets base dd'') in *.
           assert (Hcert : eval_matchcond (MConcatSet [f1; f2] false (setname n)) ed p
                   = existsb (fun ab => andb (eval_matchcond (MCmp f1 CEq (fst ab)) ed p)
                                             (eval_matchcond (MCmp f2 CEq (snd ab)) ed p))
                             tuples).
           { apply (concat_two_fields_certificate_N f1 f2 tuples (setname n) ed p).
             - exact Hlook.
             - intros a b Hin Hld.
               assert (Hfx : field_fixed_len f1 = Some (Datatypes.length a)).
               { destruct (take_concat_run_head_width r1 f1 a1 f2 b1 body r2 rest
                             (t :: ts') rest' Ehd Erun ltac:(discriminate)) as [Hh1 _].
                 subst tuples. destruct Hin as [Hab | Hin].
                 - injection Hab as -> ->. exact Hh1.
                 - apply (HwA a b Hin). }
               apply (field_fixed_len_loaded f1 (Datatypes.length a) ed p Hfx Hld).
             - intros a b Hin Hld.
               assert (Hfx : field_fixed_len f2 = Some (Datatypes.length b)).
               { destruct (take_concat_run_head_width r1 f1 a1 f2 b1 body r2 rest
                             (t :: ts') rest' Ehd Erun ltac:(discriminate)) as [_ Hh2].
                 subst tuples. destruct Hin as [Hab | Hin].
                 - injection Hab as -> ->. exact Hh2.
                 - apply (HwB a b Hin). }
               apply (field_fixed_len_loaded f2 (Datatypes.length b) ed p Hfx Hld). }
           transitivity (eval_rules
             (map (fun ab => orig_rule2 f1 f2 (fst ab) (snd ab) body r1) tuples ++ rr'') ed p).
           { apply (eval_rules_run_collapse
                      (map (fun ab => orig_rule2 f1 f2 (fst ab) (snd ab) body r1) tuples)
                      (rule_loadable (merged_rule2 f1 f2 (setname n) body r1) ed p)
                      (outcome (merged_rule2 f1 f2 (setname n) body r1) ed p)
                      (merged_rule2 f1 f2 (setname n) body r1) rr'' ed p).
             - subst tuples. discriminate.
             - intros r Hr. apply in_map_iff in Hr as [ab [Hab _]]. subst r.
               symmetry. apply merged_rule2_loadable_eq_orig.
             - intros r Hr. apply in_map_iff in Hr as [ab [Hab _]]. subst r.
               symmetry. apply merged_rule2_outcome_eq_orig.
             - reflexivity.
             - reflexivity.
             - rewrite merged_rule2_applies. rewrite Hcert.
               rewrite existsb_map_eq.
               transitivity (existsb (fun ab =>
                   andb (andb (eval_matchcond (MCmp f1 CEq (fst ab)) ed p)
                              (eval_matchcond (MCmp f2 CEq (snd ab)) ed p))
                        (rule_applies_walk body ed p)) tuples).
               + rewrite existsb_andb_const. reflexivity.
               + apply existsb_ext. intros ab _. symmetry. apply orig_rule2_applies. }
           assert (Htail' : eval_rules rr'' ed p = eval_rules rest' ed p).
           { rewrite Htail. unfold ed.
             apply (eval_rules_agree_gen rest' p base dn dd'').
             intros r Hr. apply decls_agree_rule_sym.
             apply (decls_agree_rule_setseam base dn dd'' r (S n)).
             - apply (optimize_rules_concat_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_concat_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_concat_assoc_stable fuel (S n) dn rest'
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - rewrite Forall_forall in Hrf_rest'. apply Hrf_rest'; exact Hr. }
           rewrite (eval_rules_app_cong
                      (map (fun ab => orig_rule2 f1 f2 (fst ab) (snd ab) body r1) tuples)
                      rr'' rest' ed p Htail').
           rewrite <- Hrun_eq.
           unfold ed. apply (eval_rules_agree_gen (r1 :: r2 :: rest) p base dd'' d).
           intros r Hr. apply (decls_agree_rule_setseam base d dd'' r n Hvm_dd Hmaps_dd Hassoc_dd).
           rewrite Forall_forall in Hrf. apply Hrf; exact Hr.
      * remember (optimize_rules_concat fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        cbn [eval_rules].
        rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
        assert (Hda1 : decls_agree_rule base dd'' d r1).
        { apply (decls_agree_rule_setseam base d dd'' r1 n).
          - apply (optimize_rules_concat_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - apply (optimize_rules_concat_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - intros nm X Hf. apply (optimize_rules_concat_assoc_stable fuel n d (r2 :: rest)
                                    m'' dd'' rr'' nm X (eq_sym Erec) Hf).
          - exact Hf1. }
        rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
        rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
        rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
Qed.

(** *** concatguarded (the guarded transport-key concat pass, Optimize_ConcatGuarded).  Mirrors
    [concat] verbatim EXCEPT the merged rule hoists the shared guard [gm] to the head
    (matching nft -o) and each original carries [gm] between its two selectors.  The
    MConcatSet membership certificate ([concat_two_fields_certificate_N]) is REUSED
    unchanged — the guard is factored out of the run-collapse [existsb] by boolean
    algebra ([existsb_guard_factor]). *)
(** STAGE — composed into [optimize_table_correct_uncond_gen]; not a standalone headline. *)
Theorem optimize_rules_concatguarded_correct_uncond : forall fuel rs n d n' d' rs' base p,
  optimize_rules_concatguarded fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) rs ->
  eval_rules rs' (env_with_sets base d') p
  = eval_rules rs  (env_with_sets base d) p.
Proof.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base p H Hfresh Hrf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_concatguarded_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_value2g r1) as [[[[[[f1 a1] gm] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concatg_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct (take_concatg_run_shape r1 f1 a1 gm f2 b1 body (r2 :: rest) ts rest' Ehd Erun)
          as [Hsplit [HwA HwB]].
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concatguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           cbn [eval_rules].
           rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
           assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_setseam base d dd'' r1 n).
             - apply (optimize_rules_concatguarded_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_concatguarded_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_concatguarded_assoc_stable fuel n d (r2 :: rest)
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
           rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
           rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
           rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
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
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun ab => orig_rule2g f1 f2 gm (fst ab) (snd ab) body r1) tuples
                     ++ rest').
           { subst tuples. cbn [map app fst snd]. f_equal.
             - apply (head_value2g_canon r1 f1 a1 gm f2 b1 body Ehd).
             - exact Hsplit. }
           assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia | exact Hr] |].
             assert (Hsub : Forall (rule_set_fresh n) rest').
             { rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
             exact Hsub. }
           assert (Hvm_dd : sd_vmaps dd'' = sd_vmaps d).
           { rewrite (optimize_rules_concatguarded_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hmaps_dd : sd_maps dd'' = sd_maps d).
           { rewrite (optimize_rules_concatguarded_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hassoc_dd : forall nm X, (forall k, n <= k -> nm <> setname k) ->
                     assoc_str nm (sd_sets dd'') X = assoc_str nm (sd_sets d) X).
           { intros nm X Hf.
             rewrite (optimize_rules_concatguarded_assoc_stable fuel (S n) dn rest' m'' dd'' rr'' nm X
                        (eq_sym Erec) (fun k Hk => Hf k ltac:(lia))).
             subst dn; cbn [sd_sets assoc_str].
             destruct (String.eqb nm (setname n)) eqn:Eq.
             - apply String.eqb_eq in Eq. exfalso. apply (Hf n (Nat.le_refl n) Eq).
             - reflexivity. }
           assert (Htail : eval_rules rr'' (env_with_sets base dd'') p
                           = eval_rules rest' (env_with_sets base dn) p).
           { eapply (IH rest' (S n) dn m'' dd'' rr'' base p (eq_sym Erec)); [| exact Hrf_rest'].
             intros k Hk Hin. subst dn; cbn [sd_sets map] in Hin.
             destruct Hin as [Heq | Hin].
             - apply setname_inj in Heq. lia.
             - apply (Hfresh k); [lia | exact Hin]. }
           assert (Hlook : e_set (env_with_sets base dd'')
                             (setname n) = map pack_tuple tuples).
           { rewrite e_set_declared.
             erewrite (optimize_rules_concatguarded_assoc_stable fuel (S n) dn rest' _ _ _
                         (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           set (ed := env_with_sets base dd'') in *.
           assert (Hcert : eval_matchcond (MConcatSet [f1; f2] false (setname n)) ed p
                   = existsb (fun ab => andb (eval_matchcond (MCmp f1 CEq (fst ab)) ed p)
                                             (eval_matchcond (MCmp f2 CEq (snd ab)) ed p))
                             tuples).
           { apply (concat_two_fields_certificate_N f1 f2 tuples (setname n) ed p).
             - exact Hlook.
             - intros a b Hin Hld.
               assert (Hfx : field_fixed_len f1 = Some (Datatypes.length a)).
               { destruct (take_concatg_run_head_width r1 f1 a1 gm f2 b1 body r2 rest
                             (t :: ts') rest' Ehd Erun ltac:(discriminate)) as [Hh1 _].
                 subst tuples. destruct Hin as [Hab | Hin].
                 - injection Hab as -> ->. exact Hh1.
                 - apply (HwA a b Hin). }
               apply (field_fixed_len_loaded f1 (Datatypes.length a) ed p Hfx Hld).
             - intros a b Hin Hld.
               assert (Hfx : field_fixed_len f2 = Some (Datatypes.length b)).
               { destruct (take_concatg_run_head_width r1 f1 a1 gm f2 b1 body r2 rest
                             (t :: ts') rest' Ehd Erun ltac:(discriminate)) as [_ Hh2].
                 subst tuples. destruct Hin as [Hab | Hin].
                 - injection Hab as -> ->. exact Hh2.
                 - apply (HwB a b Hin). }
               apply (field_fixed_len_loaded f2 (Datatypes.length b) ed p Hfx Hld). }
           transitivity (eval_rules
             (map (fun ab => orig_rule2g f1 f2 gm (fst ab) (snd ab) body r1) tuples ++ rr'') ed p).
           { apply (eval_rules_run_collapse
                      (map (fun ab => orig_rule2g f1 f2 gm (fst ab) (snd ab) body r1) tuples)
                      (rule_loadable (merged_rule2g f1 f2 gm (setname n) body r1) ed p)
                      (outcome (merged_rule2g f1 f2 gm (setname n) body r1) ed p)
                      (merged_rule2g f1 f2 gm (setname n) body r1) rr'' ed p).
             - subst tuples. discriminate.
             - intros r Hr. apply in_map_iff in Hr as [ab [Hab _]]. subst r.
               symmetry. apply merged_rule2g_loadable_eq_orig.
             - intros r Hr. apply in_map_iff in Hr as [ab [Hab _]]. subst r.
               symmetry. apply merged_rule2g_outcome_eq_orig.
             - reflexivity.
             - reflexivity.
             - rewrite merged_rule2g_applies. rewrite Hcert.
               rewrite existsb_map_eq.
               transitivity (existsb (fun ab =>
                   andb (andb (andb (eval_matchcond (MCmp f1 CEq (fst ab)) ed p)
                                    (eval_matchcond gm ed p))
                              (eval_matchcond (MCmp f2 CEq (snd ab)) ed p))
                        (rule_applies_walk body ed p)) tuples).
               + rewrite existsb_guard_factor. rewrite Bool.andb_assoc. reflexivity.
               + apply existsb_ext. intros ab _. symmetry. apply orig_rule2g_applies. }
           assert (Htail' : eval_rules rr'' ed p = eval_rules rest' ed p).
           { rewrite Htail. unfold ed.
             apply (eval_rules_agree_gen rest' p base dn dd'').
             intros r Hr. apply decls_agree_rule_sym.
             apply (decls_agree_rule_setseam base dn dd'' r (S n)).
             - apply (optimize_rules_concatguarded_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_concatguarded_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_concatguarded_assoc_stable fuel (S n) dn rest'
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - rewrite Forall_forall in Hrf_rest'. apply Hrf_rest'; exact Hr. }
           rewrite (eval_rules_app_cong
                      (map (fun ab => orig_rule2g f1 f2 gm (fst ab) (snd ab) body r1) tuples)
                      rr'' rest' ed p Htail').
           rewrite <- Hrun_eq.
           unfold ed. apply (eval_rules_agree_gen (r1 :: r2 :: rest) p base dd'' d).
           intros r Hr. apply (decls_agree_rule_setseam base d dd'' r n Hvm_dd Hmaps_dd Hassoc_dd).
           rewrite Forall_forall in Hrf. apply Hrf; exact Hr.
      * remember (optimize_rules_concatguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        cbn [eval_rules].
        rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
        assert (Hda1 : decls_agree_rule base dd'' d r1).
        { apply (decls_agree_rule_setseam base d dd'' r1 n).
          - apply (optimize_rules_concatguarded_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - apply (optimize_rules_concatguarded_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - intros nm X Hf. apply (optimize_rules_concatguarded_assoc_stable fuel n d (r2 :: rest)
                                    m'' dd'' rr'' nm X (eq_sym Erec) Hf).
          - exact Hf1. }
        rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
        rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
        rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
Qed.

(** *** setguarded (the guarded single-field value->set pass, Optimize_SetGuarded).  Mirrors
    [concatguarded] verbatim EXCEPT the single-field membership certificate is
    [concat_set_existsb] (one field, [map (fun v => (v,v)) vals] elements) and the
    HEAD guard [gm] is factored out of the run-collapse [existsb] by
    [existsb_guardhead_factor]. *)
(** STAGE — composed into [optimize_table_correct_uncond_gen]; not a standalone headline. *)
Theorem optimize_rules_setguarded_correct_uncond : forall fuel rs n d n' d' rs' base p,
  optimize_rules_setguarded fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) rs ->
  eval_rules rs' (env_with_sets base d') p
  = eval_rules rs  (env_with_sets base d) p.
Proof.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base p H Hfresh Hrf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_setguarded_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_valueGs r1) as [[[[gm f] v1] body] |] eqn:Ehd.
      * destruct (take_setg_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct (take_setg_run_shape r1 gm f v1 body (r2 :: rest) vs rest' Ehd Erun)
          as [Hsplit Hall].
        destruct vs as [| v0 vs'].
        -- remember (optimize_rules_setguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           cbn [eval_rules].
           rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
           assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_setseam base d dd'' r1 n).
             - apply (optimize_rules_setguarded_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_setguarded_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_setguarded_assoc_stable fuel n d (r2 :: rest)
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
           rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
           rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
           rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
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
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun v => orig_ruleGs f gm v body r1) vals ++ rest').
           { subst vals. cbn [map app]. f_equal.
             - apply (head_valueGs_canon r1 gm f v1 body Ehd).
             - exact Hsplit. }
           assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia | exact Hr] |].
             assert (Hsub : Forall (rule_set_fresh n) rest').
             { rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
             exact Hsub. }
           assert (Hvm_dd : sd_vmaps dd'' = sd_vmaps d).
           { rewrite (optimize_rules_setguarded_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hmaps_dd : sd_maps dd'' = sd_maps d).
           { rewrite (optimize_rules_setguarded_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hassoc_dd : forall nm X, (forall k, n <= k -> nm <> setname k) ->
                     assoc_str nm (sd_sets dd'') X = assoc_str nm (sd_sets d) X).
           { intros nm X Hf.
             rewrite (optimize_rules_setguarded_assoc_stable fuel (S n) dn rest' m'' dd'' rr'' nm X
                        (eq_sym Erec) (fun k Hk => Hf k ltac:(lia))).
             subst dn; cbn [sd_sets assoc_str].
             destruct (String.eqb nm (setname n)) eqn:Eq.
             - apply String.eqb_eq in Eq. exfalso. apply (Hf n (Nat.le_refl n) Eq).
             - reflexivity. }
           assert (Htail : eval_rules rr'' (env_with_sets base dd'') p
                           = eval_rules rest' (env_with_sets base dn) p).
           { eapply (IH rest' (S n) dn m'' dd'' rr'' base p (eq_sym Erec)); [| exact Hrf_rest'].
             intros k Hk Hin. subst dn; cbn [sd_sets map] in Hin.
             destruct Hin as [Heq | Hin].
             - apply setname_inj in Heq. lia.
             - apply (Hfresh k); [lia | exact Hin]. }
           assert (Hlook : e_set (env_with_sets base dd'')
                             (setname n) = map (fun v => (v, v)) vals).
           { rewrite e_set_declared.
             erewrite (optimize_rules_setguarded_assoc_stable fuel (S n) dn rest' _ _ _
                         (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           set (ed := env_with_sets base dd'') in *.
           assert (Hcert : eval_matchcond (MConcatSet [f] false (setname n)) ed p
                   = existsb (fun v => eval_matchcond (MCmp f CEq v) ed p) vals).
           { apply (concat_set_existsb f vals (setname n) ed p).
             - exact Hlook.
             - intros v Hin Hld.
               assert (Hfx : field_fixed_len f = Some (Datatypes.length v)).
               { destruct Hin as [Hv | Hin].
                 - subst v. apply (take_setg_run_head_width r1 gm f v1 body r2 rest
                                     (v0 :: vs') rest' Ehd Erun ltac:(discriminate)).
                 - apply (Hall v Hin). }
               apply (field_fixed_len_loaded f (Datatypes.length v) ed p Hfx Hld). }
           transitivity (eval_rules
             (map (fun v => orig_ruleGs f gm v body r1) vals ++ rr'') ed p).
           { apply (eval_rules_run_collapse
                      (map (fun v => orig_ruleGs f gm v body r1) vals)
                      (rule_loadable (merged_ruleGs f gm (setname n) body r1) ed p)
                      (outcome (merged_ruleGs f gm (setname n) body r1) ed p)
                      (merged_ruleGs f gm (setname n) body r1) rr'' ed p).
             - subst vals. discriminate.
             - intros r Hr. apply in_map_iff in Hr as [v [Hv _]]. subst r.
               symmetry. apply merged_ruleGs_loadable_eq_orig.
             - intros r Hr. apply in_map_iff in Hr as [v [Hv _]]. subst r.
               symmetry. apply merged_ruleGs_outcome_eq_orig.
             - reflexivity.
             - reflexivity.
             - rewrite merged_ruleGs_applies. rewrite Hcert.
               rewrite existsb_map_eq.
               rewrite (existsb_ext _ _ _ vals
                          (fun v (_ : In v vals) => orig_ruleGs_applies f gm v body r1 ed p)).
               symmetry. apply existsb_guardhead_factor. }
           assert (Htail' : eval_rules rr'' ed p = eval_rules rest' ed p).
           { rewrite Htail. unfold ed.
             apply (eval_rules_agree_gen rest' p base dn dd'').
             intros r Hr. apply decls_agree_rule_sym.
             apply (decls_agree_rule_setseam base dn dd'' r (S n)).
             - apply (optimize_rules_setguarded_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_setguarded_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_setguarded_assoc_stable fuel (S n) dn rest'
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - rewrite Forall_forall in Hrf_rest'. apply Hrf_rest'; exact Hr. }
           rewrite (eval_rules_app_cong
                      (map (fun v => orig_ruleGs f gm v body r1) vals)
                      rr'' rest' ed p Htail').
           rewrite <- Hrun_eq.
           unfold ed. apply (eval_rules_agree_gen (r1 :: r2 :: rest) p base dd'' d).
           intros r Hr. apply (decls_agree_rule_setseam base d dd'' r n Hvm_dd Hmaps_dd Hassoc_dd).
           rewrite Forall_forall in Hrf. apply Hrf; exact Hr.
      * remember (optimize_rules_setguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        cbn [eval_rules].
        rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
        assert (Hda1 : decls_agree_rule base dd'' d r1).
        { apply (decls_agree_rule_setseam base d dd'' r1 n).
          - apply (optimize_rules_setguarded_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - apply (optimize_rules_setguarded_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - intros nm X Hf. apply (optimize_rules_setguarded_assoc_stable fuel n d (r2 :: rest)
                                    m'' dd'' rr'' nm X (eq_sym Erec) Hf).
          - exact Hf1. }
        rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
        rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
        rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
Qed.

(** *** concatmulti (the N>=3-field pairwise concat pass, Optimize_ConcatMulti).  Mirrors
    the [concat] correctness but uses [eval_rules_concat_mergeK] (which bundles the
    matchcond certificate + run-collapse) on the two-row merge. *)
(** STAGE — composed into [optimize_table_correct_uncond_gen]; not a standalone headline. *)
Theorem optimize_rules_concatmulti_correct_uncond : forall rs n d n' d' rs' base p,
  optimize_rules_concatmulti n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) rs ->
  eval_rules rs' (env_with_sets base d') p
  = eval_rules rs  (env_with_sets base d) p.
Proof.
  induction rs as [rs IHrs] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' base p H Hfresh Hrf.
  destruct rs as [| r1 [| r2 rest] ].
  - cbn in H. inversion H; subst; reflexivity.
  - cbn in H. inversion H; subst; reflexivity.
  - rewrite optimize_rules_concatmulti_cons2 in H.
    inversion Hrf as [| ? ? Hf1 Hrf2]; subst.
    inversion Hrf2 as [| ? ? Hf2 Hrf_rest]; subst.
    destruct (concat_mergeK_pair r1 r2) as [[[[fields row1] row2] body] |] eqn:Em.
    + cbv zeta in H.
      destruct (concat_mergeK_pair_shape r1 r2 fields row1 row2 body Em)
        as [Hr1eq [Hr2eq [Hwf1 [Hwf2 [Hfne _]]]]].
      set (dn := {| sd_sets := (setname n, map pack_row [row1; row2]) :: sd_sets d;
                    sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
      remember (optimize_rules_concatmulti (S n) dn rest) as tt eqn:Erec.
      destruct tt as [[m'' dd''] rr'']. injection H as Hn' Hd' Hr'. subst n' d' rs'.
      assert (Hrest_fresh : Forall (rule_set_fresh (S n)) rest).
      { eapply Forall_impl;
          [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia|exact Hr]|exact Hrf_rest]. }
      assert (Hfresh_dn : forall k, S n <= k -> ~ In (setname k) (map fst (sd_sets dn))).
      { intros k Hk Hin. subst dn; cbn [sd_sets map] in Hin. destruct Hin as [Heq|Hin].
        - apply setname_inj in Heq. lia.
        - apply (Hfresh k); [lia|exact Hin]. }
      assert (Htail : eval_rules rr'' (env_with_sets base dd'') p
                      = eval_rules rest (env_with_sets base dn) p).
      { apply (IHrs rest ltac:(unfold ltof; cbn; lia) (S n) dn m'' dd'' rr'' base p
                 (eq_sym Erec) Hfresh_dn Hrest_fresh). }
      assert (Hvm_dd : sd_vmaps dd'' = sd_vmaps d).
      { rewrite (optimize_rules_concatmulti_vmaps rest (S n) dn m'' dd'' rr'' (eq_sym Erec)).
        subst dn; reflexivity. }
      assert (Hmaps_dd : sd_maps dd'' = sd_maps d).
      { rewrite (optimize_rules_concatmulti_maps rest (S n) dn m'' dd'' rr'' (eq_sym Erec)).
        subst dn; reflexivity. }
      assert (Hassoc_dd : forall nm X, (forall k, n <= k -> nm <> setname k) ->
                assoc_str nm (sd_sets dd'') X = assoc_str nm (sd_sets d) X).
      { intros nm X Hf.
        rewrite (optimize_rules_concatmulti_assoc_stable rest (S n) dn m'' dd'' rr'' nm X
                   (eq_sym Erec) (fun k Hk => Hf k ltac:(lia))).
        subst dn; cbn [sd_sets assoc_str]. destruct (String.eqb nm (setname n)) eqn:Eq.
        - apply String.eqb_eq in Eq. exfalso. apply (Hf n (Nat.le_refl n) Eq).
        - reflexivity. }
      set (ed := env_with_sets base dd'') in *.
      assert (Hlook : e_set ed (setname n) = map pack_row [row1; row2]).
      { unfold ed. rewrite e_set_declared.
        erewrite (optimize_rules_concatmulti_assoc_stable rest (S n) dn m'' dd'' rr'' (setname n) _
                    (eq_sym Erec)).
        - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
        - intros k Hk Heq. apply setname_inj in Heq. lia. }
      assert (Htail' : eval_rules rr'' ed p = eval_rules rest ed p).
      { rewrite Htail. unfold ed. apply (eval_rules_agree_gen rest p base dn dd'').
        intros r Hr. apply decls_agree_rule_sym.
        apply (decls_agree_rule_setseam base dn dd'' r (S n)).
        - apply (optimize_rules_concatmulti_vmaps rest (S n) dn m'' dd'' rr'' (eq_sym Erec)).
        - apply (optimize_rules_concatmulti_maps rest (S n) dn m'' dd'' rr'' (eq_sym Erec)).
        - intros nm X Hf. apply (optimize_rules_concatmulti_assoc_stable rest (S n) dn m'' dd'' rr''
                                   nm X (eq_sym Erec) Hf).
        - rewrite Forall_forall in Hrest_fresh. apply Hrest_fresh; exact Hr. }
      (* collapse the merged rule to its two originals (= r1, r2) at env dd'' *)
      rewrite (eval_rules_concat_mergeK fields [row1; row2] (setname n) body r1 rr'' ed p
                 Hfne ltac:(discriminate) Hlook
                 ltac:(intros row Hin; destruct Hin as [<-|[<-|[]]]; assumption)).
      cbn [map]. rewrite <- Hr1eq, <- Hr2eq.
      (* eval_rules (r1::r2::rr'') ed p = eval_rules (r1::r2::rest) [d] *)
      transitivity (eval_rules (r1 :: r2 :: rest) ed p).
      { exact (eval_rules_app_cong [r1; r2] rr'' rest ed p Htail'). }
      unfold ed. apply (eval_rules_agree_gen (r1 :: r2 :: rest) p base dd'' d).
      intros r Hr. apply (decls_agree_rule_setseam base d dd'' r n Hvm_dd Hmaps_dd Hassoc_dd).
      rewrite Forall_forall in Hrf. apply Hrf; exact Hr.
    + remember (optimize_rules_concatmulti n d (r2 :: rest)) as tt eqn:Erec.
      destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
      injection H as Hn' Hd' Hr'. subst n' d' rs'.
      cbn [eval_rules].
      rewrite (IHrs (r2 :: rest) ltac:(unfold ltof; cbn; lia) n d m'' dd'' rr'' base p
                 (eq_sym Erec) Hfresh Hrf2).
      assert (Hda1 : decls_agree_rule base dd'' d r1).
      { apply (decls_agree_rule_setseam base d dd'' r1 n).
        - apply (optimize_rules_concatmulti_vmaps (r2 :: rest) n d m'' dd'' rr'' (eq_sym Erec)).
        - apply (optimize_rules_concatmulti_maps (r2 :: rest) n d m'' dd'' rr'' (eq_sym Erec)).
        - intros nm X Hf. apply (optimize_rules_concatmulti_assoc_stable (r2 :: rest) n d m'' dd'' rr''
                                   nm X (eq_sym Erec) Hf).
        - exact Hf1. }
      rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
      rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
      rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
Qed.

(** *** vmap.  The vmap merge is GATED on [body_vmap_safe] (no synproxy/notrack in
    the body), which the merge condition now enforces; that gate is what makes the
    vmap pass SOUND on arbitrary input (the merge is genuinely unsound for a
    [notrack] body, since the merged rule reads its key field at the body-threaded
    packet).  Read-freshness is in the [vmapname] namespace. *)
(** STAGE — composed into [optimize_table_correct_uncond_gen]; not a standalone headline. *)
Theorem optimize_rules_vmap_correct_uncond : forall fuel rs n d n' d' rs' base p,
  optimize_rules_vmap fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  Forall (rule_vmap_fresh n) rs ->
  eval_rules rs' (env_with_sets base d') p
  = eval_rules rs  (env_with_sets base d) p.
Proof.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base p H Hfresh Hrf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_vmap_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_vmap_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct (take_vmap_run_shape r1 f v1 body (r2 :: rest) es rest' Ehd Erun)
          as [Hsplit [HwK HwT]].
        assert (Hrf_rest_n : Forall (rule_vmap_fresh n) rest').
        { rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
        destruct es as [| e es'].
        -- remember (optimize_rules_vmap fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           cbn [eval_rules].
           rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
           assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_vmapseam base d dd'' r1 n).
             - apply (optimize_rules_vmap_sets fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_vmap_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_vmap_assoc_stable fuel n d (r2 :: rest) m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
           rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
           rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
           rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
        -- destruct (take_vmap_run_head r1 f v1 body r2 rest (e :: es') rest' Ehd Erun
                       ltac:(discriminate)) as [Hr1eq [HwK1 HwT1]].
           destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           2:{ remember (optimize_rules_vmap fuel n d (r2 :: rest)) as tt eqn:Erec.
               destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
               injection H as Hn' Hd' Hr'. subst n' d' rs'.
               cbn [eval_rules].
               rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
               assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_vmapseam base d dd'' r1 n).
             - apply (optimize_rules_vmap_sets fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_vmap_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_vmap_assoc_stable fuel n d (r2 :: rest) m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
               rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
               rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
               rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity. }
           (* merge: discharge synproxy/notrack from the body_vmap_safe gate *)
           apply Bool.andb_true_iff in Hdv as [_ Hsafe].
           apply Bool.andb_true_iff in Hsafe as [Hns Hnt].
           apply Bool.negb_true_iff in Hns. apply Bool.negb_true_iff in Hnt.
           cbv zeta in H.
           remember (optimize_rules_vmap fuel (S n)
                       {| sd_sets := sd_sets d;
                          sd_vmaps := (vmapname n,
                            map vmap_pt ((v1, r_verdict r1) :: e :: es')) :: sd_vmaps d;
                          sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (entries := (v1, r_verdict r1) :: e :: es') in *.
           set (dn := {| sd_sets := sd_sets d;
                         sd_vmaps := (vmapname n, map vmap_pt entries) :: sd_vmaps d;
                         sd_maps := sd_maps d |}) in *.
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun vw => orig_rule f (fst vw) body (snd vw)) entries ++ rest').
           { subst entries. cbn [map app fst snd]. f_equal; [exact Hr1eq | exact Hsplit]. }
           assert (Hrf_rest' : Forall (rule_vmap_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_vmap_fresh_mono n (S n) r); [lia | exact Hr] |].
             exact Hrf_rest_n. }
           assert (Hsets_dd : sd_sets dd'' = sd_sets dn)
             by (apply (optimize_rules_vmap_sets _ _ _ _ _ _ _ (eq_sym Erec))).
           assert (Hsets_dn : sd_sets dn = sd_sets d) by (subst dn; reflexivity).
           assert (Hmaps_dd : sd_maps dd'' = sd_maps dn)
             by (apply (optimize_rules_vmap_maps _ _ _ _ _ _ _ (eq_sym Erec))).
           assert (Hmaps_dn : sd_maps dn = sd_maps d) by (subst dn; reflexivity).
           assert (Htail : eval_rules rr'' (env_with_sets base dd'') p
                           = eval_rules rest' (env_with_sets base dn) p).
           { eapply (IH rest' (S n) dn m'' dd'' rr'' base p (eq_sym Erec)); [| exact Hrf_rest'].
             intros k Hk Hin. subst dn; cbn [sd_vmaps map] in Hin.
             destruct Hin as [Heq | Hin].
             - apply vmapname_inj in Heq. lia.
             - apply (Hfresh k); [lia | exact Hin]. }
           assert (Hlook : e_vmap (env_with_sets base dd'')
                             (vmapname n) = map vmap_pt entries).
           { rewrite e_vmap_env_with_sets.
             erewrite (optimize_rules_vmap_assoc_stable fuel (S n) dn _ _ _ _
                         (vmapname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_vmaps assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply vmapname_inj in Heq. lia. }
           set (ed := env_with_sets base dd'') in *.
           transitivity (eval_rules
             (map (fun vw => orig_rule f (fst vw) body (snd vw)) entries ++ rr'') ed p).
           { unfold ed. apply (eval_rules_vmap_mergeN f (vmapname n) entries body rr''
                                 (env_with_sets base dd'') p).
             - exact Hlook.
             - intros v w Hin. subst entries. destruct Hin as [Hvw | Hin];
                 [ inversion Hvw; subst; exact HwK1 | apply (HwK v w Hin) ].
             - intros v w Hin. subst entries. destruct Hin as [Hvw | Hin];
                 [ inversion Hvw; subst; exact HwT1 | apply (HwT v w Hin) ].
             - apply (body_has_synproxy_false_stops body p Hns).
             - exact Hnt. }
           assert (Htail' : eval_rules rr'' ed p = eval_rules rest' ed p).
           { rewrite Htail. unfold ed.
             apply (eval_rules_agree_gen rest' p base dn dd'').
             intros r Hr. apply decls_agree_rule_sym.
             apply (decls_agree_rule_vmapseam base dn dd'' r (S n)).
             - apply (optimize_rules_vmap_sets fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_vmap_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_vmap_assoc_stable fuel (S n) dn rest'
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - rewrite Forall_forall in Hrf_rest'. apply Hrf_rest'; exact Hr. }
           rewrite (eval_rules_app_cong
                      (map (fun vw => orig_rule f (fst vw) body (snd vw)) entries)
                      rr'' rest' ed p Htail').
           rewrite <- Hrun_eq.
           unfold ed. apply (eval_rules_agree_gen (r1 :: r2 :: rest) p base dd'' d).
           intros r Hr. apply (decls_agree_rule_vmapseam base d dd'' r n).
           ++ rewrite Hsets_dd, Hsets_dn; reflexivity.
           ++ rewrite Hmaps_dd, Hmaps_dn; reflexivity.
           ++ intros nm X Hf.
              rewrite (optimize_rules_vmap_assoc_stable fuel (S n) dn rest' m'' dd'' rr'' nm X
                         (eq_sym Erec) (fun k Hk => Hf k ltac:(lia))).
              subst dn; cbn [sd_vmaps assoc_str].
              destruct (String.eqb nm (vmapname n)) eqn:Eq.
              ** apply String.eqb_eq in Eq. exfalso. apply (Hf n (Nat.le_refl n) Eq).
              ** reflexivity.
           ++ rewrite Forall_forall in Hrf. apply Hrf; exact Hr.
      * remember (optimize_rules_vmap fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        cbn [eval_rules].
        rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
        assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_vmapseam base d dd'' r1 n).
             - apply (optimize_rules_vmap_sets fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_vmap_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_vmap_assoc_stable fuel n d (r2 :: rest) m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
        rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
        rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
        rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
Qed.

(** *** vmapguarded.  The GUARDED verdict-map merge (Optimize_VmapGuarded), a verbatim mirror of
    the vmap proof above EXCEPT the recogniser is [head_valueGs] (guard + selector),
    the run collapse is [eval_rules_vmap_mergeNg] (reduced to [eval_rules_vmap_mergeN]
    on body [BMatch gm :: body] via the SWAP equivalence), and the merged rule is
    [merged_ruleGv].  Read-freshness is in the same [vmapname] namespace, so the SAME
    [rule_vmap_fresh] / [decls_agree_rule_vmapseam] machinery applies. *)
(** STAGE — composed into [optimize_table_correct_uncond_gen]; not a standalone headline. *)
Theorem optimize_rules_vmapguarded_correct_uncond : forall fuel rs n d n' d' rs' base p,
  optimize_rules_vmapguarded fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  Forall (rule_vmap_fresh n) rs ->
  eval_rules rs' (env_with_sets base d') p
  = eval_rules rs  (env_with_sets base d) p.
Proof.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base p H Hfresh Hrf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_vmapguarded_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_valueGs r1) as [[[[gm f] v1] body] |] eqn:Ehd.
      * destruct (take_vmapG_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct (take_vmapG_run_shape r1 gm f v1 body (r2 :: rest) es rest' Ehd Erun)
          as [Hsplit [HwK HwT]].
        assert (Hrf_rest_n : Forall (rule_vmap_fresh n) rest').
        { rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
        destruct es as [| e es'].
        -- remember (optimize_rules_vmapguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           cbn [eval_rules].
           rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
           assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_vmapseam base d dd'' r1 n).
             - apply (optimize_rules_vmapguarded_sets fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_vmapguarded_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_vmapguarded_assoc_stable fuel n d (r2 :: rest) m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
           rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
           rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
           rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
        -- destruct (take_vmapG_run_head r1 gm f v1 body r2 rest (e :: es') rest' Ehd Erun
                       ltac:(discriminate)) as [Hr1eq [HwK1 HwT1]].
           destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           2:{ remember (optimize_rules_vmapguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
               destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
               injection H as Hn' Hd' Hr'. subst n' d' rs'.
               cbn [eval_rules].
               rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
               assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_vmapseam base d dd'' r1 n).
             - apply (optimize_rules_vmapguarded_sets fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_vmapguarded_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_vmapguarded_assoc_stable fuel n d (r2 :: rest) m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
               rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
               rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
               rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity. }
           (* merge: discharge synproxy/notrack from the body_vmap_safe gate *)
           apply Bool.andb_true_iff in Hdv as [_ Hsafe].
           apply Bool.andb_true_iff in Hsafe as [Hns Hnt].
           apply Bool.negb_true_iff in Hns. apply Bool.negb_true_iff in Hnt.
           cbv zeta in H.
           remember (optimize_rules_vmapguarded fuel (S n)
                       {| sd_sets := sd_sets d;
                          sd_vmaps := (vmapname n,
                            map vmap_pt ((v1, r_verdict r1) :: e :: es')) :: sd_vmaps d;
                          sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (entries := (v1, r_verdict r1) :: e :: es') in *.
           set (dn := {| sd_sets := sd_sets d;
                         sd_vmaps := (vmapname n, map vmap_pt entries) :: sd_vmaps d;
                         sd_maps := sd_maps d |}) in *.
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun vw => orig_ruleGv f gm (fst vw) body (snd vw)) entries ++ rest').
           { subst entries. cbn [map app fst snd]. f_equal; [exact Hr1eq | exact Hsplit]. }
           assert (Hrf_rest' : Forall (rule_vmap_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_vmap_fresh_mono n (S n) r); [lia | exact Hr] |].
             exact Hrf_rest_n. }
           assert (Hsets_dd : sd_sets dd'' = sd_sets dn)
             by (apply (optimize_rules_vmapguarded_sets _ _ _ _ _ _ _ (eq_sym Erec))).
           assert (Hsets_dn : sd_sets dn = sd_sets d) by (subst dn; reflexivity).
           assert (Hmaps_dd : sd_maps dd'' = sd_maps dn)
             by (apply (optimize_rules_vmapguarded_maps _ _ _ _ _ _ _ (eq_sym Erec))).
           assert (Hmaps_dn : sd_maps dn = sd_maps d) by (subst dn; reflexivity).
           assert (Htail : eval_rules rr'' (env_with_sets base dd'') p
                           = eval_rules rest' (env_with_sets base dn) p).
           { eapply (IH rest' (S n) dn m'' dd'' rr'' base p (eq_sym Erec)); [| exact Hrf_rest'].
             intros k Hk Hin. subst dn; cbn [sd_vmaps map] in Hin.
             destruct Hin as [Heq | Hin].
             - apply vmapname_inj in Heq. lia.
             - apply (Hfresh k); [lia | exact Hin]. }
           assert (Hlook : e_vmap (env_with_sets base dd'')
                             (vmapname n) = map vmap_pt entries).
           { rewrite e_vmap_env_with_sets.
             erewrite (optimize_rules_vmapguarded_assoc_stable fuel (S n) dn _ _ _ _
                         (vmapname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_vmaps assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply vmapname_inj in Heq. lia. }
           set (ed := env_with_sets base dd'') in *.
           transitivity (eval_rules
             (map (fun vw => orig_ruleGv f gm (fst vw) body (snd vw)) entries ++ rr'') ed p).
           { unfold ed. apply (eval_rules_vmap_mergeNg f gm (vmapname n) entries body rr''
                                 (env_with_sets base dd'') p).
             - exact Hlook.
             - intros v w Hin. subst entries. destruct Hin as [Hvw | Hin];
                 [ inversion Hvw; subst; exact HwK1 | apply (HwK v w Hin) ].
             - intros v w Hin. subst entries. destruct Hin as [Hvw | Hin];
                 [ inversion Hvw; subst; exact HwT1 | apply (HwT v w Hin) ].
             - apply (body_has_synproxy_false_stops body p Hns).
             - exact Hnt. }
           assert (Htail' : eval_rules rr'' ed p = eval_rules rest' ed p).
           { rewrite Htail. unfold ed.
             apply (eval_rules_agree_gen rest' p base dn dd'').
             intros r Hr. apply decls_agree_rule_sym.
             apply (decls_agree_rule_vmapseam base dn dd'' r (S n)).
             - apply (optimize_rules_vmapguarded_sets fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_vmapguarded_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_vmapguarded_assoc_stable fuel (S n) dn rest'
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - rewrite Forall_forall in Hrf_rest'. apply Hrf_rest'; exact Hr. }
           rewrite (eval_rules_app_cong
                      (map (fun vw => orig_ruleGv f gm (fst vw) body (snd vw)) entries)
                      rr'' rest' ed p Htail').
           rewrite <- Hrun_eq.
           unfold ed. apply (eval_rules_agree_gen (r1 :: r2 :: rest) p base dd'' d).
           intros r Hr. apply (decls_agree_rule_vmapseam base d dd'' r n).
           ++ rewrite Hsets_dd, Hsets_dn; reflexivity.
           ++ rewrite Hmaps_dd, Hmaps_dn; reflexivity.
           ++ intros nm X Hf.
              rewrite (optimize_rules_vmapguarded_assoc_stable fuel (S n) dn rest' m'' dd'' rr'' nm X
                         (eq_sym Erec) (fun k Hk => Hf k ltac:(lia))).
              subst dn; cbn [sd_vmaps assoc_str].
              destruct (String.eqb nm (vmapname n)) eqn:Eq.
              ** apply String.eqb_eq in Eq. exfalso. apply (Hf n (Nat.le_refl n) Eq).
              ** reflexivity.
           ++ rewrite Forall_forall in Hrf. apply Hrf; exact Hr.
      * remember (optimize_rules_vmapguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        cbn [eval_rules].
        rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
        assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_vmapseam base d dd'' r1 n).
             - apply (optimize_rules_vmapguarded_sets fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_vmapguarded_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_vmapguarded_assoc_stable fuel n d (r2 :: rest) m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
        rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
        rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
        rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
Qed.

(** vmapguarded output read-freshness (own [vmapname] namespace): the merged
    [merged_ruleGv] reads only the freshly minted [vmapname n], and passed-through
    rules read no minted name — so [rule_vmap_fresh n] input yields
    [rule_vmap_fresh n'] output. *)
Lemma rule_vmap_name_merged_ruleGv : forall f gm nm body,
  rule_vmap_name (merged_ruleGv f gm nm body) = [nm].
Proof. reflexivity. Qed.

Lemma optimize_rules_vmapguarded_output_vmap_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_vmapguarded fuel n d rs = (n', d', rs') ->
  Forall (rule_vmap_fresh n) rs ->
  Forall (rule_vmap_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_vmapguarded_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_valueGs r1) as [[[[gm f] v1] body] |] eqn:Ehd.
      * destruct (take_vmapG_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct (take_vmapG_run_shape r1 gm f v1 body (r2 :: rest) es rest' Ehd Erun)
          as [Hsplit _].
        destruct es as [| e es'].
        -- remember (optimize_rules_vmapguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_vmapguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                        | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
        -- destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           2:{ remember (optimize_rules_vmapguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
               destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
               injection H as Hn' Hd' Hr'. subst n' d' rs'.
               assert (Hmono : n <= m'')
                 by (apply (optimize_rules_vmapguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
               constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                            | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)]. }
           cbv zeta in H.
           remember (optimize_rules_vmapguarded fuel (S n)
                       {| sd_sets := sd_sets d;
                          sd_vmaps := (vmapname n,
                            map vmap_pt ((v1, r_verdict r1) :: e :: es')) :: sd_vmaps d;
                          sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_vmapguarded_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_vmap_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_vmap_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ intros k Hk Hin. rewrite rule_vmap_name_merged_ruleGv in Hin.
              cbn [In] in Hin. destruct Hin as [Heq | []].
              apply vmapname_inj in Heq. lia.
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_vmapguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_vmapguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                     | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
Qed.

(** *** dscpvmap.  The masked-payload value+VERDICT->vmap merge (Optimize_DscpVmap),
    a verbatim mirror of the vmapguarded proof above EXCEPT the recogniser is [head_dscp]
    (the masked [MMasked f CEq mask xor v] head), the run collapse is
    [eval_rules_dscpv_mergeN] (the transform-keyed vmap), and the merged rule is
    [mk_vmap_rule_t f [TBitAnd mask xor] name body].  Read-freshness is in the same
    [vmapname] namespace, so the SAME [rule_vmap_fresh] / [decls_agree_rule_vmapseam]
    machinery applies. *)
(** STAGE — composed into [optimize_table_correct_uncond_gen]; not a standalone headline. *)
Theorem optimize_rules_dscpvmap_correct_uncond : forall fuel rs n d n' d' rs' base p,
  optimize_rules_dscpvmap fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  Forall (rule_vmap_fresh n) rs ->
  eval_rules rs' (env_with_sets base d') p
  = eval_rules rs  (env_with_sets base d) p.
Proof.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base p H Hfresh Hrf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_dscpvmap_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_dscp r1) as [[[[[f mask] xor] v1] body] |] eqn:Ehd.
      * destruct (take_dscpv_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct (take_dscpv_run_shape r1 f mask xor v1 body (r2 :: rest) es rest' Ehd Erun)
          as [Hsplit [HwK [HwM [HwX HwT]]]].
        assert (Hrf_rest_n : Forall (rule_vmap_fresh n) rest').
        { rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
        destruct es as [| e es'].
        -- remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           cbn [eval_rules].
           rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
           assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_vmapseam base d dd'' r1 n).
             - apply (optimize_rules_dscpvmap_sets fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_dscpvmap_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_dscpvmap_assoc_stable fuel n d (r2 :: rest) m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
           rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
           rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
           rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
        -- destruct (take_dscpv_run_head r1 f mask xor v1 body r2 rest (e :: es') rest' Ehd Erun
                       ltac:(discriminate)) as [Hr1eq [HwK1 [HwM1 [HwX1 HwT1]]]].
           destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           2:{ remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
               destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
               injection H as Hn' Hd' Hr'. subst n' d' rs'.
               cbn [eval_rules].
               rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
               assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_vmapseam base d dd'' r1 n).
             - apply (optimize_rules_dscpvmap_sets fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_dscpvmap_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_dscpvmap_assoc_stable fuel n d (r2 :: rest) m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
               rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
               rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
               rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity. }
           (* merge: discharge synproxy/notrack from the body_vmap_safe gate *)
           apply Bool.andb_true_iff in Hdv as [_ Hsafe].
           apply Bool.andb_true_iff in Hsafe as [Hns Hnt].
           apply Bool.negb_true_iff in Hns. apply Bool.negb_true_iff in Hnt.
           cbv zeta in H.
           remember (optimize_rules_dscpvmap fuel (S n)
                       {| sd_sets := sd_sets d;
                          sd_vmaps := (vmapname n,
                            map vmap_pt ((v1, r_verdict r1) :: e :: es')) :: sd_vmaps d;
                          sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (entries := (v1, r_verdict r1) :: e :: es') in *.
           set (dn := {| sd_sets := sd_sets d;
                         sd_vmaps := (vmapname n, map vmap_pt entries) :: sd_vmaps d;
                         sd_maps := sd_maps d |}) in *.
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun vw => orig_rule_m f mask xor (fst vw) body (snd vw)) entries ++ rest').
           { subst entries. cbn [map app fst snd]. f_equal; [exact Hr1eq | exact Hsplit]. }
           assert (Hrf_rest' : Forall (rule_vmap_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_vmap_fresh_mono n (S n) r); [lia | exact Hr] |].
             exact Hrf_rest_n. }
           assert (Hsets_dd : sd_sets dd'' = sd_sets dn)
             by (apply (optimize_rules_dscpvmap_sets _ _ _ _ _ _ _ (eq_sym Erec))).
           assert (Hsets_dn : sd_sets dn = sd_sets d) by (subst dn; reflexivity).
           assert (Hmaps_dd : sd_maps dd'' = sd_maps dn)
             by (apply (optimize_rules_dscpvmap_maps _ _ _ _ _ _ _ (eq_sym Erec))).
           assert (Hmaps_dn : sd_maps dn = sd_maps d) by (subst dn; reflexivity).
           assert (Htail : eval_rules rr'' (env_with_sets base dd'') p
                           = eval_rules rest' (env_with_sets base dn) p).
           { eapply (IH rest' (S n) dn m'' dd'' rr'' base p (eq_sym Erec)); [| exact Hrf_rest'].
             intros k Hk Hin. subst dn; cbn [sd_vmaps map] in Hin.
             destruct Hin as [Heq | Hin].
             - apply vmapname_inj in Heq. lia.
             - apply (Hfresh k); [lia | exact Hin]. }
           assert (Hlook : e_vmap (env_with_sets base dd'')
                             (vmapname n) = map vmap_pt entries).
           { rewrite e_vmap_env_with_sets.
             erewrite (optimize_rules_dscpvmap_assoc_stable fuel (S n) dn _ _ _ _
                         (vmapname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_vmaps assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply vmapname_inj in Heq. lia. }
           set (ed := env_with_sets base dd'') in *.
           transitivity (eval_rules
             (map (fun vw => orig_rule_m f mask xor (fst vw) body (snd vw)) entries ++ rr'') ed p).
           { unfold ed. apply (eval_rules_dscpv_mergeN f mask xor (vmapname n) entries body rr''
                                 (env_with_sets base dd'') p).
             - exact Hlook.
             - intros v w Hin. subst entries. destruct Hin as [Hvw | Hin];
                 [ inversion Hvw; subst; exact HwK1 | apply (HwK v w Hin) ].
             - intros v w Hin. subst entries. destruct Hin as [Hvw | Hin];
                 [ inversion Hvw; subst; exact HwM1 | apply (HwM v w Hin) ].
             - intros v w Hin. subst entries. destruct Hin as [Hvw | Hin];
                 [ inversion Hvw; subst; exact HwX1 | apply (HwX v w Hin) ].
             - intros v w Hin. subst entries. destruct Hin as [Hvw | Hin];
                 [ inversion Hvw; subst; exact HwT1 | apply (HwT v w Hin) ].
             - apply (body_has_synproxy_false_stops body p Hns).
             - exact Hnt. }
           assert (Htail' : eval_rules rr'' ed p = eval_rules rest' ed p).
           { rewrite Htail. unfold ed.
             apply (eval_rules_agree_gen rest' p base dn dd'').
             intros r Hr. apply decls_agree_rule_sym.
             apply (decls_agree_rule_vmapseam base dn dd'' r (S n)).
             - apply (optimize_rules_dscpvmap_sets fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_dscpvmap_maps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_dscpvmap_assoc_stable fuel (S n) dn rest'
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - rewrite Forall_forall in Hrf_rest'. apply Hrf_rest'; exact Hr. }
           rewrite (eval_rules_app_cong
                      (map (fun vw => orig_rule_m f mask xor (fst vw) body (snd vw)) entries)
                      rr'' rest' ed p Htail').
           rewrite <- Hrun_eq.
           unfold ed. apply (eval_rules_agree_gen (r1 :: r2 :: rest) p base dd'' d).
           intros r Hr. apply (decls_agree_rule_vmapseam base d dd'' r n).
           ++ rewrite Hsets_dd, Hsets_dn; reflexivity.
           ++ rewrite Hmaps_dd, Hmaps_dn; reflexivity.
           ++ intros nm X Hf.
              rewrite (optimize_rules_dscpvmap_assoc_stable fuel (S n) dn rest' m'' dd'' rr'' nm X
                         (eq_sym Erec) (fun k Hk => Hf k ltac:(lia))).
              subst dn; cbn [sd_vmaps assoc_str].
              destruct (String.eqb nm (vmapname n)) eqn:Eq.
              ** apply String.eqb_eq in Eq. exfalso. apply (Hf n (Nat.le_refl n) Eq).
              ** reflexivity.
           ++ rewrite Forall_forall in Hrf. apply Hrf; exact Hr.
      * remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        cbn [eval_rules].
        rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
        assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_vmapseam base d dd'' r1 n).
             - apply (optimize_rules_dscpvmap_sets fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - apply (optimize_rules_dscpvmap_maps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_dscpvmap_assoc_stable fuel n d (r2 :: rest) m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
        rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
        rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
        rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
Qed.

(** dscpvmap output read-freshness (own [vmapname] namespace): the merged
    [mk_vmap_rule_t] reads only the freshly minted [vmapname n]. *)
Lemma rule_vmap_name_mk_vmap_rule_t : forall f ts nm body,
  rule_vmap_name (mk_vmap_rule_t f ts nm body) = [nm].
Proof. reflexivity. Qed.

Lemma optimize_rules_dscpvmap_output_vmap_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_dscpvmap fuel n d rs = (n', d', rs') ->
  Forall (rule_vmap_fresh n) rs ->
  Forall (rule_vmap_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_dscpvmap_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_dscp r1) as [[[[[f mask] xor] v1] body] |] eqn:Ehd.
      * destruct (take_dscpv_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct (take_dscpv_run_shape r1 f mask xor v1 body (r2 :: rest) es rest' Ehd Erun)
          as [Hsplit _].
        destruct es as [| e es'].
        -- remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_dscpvmap_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                        | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
        -- destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           2:{ remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
               destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
               injection H as Hn' Hd' Hr'. subst n' d' rs'.
               assert (Hmono : n <= m'')
                 by (apply (optimize_rules_dscpvmap_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
               constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                            | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)]. }
           cbv zeta in H.
           remember (optimize_rules_dscpvmap fuel (S n)
                       {| sd_sets := sd_sets d;
                          sd_vmaps := (vmapname n,
                            map vmap_pt ((v1, r_verdict r1) :: e :: es')) :: sd_vmaps d;
                          sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_dscpvmap_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_vmap_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_vmap_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ intros k Hk Hin. rewrite rule_vmap_name_mk_vmap_rule_t in Hin.
              cbn [In] in Hin. destruct Hin as [Heq | []].
              apply vmapname_inj in Heq. lia.
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_dscpvmap_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                     | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
Qed.

(** ** Part 4 prelude: read-freshness PROPAGATION through the pass outputs.

    Each pass's output rules read only (a) names an INPUT rule read, or (b) the
    minted [setname]/[vmapname] at indices in [n, n').  So input read-freshness at
    [n] yields output read-freshness at [n'].  This lets the entry point establish
    freshness ONCE (from the seed) and thread it across the three passes. *)

Lemma head_value_rbody : forall r f v body,
  head_value r = Some (f, v, body) -> r_body r = BMatch (MCmp f CEq v) :: body.
Proof.
  intros r f v body H. unfold head_value in H.
  destruct (r_body r) as [| [m | s] tl] eqn:Eb; try discriminate.
  destruct m as [ | | | | g op u | | | | | | | | ]; try discriminate.
  destruct op; try discriminate. inversion H; subst. reflexivity.
Qed.

Lemma head_value2_rbody : forall r f1 a1 f2 b1 body,
  head_value2 r = Some (f1, a1, f2, b1, body) ->
  r_body r = BMatch (MCmp f1 CEq a1) :: BMatch (MCmp f2 CEq b1) :: body.
Proof.
  intros r f1 a1 f2 b1 body H. unfold head_value2 in H.
  destruct (r_body r) as [| [m | s] tl] eqn:Eb; try discriminate.
  destruct m as [ | | | | g op u | | | | | | | | ]; try discriminate.
  destruct op; try discriminate. destruct tl as [| [m2 | s2] tl2]; try discriminate.
  destruct m2 as [ | | | | g2 op2 u2 | | | | | | | | ]; try discriminate.
  destruct op2; try discriminate. inversion H; subst. reflexivity.
Qed.

Lemma body_set_names_cons_mcmp : forall f v body,
  body_set_names (BMatch (MCmp f CEq v) :: body) = body_set_names body.
Proof. reflexivity. Qed.

Lemma body_set_names_mk_head_MConcat : forall fields name body r1,
  body_set_names (r_body (mk_head (MConcatSet fields false name) body r1))
  = name :: body_set_names body.
Proof.
  intros fields name body r1. unfold mk_head, body_set_names; cbn [r_body].
  replace (body_matches (BMatch (MConcatSet fields false name) :: body))
    with (MConcatSet fields false name :: body_matches body) by reflexivity.
  cbn [flat_map mc_set_name app]. reflexivity.
Qed.

Lemma rule_vmap_name_mk_head : forall m body r1,
  rule_vmap_name (mk_head m body r1) = rule_vmap_name r1.
Proof. intros. unfold rule_vmap_name, mk_head; cbn [r_vmap r_outcome]. reflexivity. Qed.

Lemma rule_nat_map_name_mk_head : forall m body r1,
  rule_nat_map_name (mk_head m body r1) = rule_nat_map_name r1.
Proof. intros. unfold rule_nat_map_name, mk_head; cbn [r_nat r_outcome]. reflexivity. Qed.

(** *** dscp output-freshness (its own [setname] namespace + [vmap] pass-through). *)
Lemma body_set_names_cons_mmasked : forall f mask xor v body,
  body_set_names (BMatch (MMasked f CEq mask xor v) :: body) = body_set_names body.
Proof. reflexivity. Qed.

Lemma body_set_names_mk_head_MSetT : forall f ts name body r1,
  body_set_names (r_body (mk_head (MSetT f ts false name) body r1))
  = name :: body_set_names body.
Proof.
  intros f ts name body r1. unfold mk_head, body_set_names; cbn [r_body].
  replace (body_matches (BMatch (MSetT f ts false name) :: body))
    with (MSetT f ts false name :: body_matches body) by reflexivity.
  cbn [flat_map mc_set_name app]. reflexivity.
Qed.

Lemma optimize_rules_dscp_output_set_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_dscp fuel n d rs = (n', d', rs') ->
  Forall (rule_set_fresh n) rs ->
  Forall (rule_set_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_dscp_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_dscp r1) as [[[[[f mask] xor] v1] body] |] eqn:Ehd.
      * destruct (take_dscp_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct (take_dscp_run_shape r1 f mask xor v1 body (r2 :: rest) vs rest' Ehd Erun)
          as [Hsplit _].
        destruct vs as [| v0 vs'].
        -- remember (optimize_rules_dscp fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_dscp_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor; [apply (rule_set_fresh_mono n m'' r1 Hmono Hf1)
                        | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
        -- cbv zeta in H.
           remember (optimize_rules_dscp fuel (S n)
                       {| sd_sets := (setname n, map (fun w => (w, w)) (v1 :: v0 :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_dscp_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ intros k Hk Hin.
              rewrite (body_set_names_mk_head_MSetT f [TBitAnd mask xor] (setname n) body r1) in Hin.
              rewrite <- (body_set_names_cons_mmasked f mask xor v1 body) in Hin.
              rewrite <- (head_dscp_rbody r1 f mask xor v1 body Ehd) in Hin.
              destruct Hin as [Heq | Hin].
              ** apply setname_inj in Heq. lia.
              ** apply (Hf1 k); [lia | exact Hin].
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_dscp fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_dscp_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor; [apply (rule_set_fresh_mono n m'' r1 Hmono Hf1)
                     | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
Qed.

Lemma optimize_rules_dscp_output_vmap_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_dscp fuel n d rs = (n', d', rs') ->
  Forall (rule_vmap_fresh n) rs ->
  Forall (rule_vmap_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_dscp_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_dscp r1) as [[[[[f mask] xor] v1] body] |] eqn:Ehd.
      * destruct (take_dscp_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct (take_dscp_run_shape r1 f mask xor v1 body (r2 :: rest) vs rest' Ehd Erun)
          as [Hsplit _].
        destruct vs as [| v0 vs'].
        -- remember (optimize_rules_dscp fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_dscp_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                        | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
        -- cbv zeta in H.
           remember (optimize_rules_dscp fuel (S n)
                       {| sd_sets := (setname n, map (fun w => (w, w)) (v1 :: v0 :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_dscp_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_vmap_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_vmap_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ intros k Hk Hin.
              rewrite (rule_vmap_name_mk_head (MSetT f [TBitAnd mask xor] false (setname n)) body r1) in Hin.
              apply (Hf1 k); [lia | exact Hin].
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_dscp fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_dscp_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                     | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
Qed.

(** *** intervalsethostorder output-freshness (its own [setname] namespace + [vmap] pass-through). *)
Lemma body_set_names_cons_mranget : forall f ts lo hi body,
  body_set_names (BMatch (MRangeT f ts false lo hi) :: body) = body_set_names body.
Proof. reflexivity. Qed.

Lemma optimize_rules_intervalsethostorder_output_set_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_intervalsethostorder fuel n d rs = (n', d', rs') ->
  Forall (rule_set_fresh n) rs ->
  Forall (rule_set_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_intervalsethostorder_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_ivsett r1) as [[[[[f ts] lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_ivsett_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        pose proof (take_ivsett_run_shape r1 f ts lo1 hi1 body (r2 :: rest) ivs rest' Ehd Erun) as Hsplit.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_intervalsethostorder_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor.
           ++ apply (rule_set_fresh_mono n m'' r1 Hmono Hf1).
           ++ apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail).
        -- cbv zeta in H.
           remember (optimize_rules_intervalsethostorder fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_intervalsethostorder_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ intros k Hk Hin.
              rewrite (body_set_names_mk_head_MSetT f ts (setname n) body r1) in Hin.
              rewrite <- (body_set_names_cons_mranget f ts lo1 hi1 body) in Hin.
              rewrite <- (head_ivsett_rbody r1 f ts lo1 hi1 body Ehd) in Hin.
              destruct Hin as [Heq | Hin].
              ** apply setname_inj in Heq. lia.
              ** apply (Hf1 k); [lia | exact Hin].
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_intervalsethostorder_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor.
        -- apply (rule_set_fresh_mono n m'' r1 Hmono Hf1).
        -- apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail).
Qed.

Lemma optimize_rules_intervalsethostorder_output_vmap_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_intervalsethostorder fuel n d rs = (n', d', rs') ->
  Forall (rule_vmap_fresh n) rs ->
  Forall (rule_vmap_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_intervalsethostorder_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_ivsett r1) as [[[[[f ts] lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_ivsett_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        pose proof (take_ivsett_run_shape r1 f ts lo1 hi1 body (r2 :: rest) ivs rest' Ehd Erun) as Hsplit.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_intervalsethostorder_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                        | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
        -- cbv zeta in H.
           remember (optimize_rules_intervalsethostorder fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_intervalsethostorder_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_vmap_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_vmap_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ intros k Hk Hin.
              rewrite (rule_vmap_name_mk_head (MSetT f ts false (setname n)) body r1) in Hin.
              apply (Hf1 k); [lia | exact Hin].
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_intervalsethostorder_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                     | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
Qed.

(** *** intervalset output-freshness (its own [setname] namespace + [vmap] pass-through). *)
Lemma optimize_rules_intervalset_output_set_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_intervalset fuel n d rs = (n', d', rs') ->
  Forall (rule_set_fresh n) rs ->
  Forall (rule_set_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_intervalset_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_range r1) as [[[[f lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_range_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        pose proof (take_range_run_shape r1 f lo1 hi1 body (r2 :: rest) ivs rest' Ehd Erun) as Hsplit.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_intervalset_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor.
           ++ apply (rule_set_fresh_mono n m'' r1 Hmono Hf1).
           ++ apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail).
        -- cbv zeta in H.
           remember (optimize_rules_intervalset fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_intervalset_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ intros k Hk Hin.
              rewrite (body_set_names_mk_head_MConcat [f] (setname n) body r1) in Hin.
              rewrite <- (body_set_names_cons_mrange f lo1 hi1 body) in Hin.
              rewrite <- (head_range_rbody r1 f lo1 hi1 body Ehd) in Hin.
              destruct Hin as [Heq | Hin].
              ** apply setname_inj in Heq. lia.
              ** apply (Hf1 k); [lia | exact Hin].
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_intervalset_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor.
        -- apply (rule_set_fresh_mono n m'' r1 Hmono Hf1).
        -- apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail).
Qed.

Lemma optimize_rules_intervalset_output_vmap_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_intervalset fuel n d rs = (n', d', rs') ->
  Forall (rule_vmap_fresh n) rs ->
  Forall (rule_vmap_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_intervalset_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_range r1) as [[[[f lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_range_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        pose proof (take_range_run_shape r1 f lo1 hi1 body (r2 :: rest) ivs rest' Ehd Erun) as Hsplit.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_intervalset_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor.
           ++ apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1).
           ++ apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail).
        -- cbv zeta in H.
           remember (optimize_rules_intervalset fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_intervalset_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_vmap_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_vmap_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ intros k Hk Hin. rewrite (rule_vmap_name_mk_head (MConcatSet [f] false (setname n)) body r1) in Hin.
              apply (Hf1 k); [lia | exact Hin].
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_intervalset_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor.
        -- apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1).
        -- apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail).
Qed.
(** *** valueset propagates [rule_set_fresh] (its own namespace). *)
Lemma optimize_rules_valueset_output_set_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_valueset fuel n d rs = (n', d', rs') ->
  Forall (rule_set_fresh n) rs ->
  Forall (rule_set_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_valueset_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_value_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct (take_value_run_shape r1 f v1 body (r2 :: rest) vs rest' Ehd Erun)
          as [Hsplit _].
        destruct vs as [| v vs'].
        -- remember (optimize_rules_valueset fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_valueset_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor.
           ++ apply (rule_set_fresh_mono n m'' r1 Hmono Hf1).
           ++ apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail).
        -- cbv zeta in H.
           remember (optimize_rules_valueset fuel (S n)
                       {| sd_sets := (setname n, map (fun w => (w,w)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_valueset_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ (* merged rule reads [setname n] (< m'') and body_set_names r1 (fresh at n) *)
              intros k Hk Hin.
              rewrite (body_set_names_mk_head_MConcat [f] (setname n) body r1) in Hin.
              rewrite <- (body_set_names_cons_mcmp f v1 body) in Hin.
              rewrite <- (head_value_rbody r1 f v1 body Ehd) in Hin.
              destruct Hin as [Heq | Hin].
              ** apply setname_inj in Heq. lia.
              ** apply (Hf1 k); [lia | exact Hin].
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_valueset fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_valueset_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor.
        -- apply (rule_set_fresh_mono n m'' r1 Hmono Hf1).
        -- apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail).
Qed.

(** valueset propagates [rule_vmap_fresh] (it adds NO vmap name; merged rule keeps
    [r1]'s vmap). *)
Lemma optimize_rules_valueset_output_vmap_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_valueset fuel n d rs = (n', d', rs') ->
  Forall (rule_vmap_fresh n) rs ->
  Forall (rule_vmap_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_valueset_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_value_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct (take_value_run_shape r1 f v1 body (r2 :: rest) vs rest' Ehd Erun)
          as [Hsplit _].
        destruct vs as [| v vs'].
        -- remember (optimize_rules_valueset fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_valueset_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor.
           ++ apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1).
           ++ apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail).
        -- cbv zeta in H.
           remember (optimize_rules_valueset fuel (S n)
                       {| sd_sets := (setname n, map (fun w => (w,w)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_valueset_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_vmap_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_vmap_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ (* merged rule vmap-name = r1's, fresh at n -> at m'' *)
              intros k Hk Hin. rewrite (rule_vmap_name_mk_head (MConcatSet [f] false (setname n)) body r1) in Hin.
              apply (Hf1 k); [lia | exact Hin].
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_valueset fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_valueset_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor.
        -- apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1).
        -- apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail).
Qed.

Lemma optimize_rules_valueset_output_nat_map_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_valueset fuel n d rs = (n', d', rs') ->
  Forall (rule_nat_map_fresh n) rs ->
  Forall (rule_nat_map_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_valueset_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_value_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct (take_value_run_shape r1 f v1 body (r2 :: rest) vs rest' Ehd Erun)
          as [Hsplit _].
        destruct vs as [| v vs'].
        -- remember (optimize_rules_valueset fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_valueset_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor.
           ++ apply (rule_nat_map_fresh_mono n m'' r1 Hmono Hf1).
           ++ apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail).
        -- cbv zeta in H.
           remember (optimize_rules_valueset fuel (S n)
                       {| sd_sets := (setname n, map (fun w => (w,w)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_valueset_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_nat_map_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_nat_map_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ (* merged rule vmap-name = r1's, fresh at n -> at m'' *)
              intros k Hk Hin. rewrite (rule_nat_map_name_mk_head (MConcatSet [f] false (setname n)) body r1) in Hin.
              apply (Hf1 k); [lia | exact Hin].
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_valueset fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_valueset_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor.
        -- apply (rule_nat_map_fresh_mono n m'' r1 Hmono Hf1).
        -- apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail).
Qed.

Lemma body_set_names_cons2_mcmp : forall f1 a1 f2 b1 body,
  body_set_names (BMatch (MCmp f1 CEq a1) :: BMatch (MCmp f2 CEq b1) :: body)
  = body_set_names body.
Proof. reflexivity. Qed.

(** *** concat propagates [rule_set_fresh] and [rule_vmap_fresh]. *)
Lemma optimize_rules_concat_output_set_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_concat fuel n d rs = (n', d', rs') ->
  Forall (rule_set_fresh n) rs ->
  Forall (rule_set_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_concat_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_value2 r1) as [[[[[f1 a1] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concat_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct (take_concat_run_shape r1 f1 a1 f2 b1 body (r2 :: rest) ts rest' Ehd Erun)
          as [Hsplit _].
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concat fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_concat_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor; [apply (rule_set_fresh_mono n m'' r1 Hmono Hf1)
                        | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
        -- cbv zeta in H.
           remember (optimize_rules_concat fuel (S n)
                       {| sd_sets := (setname n, map pack_tuple ((a1,b1) :: t :: ts'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_concat_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ intros k Hk Hin. unfold merged_rule2 in Hin.
              rewrite (body_set_names_mk_head_MConcat [f1; f2] (setname n) body r1) in Hin.
              rewrite <- (body_set_names_cons2_mcmp f1 a1 f2 b1 body) in Hin.
              rewrite <- (head_value2_rbody r1 f1 a1 f2 b1 body Ehd) in Hin.
              destruct Hin as [Heq | Hin].
              ** apply setname_inj in Heq. lia.
              ** apply (Hf1 k); [lia | exact Hin].
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_concat fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_concat_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor; [apply (rule_set_fresh_mono n m'' r1 Hmono Hf1)
                     | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
Qed.

Lemma optimize_rules_concat_output_vmap_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_concat fuel n d rs = (n', d', rs') ->
  Forall (rule_vmap_fresh n) rs ->
  Forall (rule_vmap_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_concat_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_value2 r1) as [[[[[f1 a1] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concat_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct (take_concat_run_shape r1 f1 a1 f2 b1 body (r2 :: rest) ts rest' Ehd Erun)
          as [Hsplit _].
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concat fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_concat_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                        | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
        -- cbv zeta in H.
           remember (optimize_rules_concat fuel (S n)
                       {| sd_sets := (setname n, map pack_tuple ((a1,b1) :: t :: ts'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_concat_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_vmap_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_vmap_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ intros k Hk Hin. unfold merged_rule2 in Hin.
              rewrite (rule_vmap_name_mk_head (MConcatSet [f1; f2] false (setname n)) body r1) in Hin.
              apply (Hf1 k); [lia | exact Hin].
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_concat fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_concat_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                     | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
Qed.

(** *** concatguarded output-freshness (its own [setname] namespace + [vmap] pass-through). *)
Lemma body_set_names_merged_rule2g : forall f1 f2 gm name body r1,
  body_set_names (r_body (merged_rule2g f1 f2 gm name body r1))
  = (match mc_set_name gm with Some nm => [nm] | None => [] end) ++ name :: body_set_names body.
Proof.
  intros. unfold merged_rule2g, mk_head, body_set_names; cbn [r_body].
  replace (body_matches (BMatch gm :: BMatch (MConcatSet [f1; f2] false name) :: body))
    with (gm :: MConcatSet [f1; f2] false name :: body_matches body) by reflexivity.
  cbn [flat_map mc_set_name]. reflexivity.
Qed.

Lemma body_set_names_orig_head2g : forall r1 f1 a1 gm f2 b1 body,
  head_value2g r1 = Some (f1, a1, gm, f2, b1, body) ->
  body_set_names (r_body r1)
  = (match mc_set_name gm with Some nm => [nm] | None => [] end) ++ body_set_names body.
Proof.
  intros r1 f1 a1 gm f2 b1 body H.
  rewrite (head_value2g_rbody r1 f1 a1 gm f2 b1 body H).
  unfold body_set_names.
  replace (body_matches (BMatch (MCmp f1 CEq a1) :: BMatch gm :: BMatch (MCmp f2 CEq b1) :: body))
    with (MCmp f1 CEq a1 :: gm :: MCmp f2 CEq b1 :: body_matches body) by reflexivity.
  cbn [flat_map mc_set_name app]. reflexivity.
Qed.

Lemma optimize_rules_concatguarded_output_set_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_concatguarded fuel n d rs = (n', d', rs') ->
  Forall (rule_set_fresh n) rs ->
  Forall (rule_set_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_concatguarded_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_value2g r1) as [[[[[[f1 a1] gm] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concatg_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct (take_concatg_run_shape r1 f1 a1 gm f2 b1 body (r2 :: rest) ts rest' Ehd Erun)
          as [Hsplit _].
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concatguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_concatguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor; [apply (rule_set_fresh_mono n m'' r1 Hmono Hf1)
                        | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
        -- cbv zeta in H.
           remember (optimize_rules_concatguarded fuel (S n)
                       {| sd_sets := (setname n, map pack_tuple ((a1,b1) :: t :: ts'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_concatguarded_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ intros k Hk Hin.
              rewrite (body_set_names_merged_rule2g f1 f2 gm (setname n) body r1) in Hin.
              rewrite in_app_iff in Hin. destruct Hin as [Hgm | Hrest_in].
              ** apply (Hf1 k); [lia |].
                 rewrite (body_set_names_orig_head2g r1 f1 a1 gm f2 b1 body Ehd).
                 rewrite in_app_iff. left; exact Hgm.
              ** cbn [In] in Hrest_in. destruct Hrest_in as [Heq | Hin].
                 --- apply setname_inj in Heq. lia.
                 --- apply (Hf1 k); [lia |].
                     rewrite (body_set_names_orig_head2g r1 f1 a1 gm f2 b1 body Ehd).
                     rewrite in_app_iff. right; exact Hin.
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_concatguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_concatguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor; [apply (rule_set_fresh_mono n m'' r1 Hmono Hf1)
                     | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
Qed.

Lemma optimize_rules_concatguarded_output_vmap_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_concatguarded fuel n d rs = (n', d', rs') ->
  Forall (rule_vmap_fresh n) rs ->
  Forall (rule_vmap_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_concatguarded_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_value2g r1) as [[[[[[f1 a1] gm] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concatg_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct (take_concatg_run_shape r1 f1 a1 gm f2 b1 body (r2 :: rest) ts rest' Ehd Erun)
          as [Hsplit _].
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concatguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_concatguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                        | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
        -- cbv zeta in H.
           remember (optimize_rules_concatguarded fuel (S n)
                       {| sd_sets := (setname n, map pack_tuple ((a1,b1) :: t :: ts'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_concatguarded_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_vmap_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_vmap_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ intros k Hk Hin. unfold merged_rule2g in Hin.
              rewrite (rule_vmap_name_mk_head gm (BMatch (MConcatSet [f1; f2] false (setname n)) :: body) r1) in Hin.
              apply (Hf1 k); [lia | exact Hin].
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_concatguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_concatguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                     | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
Qed.

(** *** setguarded output-freshness (its own [setname] namespace + [vmap] pass-through). *)
Lemma body_set_names_merged_ruleGs : forall f gm name body r1,
  body_set_names (r_body (merged_ruleGs f gm name body r1))
  = (match mc_set_name gm with Some nm => [nm] | None => [] end) ++ name :: body_set_names body.
Proof.
  intros. unfold merged_ruleGs, mk_head, body_set_names; cbn [r_body].
  replace (body_matches (BMatch gm :: BMatch (MConcatSet [f] false name) :: body))
    with (gm :: MConcatSet [f] false name :: body_matches body) by reflexivity.
  cbn [flat_map mc_set_name]. reflexivity.
Qed.

Lemma body_set_names_orig_headGs : forall r1 gm f v1 body,
  head_valueGs r1 = Some (gm, f, v1, body) ->
  body_set_names (r_body r1)
  = (match mc_set_name gm with Some nm => [nm] | None => [] end) ++ body_set_names body.
Proof.
  intros r1 gm f v1 body H.
  rewrite (head_valueGs_rbody r1 gm f v1 body H).
  unfold body_set_names.
  replace (body_matches (BMatch gm :: BMatch (MCmp f CEq v1) :: body))
    with (gm :: MCmp f CEq v1 :: body_matches body) by reflexivity.
  cbn [flat_map mc_set_name app]. reflexivity.
Qed.

Lemma optimize_rules_setguarded_output_set_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_setguarded fuel n d rs = (n', d', rs') ->
  Forall (rule_set_fresh n) rs ->
  Forall (rule_set_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_setguarded_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_valueGs r1) as [[[[gm f] v1] body] |] eqn:Ehd.
      * destruct (take_setg_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct (take_setg_run_shape r1 gm f v1 body (r2 :: rest) vs rest' Ehd Erun)
          as [Hsplit _].
        destruct vs as [| v0 vs'].
        -- remember (optimize_rules_setguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_setguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor; [apply (rule_set_fresh_mono n m'' r1 Hmono Hf1)
                        | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
        -- cbv zeta in H.
           remember (optimize_rules_setguarded fuel (S n)
                       {| sd_sets := (setname n, map (fun v => (v, v)) (v1 :: v0 :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_setguarded_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ intros k Hk Hin.
              rewrite (body_set_names_merged_ruleGs f gm (setname n) body r1) in Hin.
              rewrite in_app_iff in Hin. destruct Hin as [Hgm | Hrest_in].
              ** apply (Hf1 k); [lia |].
                 rewrite (body_set_names_orig_headGs r1 gm f v1 body Ehd).
                 rewrite in_app_iff. left; exact Hgm.
              ** cbn [In] in Hrest_in. destruct Hrest_in as [Heq | Hin].
                 --- apply setname_inj in Heq. lia.
                 --- apply (Hf1 k); [lia |].
                     rewrite (body_set_names_orig_headGs r1 gm f v1 body Ehd).
                     rewrite in_app_iff. right; exact Hin.
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_setguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_setguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor; [apply (rule_set_fresh_mono n m'' r1 Hmono Hf1)
                     | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
Qed.

Lemma optimize_rules_setguarded_output_vmap_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_setguarded fuel n d rs = (n', d', rs') ->
  Forall (rule_vmap_fresh n) rs ->
  Forall (rule_vmap_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_setguarded_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_valueGs r1) as [[[[gm f] v1] body] |] eqn:Ehd.
      * destruct (take_setg_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct (take_setg_run_shape r1 gm f v1 body (r2 :: rest) vs rest' Ehd Erun)
          as [Hsplit _].
        destruct vs as [| v0 vs'].
        -- remember (optimize_rules_setguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_setguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                        | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
        -- cbv zeta in H.
           remember (optimize_rules_setguarded fuel (S n)
                       {| sd_sets := (setname n, map (fun v => (v, v)) (v1 :: v0 :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_setguarded_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_vmap_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_vmap_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ intros k Hk Hin. unfold merged_ruleGs in Hin.
              rewrite (rule_vmap_name_mk_head gm (BMatch (MConcatSet [f] false (setname n)) :: body) r1) in Hin.
              apply (Hf1 k); [lia | exact Hin].
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_setguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_setguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                     | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
Qed.

(** *** intervalsetguarded propagates freshness (its own [setname] namespace; adds NO vmap name).
    The guarded range head [MRange] contributes NO set name, so — like [setguarded] — the
    merged rule's set names are [setname n] plus the original's (via the shared body). *)
Lemma body_set_names_orig_headGr : forall r1 gm f lo1 hi1 body,
  head_rangeGr r1 = Some (gm, f, lo1, hi1, body) ->
  body_set_names (r_body r1)
  = (match mc_set_name gm with Some nm => [nm] | None => [] end) ++ body_set_names body.
Proof.
  intros r1 gm f lo1 hi1 body H.
  rewrite (head_rangeGr_rbody r1 gm f lo1 hi1 body H).
  unfold body_set_names.
  replace (body_matches (BMatch gm :: BMatch (MRange f false lo1 hi1) :: body))
    with (gm :: MRange f false lo1 hi1 :: body_matches body) by reflexivity.
  cbn [flat_map mc_set_name app]. reflexivity.
Qed.

Lemma optimize_rules_intervalsetguarded_output_set_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_intervalsetguarded fuel n d rs = (n', d', rs') ->
  Forall (rule_set_fresh n) rs ->
  Forall (rule_set_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_intervalsetguarded_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_rangeGr r1) as [[[[[gm f] lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_rangeg_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        pose proof (take_rangeg_run_shape r1 gm f lo1 hi1 body (r2 :: rest) ivs rest' Ehd Erun) as Hsplit.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_intervalsetguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor; [apply (rule_set_fresh_mono n m'' r1 Hmono Hf1)
                        | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
        -- cbv zeta in H.
           remember (optimize_rules_intervalsetguarded fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_intervalsetguarded_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ intros k Hk Hin.
              rewrite (body_set_names_merged_ruleGs f gm (setname n) body r1) in Hin.
              rewrite in_app_iff in Hin. destruct Hin as [Hgm | Hrest_in].
              ** apply (Hf1 k); [lia |].
                 rewrite (body_set_names_orig_headGr r1 gm f lo1 hi1 body Ehd).
                 rewrite in_app_iff. left; exact Hgm.
              ** cbn [In] in Hrest_in. destruct Hrest_in as [Heq | Hin].
                 --- apply setname_inj in Heq. lia.
                 --- apply (Hf1 k); [lia |].
                     rewrite (body_set_names_orig_headGr r1 gm f lo1 hi1 body Ehd).
                     rewrite in_app_iff. right; exact Hin.
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_intervalsetguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor; [apply (rule_set_fresh_mono n m'' r1 Hmono Hf1)
                     | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
Qed.

Lemma optimize_rules_intervalsetguarded_output_vmap_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_intervalsetguarded fuel n d rs = (n', d', rs') ->
  Forall (rule_vmap_fresh n) rs ->
  Forall (rule_vmap_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_intervalsetguarded_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_rangeGr r1) as [[[[[gm f] lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_rangeg_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        pose proof (take_rangeg_run_shape r1 gm f lo1 hi1 body (r2 :: rest) ivs rest' Ehd Erun) as Hsplit.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_intervalsetguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                        | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
        -- cbv zeta in H.
           remember (optimize_rules_intervalsetguarded fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_intervalsetguarded_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_vmap_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_vmap_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ intros k Hk Hin. unfold merged_ruleGs in Hin.
              rewrite (rule_vmap_name_mk_head gm (BMatch (MConcatSet [f] false (setname n)) :: body) r1) in Hin.
              apply (Hf1 k); [lia | exact Hin].
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_intervalsetguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                     | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
Qed.

(** *** mixedpointrangeguarded propagates freshness (own [setname] namespace; adds NO vmap name). *)
Lemma body_set_names_orig_headGm : forall r1 gm f e1 body,
  head_mixGm r1 = Some (gm, f, e1, body) ->
  body_set_names (r_body r1)
  = (match mc_set_name gm with Some nm => [nm] | None => [] end) ++ body_set_names body.
Proof.
  intros r1 gm f e1 body H.
  rewrite (head_mixGm_rbody r1 gm f e1 body H).
  unfold body_set_names.
  replace (body_matches (BMatch gm :: BMatch (melem_mc f e1) :: body))
    with (gm :: melem_mc f e1 :: body_matches body) by reflexivity.
  destruct e1 as [v | lo hi]; cbn [melem_mc flat_map mc_set_name app]; reflexivity.
Qed.

Lemma optimize_rules_mixedpointrangeguarded_output_set_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_mixedpointrangeguarded fuel n d rs = (n', d', rs') ->
  Forall (rule_set_fresh n) rs ->
  Forall (rule_set_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_mixedpointrangeguarded_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_mixGm r1) as [[[[gm f] e1] body] |] eqn:Ehd.
      * destruct (take_mix_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        pose proof (take_mix_run_shape r1 gm f e1 body (r2 :: rest) es rest' Ehd Erun) as Hsplit.
        destruct es as [| e es'].
        -- remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_mixedpointrangeguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor; [apply (rule_set_fresh_mono n m'' r1 Hmono Hf1)
                        | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
        -- cbv zeta in H.
           remember (optimize_rules_mixedpointrangeguarded fuel (S n)
                       {| sd_sets := (setname n, map melem_iv (e1 :: e :: es')) :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_mixedpointrangeguarded_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ intros k Hk Hin.
              rewrite (body_set_names_merged_ruleGs f gm (setname n) body r1) in Hin.
              rewrite in_app_iff in Hin. destruct Hin as [Hgm | Hrest_in].
              ** apply (Hf1 k); [lia |].
                 rewrite (body_set_names_orig_headGm r1 gm f e1 body Ehd).
                 rewrite in_app_iff. left; exact Hgm.
              ** cbn [In] in Hrest_in. destruct Hrest_in as [Heq | Hin].
                 --- apply setname_inj in Heq. lia.
                 --- apply (Hf1 k); [lia |].
                     rewrite (body_set_names_orig_headGm r1 gm f e1 body Ehd).
                     rewrite in_app_iff. right; exact Hin.
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_mixedpointrangeguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor; [apply (rule_set_fresh_mono n m'' r1 Hmono Hf1)
                     | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
Qed.

Lemma optimize_rules_mixedpointrangeguarded_output_vmap_fresh : forall fuel n d rs n' d' rs',
  optimize_rules_mixedpointrangeguarded fuel n d rs = (n', d', rs') ->
  Forall (rule_vmap_fresh n) rs ->
  Forall (rule_vmap_fresh n') rs'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; exact Hrf.
    + cbn in H. inversion H; subst; exact Hrf.
    + rewrite optimize_rules_mixedpointrangeguarded_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_mixGm r1) as [[[[gm f] e1] body] |] eqn:Ehd.
      * destruct (take_mix_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        pose proof (take_mix_run_shape r1 gm f e1 body (r2 :: rest) es rest' Ehd Erun) as Hsplit.
        destruct es as [| e es'].
        -- remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : n <= m'')
             by (apply (optimize_rules_mixedpointrangeguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
           constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                        | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
        -- cbv zeta in H.
           remember (optimize_rules_mixedpointrangeguarded fuel (S n)
                       {| sd_sets := (setname n, map melem_iv (e1 :: e :: es')) :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           assert (Hmono : S n <= m'')
             by (apply (optimize_rules_mixedpointrangeguarded_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec))).
           assert (Hrf_rest' : Forall (rule_vmap_fresh (S n)) rest').
           { eapply Forall_impl; [intros r Hr; apply (rule_vmap_fresh_mono n (S n) r); [lia | exact Hr] |].
             rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
           constructor.
           ++ intros k Hk Hin. unfold merged_ruleGs in Hin.
              rewrite (rule_vmap_name_mk_head gm (BMatch (MConcatSet [f] false (setname n)) :: body) r1) in Hin.
              apply (Hf1 k); [lia | exact Hin].
           ++ apply (IH (S n) _ rest' m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
      * remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        assert (Hmono : n <= m'')
          by (apply (optimize_rules_mixedpointrangeguarded_mono fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec))).
        constructor; [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
                     | apply (IH n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec) Hrf_tail)].
Qed.

(** ** Part 4: chain-level wrappers, composition, and the END-TO-END theorems. *)

(** *** Chain-level correctness (lift the [optimize_rules_*N_correct_uncond]). *)
Lemma optimize_chain_valueset_correct_uncond : forall n d c n' d' c' base p,
  optimize_chain_valueset n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) (c_rules c) ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c  (env_with_sets base d) p.
Proof.
  intros n d c n' d' c' base p H Hfs Hrf. unfold optimize_chain_valueset in H.
  destruct (optimize_rules_valueset (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_valueset_correct_uncond (Datatypes.length (c_rules c)) (c_rules c) n d
             m'' dd'' rr'' base p E Hfs Hrf). reflexivity.
Qed.

Lemma optimize_chain_concat_correct_uncond : forall n d c n' d' c' base p,
  optimize_chain_concat n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) (c_rules c) ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c  (env_with_sets base d) p.
Proof.
  intros n d c n' d' c' base p H Hfs Hrf. unfold optimize_chain_concat in H.
  destruct (optimize_rules_concat (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_concat_correct_uncond (Datatypes.length (c_rules c)) (c_rules c) n d
             m'' dd'' rr'' base p E Hfs Hrf). reflexivity.
Qed.

Lemma optimize_chain_vmap_correct_uncond : forall n d c n' d' c' base p,
  optimize_chain_vmap n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  Forall (rule_vmap_fresh n) (c_rules c) ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c  (env_with_sets base d) p.
Proof.
  intros n d c n' d' c' base p H Hfv Hrf. unfold optimize_chain_vmap in H.
  destruct (optimize_rules_vmap (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_vmap_correct_uncond (Datatypes.length (c_rules c)) (c_rules c) n d
             m'' dd'' rr'' base p E Hfv Hrf). reflexivity.
Qed.

(** *** vmapguarded (Optimize_VmapGuarded) chain-level wrappers. *)
Lemma optimize_chain_vmapguarded_correct_uncond : forall n d c n' d' c' base p,
  optimize_chain_vmapguarded n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  Forall (rule_vmap_fresh n) (c_rules c) ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c  (env_with_sets base d) p.
Proof.
  intros n d c n' d' c' base p H Hfv Hrf. unfold optimize_chain_vmapguarded in H.
  destruct (optimize_rules_vmapguarded (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_vmapguarded_correct_uncond (Datatypes.length (c_rules c)) (c_rules c) n d
             m'' dd'' rr'' base p E Hfv Hrf). reflexivity.
Qed.

Lemma optimize_chain_vmapguarded_output_vmap_fresh : forall n d c n' d' c',
  optimize_chain_vmapguarded n d c = (n', d', c') ->
  Forall (rule_vmap_fresh n) (c_rules c) -> Forall (rule_vmap_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_vmapguarded in H.
  destruct (optimize_rules_vmapguarded (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_vmapguarded_output_vmap_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

(** vmapguarded mints [vmapname]s bounded by [n']; thread vmapname-decl-freshness past
    the stage into the following vmap stage. *)
Lemma optimize_chain_vmapguarded_fresh_vmapname : forall n d c n' d' c',
  optimize_chain_vmapguarded n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  (forall k, n' <= k -> ~ In (vmapname k) (map fst (sd_vmaps d'))).
Proof.
  intros n d c n' d' c' H Hfresh k Hk Hin.
  pose proof (optimize_chain_vmapguarded_mono n d c n' d' c' H) as Hmono.
  destruct (optimize_chain_vmapguarded_keys_bound n d c n' d' c' k H Hin) as [Hin_d | Hlt].
  - apply (Hfresh k); [lia | exact Hin_d].
  - lia.
Qed.

(** *** dscpvmap (Optimize_DscpVmap) chain-level wrappers. *)
Lemma optimize_chain_dscpvmap_correct_uncond : forall n d c n' d' c' base p,
  optimize_chain_dscpvmap n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  Forall (rule_vmap_fresh n) (c_rules c) ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c  (env_with_sets base d) p.
Proof.
  intros n d c n' d' c' base p H Hfv Hrf. unfold optimize_chain_dscpvmap in H.
  destruct (optimize_rules_dscpvmap (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_dscpvmap_correct_uncond (Datatypes.length (c_rules c)) (c_rules c) n d
             m'' dd'' rr'' base p E Hfv Hrf). reflexivity.
Qed.

Lemma optimize_chain_dscpvmap_output_vmap_fresh : forall n d c n' d' c',
  optimize_chain_dscpvmap n d c = (n', d', c') ->
  Forall (rule_vmap_fresh n) (c_rules c) -> Forall (rule_vmap_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_dscpvmap in H.
  destruct (optimize_rules_dscpvmap (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_dscpvmap_output_vmap_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_dscpvmap_fresh_vmapname : forall n d c n' d' c',
  optimize_chain_dscpvmap n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  (forall k, n' <= k -> ~ In (vmapname k) (map fst (sd_vmaps d'))).
Proof.
  intros n d c n' d' c' H Hfresh k Hk Hin.
  pose proof (optimize_chain_dscpvmap_mono n d c n' d' c' H) as Hmono.
  destruct (optimize_chain_dscpvmap_keys_bound n d c n' d' c' k H Hin) as [Hin_d | Hlt].
  - apply (Hfresh k); [lia | exact Hin_d].
  - lia.
Qed.

(** *** Chain-level read-freshness propagation. *)
Lemma optimize_chain_valueset_output_set_fresh : forall n d c n' d' c',
  optimize_chain_valueset n d c = (n', d', c') ->
  Forall (rule_set_fresh n) (c_rules c) -> Forall (rule_set_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_valueset in H.
  destruct (optimize_rules_valueset (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_valueset_output_set_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_valueset_output_vmap_fresh : forall n d c n' d' c',
  optimize_chain_valueset n d c = (n', d', c') ->
  Forall (rule_vmap_fresh n) (c_rules c) -> Forall (rule_vmap_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_valueset in H.
  destruct (optimize_rules_valueset (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_valueset_output_vmap_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_valueset_output_nat_map_fresh : forall n d c n' d' c',
  optimize_chain_valueset n d c = (n', d', c') ->
  Forall (rule_nat_map_fresh n) (c_rules c) -> Forall (rule_nat_map_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_valueset in H.
  destruct (optimize_rules_valueset (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_valueset_output_nat_map_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_concat_output_set_fresh : forall n d c n' d' c',
  optimize_chain_concat n d c = (n', d', c') ->
  Forall (rule_set_fresh n) (c_rules c) -> Forall (rule_set_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_concat in H.
  destruct (optimize_rules_concat (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_concat_output_set_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_concat_output_vmap_fresh : forall n d c n' d' c',
  optimize_chain_concat n d c = (n', d', c') ->
  Forall (rule_vmap_fresh n) (c_rules c) -> Forall (rule_vmap_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_concat in H.
  destruct (optimize_rules_concat (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_concat_output_vmap_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

(** concat preserves [setname]-freshness (mints names bounded by [n']) — threads
    freshness past concat into the following concatguarded stage. *)
Lemma optimize_chain_concat_fresh_setname : forall n d c n' d' c',
  optimize_chain_concat n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n' <= k -> ~ In (setname k) (map fst (sd_sets d'))).
Proof.
  intros n d c n' d' c' H Hfresh k Hk Hin.
  pose proof (optimize_chain_concat_mono n d c n' d' c' H) as Hmono.
  destruct (optimize_chain_concat_keys_bound n d c n' d' c' k H Hin) as [Hin_d | Hlt].
  - apply (Hfresh k); [lia | exact Hin_d].
  - lia.
Qed.

(** *** concatguarded chain-level wrappers. *)
Lemma optimize_chain_concatguarded_correct_uncond : forall n d c n' d' c' base p,
  optimize_chain_concatguarded n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) (c_rules c) ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c  (env_with_sets base d) p.
Proof.
  intros n d c n' d' c' base p H Hfs Hrf. unfold optimize_chain_concatguarded in H.
  destruct (optimize_rules_concatguarded (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_concatguarded_correct_uncond (Datatypes.length (c_rules c)) (c_rules c) n d
             m'' dd'' rr'' base p E Hfs Hrf). reflexivity.
Qed.

Lemma optimize_chain_concatguarded_output_set_fresh : forall n d c n' d' c',
  optimize_chain_concatguarded n d c = (n', d', c') ->
  Forall (rule_set_fresh n) (c_rules c) -> Forall (rule_set_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_concatguarded in H.
  destruct (optimize_rules_concatguarded (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_concatguarded_output_set_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_concatguarded_output_vmap_fresh : forall n d c n' d' c',
  optimize_chain_concatguarded n d c = (n', d', c') ->
  Forall (rule_vmap_fresh n) (c_rules c) -> Forall (rule_vmap_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_concatguarded in H.
  destruct (optimize_rules_concatguarded (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_concatguarded_output_vmap_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

(** concatguarded mints [setname]s bounded by [n']; thread setname-freshness past concatguarded
    into the following intervalset stage. *)
Lemma optimize_chain_concatguarded_fresh_setname : forall n d c n' d' c',
  optimize_chain_concatguarded n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n' <= k -> ~ In (setname k) (map fst (sd_sets d'))).
Proof.
  intros n d c n' d' c' H Hfresh k Hk Hin.
  pose proof (optimize_chain_concatguarded_mono n d c n' d' c' H) as Hmono.
  destruct (optimize_chain_concatguarded_keys_bound n d c n' d' c' k H Hin) as [Hin_d | Hlt].
  - apply (Hfresh k); [lia | exact Hin_d].
  - lia.
Qed.

(** *** setguarded chain-level wrappers. *)
Lemma optimize_chain_setguarded_correct_uncond : forall n d c n' d' c' base p,
  optimize_chain_setguarded n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) (c_rules c) ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c  (env_with_sets base d) p.
Proof.
  intros n d c n' d' c' base p H Hfs Hrf. unfold optimize_chain_setguarded in H.
  destruct (optimize_rules_setguarded (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_setguarded_correct_uncond (Datatypes.length (c_rules c)) (c_rules c) n d
             m'' dd'' rr'' base p E Hfs Hrf). reflexivity.
Qed.

Lemma optimize_chain_setguarded_output_set_fresh : forall n d c n' d' c',
  optimize_chain_setguarded n d c = (n', d', c') ->
  Forall (rule_set_fresh n) (c_rules c) -> Forall (rule_set_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_setguarded in H.
  destruct (optimize_rules_setguarded (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_setguarded_output_set_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_setguarded_output_vmap_fresh : forall n d c n' d' c',
  optimize_chain_setguarded n d c = (n', d', c') ->
  Forall (rule_vmap_fresh n) (c_rules c) -> Forall (rule_vmap_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_setguarded in H.
  destruct (optimize_rules_setguarded (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_setguarded_output_vmap_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_setguarded_fresh_setname : forall n d c n' d' c',
  optimize_chain_setguarded n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n' <= k -> ~ In (setname k) (map fst (sd_sets d'))).
Proof.
  intros n d c n' d' c' H Hfresh k Hk Hin.
  pose proof (optimize_chain_setguarded_mono n d c n' d' c' H) as Hmono.
  destruct (optimize_chain_setguarded_keys_bound n d c n' d' c' k H Hin) as [Hin_d | Hlt].
  - apply (Hfresh k); [lia | exact Hin_d].
  - lia.
Qed.

(** *** intervalset chain-level wrappers. *)
Lemma optimize_chain_intervalset_correct_uncond : forall n d c n' d' c' base p,
  optimize_chain_intervalset n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) (c_rules c) ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c  (env_with_sets base d) p.
Proof.
  intros n d c n' d' c' base p H Hfs Hrf. unfold optimize_chain_intervalset in H.
  destruct (optimize_rules_intervalset (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_intervalset_correct_uncond (Datatypes.length (c_rules c)) (c_rules c) n d
             m'' dd'' rr'' base p E Hfs Hrf). reflexivity.
Qed.

Lemma optimize_chain_intervalset_output_vmap_fresh : forall n d c n' d' c',
  optimize_chain_intervalset n d c = (n', d', c') ->
  Forall (rule_vmap_fresh n) (c_rules c) -> Forall (rule_vmap_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_intervalset in H.
  destruct (optimize_rules_intervalset (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_intervalset_output_vmap_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_intervalset_fresh_setname : forall n d c n' d' c',
  optimize_chain_intervalset n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n' <= k -> ~ In (setname k) (map fst (sd_sets d'))).
Proof.
  intros n d c n' d' c' H Hfresh k Hk Hin.
  pose proof (optimize_chain_intervalset_mono n d c n' d' c' H) as Hmono.
  destruct (optimize_chain_intervalset_keys_bound n d c n' d' c' k H Hin) as [Hin_d | Hlt].
  - apply (Hfresh k); [lia | exact Hin_d].
  - lia.
Qed.

Lemma optimize_chain_intervalset_output_set_fresh : forall n d c n' d' c',
  optimize_chain_intervalset n d c = (n', d', c') ->
  Forall (rule_set_fresh n) (c_rules c) -> Forall (rule_set_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_intervalset in H.
  destruct (optimize_rules_intervalset (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_intervalset_output_set_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

(** *** dscp chain-level wrappers (masked-payload value->set pass). *)
Lemma optimize_chain_dscp_correct_uncond : forall n d c n' d' c' base p,
  optimize_chain_dscp n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) (c_rules c) ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c  (env_with_sets base d) p.
Proof.
  intros n d c n' d' c' base p H Hfs Hrf. unfold optimize_chain_dscp in H.
  destruct (optimize_rules_dscp (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_dscp_correct_uncond (Datatypes.length (c_rules c)) (c_rules c) n d
             m'' dd'' rr'' base p E Hfs Hrf). reflexivity.
Qed.

Lemma optimize_chain_dscp_output_vmap_fresh : forall n d c n' d' c',
  optimize_chain_dscp n d c = (n', d', c') ->
  Forall (rule_vmap_fresh n) (c_rules c) -> Forall (rule_vmap_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_dscp in H.
  destruct (optimize_rules_dscp (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_dscp_output_vmap_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_dscp_fresh_setname : forall n d c n' d' c',
  optimize_chain_dscp n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n' <= k -> ~ In (setname k) (map fst (sd_sets d'))).
Proof.
  intros n d c n' d' c' H Hfresh k Hk Hin.
  pose proof (optimize_chain_dscp_mono n d c n' d' c' H) as Hmono.
  destruct (optimize_chain_dscp_keys_bound n d c n' d' c' k H Hin) as [Hin_d | Hlt].
  - apply (Hfresh k); [lia | exact Hin_d].
  - lia.
Qed.

Lemma optimize_chain_dscp_output_set_fresh : forall n d c n' d' c',
  optimize_chain_dscp n d c = (n', d', c') ->
  Forall (rule_set_fresh n) (c_rules c) -> Forall (rule_set_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_dscp in H.
  destruct (optimize_rules_dscp (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_dscp_output_set_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

(** *** intervalsethostorder chain-level wrappers (host-order interval-set pass). *)
Lemma optimize_chain_intervalsethostorder_correct_uncond : forall n d c n' d' c' base p,
  optimize_chain_intervalsethostorder n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) (c_rules c) ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c  (env_with_sets base d) p.
Proof.
  intros n d c n' d' c' base p H Hfs Hrf. unfold optimize_chain_intervalsethostorder in H.
  destruct (optimize_rules_intervalsethostorder (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_intervalsethostorder_correct_uncond (Datatypes.length (c_rules c)) (c_rules c) n d
             m'' dd'' rr'' base p E Hfs Hrf). reflexivity.
Qed.

Lemma optimize_chain_intervalsethostorder_output_vmap_fresh : forall n d c n' d' c',
  optimize_chain_intervalsethostorder n d c = (n', d', c') ->
  Forall (rule_vmap_fresh n) (c_rules c) -> Forall (rule_vmap_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_intervalsethostorder in H.
  destruct (optimize_rules_intervalsethostorder (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_intervalsethostorder_output_vmap_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_intervalsethostorder_fresh_setname : forall n d c n' d' c',
  optimize_chain_intervalsethostorder n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n' <= k -> ~ In (setname k) (map fst (sd_sets d'))).
Proof.
  intros n d c n' d' c' H Hfresh k Hk Hin.
  pose proof (optimize_chain_intervalsethostorder_mono n d c n' d' c' H) as Hmono.
  destruct (optimize_chain_intervalsethostorder_keys_bound n d c n' d' c' k H Hin) as [Hin_d | Hlt].
  - apply (Hfresh k); [lia | exact Hin_d].
  - lia.
Qed.

Lemma optimize_chain_intervalsethostorder_output_set_fresh : forall n d c n' d' c',
  optimize_chain_intervalsethostorder n d c = (n', d', c') ->
  Forall (rule_set_fresh n) (c_rules c) -> Forall (rule_set_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_intervalsethostorder in H.
  destruct (optimize_rules_intervalsethostorder (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_intervalsethostorder_output_set_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

(** *** intervalsetguarded chain-level wrappers (guarded interval-set pass). *)
Lemma optimize_chain_intervalsetguarded_correct_uncond : forall n d c n' d' c' base p,
  optimize_chain_intervalsetguarded n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) (c_rules c) ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c  (env_with_sets base d) p.
Proof.
  intros n d c n' d' c' base p H Hfs Hrf. unfold optimize_chain_intervalsetguarded in H.
  destruct (optimize_rules_intervalsetguarded (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_intervalsetguarded_correct_uncond (Datatypes.length (c_rules c)) (c_rules c) n d
             m'' dd'' rr'' base p E Hfs Hrf). reflexivity.
Qed.

Lemma optimize_chain_intervalsetguarded_output_set_fresh : forall n d c n' d' c',
  optimize_chain_intervalsetguarded n d c = (n', d', c') ->
  Forall (rule_set_fresh n) (c_rules c) -> Forall (rule_set_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_intervalsetguarded in H.
  destruct (optimize_rules_intervalsetguarded (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_intervalsetguarded_output_set_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_intervalsetguarded_output_vmap_fresh : forall n d c n' d' c',
  optimize_chain_intervalsetguarded n d c = (n', d', c') ->
  Forall (rule_vmap_fresh n) (c_rules c) -> Forall (rule_vmap_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_intervalsetguarded in H.
  destruct (optimize_rules_intervalsetguarded (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_intervalsetguarded_output_vmap_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_intervalsetguarded_fresh_setname : forall n d c n' d' c',
  optimize_chain_intervalsetguarded n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n' <= k -> ~ In (setname k) (map fst (sd_sets d'))).
Proof.
  intros n d c n' d' c' H Hfresh k Hk Hin.
  pose proof (optimize_chain_intervalsetguarded_mono n d c n' d' c' H) as Hmono.
  destruct (optimize_chain_intervalsetguarded_keys_bound n d c n' d' c' k H Hin) as [Hin_d | Hlt].
  - apply (Hfresh k); [lia | exact Hin_d].
  - lia.
Qed.

(** *** mixedpointrangeguarded chain-level wrappers (guarded mixed point+range set pass). *)
Lemma optimize_chain_mixedpointrangeguarded_correct_uncond : forall n d c n' d' c' base p,
  optimize_chain_mixedpointrangeguarded n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) (c_rules c) ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c  (env_with_sets base d) p.
Proof.
  intros n d c n' d' c' base p H Hfs Hrf. unfold optimize_chain_mixedpointrangeguarded in H.
  destruct (optimize_rules_mixedpointrangeguarded (Datatypes.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_mixedpointrangeguarded_correct_uncond (Datatypes.length (c_rules c)) (c_rules c) n d
             m'' dd'' rr'' base p E Hfs Hrf). reflexivity.
Qed.

Lemma optimize_chain_mixedpointrangeguarded_output_set_fresh : forall n d c n' d' c',
  optimize_chain_mixedpointrangeguarded n d c = (n', d', c') ->
  Forall (rule_set_fresh n) (c_rules c) -> Forall (rule_set_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_mixedpointrangeguarded in H.
  destruct (optimize_rules_mixedpointrangeguarded (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_mixedpointrangeguarded_output_set_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_mixedpointrangeguarded_output_vmap_fresh : forall n d c n' d' c',
  optimize_chain_mixedpointrangeguarded n d c = (n', d', c') ->
  Forall (rule_vmap_fresh n) (c_rules c) -> Forall (rule_vmap_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_mixedpointrangeguarded in H.
  destruct (optimize_rules_mixedpointrangeguarded (Datatypes.length (c_rules c)) n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_mixedpointrangeguarded_output_vmap_fresh _ _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_mixedpointrangeguarded_fresh_setname : forall n d c n' d' c',
  optimize_chain_mixedpointrangeguarded n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n' <= k -> ~ In (setname k) (map fst (sd_sets d'))).
Proof.
  intros n d c n' d' c' H Hfresh k Hk Hin.
  pose proof (optimize_chain_mixedpointrangeguarded_mono n d c n' d' c' H) as Hmono.
  destruct (optimize_chain_mixedpointrangeguarded_keys_bound n d c n' d' c' k H Hin) as [Hin_d | Hlt].
  - apply (Hfresh k); [lia | exact Hin_d].
  - lia.
Qed.

(** [kmatches] (the K head matches) contribute NO set names (all are [MCmp]). *)
Lemma body_set_names_kmatches : forall fields row body,
  body_set_names (kmatches fields row ++ body) = body_set_names body.
Proof.
  intros fields row body. unfold kmatches.
  induction (combine fields row) as [|[f a] l IH]; [reflexivity|].
  cbn [map app]. rewrite (body_set_names_cons_mcmp f a). exact IH.
Qed.

(** concatmulti propagates [rule_set_fresh] (its own [setname] namespace). *)
Lemma optimize_rules_concatmulti_output_set_fresh : forall rs n d n' d' rs',
  optimize_rules_concatmulti n d rs = (n', d', rs') ->
  Forall (rule_set_fresh n) rs ->
  Forall (rule_set_fresh n') rs'.
Proof.
  induction rs as [rs IHrs] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H Hrf.
  destruct rs as [| r1 [| r2 rest] ].
  - cbn in H. inversion H; subst; exact Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - rewrite optimize_rules_concatmulti_cons2 in H.
    inversion Hrf as [| ? ? Hf1 Hrf2]; subst.
    inversion Hrf2 as [| ? ? Hf2 Hrf_rest]; subst.
    destruct (concat_mergeK_pair r1 r2) as [[[[fields row1] row2] body] |] eqn:Em.
    + cbv zeta in H.
      destruct (concat_mergeK_pair_shape r1 r2 fields row1 row2 body Em) as [Hr1eq _].
      remember (optimize_rules_concatmulti (S n)
                  {| sd_sets := (setname n, map pack_row [row1; row2]) :: sd_sets d;
                     sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest) as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. injection H as Hn' Hd' Hr'. subst n' d' rs'.
      assert (Hmono : S n <= m'')
        by (apply (optimize_rules_concatmulti_mono rest (S n) _ m'' dd'' rr'' (eq_sym Erec))).
      assert (Hrf_rest' : Forall (rule_set_fresh (S n)) rest).
      { eapply Forall_impl;
          [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia|exact Hr]|exact Hrf_rest]. }
      assert (Hb : r_body r1 = kmatches fields row1 ++ body) by (rewrite Hr1eq at 1; reflexivity).
      constructor.
      * intros k Hk Hin. unfold merged_ruleK in Hin.
        rewrite (body_set_names_mk_head_MConcat fields (setname n) body r1) in Hin.
        destruct Hin as [Heq | Hin].
        -- apply setname_inj in Heq. lia.
        -- apply (Hf1 k); [lia|]. rewrite Hb, body_set_names_kmatches. exact Hin.
      * apply (IHrs rest ltac:(unfold ltof; cbn; lia) (S n) _ m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
    + remember (optimize_rules_concatmulti n d (r2 :: rest)) as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'. subst n' d' rs'.
      assert (Hmono : n <= m'')
        by (apply (optimize_rules_concatmulti_mono (r2 :: rest) n d m'' dd'' rr'' (eq_sym Erec))).
      constructor;
        [apply (rule_set_fresh_mono n m'' r1 Hmono Hf1)
        |apply (IHrs (r2 :: rest) ltac:(unfold ltof; cbn; lia) n d m'' dd'' rr'' (eq_sym Erec));
           constructor; assumption].
Qed.

(** concatmulti propagates [rule_vmap_fresh] (it adds NO vmap name; merged keeps r1's). *)
Lemma optimize_rules_concatmulti_output_vmap_fresh : forall rs n d n' d' rs',
  optimize_rules_concatmulti n d rs = (n', d', rs') ->
  Forall (rule_vmap_fresh n) rs ->
  Forall (rule_vmap_fresh n') rs'.
Proof.
  induction rs as [rs IHrs] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H Hrf.
  destruct rs as [| r1 [| r2 rest] ].
  - cbn in H. inversion H; subst; exact Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - rewrite optimize_rules_concatmulti_cons2 in H.
    inversion Hrf as [| ? ? Hf1 Hrf2]; subst.
    inversion Hrf2 as [| ? ? Hf2 Hrf_rest]; subst.
    destruct (concat_mergeK_pair r1 r2) as [[[[fields row1] row2] body] |] eqn:Em.
    + cbv zeta in H.
      remember (optimize_rules_concatmulti (S n)
                  {| sd_sets := (setname n, map pack_row [row1; row2]) :: sd_sets d;
                     sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest) as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. injection H as Hn' Hd' Hr'. subst n' d' rs'.
      assert (Hmono : S n <= m'')
        by (apply (optimize_rules_concatmulti_mono rest (S n) _ m'' dd'' rr'' (eq_sym Erec))).
      assert (Hrf_rest' : Forall (rule_vmap_fresh (S n)) rest).
      { eapply Forall_impl;
          [intros r Hr; apply (rule_vmap_fresh_mono n (S n) r); [lia|exact Hr]|exact Hrf_rest]. }
      constructor.
      * intros k Hk Hin. unfold merged_ruleK in Hin.
        rewrite (rule_vmap_name_mk_head (MConcatSet fields false (setname n)) body r1) in Hin.
        apply (Hf1 k); [lia|exact Hin].
      * apply (IHrs rest ltac:(unfold ltof; cbn; lia) (S n) _ m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
    + remember (optimize_rules_concatmulti n d (r2 :: rest)) as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'. subst n' d' rs'.
      assert (Hmono : n <= m'')
        by (apply (optimize_rules_concatmulti_mono (r2 :: rest) n d m'' dd'' rr'' (eq_sym Erec))).
      constructor;
        [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
        |apply (IHrs (r2 :: rest) ltac:(unfold ltof; cbn; lia) n d m'' dd'' rr'' (eq_sym Erec));
           constructor; assumption].
Qed.

Lemma optimize_rules_concatmulti_output_nat_map_fresh : forall rs n d n' d' rs',
  optimize_rules_concatmulti n d rs = (n', d', rs') ->
  Forall (rule_nat_map_fresh n) rs ->
  Forall (rule_nat_map_fresh n') rs'.
Proof.
  induction rs as [rs IHrs] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H Hrf.
  destruct rs as [| r1 [| r2 rest] ].
  - cbn in H. inversion H; subst; exact Hrf.
  - cbn in H. inversion H; subst; exact Hrf.
  - rewrite optimize_rules_concatmulti_cons2 in H.
    inversion Hrf as [| ? ? Hf1 Hrf2]; subst.
    inversion Hrf2 as [| ? ? Hf2 Hrf_rest]; subst.
    destruct (concat_mergeK_pair r1 r2) as [[[[fields row1] row2] body] |] eqn:Em.
    + cbv zeta in H.
      remember (optimize_rules_concatmulti (S n)
                  {| sd_sets := (setname n, map pack_row [row1; row2]) :: sd_sets d;
                     sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest) as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. injection H as Hn' Hd' Hr'. subst n' d' rs'.
      assert (Hmono : S n <= m'')
        by (apply (optimize_rules_concatmulti_mono rest (S n) _ m'' dd'' rr'' (eq_sym Erec))).
      assert (Hrf_rest' : Forall (rule_nat_map_fresh (S n)) rest).
      { eapply Forall_impl;
          [intros r Hr; apply (rule_nat_map_fresh_mono n (S n) r); [lia|exact Hr]|exact Hrf_rest]. }
      constructor.
      * intros k Hk Hin. unfold merged_ruleK in Hin.
        rewrite (rule_nat_map_name_mk_head (MConcatSet fields false (setname n)) body r1) in Hin.
        apply (Hf1 k); [lia|exact Hin].
      * apply (IHrs rest ltac:(unfold ltof; cbn; lia) (S n) _ m'' dd'' rr'' (eq_sym Erec) Hrf_rest').
    + remember (optimize_rules_concatmulti n d (r2 :: rest)) as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'. subst n' d' rs'.
      assert (Hmono : n <= m'')
        by (apply (optimize_rules_concatmulti_mono (r2 :: rest) n d m'' dd'' rr'' (eq_sym Erec))).
      constructor;
        [apply (rule_nat_map_fresh_mono n m'' r1 Hmono Hf1)
        |apply (IHrs (r2 :: rest) ltac:(unfold ltof; cbn; lia) n d m'' dd'' rr'' (eq_sym Erec));
           constructor; assumption].
Qed.

(** *** Chain-level wrappers for concatmulti. *)
Lemma optimize_chain_concatmulti_correct_uncond : forall n d c n' d' c' base p,
  optimize_chain_concatmulti n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) (c_rules c) ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c  (env_with_sets base d) p.
Proof.
  intros n d c n' d' c' base p H Hfs Hrf. unfold optimize_chain_concatmulti in H.
  destruct (optimize_rules_concatmulti n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_concatmulti_correct_uncond (c_rules c) n d m'' dd'' rr'' base p E Hfs Hrf).
  reflexivity.
Qed.

Lemma optimize_chain_concatmulti_output_set_fresh : forall n d c n' d' c',
  optimize_chain_concatmulti n d c = (n', d', c') ->
  Forall (rule_set_fresh n) (c_rules c) -> Forall (rule_set_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_concatmulti in H.
  destruct (optimize_rules_concatmulti n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_concatmulti_output_set_fresh _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_concatmulti_output_vmap_fresh : forall n d c n' d' c',
  optimize_chain_concatmulti n d c = (n', d', c') ->
  Forall (rule_vmap_fresh n) (c_rules c) -> Forall (rule_vmap_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_concatmulti in H.
  destruct (optimize_rules_concatmulti n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_concatmulti_output_vmap_fresh _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_concatmulti_output_nat_map_fresh : forall n d c n' d' c',
  optimize_chain_concatmulti n d c = (n', d', c') ->
  Forall (rule_nat_map_fresh n) (c_rules c) -> Forall (rule_nat_map_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_concatmulti in H.
  destruct (optimize_rules_concatmulti n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_concatmulti_output_nat_map_fresh _ _ _ _ _ _ E Hrf).
Qed.

Lemma optimize_chain_concatmulti_fresh_setname : forall n d c n' d' c',
  optimize_chain_concatmulti n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n' <= k -> ~ In (setname k) (map fst (sd_sets d'))).
Proof.
  intros n d c n' d' c' H Hfresh k Hk Hin.
  pose proof (optimize_chain_concatmulti_mono n d c n' d' c' H) as Hmono.
  destruct (optimize_chain_concatmulti_keys_bound n d c n' d' c' k H Hin) as [Hin_d | Hlt].
  - apply (Hfresh k); [lia | exact Hin_d].
  - lia.
Qed.


(* ================================================================== *)
(** *** mapN stage (the data-value-map merge, Optimize_DataMap).  Its VERDICT effect is
    ENV-INDEPENDENT (the merged Continue rules fall through for any env), so the
    chain correctness is the env-indep [optimize_rules_datamap_eval] composed with the
    standard set-seam env-stability for the passed-through rules. *)

(** The merged map rule reads exactly one set name ([setname n], its head guard);
    its body statement (a `meta set … map`) contributes NO set name. *)
Lemma body_set_names_mk_map_rule : forall f setname mapname k,
  body_set_names (r_body (mk_map_rule f setname mapname k)) = [setname].
Proof. reflexivity. Qed.

Lemma rule_vmap_name_mk_map_rule : forall f setname mapname k,
  rule_vmap_name (mk_map_rule f setname mapname k) = [].
Proof. reflexivity. Qed.

Lemma optimize_rules_datamap_output_set_fresh : forall rs n d n' d' rs',
  optimize_rules_datamap n d rs = (n', d', rs') ->
  Forall (rule_set_fresh n) rs -> Forall (rule_set_fresh n') rs'.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H Hrf. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; exact Hrf.
  - cbn in H; inversion H; subst; exact Hrf.
  - rewrite optimize_rules_datamap_cons2 in H.
    inversion Hrf as [| ? ? Hf1 Hrf2]; subst.
    inversion Hrf2 as [| ? ? Hf2 Hrf_rest]; subst.
    destruct (map_merge_pair r1 r2) as [[[[[[f v1] v2] M1] M2] k]|]; cbv zeta in H.
    + remember (optimize_rules_datamap (S n)
                  {| sd_sets := (setname n, map2_set v1 v2) :: sd_sets d;
                     sd_vmaps := sd_vmaps d;
                     sd_maps := (mapname n, map2_map v1 v2 M1 M2) :: sd_maps d |} rest)
        as t eqn:E.
      destruct t as [[m'' dd''] rr'']. injection H as Hn Hd Hr; subst n' d' rs'.
      pose proof (optimize_rules_datamap_mono rest (S n) _ _ _ _ (eq_sym E)) as Hmono.
      constructor.
      * intros j Hj Hin. rewrite body_set_names_mk_map_rule in Hin.
        destruct Hin as [Heq|[]]. apply setname_inj in Heq. lia.
      * apply (IH rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E)).
        eapply Forall_impl; [intros r Hr; apply (rule_set_fresh_mono n (S n) r); [lia|exact Hr]
                            |exact Hrf_rest].
    + remember (optimize_rules_datamap n d (r2 :: rest)) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. injection H as Hn Hd Hr; subst n' d' rs'.
      pose proof (optimize_rules_datamap_mono (r2 :: rest) n d _ _ _ (eq_sym E)) as Hmono.
      constructor;
        [apply (rule_set_fresh_mono n m'' r1 Hmono Hf1)
        |apply (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E));
           constructor; assumption].
Qed.

Lemma optimize_rules_datamap_output_vmap_fresh : forall rs n d n' d' rs',
  optimize_rules_datamap n d rs = (n', d', rs') ->
  Forall (rule_vmap_fresh n) rs -> Forall (rule_vmap_fresh n') rs'.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H Hrf. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; exact Hrf.
  - cbn in H; inversion H; subst; exact Hrf.
  - rewrite optimize_rules_datamap_cons2 in H.
    inversion Hrf as [| ? ? Hf1 Hrf2]; subst.
    inversion Hrf2 as [| ? ? Hf2 Hrf_rest]; subst.
    destruct (map_merge_pair r1 r2) as [[[[[[f v1] v2] M1] M2] k]|]; cbv zeta in H.
    + remember (optimize_rules_datamap (S n)
                  {| sd_sets := (setname n, map2_set v1 v2) :: sd_sets d;
                     sd_vmaps := sd_vmaps d;
                     sd_maps := (mapname n, map2_map v1 v2 M1 M2) :: sd_maps d |} rest)
        as t eqn:E.
      destruct t as [[m'' dd''] rr'']. injection H as Hn Hd Hr; subst n' d' rs'.
      pose proof (optimize_rules_datamap_mono rest (S n) _ _ _ _ (eq_sym E)) as Hmono.
      constructor.
      * intros j Hj Hin. rewrite rule_vmap_name_mk_map_rule in Hin. destruct Hin.
      * apply (IH rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E)).
        eapply Forall_impl; [intros r Hr; apply (rule_vmap_fresh_mono n (S n) r); [lia|exact Hr]
                            |exact Hrf_rest].
    + remember (optimize_rules_datamap n d (r2 :: rest)) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. injection H as Hn Hd Hr; subst n' d' rs'.
      pose proof (optimize_rules_datamap_mono (r2 :: rest) n d _ _ _ (eq_sym E)) as Hmono.
      constructor;
        [apply (rule_vmap_fresh_mono n m'' r1 Hmono Hf1)
        |apply (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E));
           constructor; assumption].
Qed.

(** Chain-level wrappers. *)
Lemma optimize_chain_datamap_correct_uncond : forall n d c n' d' c' base p,
  optimize_chain_datamap n d c = (n', d', c') ->
  Forall (rule_set_fresh n) (c_rules c) ->
  Forall (rule_nat_map_fresh n) (c_rules c) ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c  (env_with_sets base d) p.
Proof.
  intros n d c n' d' c' base p H Hrf Hrfm. unfold optimize_chain_datamap in H.
  destruct (optimize_rules_datamap n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'. unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_datamap_eval (c_rules c) n d m'' dd'' rr''
             (env_with_sets base dd'') p E).
  erewrite (eval_rules_agree_gen (c_rules c) p base dd'' d); [reflexivity|].
  intros r Hr. apply (decls_agree_rule_mapseam base d dd'' r n).
  - apply (optimize_rules_datamap_vmaps (c_rules c) n d m'' dd'' rr'' E).
  - intros nm X Hf. apply (optimize_rules_datamap_assoc_stable (c_rules c) n d m'' dd'' rr'' nm X E Hf).
  - intros nm X Hf. apply (optimize_rules_datamap_maps_assoc_stable (c_rules c) n d m'' dd'' rr'' nm X E Hf).
  - rewrite Forall_forall in Hrf. apply Hrf; exact Hr.
  - rewrite Forall_forall in Hrfm. apply Hrfm; exact Hr.
Qed.

Lemma optimize_chain_datamap_output_set_fresh : forall n d c n' d' c',
  optimize_chain_datamap n d c = (n', d', c') ->
  Forall (rule_set_fresh n) (c_rules c) -> Forall (rule_set_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_datamap in H.
  destruct (optimize_rules_datamap n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_datamap_output_set_fresh _ _ _ _ _ _ E Hrf).
Qed.
Lemma optimize_chain_datamap_output_vmap_fresh : forall n d c n' d' c',
  optimize_chain_datamap n d c = (n', d', c') ->
  Forall (rule_vmap_fresh n) (c_rules c) -> Forall (rule_vmap_fresh n') (c_rules c').
Proof.
  intros n d c n' d' c' H Hrf. unfold optimize_chain_datamap in H.
  destruct (optimize_rules_datamap n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. cbn [c_rules].
  apply (optimize_rules_datamap_output_vmap_fresh _ _ _ _ _ _ E Hrf).
Qed.
Lemma optimize_chain_datamap_fresh_setname : forall n d c n' d' c',
  optimize_chain_datamap n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n' <= k -> ~ In (setname k) (map fst (sd_sets d'))).
Proof.
  intros n d c n' d' c' H Hfresh k Hk Hin.
  pose proof (optimize_chain_datamap_mono n d c n' d' c' H) as Hmono.
  destruct (optimize_chain_datamap_keys_bound n d c n' d' c' k H Hin) as [Hin_d | Hlt].
  - apply (Hfresh k); [lia | exact Hin_d].
  - lia.
Qed.

(** *** ctmask-stage freshness transfer: a merged bitmask-union rule reads exactly
    its base rule's names, so all three fresh-name predicates survive the pass. *)
Lemma ctmask_chain_set_fresh : forall n c,
  Forall (rule_set_fresh n) (c_rules c) ->
  Forall (rule_set_fresh n) (c_rules (ctmask_chain c)).
Proof.
  intros n c HF. unfold ctmask_chain. cbn [c_rules].
  apply optimize_rules_ctmask_Forall; [| exact HF].
  intros r1 r2 f m1 m2 z body Hp HP1. unfold rule_set_fresh in *.
  intros k Hk. rewrite (ctmask_merged_body_set_names r1 r2 f m1 m2 z body Hp).
  apply HP1. exact Hk.
Qed.

Lemma ctmask_chain_vmap_fresh : forall n c,
  Forall (rule_vmap_fresh n) (c_rules c) ->
  Forall (rule_vmap_fresh n) (c_rules (ctmask_chain c)).
Proof.
  intros n c HF. unfold ctmask_chain. cbn [c_rules].
  apply optimize_rules_ctmask_Forall; [| exact HF].
  intros r1 r2 f m1 m2 z body Hp HP1. unfold rule_vmap_fresh in *.
  intros k Hk. rewrite (ctmask_merged_vmap_name r1 f m1 m2 z body).
  apply HP1. exact Hk.
Qed.

Lemma ctmask_chain_nat_map_fresh : forall n c,
  Forall (rule_nat_map_fresh n) (c_rules c) ->
  Forall (rule_nat_map_fresh n) (c_rules (ctmask_chain c)).
Proof.
  intros n c HF. unfold ctmask_chain. cbn [c_rules].
  apply optimize_rules_ctmask_Forall; [| exact HF].
  intros r1 r2 f m1 m2 z body Hp HP1. unfold rule_nat_map_fresh in *.
  intros k Hk. rewrite (ctmask_merged_nat_map_name r1 f m1 m2 z body).
  apply HP1. exact Hk.
Qed.

(** *** UNCONDITIONAL [optimize_table] correctness (arbitrary [d], with read-freshness
    of the base-optimised chain in BOTH namespaces — NO [rules_clean]). *)
Theorem optimize_table_correct_uncond_gen : forall n d c n' d' c' base p,
  optimize_table n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k)  (map fst (sd_sets  d))) ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  (forall k, n <= k -> ~ In (mapname k)  (map fst (sd_maps  d))) ->
  Forall (rule_set_fresh  n) (c_rules (optimize_chain c)) ->
  Forall (rule_vmap_fresh n) (c_rules (optimize_chain c)) ->
  Forall (rule_nat_map_fresh n) (c_rules (optimize_chain c)) ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c  (env_with_sets base d) p.
Proof.
  intros n d c n' d' c' base p H Hfs Hfv Hfm Hrs Hrv Hrm.
  unfold optimize_table in H.
  (* absorb stage (Optimize_Absorb): counter/decls pass through UNCHANGED
     (nA = n, dA = d); the chain shrinks to [absorb_chain (optimize_chain c)], a
     SUBSET of [optimize_chain c]'s rules, so every rule-level freshness transfers. *)
  destruct (optimize_chain_absorb n d (optimize_chain c)) as [[nA dA] cA] eqn:EA.
  pose proof (optimize_chain_absorb_eq n d (optimize_chain c)) as Habs.
  rewrite EA in Habs. injection Habs as HnA HdA HcA. subst nA dA.
  assert (Hrs_A : Forall (rule_set_fresh n) (c_rules cA))
    by (rewrite HcA; apply absorb_chain_Forall; exact Hrs).
  assert (Hrv_A : Forall (rule_vmap_fresh n) (c_rules cA))
    by (rewrite HcA; apply absorb_chain_Forall; exact Hrv).
  assert (Hrm_A : Forall (rule_nat_map_fresh n) (c_rules cA))
    by (rewrite HcA; apply absorb_chain_Forall; exact Hrm).
  (* ctmask stage (Optimize_CtMask): counter/decls pass through UNCHANGED
     (nT = n, dT = d); rules are rewritten (adjacent `ct state`/bitmask-union folds)
     but every merged rule reads EXACTLY its base rule's names, so all three
     rule-level freshness facts transfer. *)
  destruct (optimize_chain_ctmask n d cA) as [[nT dT] cT] eqn:ET.
  pose proof (optimize_chain_ctmask_eq n d cA) as Hct.
  rewrite ET in Hct. injection Hct as HnT HdT HcT. subst nT dT.
  assert (Hrs_T : Forall (rule_set_fresh n) (c_rules cT))
    by (rewrite HcT; apply ctmask_chain_set_fresh; exact Hrs_A).
  assert (Hrv_T : Forall (rule_vmap_fresh n) (c_rules cT))
    by (rewrite HcT; apply ctmask_chain_vmap_fresh; exact Hrv_A).
  assert (Hrm_T : Forall (rule_nat_map_fresh n) (c_rules cT))
    by (rewrite HcT; apply ctmask_chain_nat_map_fresh; exact Hrm_A).
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
  (* dnat stage: counter monotone, sd_sets/sd_vmaps preserved, freshness threaded *)
  pose proof (optimize_chain_dnat_mono n d cT nD dD cD ED) as HmnD.
  assert (Hfs_D : forall k, nD <= k -> ~ In (setname k) (map fst (sd_sets dD))).
  { intros k Hk. rewrite (optimize_chain_dnat_sets n d cT nD dD cD ED).
    apply Hfs. lia. }
  assert (Hfv_D : forall k, nD <= k -> ~ In (vmapname k) (map fst (sd_vmaps dD))).
  { intros k Hk. rewrite (optimize_chain_dnat_vmaps n d cT nD dD cD ED).
    apply Hfv. lia. }
  assert (Hfm_D : forall k, nD <= k -> ~ In (mapname k) (map fst (sd_maps dD))).
  { apply (optimize_chain_dnat_fresh_mapname n d cT nD dD cD ED Hfm). }
  pose proof (optimize_chain_dnat_output_set_fresh n d cT nD dD cD ED Hrs_T) as Hrs_D.
  pose proof (optimize_chain_dnat_output_vmap_fresh n d cT nD dD cD ED Hrv_T) as Hrv_D.
  pose proof (optimize_chain_dnat_output_nat_map_fresh n d cT nD dD cD ED Hrm_T) as Hrm_D.
  (* snat stage: structurally identical to dnat (mints [mapname]s on the SOURCE slot),
     threaded on top of the dnat outputs *)
  pose proof (optimize_chain_snat_mono nD dD cD nS dS cS ES) as HmnS.
  assert (Hfs_S : forall k, nS <= k -> ~ In (setname k) (map fst (sd_sets dS))).
  { intros k Hk. rewrite (optimize_chain_snat_sets nD dD cD nS dS cS ES).
    apply Hfs_D. lia. }
  assert (Hfv_S : forall k, nS <= k -> ~ In (vmapname k) (map fst (sd_vmaps dS))).
  { intros k Hk. rewrite (optimize_chain_snat_vmaps nD dD cD nS dS cS ES).
    apply Hfv_D. lia. }
  pose proof (optimize_chain_snat_output_set_fresh nD dD cD nS dS cS ES Hrs_D) as Hrs_S.
  pose proof (optimize_chain_snat_output_vmap_fresh nD dD cD nS dS cS ES Hrv_D) as Hrv_S.
  pose proof (optimize_chain_snat_output_nat_map_fresh nD dD cD nS dS cS ES Hrm_D) as Hrm_S.
  (* counter monotonicity chain nS <= n1 <= nK <= nM <= n2 *)
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
  (* setname-freshness threading through valueset, concatmulti, datamap, concat (all mint setnames) *)
  pose proof (optimize_chain_valueset_fresh_setname nS dS cS n1 d1 c1 E1 Hfs_S) as Hfs1.
  pose proof (optimize_chain_concatmulti_fresh_setname n1 d1 c1 nK dK cK EK Hfs1) as HfsK.
  pose proof (optimize_chain_datamap_fresh_setname nK dK cK nM dM cM EM HfsK) as HfsM.
  pose proof (optimize_chain_concat_fresh_setname nM dM cM n2 d2 c2 E2 HfsM) as Hfs2.
  pose proof (optimize_chain_concatguarded_fresh_setname n2 d2 c2 nG dG cG EG Hfs2) as HfsG.
  pose proof (optimize_chain_setguarded_fresh_setname nG dG cG nGs dGs cGs EGs HfsG) as HfsGs.
  (* sd_vmaps unchanged across valueset, concatmulti, datamap, concat, concatguarded, setguarded, intervalset *)
  assert (HvmG : sd_vmaps dG = sd_vmaps dS).
  { rewrite (optimize_chain_concatguarded_vmaps n2 d2 c2 nG dG cG EG).
    rewrite (optimize_chain_concat_vmaps nM dM cM n2 d2 c2 E2).
    rewrite (optimize_chain_datamap_vmaps nK dK cK nM dM cM EM).
    rewrite (optimize_chain_concatmulti_vmaps n1 d1 c1 nK dK cK EK).
    apply (optimize_chain_valueset_vmaps nS dS cS n1 d1 c1 E1). }
  assert (HvmGs : sd_vmaps dGs = sd_vmaps dS).
  { rewrite (optimize_chain_setguarded_vmaps nG dG cG nGs dGs cGs EGs). exact HvmG. }
  assert (HvmI : sd_vmaps dI = sd_vmaps dS).
  { rewrite (optimize_chain_intervalset_vmaps nGs dGs cGs nI dI cI EI). exact HvmGs. }
  assert (HvmIt : sd_vmaps dIt = sd_vmaps dS).
  { rewrite (optimize_chain_intervalsethostorder_vmaps nI dI cI nIt dIt cIt EIt). exact HvmI. }
  assert (HvmDs : sd_vmaps dDs = sd_vmaps dS).
  { rewrite (optimize_chain_dscp_vmaps nIt dIt cIt nDs dDs cDs EDs). exact HvmIt. }
  assert (HvmIg : sd_vmaps dIg = sd_vmaps dS).
  { rewrite (optimize_chain_intervalsetguarded_vmaps nDs dDs cDs nIg dIg cIg EIg). exact HvmDs. }
  assert (HfvIg : forall k, nIg <= k -> ~ In (vmapname k) (map fst (sd_vmaps dIg))).
  { intros k Hk. rewrite HvmIg. apply Hfv_S. lia. }
  assert (HvmMx : sd_vmaps dMx = sd_vmaps dS).
  { rewrite (optimize_chain_mixedpointrangeguarded_vmaps nIg dIg cIg nMx dMx cMx EMx). exact HvmIg. }
  assert (HfvMx : forall k, nMx <= k -> ~ In (vmapname k) (map fst (sd_vmaps dMx))).
  { intros k Hk. rewrite HvmMx. apply Hfv_S. lia. }
  (* read-freshness threading: valueset -> concatmulti -> datamap -> concat -> concatguarded *)
  pose proof (optimize_chain_valueset_output_set_fresh nS dS cS n1 d1 c1 E1 Hrs_S) as Hrs1.
  pose proof (optimize_chain_valueset_output_vmap_fresh nS dS cS n1 d1 c1 E1 Hrv_S) as Hrv1.
  pose proof (optimize_chain_concatmulti_output_set_fresh n1 d1 c1 nK dK cK EK Hrs1) as HrsK.
  (* nat-map read-freshness threading: snat -> valueset -> concatmulti -> datamap input *)
  pose proof (optimize_chain_valueset_output_nat_map_fresh nS dS cS n1 d1 c1 E1 Hrm_S) as Hrm1.
  pose proof (optimize_chain_concatmulti_output_nat_map_fresh n1 d1 c1 nK dK cK EK Hrm1) as HrmK.
  pose proof (optimize_chain_concatmulti_output_vmap_fresh n1 d1 c1 nK dK cK EK Hrv1) as HrvK.
  pose proof (optimize_chain_datamap_output_set_fresh nK dK cK nM dM cM EM HrsK) as HrsM.
  pose proof (optimize_chain_datamap_output_vmap_fresh nK dK cK nM dM cM EM HrvK) as HrvM.
  pose proof (optimize_chain_concat_output_set_fresh nM dM cM n2 d2 c2 E2 HrsM) as Hrs2.
  pose proof (optimize_chain_concat_output_vmap_fresh nM dM cM n2 d2 c2 E2 HrvM) as Hrv2.
  pose proof (optimize_chain_concatguarded_output_vmap_fresh n2 d2 c2 nG dG cG EG Hrv2) as HrvG.
  pose proof (optimize_chain_concatguarded_output_set_fresh n2 d2 c2 nG dG cG EG Hrs2) as HrsG.
  pose proof (optimize_chain_setguarded_output_vmap_fresh nG dG cG nGs dGs cGs EGs HrvG) as HrvGs.
  pose proof (optimize_chain_setguarded_output_set_fresh nG dG cG nGs dGs cGs EGs HrsG) as HrsGs.
  pose proof (optimize_chain_intervalset_output_vmap_fresh nGs dGs cGs nI dI cI EI HrvGs) as HrvI.
  pose proof (optimize_chain_intervalset_fresh_setname nGs dGs cGs nI dI cI EI HfsGs) as HfsI.
  pose proof (optimize_chain_intervalset_output_set_fresh nGs dGs cGs nI dI cI EI HrsGs) as HrsI.
  (* intervalsethostorder stage (host-order interval->set): mints [setname]s, preserves sd_vmaps,
     threads setname-decl-freshness + rule_set/vmap-freshness into dscp. *)
  pose proof (optimize_chain_intervalsethostorder_output_vmap_fresh nI dI cI nIt dIt cIt EIt HrvI) as HrvIt.
  pose proof (optimize_chain_intervalsethostorder_fresh_setname nI dI cI nIt dIt cIt EIt HfsI) as HfsIt.
  pose proof (optimize_chain_intervalsethostorder_output_set_fresh nI dI cI nIt dIt cIt EIt HrsI) as HrsIt.
  (* dscp stage (masked-payload value->set): mints [setname]s, preserves sd_vmaps,
     threads setname-decl-freshness + rule_set/vmap-freshness into intervalsetguarded. *)
  pose proof (optimize_chain_dscp_output_vmap_fresh nIt dIt cIt nDs dDs cDs EDs HrvIt) as HrvDs.
  pose proof (optimize_chain_dscp_fresh_setname nIt dIt cIt nDs dDs cDs EDs HfsIt) as HfsDs.
  pose proof (optimize_chain_dscp_output_set_fresh nIt dIt cIt nDs dDs cDs EDs HrsIt) as HrsDs.
  pose proof (optimize_chain_intervalsetguarded_output_vmap_fresh nDs dDs cDs nIg dIg cIg EIg HrvDs) as HrvIg.
  (* intervalsetguarded setname-decl-freshness + rule_set_fresh, threaded into the mixedpointrangeguarded stage. *)
  pose proof (optimize_chain_intervalsetguarded_fresh_setname nDs dDs cDs nIg dIg cIg EIg HfsDs) as HfsIg.
  pose proof (optimize_chain_intervalsetguarded_output_set_fresh nDs dDs cDs nIg dIg cIg EIg HrsDs) as HrsIg.
  pose proof (optimize_chain_mixedpointrangeguarded_output_vmap_fresh nIg dIg cIg nMx dMx cMx EMx HrvIg) as HrvMx.
  (* vmapguarded stage (guarded value+verdict->vmap): mints [vmapname]s onto sd_vmaps,
     threads vmapname-decl-freshness and rule_vmap_fresh into the final vmap stage. *)
  pose proof (optimize_chain_vmapguarded_fresh_vmapname nMx dMx cMx nVg dVg cVg EVg HfvMx) as HfvVg.
  pose proof (optimize_chain_vmapguarded_output_vmap_fresh nMx dMx cMx nVg dVg cVg EVg HrvMx) as HrvVg.
  (* dscpvmap stage (masked value+verdict->vmap, Optimize_DscpVmap): mints [vmapname]s onto sd_vmaps,
     threads vmapname-decl-freshness and rule_vmap_fresh into the final vmap stage. *)
  pose proof (optimize_chain_dscpvmap_fresh_vmapname nVg dVg cVg nDv dDv cDv EDv HfvVg) as HfvDv.
  pose proof (optimize_chain_dscpvmap_output_vmap_fresh nVg dVg cVg nDv dDv cDv EDv HrvVg) as HrvDv.
  rewrite (optimize_chain_vmap_correct_uncond nDv dDv cDv n' d' c' base p H HfvDv HrvDv).
  rewrite (optimize_chain_dscpvmap_correct_uncond nVg dVg cVg nDv dDv cDv base p EDv HfvVg HrvVg).
  rewrite (optimize_chain_vmapguarded_correct_uncond nMx dMx cMx nVg dVg cVg base p EVg HfvMx HrvMx).
  rewrite (optimize_chain_mixedpointrangeguarded_correct_uncond nIg dIg cIg nMx dMx cMx base p EMx HfsIg HrsIg).
  rewrite (optimize_chain_intervalsetguarded_correct_uncond nDs dDs cDs nIg dIg cIg base p EIg HfsDs HrsDs).
  rewrite (optimize_chain_dscp_correct_uncond nIt dIt cIt nDs dDs cDs base p EDs HfsIt HrsIt).
  rewrite (optimize_chain_intervalsethostorder_correct_uncond nI dI cI nIt dIt cIt base p EIt HfsI HrsI).
  rewrite (optimize_chain_intervalset_correct_uncond nGs dGs cGs nI dI cI base p EI HfsGs HrsGs).
  rewrite (optimize_chain_setguarded_correct_uncond nG dG cG nGs dGs cGs base p EGs HfsG HrsG).
  rewrite (optimize_chain_concatguarded_correct_uncond n2 d2 c2 nG dG cG base p EG Hfs2 Hrs2).
  rewrite (optimize_chain_concat_correct_uncond nM dM cM n2 d2 c2 base p E2 HfsM HrsM).
  rewrite (optimize_chain_datamap_correct_uncond nK dK cK nM dM cM base p EM HrsK HrmK).
  rewrite (optimize_chain_concatmulti_correct_uncond n1 d1 c1 nK dK cK base p EK Hfs1 Hrs1).
  rewrite (optimize_chain_valueset_correct_uncond nS dS cS n1 d1 c1 base p E1 Hfs_S Hrs_S).
  rewrite (optimize_chain_snat_eval nD dD cD nS dS cS base p ES Hfm_D Hrm_D).
  rewrite (optimize_chain_dnat_eval n d cT nD dD cD base p ED Hfm Hrm_T).
  rewrite HcT, ctmask_chain_eval, HcA, absorb_chain_eval. apply optimize_chain_correct.
Qed.

(** *** The fresh-counter seed: choose the start counter STRICTLY above the length
    of every name the base-optimised chain reads, so minted names avoid the seed. *)
Definition chain_seed (c : chain) : list string :=
  flat_map (fun r => body_set_names (r_body r) ++ rule_vmap_name r ++ rule_nat_map_name r)
           (c_rules c).

Definition seed_start (c : chain) : nat :=
  S (list_max (map String.length (chain_seed c))).

Lemma chain_seed_set_in : forall c r nm,
  In r (c_rules c) -> In nm (body_set_names (r_body r)) -> In nm (chain_seed c).
Proof.
  intros c r nm Hr Hnm. unfold chain_seed. apply in_flat_map. exists r.
  split; [exact Hr | apply in_or_app; left; exact Hnm].
Qed.

Lemma chain_seed_vmap_in : forall c r nm,
  In r (c_rules c) -> In nm (rule_vmap_name r) -> In nm (chain_seed c).
Proof.
  intros c r nm Hr Hnm. unfold chain_seed. apply in_flat_map. exists r.
  split; [exact Hr | apply in_or_app; right; apply in_or_app; left; exact Hnm].
Qed.

Lemma chain_seed_nat_map_in : forall c r nm,
  In r (c_rules c) -> In nm (rule_nat_map_name r) -> In nm (chain_seed c).
Proof.
  intros c r nm Hr Hnm. unfold chain_seed. apply in_flat_map. exists r.
  split; [exact Hr | apply in_or_app; right; apply in_or_app; right; exact Hnm].
Qed.

Lemma seed_start_set_fresh : forall c, Forall (rule_set_fresh (seed_start c)) (c_rules c).
Proof.
  intro c. apply Forall_forall. intros r Hr k Hk Hin.
  apply (not_in_of_length_gt (setname k) (chain_seed c)).
  - rewrite setname_length. unfold seed_start in Hk. lia.
  - apply (chain_seed_set_in c r (setname k) Hr Hin).
Qed.

Lemma seed_start_vmap_fresh : forall c, Forall (rule_vmap_fresh (seed_start c)) (c_rules c).
Proof.
  intro c. apply Forall_forall. intros r Hr k Hk Hin.
  apply (not_in_of_length_gt (vmapname k) (chain_seed c)).
  - rewrite vmapname_length. unfold seed_start in Hk. lia.
  - apply (chain_seed_vmap_in c r (vmapname k) Hr Hin).
Qed.

Lemma seed_start_nat_map_fresh : forall c, Forall (rule_nat_map_fresh (seed_start c)) (c_rules c).
Proof.
  intro c. apply Forall_forall. intros r Hr k Hk Hin.
  apply (not_in_of_length_gt (mapname k) (chain_seed c)).
  - rewrite mapname_length. unfold seed_start in Hk. lia.
  - apply (chain_seed_nat_map_in c r (mapname k) Hr Hin).
Qed.

(** *** The UNCONDITIONAL entry point: optimise a fresh table starting the
    fresh-name counter at [seed_start] of the base-optimised chain. *)
Definition empty_decls : set_decls := {| sd_sets := []; sd_vmaps := []; sd_maps := [] |}.

(** Run the verdict-preserving head normalisation ([MEq f v -> MCmp f CEq v],
    [Optimize_Normalize]) FIRST, so the merge recognisers ([head_value] etc., which
    match [MCmp _ CEq _]) fire on PARSER output (which lowers `==` to [MEq]).  This
    is what makes the SHIPPED optimizer consolidate real `.nft` rulesets. *)
Definition optimize_table_uncond (c : chain) : nat * set_decls * chain :=
  let c0 := normalize_chain c in
  optimize_table (seed_start (optimize_chain c0)) empty_decls c0.

(** END-TO-END, NO HYPOTHESIS ON [c]: the optimised chain, run against the
    synthesised declarations, has EXACTLY the DSL verdict of the original chain.
    (SUPPORTING form of the optimizer HEADLINE below: DSL-level, per chain.) *)
Theorem optimize_table_uncond_correct : forall c base p n' d' c',
  optimize_table_uncond c = (n', d', c') ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c (env_with_sets base empty_decls) p.
Proof.
  intros c base p n' d' c' H. unfold optimize_table_uncond in H.
  (* the pipeline runs on [normalize_chain c]; relate its verdict back to [c]'s *)
  rewrite <- (normalize_chain_eval c (env_with_sets base empty_decls) p).
  apply (optimize_table_correct_uncond_gen (seed_start (optimize_chain (normalize_chain c)))
           empty_decls (normalize_chain c) n' d' c' base p H).
  - intros k _ Hin; cbn in Hin; exact Hin.
  - intros k _ Hin; cbn in Hin; exact Hin.
  - intros k _ Hin; cbn in Hin; exact Hin.
  - apply seed_start_set_fresh.
  - apply seed_start_vmap_fresh.
  - apply seed_start_nat_map_fresh.
Qed.

(** The final compile step of the shipped `nftc optimize`/`nftc send` path is
    the DEFAULT pipeline [Optimize_Linearize.compile_chain_default] (nft's
    always-on payload-merge + xor-fold linearization, then [compile_chain]) —
    so the composed headline below is stated over THAT pipeline. *)
From Nft Require Optimize_Linearize.

(** HEADLINE (optimizer axis; see proof/THEOREMS.md and theories/Compiler/Main.v) —
    END-TO-END to the BYTECODE: DEFAULT-compile the optimised chain
    (linearize + compile), run the VM against the synthesised declarations —
    EXACTLY the original chain's DSL verdict.

    Scope note 1: PER CHAIN — quantified over a single chain and ALL environments
    and packets; multi-chain/hook preservation is the separate
    [compile_ruleset_correct]/[compile_hook_correct] family (Correct.v), not
    composed with the optimizer.

    Scope note 2: VERDICTS ONLY — this theorem (and every [_correct_uncond]
    stage composed into it) is quantified over [eval_chain], the write-blind,
    NAT-blind, jump-free evaluator.  Pipeline stages DO rewrite write-effectful
    statements — [datamap] folds `meta mark set` runs, [dnat]/[snat] fold NAT
    terminals — and mark/NAT effects are exactly what LATER hooks observe
    (Examples/Optiplex_Mark.v's masquerade is gated on the mark).  The per-stage
    EFFECT certificates that exist —
    [Optimize_DataMap.eval_rules_mut_map_merge] (mut-level verdict+state for
    the datamap merge shape), [Optimize_Dnat.apply_nat_dnat_eq] /
    [Optimize_Snat.apply_nat_snat_eq] (the folded NAT's data-plane effect
    equals the originals') — are PER-MERGE-SHAPE lemmas, NOT composed through
    [optimize_table]: no theorem lifts the 18-stage pipeline to
    the effect-threading [eval_chain_mut].  So, formally, a stage could preserve
    every [eval_chain] verdict while altering a mark write that flips a later
    hook's decision — the effect certificates are evidence the shipped merges
    do not, but the COMPOSED guarantee is verdict-only.  Why not lifted: a
    mut/trace-level pipeline theorem needs mut-level seam lemmas for all 18
    stages PLUS write-safety proofs for the rule-DELETING passes (base-pass
    dce/absorb: deleting a shadowed rule preserves verdicts but not its
    writes/limiter depletion), i.e. a second full composition stack for the
    one write-mutating stage family; future work if the optimizer is ever run
    on mutation-relied-upon chains.  Until then: optimizing a chain whose
    LATER-observed writes matter is outside this theorem's certified scope. *)
Theorem optimize_table_uncond_compile_correct : forall c base p n' d' c',
  optimize_table_uncond c = (n', d', c') ->
  run_chain (Optimize_Linearize.compile_chain_default c') (c_policy c')
            (env_with_sets base d') p
  = eval_chain c (env_with_sets base empty_decls) p.
Proof.
  intros c base p n' d' c' H.
  rewrite (Optimize_Linearize.compile_chain_default_sets_correct c' base d' p).
  exact (optimize_table_uncond_correct c base p n' d' c' H).
Qed.

(** ** Axiom-freedom audit (build-time guard; mirrors Fib_Local.v / Optimize_Table.v).
    The two UNCONDITIONAL headline results — no hypothesis on the input chain.
    Prints "Closed under the global context"; an introduced axiom/admit would
    surface in the build log here. *)
Print Assumptions optimize_table_uncond_correct.
Print Assumptions optimize_table_uncond_compile_correct.
