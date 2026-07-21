(** * Optimize_Uncond: the [nft -o] consolidation term and its
    by-construction freshness infrastructure.

    This file defines the shipped consolidation pipeline
    ([optimize_table_uncond], the term the CLI executes: [normalize_chain]
    then [optimize_table] seeded past every name the input reads) and the
    read-freshness infrastructure its correctness rests on: the length-based
    fresh-counter ([seed_start]/[chain_seed]) and the per-pass
    output-freshness lemmas ([optimize_rules_*_output_set_fresh] etc.).

    The synthesised [setname]/[vmapname]/[mapname] declarations are minted from
    a counter chosen past the LENGTH of every name the input reads, so no
    passed-through rule can read a minted name; a passed-through rule therefore
    evaluates identically with or without the fresh declaration —
    UNCONDITIONALLY, for an ARBITRARY (possibly unclean) input chain.  The
    freshness lemmas below discharge exactly that obligation.

    The consolidation is certified over the state fold in [Optimize_MutEnv]
    (per-pass state preservation) and composed to the bytecode in
    [Optimize_Linearize_MutSt.optimize_table_uncond_compile_mut_st_correct]
    (re-exported as the Main optimizer headline); this file supplies the
    definitions and freshness lemmas those proofs consume.

    Part 1: generalised env-AGREEMENT for an ARBITRARY rule (drop the
            [body_only_matches] restriction of [Optimize_Table_Inv]).
    Part 2: the length-based fresh-counter ([seed_bound]) + its freshness lemmas.
    Part 3: per-pass output-freshness lemmas.
    Part 4: the [optimize_table_uncond] consolidation term. *)

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
  rewrite ?eval_rules_cons, ?eval_rules_nil.
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
  intros r X Y e1 e2 p HL HA HO HXY. rewrite ?eval_rules_cons, ?eval_rules_nil. rewrite HL, HA, HO, HXY. reflexivity.
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

(** *** dscp (masked-payload value->set consolidation, Optimize_Dscp).  Structurally
    identical to [valueset], but the run's heads are masked equalities [MMasked f CEq
    mask xor v] and the merged head is a masked-lookup [MSetT f [TBitAnd mask xor]
    false __setN] over the N point values; [mmasked_set_existsb] is the membership
    certificate (with the [data_bitops] width discharged from the fixed-width side
    condition), and the state-fold run-merge substrate
    [Optimize_MutEnv.eval_rules_mut_st_run_merge_abs] collapses the run (both merged
    and run heads share [match_loadable = field_loadable f]). *)

(** *** intervalsethostorder (host-order interval / range set consolidation, Optimize_IntervalSetHostOrder).
    Structurally identical to [intervalset], but the run's heads are transformed ranges
    [MRangeT f ts false lo hi] and the synthesised set head is [MSetT f ts false __setN]
    — the byteorder transform [ts] is carried IDENTICALLY on both, and the membership
    certificate ([msett_ivs_existsb]) collapses the [MSetT] to the run's [existsb]. *)

(** *** intervalset (interval / range set consolidation, Optimize_IntervalSet).  Structurally a
    single-field set merge like valueset, but the run's heads are [MRange]s and the
    synthesised set carries the intervals directly — NO fixed-width side-condition
    (range membership uses [data_le], which does not truncate). *)

(** An [MRange] head contributes NO set name, so a range-head shell's set names are
    exactly its tail's. *)
Lemma body_set_names_cons_mrange : forall f lo hi body,
  body_set_names (BMatch (MRange f false lo hi) :: body) = body_set_names body.
Proof. reflexivity. Qed.

(** *** intervalsetguarded (GUARDED interval / range set consolidation, Optimize_IntervalSetGuarded).
    Combines the guarded run-collapse of [setguarded] ([existsb_guardhead_factor] factors
    the head l4proto/nfproto guard out of the [existsb]) with the interval membership
    certificate of [intervalset] ([concat_set_ivs_existsb]): a single-field [MConcatSet]
    over an interval set is EXACTLY the [existsb] disjunction of the [MRange] matches.
    No fixed-width side-condition. *)

(** *** mixedpointrangeguarded (GUARDED MIXED point+range set consolidation, Optimize_MixedPointRangeGuarded).
    Structurally identical to [intervalsetguarded]; the only new content is the per-element
    verdict bridge [eval_melem_mrange] (a point head [MCmp f CEq v] equals the
    degenerate-interval [MRange f false v v] match under the field's FIXED-WIDTH
    guard), applied through the interval membership certificate. *)

(** *** concat. *)

(** *** concatguarded (the guarded transport-key concat pass, Optimize_ConcatGuarded).  Mirrors
    [concat] verbatim EXCEPT the merged rule hoists the shared guard [gm] to the head
    (matching nft -o) and each original carries [gm] between its two selectors.  The
    MConcatSet membership certificate ([concat_two_fields_certificate_N]) is REUSED
    unchanged — the guard is factored out of the run-collapse [existsb] by boolean
    algebra ([existsb_guard_factor]). *)

(** *** setguarded (the guarded single-field value->set pass, Optimize_SetGuarded).  Mirrors
    [concatguarded] verbatim EXCEPT the single-field membership certificate is
    [concat_set_existsb] (one field, [map (fun v => (v,v)) vals] elements) and the
    HEAD guard [gm] is factored out of the run-collapse [existsb] by
    [existsb_guardhead_factor]. *)

(** *** concatmulti (the N>=3-field pairwise concat pass, Optimize_ConcatMulti).  Mirrors
    the [concat] correctness but uses [eval_rules_concat_mergeK] (which bundles the
    matchcond certificate + run-collapse) on the two-row merge. *)

(** *** vmap.  The vmap merge is GATED on [body_vmap_safe] (no synproxy/notrack in
    the body), which the merge condition now enforces; that gate is what makes the
    vmap pass SOUND on arbitrary input (the merge is genuinely unsound for a
    [notrack] body, since the merged rule reads its key field at the body-threaded
    packet).  Read-freshness is in the [vmapname] namespace. *)

(** *** vmapguarded.  The GUARDED verdict-map merge (Optimize_VmapGuarded), a verbatim mirror of
    the vmap proof above EXCEPT the recogniser is [head_valueGs] (guard + selector),
    the run collapse is [eval_rules_vmap_mergeNg] (reduced to [eval_rules_vmap_mergeN]
    on body [BMatch gm :: body] via the SWAP equivalence), and the merged rule is
    [merged_ruleGv].  Read-freshness is in the same [vmapname] namespace, so the SAME
    [rule_vmap_fresh] / [decls_agree_rule_vmapseam] machinery applies. *)

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

(** *** The fresh-counter seed: choose the start counter STRICTLY above the length
    of every name the base-optimised chain reads — AND every name it WRITES.

    The dynset WRITE targets ([SDynset]'s set/map name, the one statement
    family that mutates the shared [e_set]/[e_map] environment) are included
    so the EFFECT-level pipeline theorem
    ([Optimize_MutEnv.optimize_table_uncond_mut_st_correct]) gets, by construction,
    that no rule can clobber a minted declaration: a minted [setname]/[mapname]
    is strictly longer than every dynset target.  (The verdict-level theorems
    ignore the extra margin — the seed only grows.) *)
Definition stmt_dynset_names (s : stmt) : list String.string :=
  match s with SDynset _ name _ _ => [name] | _ => [] end.

Definition body_dynset_names (b : list body_item) : list String.string :=
  flat_map (fun it => match it with BStmt s => stmt_dynset_names s | BMatch _ => [] end) b.

Definition rule_dynset_names (r : rule) : list String.string :=
  body_dynset_names (r_body r) ++ flat_map stmt_dynset_names (r_after r).

(** Write-target freshness: the rule dynset-writes no minted name at-or-above
    [n] (both namespaces the fold can write: [e_set] and [e_map]). *)
Definition rule_dynset_fresh (n : nat) (r : rule) : Prop :=
  forall k, n <= k ->
    ~ In (setname k) (rule_dynset_names r) /\ ~ In (mapname k) (rule_dynset_names r).

Lemma rule_dynset_fresh_mono : forall n m r,
  n <= m -> rule_dynset_fresh n r -> rule_dynset_fresh m r.
Proof. intros n m r Hnm Hf k Hk. apply Hf. lia. Qed.

Definition chain_seed (c : chain) : list string :=
  flat_map (fun r => body_set_names (r_body r) ++ rule_vmap_name r
                     ++ rule_nat_map_name r ++ rule_dynset_names r)
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
  split; [exact Hr |].
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. exact Hnm.
Qed.

Lemma chain_seed_dynset_in : forall c r nm,
  In r (c_rules c) -> In nm (rule_dynset_names r) -> In nm (chain_seed c).
Proof.
  intros c r nm Hr Hnm. unfold chain_seed. apply in_flat_map. exists r.
  split; [exact Hr |].
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hnm.
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

(** The WRITE-target freshness, by construction at the seed: every dynset target
    name is in [chain_seed], so it is strictly shorter than any minted
    [setname]/[mapname] at-or-above [seed_start]. *)
Lemma seed_start_dynset_fresh : forall c,
  Forall (rule_dynset_fresh (seed_start c)) (c_rules c).
Proof.
  intro c. apply Forall_forall. intros r Hr k Hk. split; intro Hin.
  - apply (not_in_of_length_gt (setname k) (chain_seed c)).
    + rewrite setname_length. unfold seed_start in Hk. lia.
    + apply (chain_seed_dynset_in c r (setname k) Hr Hin).
  - apply (not_in_of_length_gt (mapname k) (chain_seed c)).
    + rewrite mapname_length. unfold seed_start in Hk. lia.
    + apply (chain_seed_dynset_in c r (mapname k) Hr Hin).
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
