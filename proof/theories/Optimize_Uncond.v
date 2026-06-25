(** * Optimize_Uncond: UNCONDITIONAL correctness of the [nft -o] consolidation
    pipeline.

    The per-pass [_correct] theorems (and the composed [optimize_table_correct])
    require their INPUT chain to be [rules_clean].  That hypothesis was only ever
    used for ONE thing: the env-stability of a PASSED-THROUGH rule when a sibling
    merge prepends a fresh set/vmap declaration.  The N-way run-merge lemmas
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
    Part 3: unconditional per-pass correctness (setsN / concatN / vmapN).
    Part 4: unconditional [optimize_table] + END-TO-END compile theorems. *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import String.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Correct Optimize Optimize_Merge Optimize_Vmap Optimize_Concat Optimize_Table_Inv.

Local Open Scope nat_scope.

(** ** Part 1: env-AGREEMENT for an ARBITRARY rule.

    A rule's verdict reads the set/vmap environment ONLY through the matchconds its
    body evaluates ([mc_set_name]) and the verdict map it carries ([rule_vmap_name]).
    Loadability never reads [e_set]/[e_vmap] at all.  We prove this WITHOUT the
    [body_only_matches] restriction, which means handling statement body items —
    [SSynproxy] (env-stable [synproxy_stops]) and [SNotrack] (threads [set_untracked]
    into the rest of the walk).  The latter is the only subtlety: [set_untracked]
    commutes with [set_env], so it changes the PACKET but preserves the (d1/d2) env. *)

(** [set_untracked] only flips the packet latch; it commutes with installing an
    env, so the d1/d2 environment survives the notrack threading. *)
Lemma set_untracked_set_env : forall p e,
  set_untracked (set_env p e) = set_env (set_untracked p) e.
Proof.
  intros p e. unfold set_env.
  unfold set_untracked.
  replace (pkt_ct_present (with_pkt_env p e)) with (pkt_ct_present p) by reflexivity.
  destruct (pkt_ct_present p) eqn:E.
  - reflexivity.
  - unfold with_pkt_untracked, with_pkt_env. reflexivity.
Qed.

(** Loadability of a body item is env-stable (BMatch -> match_loadable,
    BStmt -> stmt_loadable; neither reads [e_set]/[e_vmap]). *)
Lemma body_item_loadable_env : forall it p base d1 d2,
  body_item_loadable it (set_env p (env_with_sets base d1))
  = body_item_loadable it (set_env p (env_with_sets base d2)).
Proof.
  intros it p base d1 d2. destruct it as [m | s]; cbn [body_item_loadable].
  - apply match_loadable_env.
  - apply stmt_loadable_env.
Qed.

(** The whole body's loadability walk is env-stable. *)
Lemma body_loadable_walk_env : forall body p base d1 d2,
  body_loadable_walk body (set_env p (env_with_sets base d1))
  = body_loadable_walk body (set_env p (env_with_sets base d2)).
Proof.
  intros body. induction body as [| it body IH]; intros p base d1 d2; [reflexivity|].
  destruct it as [m | s].
  - cbn [body_loadable_walk]. rewrite (body_item_loadable_env (BMatch m) p base d1 d2).
    rewrite (IH p base d1 d2). reflexivity.
  - destruct s; cbn [body_loadable_walk];
      try (rewrite (body_item_loadable_env (BStmt _) p base d1 d2);
           rewrite (IH p base d1 d2); reflexivity).
    (* SSynproxy *)
    rewrite (synproxy_loadable_env p base d1 d2).
    rewrite (synproxy_stops_env p base d1 d2).
    destruct (synproxy_stops (set_env p (env_with_sets base d2)));
      [reflexivity | rewrite (IH p base d1 d2); reflexivity].
Qed.

(** Body synproxy-stop is env-stable. *)
Lemma body_synproxy_stops_env : forall body p base d1 d2,
  body_synproxy_stops body (set_env p (env_with_sets base d1))
  = body_synproxy_stops body (set_env p (env_with_sets base d2)).
Proof.
  intros body p base d1 d2. unfold body_synproxy_stops.
  induction body as [| it body IH]; [reflexivity|].
  cbn [existsb]. rewrite IH. destruct it as [m | s]; [reflexivity|].
  destruct s; reflexivity.
Qed.

(** [outcome_core] AGREES across two decls that agree on the rule's vmap name. *)
Lemma outcome_core_agree : forall r q base d1 d2,
  (forall nm, In nm (rule_vmap_name r) ->
     e_vmap (env_with_sets base d1) nm = e_vmap (env_with_sets base d2) nm) ->
  outcome_core r (set_env q (env_with_sets base d1))
  = outcome_core r (set_env q (env_with_sets base d2)).
Proof.
  intros r q base d1 d2 Hvmap. unfold outcome_core.
  destruct (r_vmap r) as [vm |] eqn:Ev; [| apply terminal_outcome_env].
  assert (Hk : match vm_keyf vm with
                 | Some (f, ts) => apply_transforms ts (field_value f (set_env q (env_with_sets base d1)))
                 | None => List.concat (map (fun f => field_value f (set_env q (env_with_sets base d1))) (vm_fields vm))
                 end
             = match vm_keyf vm with
                 | Some (f, ts) => apply_transforms ts (field_value f (set_env q (env_with_sets base d2)))
                 | None => List.concat (map (fun f => field_value f (set_env q (env_with_sets base d2))) (vm_fields vm))
                 end).
  { destruct (vm_keyf vm) as [[f ts] |].
    - rewrite (field_value_env_with_sets f q base d1 d2). reflexivity.
    - rewrite (map_ext _ _ (fun f => field_value_env_with_sets f q base d1 d2)). reflexivity. }
  rewrite Hk. cbn [set_env with_pkt_env pkt_env].
  rewrite (Hvmap (vm_name vm)) by (unfold rule_vmap_name; rewrite Ev; left; reflexivity).
  destruct (assoc_verdict _ (e_vmap (env_with_sets base d2) (vm_name vm)));
    [reflexivity | apply terminal_outcome_env].
Qed.

(** *** Generalised whole-rule agreement: ARBITRARY body (no [body_only_matches]). *)

Lemma rule_applies_walk_agree_gen : forall body p base d1 d2,
  (forall nm, In nm (body_set_names body) ->
     e_set (env_with_sets base d1) nm = e_set (env_with_sets base d2) nm) ->
  rule_applies_walk body (set_env p (env_with_sets base d1))
  = rule_applies_walk body (set_env p (env_with_sets base d2)).
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
      rewrite !set_untracked_set_env.
      apply (IH (set_untracked p) base d1 d2 (fun nm Hnm => Hag nm (Hsub nm Hnm))).
    + (* SSynproxy *)
      rewrite (synproxy_stops_env p base d1 d2).
      destruct (synproxy_stops (set_env p (env_with_sets base d2)));
        [reflexivity | apply (IH p base d1 d2 (fun nm Hnm => Hag nm (Hsub nm Hnm)))].
Qed.

Lemma rule_loadable_agree_gen : forall r p base d1 d2,
  decls_agree_rule base d1 d2 r ->
  rule_loadable r (set_env p (env_with_sets base d1))
  = rule_loadable r (set_env p (env_with_sets base d2)).
Proof.
  intros r p base d1 d2 [_ Hvmap]. unfold rule_loadable.
  rewrite (body_loadable_walk_env (r_body r) p base d1 d2).
  rewrite (body_synproxy_stops_env (r_body r) p base d1 d2).
  f_equal.
  destruct (body_synproxy_stops (r_body r) (set_env p (env_with_sets base d2)));
    [reflexivity |].
  unfold body_thread.
  destruct (body_has_notrack (r_body r)).
  - rewrite !set_untracked_set_env.
    apply (end_loadable_agree r (set_untracked p) base d1 d2 Hvmap).
  - apply (end_loadable_agree r p base d1 d2 Hvmap).
Qed.

Lemma rule_applies_agree_gen : forall r p base d1 d2,
  decls_agree_rule base d1 d2 r ->
  rule_applies r (set_env p (env_with_sets base d1))
  = rule_applies r (set_env p (env_with_sets base d2)).
Proof.
  intros r p base d1 d2 [Hset _]. unfold rule_applies.
  apply (rule_applies_walk_agree_gen (r_body r) p base d1 d2 Hset).
Qed.

Lemma outcome_agree_gen : forall r p base d1 d2,
  decls_agree_rule base d1 d2 r ->
  outcome r (set_env p (env_with_sets base d1))
  = outcome r (set_env p (env_with_sets base d2)).
Proof.
  intros r p base d1 d2 [_ Hvmap]. unfold outcome.
  rewrite (body_synproxy_stops_env (r_body r) p base d1 d2).
  destruct (body_synproxy_stops (r_body r) (set_env p (env_with_sets base d2)));
    [reflexivity |].
  unfold body_thread.
  destruct (body_has_notrack (r_body r)).
  - rewrite !set_untracked_set_env. apply (outcome_core_agree r (set_untracked p) base d1 d2 Hvmap).
  - apply (outcome_core_agree r p base d1 d2 Hvmap).
Qed.

(** [eval_rules] AGREES across two decls that agree (per-rule) on the names each
    rule reads — for an ARBITRARY rule list. *)
Lemma eval_rules_agree_gen : forall rs p base d1 d2,
  (forall r, In r rs -> decls_agree_rule base d1 d2 r) ->
  eval_rules rs (set_env p (env_with_sets base d1))
  = eval_rules rs (set_env p (env_with_sets base d2)).
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

(** *** The two seam helpers: a passed-through rule that reads no minted name
    AGREES across the extended declarations. *)

(** setsN / concatN seam: the pass adds only [setname] entries (and leaves
    [sd_vmaps] fixed); a [rule_set_fresh n] rule agrees. *)
Lemma decls_agree_rule_setseam : forall base d d' r n,
  sd_vmaps d' = sd_vmaps d ->
  (forall nm X, (forall k, n <= k -> nm <> setname k) ->
     assoc_str nm (sd_sets d') X = assoc_str nm (sd_sets d) X) ->
  rule_set_fresh n r ->
  decls_agree_rule base d' d r.
Proof.
  intros base d d' r n Hvm Hassoc Hfresh. split.
  - intros nm Hnm. rewrite !e_set_declared.
    apply Hassoc. intros k Hk Heq. subst nm. apply (Hfresh k Hk Hnm).
  - intros nm _. rewrite !e_vmap_env_with_sets. rewrite Hvm. reflexivity.
Qed.

(** vmapN seam: the pass adds only [vmapname] entries (and leaves [sd_sets]
    fixed); a [rule_vmap_fresh n] rule agrees. *)
Lemma decls_agree_rule_vmapseam : forall base d d' r n,
  sd_sets d' = sd_sets d ->
  (forall nm X, (forall k, n <= k -> nm <> vmapname k) ->
     assoc_str nm (sd_vmaps d') X = assoc_str nm (sd_vmaps d) X) ->
  rule_vmap_fresh n r ->
  decls_agree_rule base d' d r.
Proof.
  intros base d d' r n Hss Hassoc Hfresh. split.
  - intros nm _. rewrite !e_set_declared. rewrite Hss. reflexivity.
  - intros nm Hnm. rewrite !e_vmap_env_with_sets.
    apply Hassoc. intros k Hk Heq. subst nm. apply (Hfresh k Hk Hnm).
Qed.

(** A [decls_agree_rule] is symmetric in its two declaration sets. *)
Lemma decls_agree_rule_sym : forall base d1 d2 r,
  decls_agree_rule base d1 d2 r -> decls_agree_rule base d2 d1 r.
Proof.
  intros base d1 d2 r [Hset Hvmap]. split.
  - intros nm Hnm. symmetry. apply Hset; exact Hnm.
  - intros nm Hnm. symmetry. apply Hvmap; exact Hnm.
Qed.

(** ** Part 3: unconditional per-pass correctness.

    Each theorem drops [rules_clean] in favour of [Forall (rule_set_fresh n)]
    (resp. [rule_vmap_fresh]).  The MERGE case needs no cleanliness: the run-merge
    lemmas are body-agnostic.  The PASS-THROUGH case uses read-freshness +
    [decls_agree_rule_*seam] to keep the passed rule env-stable. *)

(** *** setsN. *)
Theorem optimize_rules_setsN_correct_uncond : forall fuel rs n d n' d' rs' base p,
  optimize_rules_setsN fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) rs ->
  eval_rules rs' (set_env p (env_with_sets base d'))
  = eval_rules rs  (set_env p (env_with_sets base d)).
Proof.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base p H Hfresh Hrf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_setsN_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_value_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct (take_value_run_shape r1 f v1 body (r2 :: rest) vs rest' Ehd Erun)
          as [Hsplit Hwidth].
        destruct vs as [| v vs'].
        -- (* no eligible neighbour: keep r1, recurse *)
           remember (optimize_rules_setsN fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           cbn [eval_rules].
           rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
           assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_setseam base d dd'' r1 n).
             - apply (optimize_rules_setsN_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_setsN_assoc_stable fuel n d (r2 :: rest)
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
           rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
           rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
           rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
        -- (* RUN of >= 2 rules: fold them all into one __setN *)
           cbv zeta in H.
           remember (optimize_rules_setsN fuel (S n)
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
           assert (Htail : eval_rules rr'' (set_env p (env_with_sets base dd''))
                           = eval_rules rest' (set_env p (env_with_sets base dn))).
           { eapply (IH rest' (S n) dn m'' dd'' rr'' base p (eq_sym Erec)); [| exact Hrf_rest'].
             intros k Hk Hin. subst dn; cbn [sd_sets map] in Hin.
             destruct Hin as [Heq | Hin].
             - apply setname_inj in Heq. lia.
             - apply (Hfresh k); [lia | exact Hin]. }
           assert (Hlook : e_set (pkt_env (set_env p (env_with_sets base dd''))) (setname n)
                           = elems).
           { cbn [set_env with_pkt_env pkt_env]. rewrite e_set_declared.
             erewrite (optimize_rules_setsN_assoc_stable fuel (S n) dn _ _ _ _
                         (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           set (qd := set_env p (env_with_sets base dd'')) in *.
           assert (Hcert : eval_matchcond (MConcatSet [f] false (setname n)) qd
                   = existsb (fun w => eval_matchcond (MCmp f CEq w) qd) vals).
           { apply (concat_set_existsb f vals (setname n) qd).
             - subst elems. exact Hlook.
             - intros w Hw Hld.
               assert (Hfxw : field_fixed_len f = Some (Datatypes.length w)).
               { subst vals. destruct Hw as [Hw | Hw].
                 - subst w. apply (take_value_run_head_width r1 f v1 body r2 rest
                                     (v :: vs') rest' Ehd Erun). discriminate.
                 - apply (Hwidth w Hw). }
               apply (field_fixed_len_loaded f (Datatypes.length w) qd Hfxw Hld). }
           transitivity (eval_rules
             (map (fun m => mk_head m body r1) (map (fun w => MCmp f CEq w) vals)
              ++ rr'') qd).
           { apply (eval_rules_run_merge_abs
                      (map (fun w => MCmp f CEq w) vals)
                      (fun q => fields_loadable [f] q) body r1
                      (MConcatSet [f] false (setname n)) rr'' qd).
             - subst vals. discriminate.
             - intros m Hm. apply (match_loadable_run f vals qd m Hm).
             - apply match_loadable_mconcat1.
             - rewrite Hcert. rewrite existsb_map_eq. reflexivity. }
           rewrite List.map_map.
           assert (Htail' : eval_rules rr'' qd = eval_rules rest' qd).
           { rewrite Htail. unfold qd.
             apply (eval_rules_agree_gen rest' p base dn dd'').
             intros r Hr. apply decls_agree_rule_sym.
             apply (decls_agree_rule_setseam base dn dd'' r (S n)).
             - apply (optimize_rules_setsN_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_setsN_assoc_stable fuel (S n) dn rest'
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - rewrite Forall_forall in Hrf_rest'. apply Hrf_rest'; exact Hr. }
           rewrite (eval_rules_app_cong
                      (map (fun w => mk_head (MCmp f CEq w) body r1) vals)
                      rr'' rest' qd Htail').
           rewrite <- Hrun_eq.
           (* whole input list at dd'' equals at d (read-fresh + assoc-stable) *)
           assert (Hvm_dd : sd_vmaps dd'' = sd_vmaps d).
           { rewrite (optimize_rules_setsN_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hassoc_dd : forall nm X, (forall k, n <= k -> nm <> setname k) ->
                     assoc_str nm (sd_sets dd'') X = assoc_str nm (sd_sets d) X).
           { intros nm X Hf.
             rewrite (optimize_rules_setsN_assoc_stable fuel (S n) dn rest' m'' dd'' rr'' nm X
                        (eq_sym Erec) (fun k Hk => Hf k ltac:(lia))).
             subst dn; cbn [sd_sets assoc_str].
             destruct (String.eqb nm (setname n)) eqn:Eq.
             - apply String.eqb_eq in Eq. exfalso. apply (Hf n (Nat.le_refl n) Eq).
             - reflexivity. }
           unfold qd. apply (eval_rules_agree_gen (r1 :: r2 :: rest) p base dd'' d).
           intros r Hr. apply (decls_agree_rule_setseam base d dd'' r n Hvm_dd Hassoc_dd).
           rewrite Forall_forall in Hrf. apply Hrf; exact Hr.
      * (* head not value-eligible: keep r1, recurse *)
        remember (optimize_rules_setsN fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        cbn [eval_rules].
        rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
        assert (Hda1 : decls_agree_rule base dd'' d r1).
        { apply (decls_agree_rule_setseam base d dd'' r1 n).
          - apply (optimize_rules_setsN_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - intros nm X Hf. apply (optimize_rules_setsN_assoc_stable fuel n d (r2 :: rest)
                                    m'' dd'' rr'' nm X (eq_sym Erec) Hf).
          - exact Hf1. }
        rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
        rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
        rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
Qed.

(** *** concatN. *)
Theorem optimize_rules_concatN_correct_uncond : forall fuel rs n d n' d' rs' base p,
  optimize_rules_concatN fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  Forall (rule_set_fresh n) rs ->
  eval_rules rs' (set_env p (env_with_sets base d'))
  = eval_rules rs  (set_env p (env_with_sets base d)).
Proof.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base p H Hfresh Hrf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_concatN_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_value2 r1) as [[[[[f1 a1] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concat_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct (take_concat_run_shape r1 f1 a1 f2 b1 body (r2 :: rest) ts rest' Ehd Erun)
          as [Hsplit [HwA HwB]].
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concatN fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           cbn [eval_rules].
           rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
           assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_setseam base d dd'' r1 n).
             - apply (optimize_rules_concatN_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_concatN_assoc_stable fuel n d (r2 :: rest)
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
           rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
           rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
           rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
        -- cbv zeta in H.
           remember (optimize_rules_concatN fuel (S n)
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
           { rewrite (optimize_rules_concatN_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             subst dn; reflexivity. }
           assert (Hassoc_dd : forall nm X, (forall k, n <= k -> nm <> setname k) ->
                     assoc_str nm (sd_sets dd'') X = assoc_str nm (sd_sets d) X).
           { intros nm X Hf.
             rewrite (optimize_rules_concatN_assoc_stable fuel (S n) dn rest' m'' dd'' rr'' nm X
                        (eq_sym Erec) (fun k Hk => Hf k ltac:(lia))).
             subst dn; cbn [sd_sets assoc_str].
             destruct (String.eqb nm (setname n)) eqn:Eq.
             - apply String.eqb_eq in Eq. exfalso. apply (Hf n (Nat.le_refl n) Eq).
             - reflexivity. }
           assert (Htail : eval_rules rr'' (set_env p (env_with_sets base dd''))
                           = eval_rules rest' (set_env p (env_with_sets base dn))).
           { eapply (IH rest' (S n) dn m'' dd'' rr'' base p (eq_sym Erec)); [| exact Hrf_rest'].
             intros k Hk Hin. subst dn; cbn [sd_sets map] in Hin.
             destruct Hin as [Heq | Hin].
             - apply setname_inj in Heq. lia.
             - apply (Hfresh k); [lia | exact Hin]. }
           assert (Hlook : e_set (pkt_env (set_env p (env_with_sets base dd'')))
                             (setname n) = map pack_tuple tuples).
           { cbn [set_env with_pkt_env pkt_env]. rewrite e_set_declared.
             erewrite (optimize_rules_concatN_assoc_stable fuel (S n) dn rest' _ _ _
                         (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           set (qd := set_env p (env_with_sets base dd'')) in *.
           assert (Hcert : eval_matchcond (MConcatSet [f1; f2] false (setname n)) qd
                   = existsb (fun ab => andb (eval_matchcond (MCmp f1 CEq (fst ab)) qd)
                                             (eval_matchcond (MCmp f2 CEq (snd ab)) qd))
                             tuples).
           { apply (concat_two_fields_certificate_N f1 f2 tuples (setname n) qd).
             - exact Hlook.
             - intros a b Hin Hld.
               assert (Hfx : field_fixed_len f1 = Some (Datatypes.length a)).
               { destruct (take_concat_run_head_width r1 f1 a1 f2 b1 body r2 rest
                             (t :: ts') rest' Ehd Erun ltac:(discriminate)) as [Hh1 _].
                 subst tuples. destruct Hin as [Hab | Hin].
                 - injection Hab as -> ->. exact Hh1.
                 - apply (HwA a b Hin). }
               apply (field_fixed_len_loaded f1 (Datatypes.length a) qd Hfx Hld).
             - intros a b Hin Hld.
               assert (Hfx : field_fixed_len f2 = Some (Datatypes.length b)).
               { destruct (take_concat_run_head_width r1 f1 a1 f2 b1 body r2 rest
                             (t :: ts') rest' Ehd Erun ltac:(discriminate)) as [_ Hh2].
                 subst tuples. destruct Hin as [Hab | Hin].
                 - injection Hab as -> ->. exact Hh2.
                 - apply (HwB a b Hin). }
               apply (field_fixed_len_loaded f2 (Datatypes.length b) qd Hfx Hld). }
           transitivity (eval_rules
             (map (fun ab => orig_rule2 f1 f2 (fst ab) (snd ab) body r1) tuples ++ rr'') qd).
           { apply (eval_rules_run_collapse
                      (map (fun ab => orig_rule2 f1 f2 (fst ab) (snd ab) body r1) tuples)
                      (rule_loadable (merged_rule2 f1 f2 (setname n) body r1) qd)
                      (outcome (merged_rule2 f1 f2 (setname n) body r1) qd)
                      (merged_rule2 f1 f2 (setname n) body r1) rr'' qd).
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
                   andb (andb (eval_matchcond (MCmp f1 CEq (fst ab)) qd)
                              (eval_matchcond (MCmp f2 CEq (snd ab)) qd))
                        (rule_applies_walk body qd)) tuples).
               + rewrite existsb_andb_const. reflexivity.
               + apply existsb_ext. intros ab _. symmetry. apply orig_rule2_applies. }
           assert (Htail' : eval_rules rr'' qd = eval_rules rest' qd).
           { rewrite Htail. unfold qd.
             apply (eval_rules_agree_gen rest' p base dn dd'').
             intros r Hr. apply decls_agree_rule_sym.
             apply (decls_agree_rule_setseam base dn dd'' r (S n)).
             - apply (optimize_rules_concatN_vmaps fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_concatN_assoc_stable fuel (S n) dn rest'
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - rewrite Forall_forall in Hrf_rest'. apply Hrf_rest'; exact Hr. }
           rewrite (eval_rules_app_cong
                      (map (fun ab => orig_rule2 f1 f2 (fst ab) (snd ab) body r1) tuples)
                      rr'' rest' qd Htail').
           rewrite <- Hrun_eq.
           unfold qd. apply (eval_rules_agree_gen (r1 :: r2 :: rest) p base dd'' d).
           intros r Hr. apply (decls_agree_rule_setseam base d dd'' r n Hvm_dd Hassoc_dd).
           rewrite Forall_forall in Hrf. apply Hrf; exact Hr.
      * remember (optimize_rules_concatN fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        cbn [eval_rules].
        rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
        assert (Hda1 : decls_agree_rule base dd'' d r1).
        { apply (decls_agree_rule_setseam base d dd'' r1 n).
          - apply (optimize_rules_concatN_vmaps fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
          - intros nm X Hf. apply (optimize_rules_concatN_assoc_stable fuel n d (r2 :: rest)
                                    m'' dd'' rr'' nm X (eq_sym Erec) Hf).
          - exact Hf1. }
        rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
        rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
        rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
Qed.

(** *** vmapN.  The vmap merge is GATED on [body_vmap_safe] (no synproxy/notrack in
    the body), which the merge condition now enforces; that gate is what makes the
    vmap pass SOUND on arbitrary input (the merge is genuinely unsound for a
    [notrack] body, since the merged rule reads its key field at the body-threaded
    packet).  Read-freshness is in the [vmapname] namespace. *)
Theorem optimize_rules_vmapN_correct_uncond : forall fuel rs n d n' d' rs' base p,
  optimize_rules_vmapN fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  Forall (rule_vmap_fresh n) rs ->
  eval_rules rs' (set_env p (env_with_sets base d'))
  = eval_rules rs  (set_env p (env_with_sets base d)).
Proof.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base p H Hfresh Hrf.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_vmapN_consSS in H.
      inversion Hrf as [| ? ? Hf1 Hrf_tail]; subst.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_vmap_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct (take_vmap_run_shape r1 f v1 body (r2 :: rest) es rest' Ehd Erun)
          as [Hsplit [HwK HwT]].
        assert (Hrf_rest_n : Forall (rule_vmap_fresh n) rest').
        { rewrite Hsplit in Hrf_tail. apply Forall_app in Hrf_tail. exact (proj2 Hrf_tail). }
        destruct es as [| e es'].
        -- remember (optimize_rules_vmapN fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           cbn [eval_rules].
           rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
           assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_vmapseam base d dd'' r1 n).
             - apply (optimize_rules_vmapN_sets fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_vmapN_assoc_stable fuel n d (r2 :: rest) m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
           rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
           rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
           rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
        -- destruct (take_vmap_run_head r1 f v1 body r2 rest (e :: es') rest' Ehd Erun
                       ltac:(discriminate)) as [Hr1eq [HwK1 HwT1]].
           destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           2:{ remember (optimize_rules_vmapN fuel n d (r2 :: rest)) as tt eqn:Erec.
               destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
               injection H as Hn' Hd' Hr'. subst n' d' rs'.
               cbn [eval_rules].
               rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
               assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_vmapseam base d dd'' r1 n).
             - apply (optimize_rules_vmapN_sets fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_vmapN_assoc_stable fuel n d (r2 :: rest) m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
               rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
               rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
               rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity. }
           (* merge: discharge synproxy/notrack from the body_vmap_safe gate *)
           apply Bool.andb_true_iff in Hdv as [_ Hsafe].
           apply Bool.andb_true_iff in Hsafe as [Hns Hnt].
           apply Bool.negb_true_iff in Hns. apply Bool.negb_true_iff in Hnt.
           cbv zeta in H.
           remember (optimize_rules_vmapN fuel (S n)
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
             by (apply (optimize_rules_vmapN_sets _ _ _ _ _ _ _ (eq_sym Erec))).
           assert (Hsets_dn : sd_sets dn = sd_sets d) by (subst dn; reflexivity).
           assert (Htail : eval_rules rr'' (set_env p (env_with_sets base dd''))
                           = eval_rules rest' (set_env p (env_with_sets base dn))).
           { eapply (IH rest' (S n) dn m'' dd'' rr'' base p (eq_sym Erec)); [| exact Hrf_rest'].
             intros k Hk Hin. subst dn; cbn [sd_vmaps map] in Hin.
             destruct Hin as [Heq | Hin].
             - apply vmapname_inj in Heq. lia.
             - apply (Hfresh k); [lia | exact Hin]. }
           assert (Hlook : e_vmap (pkt_env (set_env p (env_with_sets base dd'')))
                             (vmapname n) = map vmap_pt entries).
           { cbn [set_env with_pkt_env pkt_env]. rewrite e_vmap_env_with_sets.
             erewrite (optimize_rules_vmapN_assoc_stable fuel (S n) dn _ _ _ _
                         (vmapname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_vmaps assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply vmapname_inj in Heq. lia. }
           set (qd := set_env p (env_with_sets base dd'')) in *.
           transitivity (eval_rules
             (map (fun vw => orig_rule f (fst vw) body (snd vw)) entries ++ rr'') qd).
           { unfold qd. apply (eval_rules_vmap_mergeN f (vmapname n) entries body rr''
                                 (set_env p (env_with_sets base dd''))).
             - exact Hlook.
             - intros v w Hin. subst entries. destruct Hin as [Hvw | Hin];
                 [ inversion Hvw; subst; exact HwK1 | apply (HwK v w Hin) ].
             - intros v w Hin. subst entries. destruct Hin as [Hvw | Hin];
                 [ inversion Hvw; subst; exact HwT1 | apply (HwT v w Hin) ].
             - apply (body_has_synproxy_false_stops body qd Hns).
             - exact Hnt. }
           assert (Htail' : eval_rules rr'' qd = eval_rules rest' qd).
           { rewrite Htail. unfold qd.
             apply (eval_rules_agree_gen rest' p base dn dd'').
             intros r Hr. apply decls_agree_rule_sym.
             apply (decls_agree_rule_vmapseam base dn dd'' r (S n)).
             - apply (optimize_rules_vmapN_sets fuel (S n) dn rest' m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_vmapN_assoc_stable fuel (S n) dn rest'
                                       m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - rewrite Forall_forall in Hrf_rest'. apply Hrf_rest'; exact Hr. }
           rewrite (eval_rules_app_cong
                      (map (fun vw => orig_rule f (fst vw) body (snd vw)) entries)
                      rr'' rest' qd Htail').
           rewrite <- Hrun_eq.
           unfold qd. apply (eval_rules_agree_gen (r1 :: r2 :: rest) p base dd'' d).
           intros r Hr. apply (decls_agree_rule_vmapseam base d dd'' r n).
           ++ rewrite Hsets_dd, Hsets_dn; reflexivity.
           ++ intros nm X Hf.
              rewrite (optimize_rules_vmapN_assoc_stable fuel (S n) dn rest' m'' dd'' rr'' nm X
                         (eq_sym Erec) (fun k Hk => Hf k ltac:(lia))).
              subst dn; cbn [sd_vmaps assoc_str].
              destruct (String.eqb nm (vmapname n)) eqn:Eq.
              ** apply String.eqb_eq in Eq. exfalso. apply (Hf n (Nat.le_refl n) Eq).
              ** reflexivity.
           ++ rewrite Forall_forall in Hrf. apply Hrf; exact Hr.
      * remember (optimize_rules_vmapN fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        cbn [eval_rules].
        rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hfresh Hrf_tail).
        assert (Hda1 : decls_agree_rule base dd'' d r1).
           { apply (decls_agree_rule_vmapseam base d dd'' r1 n).
             - apply (optimize_rules_vmapN_sets fuel n d (r2 :: rest) m'' dd'' rr'' (eq_sym Erec)).
             - intros nm X Hf. apply (optimize_rules_vmapN_assoc_stable fuel n d (r2 :: rest) m'' dd'' rr'' nm X (eq_sym Erec) Hf).
             - exact Hf1. }
        rewrite (rule_loadable_agree_gen r1 p base dd'' d Hda1).
        rewrite (rule_applies_agree_gen r1 p base dd'' d Hda1).
        rewrite (outcome_agree_gen r1 p base dd'' d Hda1). reflexivity.
Qed.
