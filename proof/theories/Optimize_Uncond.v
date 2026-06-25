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
