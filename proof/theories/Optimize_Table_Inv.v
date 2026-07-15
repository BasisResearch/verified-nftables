(** * Optimize_Table_Inv: SEAM invariants for composing the verified nft -o passes.

    Each individual pass theorem ([optimize_chain_setsN/vmapN/concatN_correct])
    requires its INPUT chain to be [rules_clean].  But every merge pass EMITS a
    non-clean rule (an [MConcatSet] head, or an [r_vmap] verdict-map rule), so
    stage k's output is NOT [rules_clean] and cannot be fed to stage k+1's theorem
    directly.

    This file builds the two ingredients that bridge the seam:

      1. ENV-AGREEMENT: a rule's verdict depends on the set/vmap environment ONLY
         through the set names its body matchconds read ([MConcatSet]/[MSetT]/
         [MConcatSetT]) and the verdict-map name it carries ([r_vmap]).  Two
         declaration sets that AGREE on exactly those names give the SAME verdict.
         A later pass only PREPENDS entries keyed by FRESH names, so it agrees with
         the earlier [d] on every name the earlier output reads.

      2. OUTPUT INVARIANTS: each pass's counter is monotone, minted names lie in
         [n, n'), and a pass leaves the OTHER namespace's declarations untouched
         (setsN/concatN do not touch [sd_vmaps]; vmapN does not touch [sd_sets]).

    Together with the per-pass [_assoc_stable] lemmas these discharge the freshness
    and clean-input obligations at every seam of the composed [optimize_table]. *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import String.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Optimize Optimize_Merge Optimize_Vmap Optimize_Concat Optimize_ConcatM
  Optimize_Setg Optimize_Vmapg.

(** ** Part 1: env-agreement on the set/vmap names a rule reads. *)

(** The single set name a matchcond reads from the runtime environment ([None] for
    the value-only conds, which never touch [e_set]). *)
Definition mc_set_name (m : matchcond) : option string :=
  match m with
  | MConcatSet _ _ name | MSetT _ _ _ name | MConcatSetT _ _ name => Some name
  | _ => None
  end.

(** A matchcond eval AGREES across two decls that agree on the read set name. *)
Lemma eval_matchcond_agree : forall m p base d1 d2,
  (forall nm, mc_set_name m = Some nm ->
     e_set (env_with_sets base d1) nm = e_set (env_with_sets base d2) nm) ->
  eval_matchcond m (env_with_sets base d1) p
  = eval_matchcond m (env_with_sets base d2) p.
Proof.
  intros m p base d1 d2 Hag.
  unfold eval_matchcond, eval_matchcond_body, match_loadable.
  destruct m; cbn [mc_set_name] in Hag;
    repeat (match goal with
            | |- context[field_value ?f (env_with_sets base d1) p] =>
                rewrite (field_value_env_with_sets f p base d1 d2)
            end);
    try reflexivity.
  - (* MConcatSet *) rewrite (Hag _ eq_refl). reflexivity.
  - (* MSetT *) rewrite (Hag _ eq_refl). reflexivity.
  - (* MConcatSetT *) rewrite (Hag _ eq_refl). reflexivity.
Qed.

(** Set names read by a body (its matchconds). *)
Definition body_set_names (b : list body_item) : list string :=
  flat_map (fun m => match mc_set_name m with Some nm => [nm] | None => [] end)
           (body_matches b).

(** Pointwise-equal predicates give equal [forallb]. *)
Lemma forallb_ext_in {A} : forall (f g : A -> bool) (l : list A),
  (forall x, In x l -> f x = g x) -> forallb f l = forallb g l.
Proof.
  induction l as [| x l IH]; intro H; [reflexivity|].
  cbn [forallb]. rewrite (H x (or_introl eq_refl)).
  rewrite (IH (fun y Hy => H y (or_intror Hy))). reflexivity.
Qed.

(** A matchcond in [body_matches] reads a set name listed in [body_set_names]. *)
Lemma mc_in_body_read : forall body m nm,
  In m (body_matches body) -> mc_set_name m = Some nm ->
  In nm (body_set_names body).
Proof.
  intros body m nm Hm Hnm. unfold body_set_names.
  apply in_flat_map. exists m. split; [exact Hm |]. rewrite Hnm. left; reflexivity.
Qed.

(* (loadability predicates no longer take the env at all, so the old
   [match_loadable_env]-style stability lemmas are gone: stability is now a
   typing fact, visible in the signatures.) *)

(** A body all of whose items are matchconds (no statements).  Every lookup rule a
    merge pass emits ([MConcatSet] head + clean match tail, or a vmap rule whose
    body is the clean match tail) has such a body. *)
Definition body_only_matches (b : list body_item) : bool :=
  forallb (fun it => match it with BMatch _ => true | BStmt _ => false end) b.

(** On a matches-only body, [rule_applies_walk = forallb eval_matchcond]. *)
Definition rule_vmap_name (r : rule) : list string :=
  match r_vmap r with Some vm => [vm_name vm] | None => [] end.

(** The named data MAP a rule reads, if any: a map-sourced terminal NAT operand
    (`dnat to … map @name`) looks the operand up in [e_map name] — and, since the
    lookup BREAKs on a miss, [terminal_loadable] reads it too.  (Empty for every
    rule a merge pass emits and for every non-[nat_map] rule.) *)
Definition rule_nat_map_name (r : rule) : list string :=
  match r_nat r with
  | Some n => match nat_map n with Some (_, _, name) => [name] | None => [] end
  | None => []
  end.

(** Two decls AGREE for a rule [r] iff they give the same [e_set]/[e_vmap]/[e_map]
    lookup at every name [r] reads. *)
Definition decls_agree_rule (base : env) (d1 d2 : set_decls) (r : rule) : Prop :=
  (forall nm, In nm (body_set_names (r_body r)) ->
     e_set (env_with_sets base d1) nm = e_set (env_with_sets base d2) nm) /\
  (forall nm, In nm (rule_vmap_name r) ->
     e_vmap (env_with_sets base d1) nm = e_vmap (env_with_sets base d2) nm) /\
  (forall nm, In nm (rule_nat_map_name r) ->
     e_map (env_with_sets base d1) nm = e_map (env_with_sets base d2) nm).

(** [terminal_loadable] reads [e_set]/[e_vmap] never, but a map-sourced NAT operand
    reads [e_map] at its [nat_map] name (the break-on-miss test); given the two decls
    agree there ([rule_nat_map_name]), it is env-stable. *)
Lemma terminal_loadable_env : forall r p base d1 d2,
  (forall nm, In nm (rule_nat_map_name r) ->
     e_map (env_with_sets base d1) nm = e_map (env_with_sets base d2) nm) ->
  terminal_loadable r (env_with_sets base d1) p
  = terminal_loadable r (env_with_sets base d2) p.
Proof.
  intros r p base d1 d2 Hmap. unfold terminal_loadable.
  destruct (r_nat r) as [n |] eqn:Hrn.
  { destruct (nat_src n) as [vs |]; [reflexivity|].
    destruct (nat_map n) as [[[fields ts] name] |] eqn:Hnm.
    - replace (nat_map_key fields ts (env_with_sets base d1) p)
         with (nat_map_key fields ts (env_with_sets base d2) p).
      2:{ unfold nat_map_key. destruct fields as [| f0 fr]; [reflexivity|].
          rewrite (field_value_env_with_sets f0 p base d2 d1).
          rewrite (map_ext _ _ (fun f => field_value_env_with_sets f p base d2 d1)).
          reflexivity. }
      rewrite (Hmap name)
        by (unfold rule_nat_map_name; rewrite Hrn, Hnm; left; reflexivity).
      reflexivity.
    - reflexivity. }
  reflexivity.
Qed.

Lemma tail_loadable_env : forall r p base d1 d2,
  (forall nm, In nm (rule_nat_map_name r) ->
     e_map (env_with_sets base d1) nm = e_map (env_with_sets base d2) nm) ->
  tail_loadable r (env_with_sets base d1) p
  = tail_loadable r (env_with_sets base d2) p.
Proof.
  intros r p base d1 d2 Hmap. unfold tail_loadable.
  rewrite (terminal_loadable_env r p base d1 d2 Hmap).
  reflexivity.
Qed.

(** [end_loadable] AGREES across two decls that agree on the rule's vmap name. *)
Lemma end_loadable_agree : forall r p base d1 d2,
  (forall nm, In nm (rule_vmap_name r) ->
     e_vmap (env_with_sets base d1) nm = e_vmap (env_with_sets base d2) nm) ->
  (forall nm, In nm (rule_nat_map_name r) ->
     e_map (env_with_sets base d1) nm = e_map (env_with_sets base d2) nm) ->
  end_loadable r (env_with_sets base d1) p
  = end_loadable r (env_with_sets base d2) p.
Proof.
  intros r p base d1 d2 Hag Hmap. unfold end_loadable.
  destruct (r_vmap r) as [vm |] eqn:Ev; [| apply tail_loadable_env; exact Hmap].
  assert (Hk : (let key := match vm_keyf vm with
                 | Some (f, ts) => apply_transforms ts (field_value f (env_with_sets base d1) p)
                 | None => List.concat (map (fun f => field_value f (env_with_sets base d1) p) (vm_fields vm))
                 end in key)
             = (let key := match vm_keyf vm with
                 | Some (f, ts) => apply_transforms ts (field_value f (env_with_sets base d2) p)
                 | None => List.concat (map (fun f => field_value f (env_with_sets base d2) p) (vm_fields vm))
                 end in key)).
  { cbn zeta. destruct (vm_keyf vm) as [[f ts] |].
    - rewrite (field_value_env_with_sets f p base d1 d2). reflexivity.
    - rewrite (map_ext _ _ (fun f => field_value_env_with_sets f p base d1 d2)).
      reflexivity. }
  cbn zeta. cbn zeta in Hk. rewrite Hk.
  rewrite (Hag (vm_name vm)) by (unfold rule_vmap_name; rewrite Ev; left; reflexivity).
  destruct (assoc_verdict _ (e_vmap (env_with_sets base d2) (vm_name vm)));
    [reflexivity |].
  f_equal. apply tail_loadable_env; exact Hmap.
Qed.

(** Whole-rule agreement for a matches-only rule across two decls that agree on the
    names it reads. *)
Lemma optimize_rules_setsN_mono : forall fuel n d rs n' d' rs',
  optimize_rules_setsN fuel n d rs = (n', d', rs') -> n <= n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; lia.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; lia.
    + cbn in H. inversion H; subst; lia.
    + rewrite optimize_rules_setsN_consSS in H.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_value_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct vs as [| v vs'].
        -- remember (optimize_rules_setsN fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_setsN fuel (S n)
                       {| sd_sets := (setname n, map (fun w => (w,w)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n'.
           assert (S n <= m'')
             by (eapply (IH (S n) _ rest'); symmetry; exact Erec). lia.
      * remember (optimize_rules_setsN fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_setsN_vmaps : forall fuel n d rs n' d' rs',
  optimize_rules_setsN fuel n d rs = (n', d', rs') -> sd_vmaps d' = sd_vmaps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_setsN_consSS in H.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_value_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct vs as [| v vs'].
        -- remember (optimize_rules_setsN fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_setsN fuel (S n)
                       {| sd_sets := (setname n, map (fun w => (w,w)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_setsN fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_chain_setsN_mono : forall n d c n' d' c',
  optimize_chain_setsN n d c = (n', d', c') -> n <= n'.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_setsN in H.
  destruct (optimize_rules_setsN (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_setsN_mono _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_setsN_vmaps : forall n d c n' d' c',
  optimize_chain_setsN n d c = (n', d', c') -> sd_vmaps d' = sd_vmaps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_setsN in H.
  destruct (optimize_rules_setsN (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_setsN_vmaps _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_rules_setsN_maps : forall fuel n d rs n' d' rs',
  optimize_rules_setsN fuel n d rs = (n', d', rs') -> sd_maps d' = sd_maps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_setsN_consSS in H.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_value_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct vs as [| v vs'].
        -- remember (optimize_rules_setsN fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_setsN fuel (S n)
                       {| sd_sets := (setname n, map (fun w => (w,w)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_setsN fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_chain_setsN_maps : forall n d c n' d' c',
  optimize_chain_setsN n d c = (n', d', c') -> sd_maps d' = sd_maps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_setsN in H.
  destruct (optimize_rules_setsN (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_setsN_maps _ _ _ _ _ _ _ E).
Qed.

(** *** vmapN. *)
Lemma optimize_rules_vmapN_sets : forall fuel n d rs n' d' rs',
  optimize_rules_vmapN fuel n d rs = (n', d', rs') -> sd_sets d' = sd_sets d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_vmapN_consSS in H.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_vmap_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_vmapN fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           ++ cbv zeta in H.
              remember (optimize_rules_vmapN fuel (S n)
                          {| sd_sets := sd_sets d;
                             sd_vmaps := (vmapname n,
                               map vmap_pt ((v1, r_verdict r1) :: e :: es')) :: sd_vmaps d;
                             sd_maps := sd_maps d |} rest') as t eqn:Erec.
              destruct t as [[m'' dd''] rr'']. cbv zeta in H.
              injection H as Hn' Hd' Hr'. subst d'.
              rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
           ++ remember (optimize_rules_vmapN fuel n d (r2 :: rest)) as t eqn:Erec.
              destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
              eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
      * remember (optimize_rules_vmapN fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_vmapN_maps : forall fuel n d rs n' d' rs',
  optimize_rules_vmapN fuel n d rs = (n', d', rs') -> sd_maps d' = sd_maps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_vmapN_consSS in H.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_vmap_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_vmapN fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           ++ cbv zeta in H.
              remember (optimize_rules_vmapN fuel (S n)
                          {| sd_sets := sd_sets d;
                             sd_vmaps := (vmapname n,
                               map vmap_pt ((v1, r_verdict r1) :: e :: es')) :: sd_vmaps d;
                             sd_maps := sd_maps d |} rest') as t eqn:Erec.
              destruct t as [[m'' dd''] rr'']. cbv zeta in H.
              injection H as Hn' Hd' Hr'. subst d'.
              rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
           ++ remember (optimize_rules_vmapN fuel n d (r2 :: rest)) as t eqn:Erec.
              destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
              eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
      * remember (optimize_rules_vmapN fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_concatN_mono : forall fuel n d rs n' d' rs',
  optimize_rules_concatN fuel n d rs = (n', d', rs') -> n <= n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; lia.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; lia.
    + cbn in H. inversion H; subst; lia.
    + rewrite optimize_rules_concatN_consSS in H.
      destruct (head_value2 r1) as [[[[[f1 a1] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concat_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concatN fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_concatN fuel (S n) _ rest') as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n'.
           assert (S n <= m'')
             by (eapply (IH (S n) _ rest'); symmetry; exact Erec). lia.
      * remember (optimize_rules_concatN fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_concatN_vmaps : forall fuel n d rs n' d' rs',
  optimize_rules_concatN fuel n d rs = (n', d', rs') -> sd_vmaps d' = sd_vmaps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_concatN_consSS in H.
      destruct (head_value2 r1) as [[[[[f1 a1] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concat_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concatN fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_concatN fuel (S n)
                       {| sd_sets := (setname n, map pack_tuple ((a1, b1) :: t :: ts'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_concatN fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_concatN_maps : forall fuel n d rs n' d' rs',
  optimize_rules_concatN fuel n d rs = (n', d', rs') -> sd_maps d' = sd_maps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_concatN_consSS in H.
      destruct (head_value2 r1) as [[[[[f1 a1] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concat_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concatN fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_concatN fuel (S n)
                       {| sd_sets := (setname n, map pack_tuple ((a1, b1) :: t :: ts'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_concatN fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_chain_concatN_mono : forall n d c n' d' c',
  optimize_chain_concatN n d c = (n', d', c') -> n <= n'.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_concatN in H.
  destruct (optimize_rules_concatN (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_concatN_mono _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_concatN_vmaps : forall n d c n' d' c',
  optimize_chain_concatN n d c = (n', d', c') -> sd_vmaps d' = sd_vmaps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_concatN in H.
  destruct (optimize_rules_concatN (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_concatN_vmaps _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_concatN_maps : forall n d c n' d' c',
  optimize_chain_concatN n d c = (n', d', c') -> sd_maps d' = sd_maps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_concatN in H.
  destruct (optimize_rules_concatN (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_concatN_maps _ _ _ _ _ _ _ E).
Qed.

(** concatN mints [setname]s bounded by [n']; needed to thread setname-freshness
    past concatN into the following concatM stage. *)
Lemma optimize_rules_concatN_keys_bound : forall fuel n d rs n' d' rs' k,
  optimize_rules_concatN fuel n d rs = (n', d', rs') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' k H Hin.
  - cbn in H. inversion H; subst. left; exact Hin.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst. left; exact Hin.
    + cbn in H. inversion H; subst. left; exact Hin.
    + rewrite optimize_rules_concatN_consSS in H.
      destruct (head_value2 r1) as [[[[[f1 a1] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concat_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concatN fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
        -- cbv zeta in H.
           remember (optimize_rules_concatN fuel (S n)
                       {| sd_sets := (setname n, map pack_tuple ((a1, b1) :: t :: ts'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'.
           destruct (IH (S n) _ rest' m'' dd'' rr'' k (eq_sym Erec) Hin) as [Hin_dn | Hlt].
           ++ cbn [sd_sets map] in Hin_dn. destruct Hin_dn as [Heq | Hin_d].
              ** apply setname_inj in Heq. subst k. right.
                 pose proof (optimize_rules_concatN_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec)). lia.
              ** left; exact Hin_d.
           ++ right; exact Hlt.
      * remember (optimize_rules_concatN fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
        subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
Qed.

Lemma optimize_chain_concatN_keys_bound : forall n d c n' d' c' k,
  optimize_chain_concatN n d c = (n', d', c') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  intros n d c n' d' c' k H Hin. unfold optimize_chain_concatN in H.
  destruct (optimize_rules_concatN (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  apply (optimize_rules_concatN_keys_bound _ _ _ _ _ _ _ k E Hin).
Qed.

(** ** concatM (the guarded transport-key concat pass, Optimize_ConcatM) seam facts,
    structurally identical to concatN (mints [setname]s, leaves [sd_vmaps]/[sd_maps]). *)
Lemma optimize_rules_concatM_mono : forall fuel n d rs n' d' rs',
  optimize_rules_concatM fuel n d rs = (n', d', rs') -> n <= n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; lia.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; lia.
    + cbn in H. inversion H; subst; lia.
    + rewrite optimize_rules_concatM_consSS in H.
      destruct (head_value2g r1) as [[[[[[f1 a1] gm] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concatg_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concatM fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_concatM fuel (S n) _ rest') as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n'.
           assert (S n <= m'')
             by (eapply (IH (S n) _ rest'); symmetry; exact Erec). lia.
      * remember (optimize_rules_concatM fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_concatM_vmaps : forall fuel n d rs n' d' rs',
  optimize_rules_concatM fuel n d rs = (n', d', rs') -> sd_vmaps d' = sd_vmaps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_concatM_consSS in H.
      destruct (head_value2g r1) as [[[[[[f1 a1] gm] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concatg_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concatM fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_concatM fuel (S n)
                       {| sd_sets := (setname n, map pack_tuple ((a1, b1) :: t :: ts'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_concatM fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_concatM_maps : forall fuel n d rs n' d' rs',
  optimize_rules_concatM fuel n d rs = (n', d', rs') -> sd_maps d' = sd_maps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_concatM_consSS in H.
      destruct (head_value2g r1) as [[[[[[f1 a1] gm] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concatg_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concatM fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_concatM fuel (S n)
                       {| sd_sets := (setname n, map pack_tuple ((a1, b1) :: t :: ts'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_concatM fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_concatM_keys_bound : forall fuel n d rs n' d' rs' k,
  optimize_rules_concatM fuel n d rs = (n', d', rs') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' k H Hin.
  - cbn in H. inversion H; subst. left; exact Hin.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst. left; exact Hin.
    + cbn in H. inversion H; subst. left; exact Hin.
    + rewrite optimize_rules_concatM_consSS in H.
      destruct (head_value2g r1) as [[[[[[f1 a1] gm] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concatg_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concatM fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
        -- cbv zeta in H.
           remember (optimize_rules_concatM fuel (S n)
                       {| sd_sets := (setname n, map pack_tuple ((a1, b1) :: t :: ts'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'.
           destruct (IH (S n) _ rest' m'' dd'' rr'' k (eq_sym Erec) Hin) as [Hin_dn | Hlt].
           ++ cbn [sd_sets map] in Hin_dn. destruct Hin_dn as [Heq | Hin_d].
              ** apply setname_inj in Heq. subst k. right.
                 pose proof (optimize_rules_concatM_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec)). lia.
              ** left; exact Hin_d.
           ++ right; exact Hlt.
      * remember (optimize_rules_concatM fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
        subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
Qed.

Lemma optimize_chain_concatM_mono : forall n d c n' d' c',
  optimize_chain_concatM n d c = (n', d', c') -> n <= n'.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_concatM in H.
  destruct (optimize_rules_concatM (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_concatM_mono _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_concatM_vmaps : forall n d c n' d' c',
  optimize_chain_concatM n d c = (n', d', c') -> sd_vmaps d' = sd_vmaps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_concatM in H.
  destruct (optimize_rules_concatM (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_concatM_vmaps _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_concatM_maps : forall n d c n' d' c',
  optimize_chain_concatM n d c = (n', d', c') -> sd_maps d' = sd_maps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_concatM in H.
  destruct (optimize_rules_concatM (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_concatM_maps _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_concatM_keys_bound : forall n d c n' d' c' k,
  optimize_chain_concatM n d c = (n', d', c') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  intros n d c n' d' c' k H Hin. unfold optimize_chain_concatM in H.
  destruct (optimize_rules_concatM (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  apply (optimize_rules_concatM_keys_bound _ _ _ _ _ _ _ k E Hin).
Qed.

(** ** setg (the guarded single-field value->set pass, Optimize_Setg) seam facts,
    structurally identical to concatM (mints [setname]s, leaves [sd_vmaps]/[sd_maps]). *)
Lemma optimize_rules_setg_mono : forall fuel n d rs n' d' rs',
  optimize_rules_setg fuel n d rs = (n', d', rs') -> n <= n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; lia.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; lia.
    + cbn in H. inversion H; subst; lia.
    + rewrite optimize_rules_setg_consSS in H.
      destruct (head_valueGs r1) as [[[[gm f] v1] body] |] eqn:Ehd.
      * destruct (take_setg_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct vs as [| v vs'].
        -- remember (optimize_rules_setg fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_setg fuel (S n) _ rest') as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n'.
           assert (S n <= m'')
             by (eapply (IH (S n) _ rest'); symmetry; exact Erec). lia.
      * remember (optimize_rules_setg fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_setg_vmaps : forall fuel n d rs n' d' rs',
  optimize_rules_setg fuel n d rs = (n', d', rs') -> sd_vmaps d' = sd_vmaps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_setg_consSS in H.
      destruct (head_valueGs r1) as [[[[gm f] v1] body] |] eqn:Ehd.
      * destruct (take_setg_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct vs as [| v vs'].
        -- remember (optimize_rules_setg fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_setg fuel (S n)
                       {| sd_sets := (setname n, map (fun v0 => (v0, v0)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_setg fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_setg_maps : forall fuel n d rs n' d' rs',
  optimize_rules_setg fuel n d rs = (n', d', rs') -> sd_maps d' = sd_maps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_setg_consSS in H.
      destruct (head_valueGs r1) as [[[[gm f] v1] body] |] eqn:Ehd.
      * destruct (take_setg_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct vs as [| v vs'].
        -- remember (optimize_rules_setg fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_setg fuel (S n)
                       {| sd_sets := (setname n, map (fun v0 => (v0, v0)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_setg fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_setg_keys_bound : forall fuel n d rs n' d' rs' k,
  optimize_rules_setg fuel n d rs = (n', d', rs') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' k H Hin.
  - cbn in H. inversion H; subst. left; exact Hin.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst. left; exact Hin.
    + cbn in H. inversion H; subst. left; exact Hin.
    + rewrite optimize_rules_setg_consSS in H.
      destruct (head_valueGs r1) as [[[[gm f] v1] body] |] eqn:Ehd.
      * destruct (take_setg_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct vs as [| v vs'].
        -- remember (optimize_rules_setg fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
        -- cbv zeta in H.
           remember (optimize_rules_setg fuel (S n)
                       {| sd_sets := (setname n, map (fun v0 => (v0, v0)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'.
           destruct (IH (S n) _ rest' m'' dd'' rr'' k (eq_sym Erec) Hin) as [Hin_dn | Hlt].
           ++ cbn [sd_sets map] in Hin_dn. destruct Hin_dn as [Heq | Hin_d].
              ** apply setname_inj in Heq. subst k. right.
                 pose proof (optimize_rules_setg_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec)). lia.
              ** left; exact Hin_d.
           ++ right; exact Hlt.
      * remember (optimize_rules_setg fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
        subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
Qed.

Lemma optimize_chain_setg_mono : forall n d c n' d' c',
  optimize_chain_setg n d c = (n', d', c') -> n <= n'.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_setg in H.
  destruct (optimize_rules_setg (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_setg_mono _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_setg_vmaps : forall n d c n' d' c',
  optimize_chain_setg n d c = (n', d', c') -> sd_vmaps d' = sd_vmaps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_setg in H.
  destruct (optimize_rules_setg (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_setg_vmaps _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_setg_maps : forall n d c n' d' c',
  optimize_chain_setg n d c = (n', d', c') -> sd_maps d' = sd_maps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_setg in H.
  destruct (optimize_rules_setg (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_setg_maps _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_setg_keys_bound : forall n d c n' d' c' k,
  optimize_chain_setg n d c = (n', d', c') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  intros n d c n' d' c' k H Hin. unfold optimize_chain_setg in H.
  destruct (optimize_rules_setg (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  apply (optimize_rules_setg_keys_bound _ _ _ _ _ _ _ k E Hin).
Qed.

(** ** vmapNg (the guarded single-selector value+verdict->vmap pass, Optimize_Vmapg)
    seam facts, structurally identical to vmapN (mints [vmapname]s onto [sd_vmaps],
    leaves [sd_sets]/[sd_maps]). *)
Lemma optimize_rules_vmapNg_mono : forall fuel n d rs n' d' rs',
  optimize_rules_vmapNg fuel n d rs = (n', d', rs') -> n <= n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; lia.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; lia.
    + cbn in H. inversion H; subst; lia.
    + rewrite optimize_rules_vmapNg_consSS in H.
      destruct (head_valueGs r1) as [[[[gm f] v1] body] |] eqn:Ehd.
      * destruct (take_vmapG_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_vmapNg fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           ++ cbv zeta in H.
              remember (optimize_rules_vmapNg fuel (S n) _ rest') as tt eqn:Erec.
              destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
              injection H as Hn' Hd' Hr'. subst n'.
              assert (S n <= m'')
                by (eapply (IH (S n) _ rest'); symmetry; exact Erec). lia.
           ++ remember (optimize_rules_vmapNg fuel n d (r2 :: rest)) as tt eqn:Erec.
              destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
              eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
      * remember (optimize_rules_vmapNg fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_vmapNg_sets : forall fuel n d rs n' d' rs',
  optimize_rules_vmapNg fuel n d rs = (n', d', rs') -> sd_sets d' = sd_sets d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_vmapNg_consSS in H.
      destruct (head_valueGs r1) as [[[[gm f] v1] body] |] eqn:Ehd.
      * destruct (take_vmapG_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_vmapNg fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           ++ cbv zeta in H.
              remember (optimize_rules_vmapNg fuel (S n)
                          {| sd_sets := sd_sets d;
                             sd_vmaps := (vmapname n,
                               map vmap_pt ((v1, r_verdict r1) :: e :: es')) :: sd_vmaps d;
                             sd_maps := sd_maps d |} rest') as tt eqn:Erec.
              destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
              injection H as Hn' Hd' Hr'. subst d'.
              rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
           ++ remember (optimize_rules_vmapNg fuel n d (r2 :: rest)) as tt eqn:Erec.
              destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
              eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
      * remember (optimize_rules_vmapNg fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_vmapNg_maps : forall fuel n d rs n' d' rs',
  optimize_rules_vmapNg fuel n d rs = (n', d', rs') -> sd_maps d' = sd_maps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_vmapNg_consSS in H.
      destruct (head_valueGs r1) as [[[[gm f] v1] body] |] eqn:Ehd.
      * destruct (take_vmapG_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_vmapNg fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           ++ cbv zeta in H.
              remember (optimize_rules_vmapNg fuel (S n)
                          {| sd_sets := sd_sets d;
                             sd_vmaps := (vmapname n,
                               map vmap_pt ((v1, r_verdict r1) :: e :: es')) :: sd_vmaps d;
                             sd_maps := sd_maps d |} rest') as tt eqn:Erec.
              destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
              injection H as Hn' Hd' Hr'. subst d'.
              rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
           ++ remember (optimize_rules_vmapNg fuel n d (r2 :: rest)) as tt eqn:Erec.
              destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
              eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
      * remember (optimize_rules_vmapNg fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_vmapNg_keys_bound : forall fuel n d rs n' d' rs' k,
  optimize_rules_vmapNg fuel n d rs = (n', d', rs') ->
  In (vmapname k) (map fst (sd_vmaps d')) ->
  In (vmapname k) (map fst (sd_vmaps d)) \/ k < n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' k H Hin.
  - cbn in H. inversion H; subst. left; exact Hin.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst. left; exact Hin.
    + cbn in H. inversion H; subst. left; exact Hin.
    + rewrite optimize_rules_vmapNg_consSS in H.
      destruct (head_valueGs r1) as [[[[gm f] v1] body] |] eqn:Ehd.
      * destruct (take_vmapG_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_vmapNg fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
        -- destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           ++ cbv zeta in H.
              remember (optimize_rules_vmapNg fuel (S n)
                          {| sd_sets := sd_sets d;
                             sd_vmaps := (vmapname n,
                               map vmap_pt ((v1, r_verdict r1) :: e :: es')) :: sd_vmaps d;
                             sd_maps := sd_maps d |} rest') as tt eqn:Erec.
              destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
              subst n' d' rs'.
              destruct (IH (S n) _ rest' m'' dd'' rr'' k (eq_sym Erec) Hin) as [Hin_dn | Hlt].
              ** cbn [sd_vmaps map] in Hin_dn. destruct Hin_dn as [Heq | Hin_d].
                 --- apply vmapname_inj in Heq. subst k. right.
                     pose proof (optimize_rules_vmapNg_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec)). lia.
                 --- left; exact Hin_d.
              ** right; exact Hlt.
           ++ remember (optimize_rules_vmapNg fuel n d (r2 :: rest)) as tt eqn:Erec.
              destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
              subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
      * remember (optimize_rules_vmapNg fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
        subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
Qed.

Lemma optimize_chain_vmapNg_mono : forall n d c n' d' c',
  optimize_chain_vmapNg n d c = (n', d', c') -> n <= n'.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_vmapNg in H.
  destruct (optimize_rules_vmapNg (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_vmapNg_mono _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_vmapNg_sets : forall n d c n' d' c',
  optimize_chain_vmapNg n d c = (n', d', c') -> sd_sets d' = sd_sets d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_vmapNg in H.
  destruct (optimize_rules_vmapNg (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_vmapNg_sets _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_vmapNg_maps : forall n d c n' d' c',
  optimize_chain_vmapNg n d c = (n', d', c') -> sd_maps d' = sd_maps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_vmapNg in H.
  destruct (optimize_rules_vmapNg (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_vmapNg_maps _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_vmapNg_keys_bound : forall n d c n' d' c' k,
  optimize_chain_vmapNg n d c = (n', d', c') ->
  In (vmapname k) (map fst (sd_vmaps d')) ->
  In (vmapname k) (map fst (sd_vmaps d)) \/ k < n'.
Proof.
  intros n d c n' d' c' k H Hin. unfold optimize_chain_vmapNg in H.
  destruct (optimize_rules_vmapNg (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  apply (optimize_rules_vmapNg_keys_bound _ _ _ _ _ _ _ k E Hin).
Qed.

(** ** Structural facts about clean rules: their bodies are matches-only and read
    NO set name (every clean matchcond is value/range, [mc_set_name = None]). *)

Definition rule_lookup_vmapN_ok (r : rule) : Prop :=
  rule_clean r = true
  \/ (head_value r = None
      /\ body_only_matches (r_body r) = true
      /\ rule_vmap_name r = []).

Definition rs_vmapN_ok (rs : list rule) : Prop := Forall rule_lookup_vmapN_ok rs.

(** A run-head rule ([head_value = Some]) under the ok-predicate is CLEAN. *)
Lemma optimize_rules_setsN_keys_bound : forall fuel n d rs n' d' rs' k,
  optimize_rules_setsN fuel n d rs = (n', d', rs') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' k H Hin.
  - cbn in H. inversion H; subst. left; exact Hin.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst. left; exact Hin.
    + cbn in H. inversion H; subst. left; exact Hin.
    + rewrite optimize_rules_setsN_consSS in H.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_value_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct vs as [| v vs'].
        -- remember (optimize_rules_setsN fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hin].
        -- cbv zeta in H.
           remember (optimize_rules_setsN fuel (S n)
                       {| sd_sets := (setname n, map (fun w => (w,w)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           destruct (IH (S n) _ rest' m'' dd'' rr'' k (eq_sym Erec) Hin) as [Hin_dn | Hlt].
           ++ cbn [sd_sets map] in Hin_dn. destruct Hin_dn as [Heq | Hin_d].
              ** apply setname_inj in Heq. subst k. right.
                 pose proof (optimize_rules_setsN_mono fuel (S n) _ rest' m'' dd'' rr''
                               (eq_sym Erec)) as Hmono. lia.
              ** left; exact Hin_d.
           ++ right; exact Hlt.
      * remember (optimize_rules_setsN fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hin].
Qed.

Lemma optimize_chain_setsN_keys_bound : forall n d c n' d' c' k,
  optimize_chain_setsN n d c = (n', d', c') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  intros n d c n' d' c' k H Hin. unfold optimize_chain_setsN in H.
  destruct (optimize_rules_setsN (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  apply (optimize_rules_setsN_keys_bound _ _ _ _ _ _ _ k E Hin).
Qed.

(* 2. Freshness TRANSFER across setsN: an [n]-fresh setname namespace stays
      [n']-fresh in the output decls (the minted names all lie below n'). *)
Lemma optimize_chain_setsN_fresh_setname : forall n d c n' d' c',
  optimize_chain_setsN n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  (forall k, n' <= k -> ~ In (setname k) (map fst (sd_sets d'))).
Proof.
  intros n d c n' d' c' H Hfresh k Hk Hin.
  pose proof (optimize_chain_setsN_mono n d c n' d' c' H) as Hmono.
  destruct (optimize_chain_setsN_keys_bound n d c n' d' c' k H Hin) as [Hin_d | Hlt].
  - apply (Hfresh k); [lia | exact Hin_d].
  - lia.
Qed.

(* 3. setsN OUTPUT is [rs_vmapN_ok]: each output rule is clean, or a merged
      single-field [MConcatSet] lookup rule (head_value = None, matches-only body,
      no vmap) -- the right disjunct of [rule_lookup_vmapN_ok]. *)