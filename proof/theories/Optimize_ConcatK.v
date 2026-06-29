(** * Optimize_ConcatK: the N-FIELD ([K>=1]) concatenation-set membership certificate
    — groundwork for the N-dimensional concat merge (TODO 1b).

    [Optimize_Concat] handles exactly TWO selectors ([pack2],
    [concat_in_iv_two_points]).  The kernel's [Bytes.concat_in_iv] is ALREADY N-ary
    (it splits the stored bound by per-field register slots), so only the PACKER and
    the membership certificate are 2-bound.  Here [packN] lays each field in its own
    4-byte register slot (last field takes the remainder), and [concat_in_iv_pointsN]
    proves a packed POINT key is matched by a per-field value list iff EVERY field
    equals its stored value — the literal K-way conjunction generalising
    [concat_in_iv_two_points].  Axiom-free. *)

From Stdlib Require Import List PeanoNat Bool Lia Wellfounded Arith.Wf_nat.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics Optimize Optimize_Merge Optimize_Concat.
Import ListNotations.
Local Open Scope nat_scope.

Lemma existsb_map_local : forall (A B : Type) (f : B -> bool) (g : A -> B) (l : list A),
  existsb f (map g l) = existsb (fun x => f (g x)) l.
Proof. induction l as [| x l IH]; cbn [map existsb]; [reflexivity | rewrite IH; reflexivity]. Qed.

(** Pack field values into a concatenation key: each field in its own register slot
    ([pad_slot], width [reg_slot]); the LAST field takes the remainder (no padding),
    mirroring [split_by]'s last-takes-all and the kernel layout.  [packN [a;b] =
    pack2 a b]. *)
Fixpoint packN (vs : list data) : data :=
  match vs with
  | [] => []
  | [v] => v
  | v :: vs => pad_slot v ++ packN vs
  end.

Lemma packN_two : forall a b, packN [a; b] = pack2 a b.
Proof. reflexivity. Qed.

(** A point-bound field test is byte equality: [field_in_iv v (a,a) = data_eqb v a]
    (both [<=] collapse by [data_le_antisym]). *)
Lemma field_in_iv_point_eq : forall v a, field_in_iv v (a, a) = data_eqb v a.
Proof.
  intros v a. unfold field_in_iv. cbn [fst snd].
  rewrite data_le_antisym. apply data_eqb_sym.
Qed.

(** The K-way conjunction: [vals] all equal [avs] pairwise. *)
Fixpoint all_data_eqb (vals avs : list data) : bool :=
  match vals, avs with
  | [], [] => true
  | v :: vs, a :: as_ => data_eqb v a && all_data_eqb vs as_
  | _, _ => false
  end.

(** The general-branch forallb of [concat_in_iv] over [packN avs], proved DIRECTLY
    by induction on the field list (so we never route the tail through
    [concat_in_iv]'s singleton/general dispatch). *)
Lemma concat_match_packN : forall vals avs,
  Forall2 (fun v a => length v = length a) vals avs ->
  forallb (fun t => let '(val, (lo, hi)) := t in
             field_in_iv val (firstn (length val) lo, firstn (length val) hi))
          (combine vals
             (combine (split_by (map (fun v => reg_slot (length v)) vals) (packN avs))
                      (split_by (map (fun v => reg_slot (length v)) vals) (packN avs))))
  = all_data_eqb vals avs.
Proof.
  induction vals as [| v vals IH]; intros avs Hf2.
  - inversion Hf2; subst. reflexivity.
  - inversion Hf2 as [| ? a ? as_ Hva Hrest Heq1 Heq2]; subst.
    destruct vals as [| v2 vals].
    + (* last (only) field: split_by [_] (packN [a]) = [a] *)
      inversion Hrest; subst. cbn [map split_by combine forallb packN].
      rewrite Bool.andb_true_r, firstn_all2 by lia.
      cbn [all_data_eqb]. rewrite Bool.andb_true_r, field_in_iv_point_eq. reflexivity.
    + (* non-last field [v]: slots has >=2 entries, packN avs = pad_slot a ++ packN tail *)
      assert (Has : as_ <> []) by (intro Hc; subst as_; inversion Hrest).
      destruct as_ as [| a2 as_]; [contradiction|].
      cbn [map]. cbn [packN].
      (* split_by (reg_slot(len v) :: slots_rest) (pad_slot a ++ packN (a2::as_)) *)
      cbn [split_by].
      assert (Hw : reg_slot (length v) = length (pad_slot a))
        by (rewrite pad_slot_len, Hva; reflexivity).
      rewrite Hw.
      rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all.
      rewrite skipn_app, Nat.sub_diag, skipn_O, skipn_all2 by lia.
      cbn [app combine forallb].
      (* head field-test: firstn (len v) (pad_slot a) = a, then point equality *)
      rewrite Hva, pad_slot_firstn, field_in_iv_point_eq.
      cbn [all_data_eqb]. f_equal.
      (* tail = the same forallb over the remaining fields = IH *)
      exact (IH (a2 :: as_) Hrest).
Qed.

(** *** The N-field membership certificate at a packed POINT key: a stored element
    [(packN avs, packN avs)] is matched by [vals] iff every field equals its stored
    value, when the fields are pairwise length-matched. *)
Lemma concat_in_iv_pointsN : forall vals avs,
  Forall2 (fun v a => length v = length a) vals avs ->
  vals <> [] ->
  concat_in_iv vals (packN avs, packN avs) = all_data_eqb vals avs.
Proof.
  intros vals avs Hf2 Hne.
  destruct vals as [| v1 vals]; [contradiction|].
  destruct vals as [| v2 vals].
  - (* single field: concat_in_iv [v] uses the singleton branch = field_in_iv v *)
    inversion Hf2 as [| ? a1 ? as_ Hva Hrest]; subst.
    inversion Hrest; subst. cbn [concat_in_iv all_data_eqb].
    change (packN [a1]) with a1. rewrite Bool.andb_true_r.
    apply field_in_iv_point_eq.
  - (* >=2 fields: concat_in_iv uses the general branch = concat_match_packN *)
    unfold concat_in_iv at 1. cbn [fst snd].
    exact (concat_match_packN (v1 :: v2 :: vals) avs Hf2).
Qed.

(* ================================================================== *)
(** ** Matchcond-level certificate: the merged [MConcatSet] head over K fields,
    when its name resolves to packed POINT rows, tests exactly the [existsb] over
    rows of the per-field [MCmp f_i CEq a_i] conjunction. *)

(** A packed point row as a stored set element. *)
Definition pack_row (row : list data) : data * data := (packN row, packN row).

(** On a row whose fields all LOAD and length-match, the byte-equality conjunction
    [all_data_eqb] over the field values equals the [forallb] of the per-field
    [MCmp] tests. *)
Lemma all_data_eqb_mcmp : forall fields row q,
  Forall2 (fun f a => field_loadable f q = true /\ length (field_value f q) = length a) fields row ->
  all_data_eqb (map (fun f => field_value f q) fields) row
  = forallb (fun fa => eval_matchcond (MCmp (fst fa) CEq (snd fa)) q) (combine fields row).
Proof.
  intros fields row q Hf2. induction Hf2 as [| f a fl rl HR Htl IH]; [reflexivity|].
  destruct HR as [Hld Hlen].
  cbn [map all_data_eqb combine forallb fst snd].
  rewrite (eval_mcmp_point f a q Hld Hlen), IH. reflexivity.
Qed.

(** If some field does not load, every row's per-field conjunction is [false]. *)
Lemma forallb_mcmp_unload : forall fields row q,
  fields_loadable fields q = false ->
  length fields = length row ->
  forallb (fun fa => eval_matchcond (MCmp (fst fa) CEq (snd fa)) q) (combine fields row) = false.
Proof.
  induction fields as [| f fields IH]; intros row q Hfl Hlen.
  - cbn in Hfl. discriminate.
  - destruct row as [| a row]; [cbn in Hlen; discriminate|].
    cbn [combine forallb fst snd].
    unfold fields_loadable in Hfl. cbn [forallb] in Hfl.
    apply Bool.andb_false_iff in Hfl as [Hf | Hfs].
    + rewrite (eval_mcmp_point_unload f a q Hf). reflexivity.
    + rewrite (IH row q Hfs ltac:(cbn in Hlen; lia)). apply Bool.andb_false_r.
Qed.

(** From fixed-width fields that all LOAD, the per-field loadable+length facts.
    The loadability premise is introduced AFTER the induction, so it specialises to
    each tail (avoiding the dependent-hypothesis pitfall). *)
Lemma cert_loadable_facts : forall (fields : list field) (row : list data) q,
  Forall2 (fun f a => field_fixed_len f = Some (length a)) fields row ->
  (forall f, In f fields -> field_loadable f q = true) ->
  Forall2 (fun f a => field_loadable f q = true /\ length (field_value f q) = length a) fields row.
Proof.
  intros fields row q Hwf. induction Hwf as [| f a fs rs Hfx Hrest IH]; intro Hfl'; [constructor|].
  constructor.
  - split; [apply Hfl'; left; reflexivity
           | apply (field_fixed_len_loaded f (length a) q Hfx), Hfl'; left; reflexivity].
  - apply IH. intros f' Hf'. apply Hfl'; right; exact Hf'.
Qed.

Lemma forall2_pair_to_lenmap : forall (fields : list field) (row : list data) q,
  Forall2 (fun f a => field_loadable f q = true /\ length (field_value f q) = length a) fields row ->
  Forall2 (fun v a => length v = length a) (map (fun f => field_value f q) fields) row.
Proof.
  intros fields row q H.
  induction H as [| f a fs rs [_ Hlen] Hrest IH]; cbn [map]; constructor;
    [exact Hlen | exact IH].
Qed.

Lemma concat_fields_certificate_N : forall fields rows name q,
  fields <> [] ->
  e_set (pkt_env q) name = map pack_row rows ->
  (forall row, In row rows ->
     Forall2 (fun f a => field_fixed_len f = Some (length a)) fields row) ->
  eval_matchcond (MConcatSet fields false name) q
  = existsb (fun row => forallb (fun fa => eval_matchcond (MCmp (fst fa) CEq (snd fa)) q)
                                (combine fields row)) rows.
Proof.
  intros fields rows name q Hne Hset Hwf.
  unfold eval_matchcond at 1, eval_matchcond_body at 1, match_loadable.
  cbn [andb]. rewrite Bool.xorb_false_l.
  assert (Hfl' : fields_loadable fields q = true ->
                 forall f, In f fields -> field_loadable f q = true).
  { intros Hfl f Hf. unfold fields_loadable in Hfl. rewrite forallb_forall in Hfl.
    apply Hfl, Hf. }
  destruct (fields_loadable fields q) eqn:Hfl; cbn [andb].
  - (* all fields load: membership = existsb of the byte-equality conjunctions *)
    rewrite Hset. unfold concat_set_mem. rewrite existsb_map_local.
    apply existsb_ext. intros row Hin. unfold pack_row.
    pose proof (cert_loadable_facts fields row q (Hwf row Hin) (Hfl' eq_refl)) as Hfacts.
    rewrite (concat_in_iv_pointsN (map (fun f => field_value f q) fields) row
               (forall2_pair_to_lenmap fields row q Hfacts)
               ltac:(intro Hc; apply map_eq_nil in Hc; contradiction)).
    apply all_data_eqb_mcmp; exact Hfacts.
  - (* some field does not load: both sides false *)
    symmetry. apply existsb_false_forall. intros row Hin.
    apply forallb_mcmp_unload; [exact Hfl |].
    apply Forall2_length with (1 := Hwf row Hin).
Qed.

(* ================================================================== *)
(** ** The eval_rules-level N-field concat merge.

    [merged_ruleK] has ONE head — the concat set over [fields] — atop the shared
    [body]; each [orig_ruleK fields row body r1] has K head matches (one [MCmp f_i
    CEq a_i] per field) atop the SAME body/end.  The K-match prefix is transparent
    to synproxy/notrack/thread and contributes its loadability/applicability
    value-independently, so all rows share one loadability + outcome; the merged
    rule's applicability is the [existsb] the matchcond certificate pins down.  Via
    [eval_rules_run_collapse] the merged rule replaces the whole run. *)

Definition kmatches (fields : list field) (row : list data) : list body_item :=
  map (fun fa => BMatch (MCmp (fst fa) CEq (snd fa))) (combine fields row).

Definition orig_ruleK (fields : list field) (row : list data)
                      (body : list body_item) (r1 : rule) : rule :=
  {| r_body := kmatches fields row ++ body;
     r_verdict := r_verdict r1; r_vmap := r_vmap r1; r_nat := r_nat r1;
     r_tproxy := r_tproxy r1; r_fwd := r_fwd r1; r_queue := r_queue r1;
     r_after := r_after r1 |}.

Definition merged_ruleK (fields : list field) (name : String.string)
                        (body : list body_item) (r1 : rule) : rule :=
  mk_head (MConcatSet fields false name) body r1.

(** *** The K-match prefix is transparent to synproxy/notrack/thread. *)
Lemma kmatches_synproxy : forall fields row body p,
  body_synproxy_stops (kmatches fields row ++ body) p = body_synproxy_stops body p.
Proof.
  intros fields row body p. unfold kmatches.
  induction (combine fields row) as [| fa l IH]; [reflexivity|].
  cbn [map app]. rewrite synproxy_stops_bmatch. exact IH.
Qed.

Lemma kmatches_notrack : forall fields row body,
  body_has_notrack (kmatches fields row ++ body) = body_has_notrack body.
Proof.
  intros fields row body. unfold kmatches.
  induction (combine fields row) as [| fa l IH]; [reflexivity|].
  cbn [map app]. rewrite has_notrack_bmatch. exact IH.
Qed.

Lemma kmatches_thread : forall fields row body p,
  body_thread (kmatches fields row ++ body) p = body_thread body p.
Proof. intros. unfold body_thread. rewrite kmatches_notrack. reflexivity. Qed.

(** Loadability of the prefix++body: each head match contributes [field_loadable],
    value-independently. *)
Lemma kmatches_loadable_walk : forall fields row body p,
  body_loadable_walk (kmatches fields row ++ body) p
  = forallb (fun fa => field_loadable (fst fa) p) (combine fields row)
    && body_loadable_walk body p.
Proof.
  intros fields row body p. unfold kmatches.
  induction (combine fields row) as [| fa l IH]; [reflexivity|].
  cbn [map app forallb body_loadable_walk body_item_loadable match_loadable].
  rewrite IH, Bool.andb_assoc. reflexivity.
Qed.

Lemma kmatches_applies_walk : forall fields row body p,
  rule_applies_walk (kmatches fields row ++ body) p
  = forallb (fun fa => eval_matchcond (MCmp (fst fa) CEq (snd fa)) p) (combine fields row)
    && rule_applies_walk body p.
Proof.
  intros fields row body p. unfold kmatches.
  induction (combine fields row) as [| fa l IH]; [reflexivity|].
  cbn [map app forallb rule_applies_walk].
  rewrite IH, Bool.andb_assoc. reflexivity.
Qed.

(** [field_loadable] over [combine fields row] = [fields_loadable fields] when the
    two have equal length (so [map fst (combine fields row) = fields]). *)
Lemma forallb_field_loadable_combine : forall (fields : list field) (row : list data) p,
  length fields = length row ->
  forallb (fun fa => field_loadable (fst fa) p) (combine fields row)
  = fields_loadable fields p.
Proof.
  induction fields as [| f fs IH]; intros [| a row] p Hlen; try (cbn in Hlen; discriminate);
    [reflexivity|].
  cbn [combine forallb fst]. unfold fields_loadable. cbn [forallb].
  rewrite (IH row p ltac:(cbn in Hlen; lia)). reflexivity.
Qed.

(** orig_ruleK's loadability / outcome are VALUE-INDEPENDENT (head matches only
    contribute field loadability + are transparent to outcome). *)
Lemma orig_ruleK_loadable : forall fields row body r1 p,
  length fields = length row ->
  rule_loadable (orig_ruleK fields row body r1) p
  = fields_loadable fields p &&
    (body_loadable_walk body p &&
     (if body_synproxy_stops body p then true else end_loadable r1 (body_thread body p))).
Proof.
  intros fields row body r1 p Hlen. unfold rule_loadable, orig_ruleK. cbn [r_body].
  rewrite kmatches_loadable_walk, kmatches_synproxy, kmatches_thread.
  rewrite (forallb_field_loadable_combine fields row p Hlen).
  (* end_loadable of the record = end_loadable r1 (it copies the end fields) *)
  assert (Hend : forall q, end_loadable (orig_ruleK fields row body r1) q = end_loadable r1 q)
    by reflexivity.
  rewrite <- Bool.andb_assoc.
  destruct (body_synproxy_stops body p); reflexivity.
Qed.

Lemma merged_ruleK_loadable : forall fields name body r1 p,
  rule_loadable (merged_ruleK fields name body r1) p
  = fields_loadable fields p &&
    (body_loadable_walk body p &&
     (if body_synproxy_stops body p then true else end_loadable r1 (body_thread body p))).
Proof.
  intros fields name body r1 p. unfold merged_ruleK. rewrite rule_loadable_mk_head.
  cbn [match_loadable]. reflexivity.
Qed.

Lemma orig_ruleK_outcome : forall fields row body r1 p,
  outcome (orig_ruleK fields row body r1) p
  = (if body_synproxy_stops body p then Some Drop
     else outcome_core r1 (body_thread body p)).
Proof.
  intros fields row body r1 p. unfold outcome, orig_ruleK. cbn [r_body].
  rewrite kmatches_synproxy, kmatches_thread.
  assert (Hoc : outcome_core (orig_ruleK fields row body r1) (body_thread body p)
                = outcome_core r1 (body_thread body p)) by reflexivity.
  unfold orig_ruleK in Hoc. cbn [r_body] in Hoc.
  destruct (body_synproxy_stops body p); [reflexivity|]. exact Hoc.
Qed.

Lemma merged_ruleK_outcome : forall fields name body r1 p,
  outcome (merged_ruleK fields name body r1) p
  = (if body_synproxy_stops body p then Some Drop
     else outcome_core r1 (body_thread body p)).
Proof. intros. unfold merged_ruleK. apply outcome_mk_head. Qed.

Lemma orig_ruleK_applies : forall fields row body r1 p,
  rule_applies (orig_ruleK fields row body r1) p
  = forallb (fun fa => eval_matchcond (MCmp (fst fa) CEq (snd fa)) p) (combine fields row)
    && rule_applies_walk body p.
Proof.
  intros fields row body r1 p. unfold rule_applies, orig_ruleK. cbn [r_body].
  apply kmatches_applies_walk.
Qed.

(** *** The K-field concat merge, verdict-preserving on every packet. *)
Theorem eval_rules_concat_mergeK : forall fields rows name body r1 rest p,
  fields <> [] -> rows <> [] ->
  e_set (pkt_env p) name = map pack_row rows ->
  (forall row, In row rows ->
     Forall2 (fun f a => field_fixed_len f = Some (length a)) fields row) ->
  eval_rules (merged_ruleK fields name body r1 :: rest) p
  = eval_rules (map (fun row => orig_ruleK fields row body r1) rows ++ rest) p.
Proof.
  intros fields rows name body r1 rest p Hfne Hrne Hset Hwf.
  (* every row has length = length fields (from the Forall2) *)
  assert (Hlenrow : forall row, In row rows -> length fields = length row)
    by (intros row Hin; apply (Forall2_length (Hwf row Hin))).
  set (LL := fields_loadable fields p &&
             (body_loadable_walk body p &&
              (if body_synproxy_stops body p then true
               else end_loadable r1 (body_thread body p)))).
  set (O := if body_synproxy_stops body p then Some Drop
            else outcome_core r1 (body_thread body p)).
  apply (eval_rules_run_collapse
           (map (fun row => orig_ruleK fields row body r1) rows) LL O
           (merged_ruleK fields name body r1) rest p).
  - (* run nonempty *)
    intro Hc. apply map_eq_nil in Hc. contradiction.
  - (* all rows: rule_loadable = LL *)
    intros r Hin. apply in_map_iff in Hin as [row [Heq Hin]]. subst r.
    unfold LL. apply (orig_ruleK_loadable fields row body r1 p (Hlenrow row Hin)).
  - (* all rows: outcome = O *)
    intros r Hin. apply in_map_iff in Hin as [row [Heq Hin]]. subst r.
    unfold O. apply orig_ruleK_outcome.
  - (* merged loadable = LL *)
    unfold LL. apply merged_ruleK_loadable.
  - (* merged outcome = O *)
    unfold O. apply merged_ruleK_outcome.
  - (* merged applies = existsb (orig applies) *)
    unfold merged_ruleK. rewrite rule_applies_mk_head.
    (* eval_matchcond (MConcatSet ..) = existsb (per-row K-conjunction)  [certificate] *)
    rewrite (concat_fields_certificate_N fields rows name p Hfne Hset Hwf).
    (* existsb (orig applies) = existsb ((K-conj) && walk) = (existsb K-conj) && walk *)
    rewrite (existsb_map_local _ _ (fun r => rule_applies r p)
                               (fun row => orig_ruleK fields row body r1) rows).
    symmetry.
    rewrite (existsb_ext _
               (fun row => rule_applies (orig_ruleK fields row body r1) p)
               (fun row => forallb (fun fa => eval_matchcond (MCmp (fst fa) CEq (snd fa)) p)
                                   (combine fields row) && rule_applies_walk body p)
               rows
               (fun row _ => orig_ruleK_applies fields row body r1 p)).
    apply existsb_andb_const.
Qed.

(* ================================================================== *)
(** ** The recogniser: extract a rule's maximal leading [MCmp _ CEq _] run. *)

Fixpoint take_mcmp_prefix (body : list body_item) : list (field * data) * list body_item :=
  match body with
  | BMatch (MCmp f CEq v) :: rest =>
      let '(ps, tl) := take_mcmp_prefix rest in ((f, v) :: ps, tl)
  | _ => ([], body)
  end.

(** [combine] of the projections recovers the pair list. *)
Lemma combine_fst_snd : forall (ps : list (field * data)),
  combine (map fst ps) (map snd ps) = ps.
Proof.
  induction ps as [| [f a] ps IH]; [reflexivity|]. cbn [map fst snd combine]. rewrite IH. reflexivity.
Qed.

(** [kmatches] over the projections is the raw [BMatch (MCmp …)] map. *)
Lemma kmatches_proj : forall (ps : list (field * data)),
  kmatches (map fst ps) (map snd ps)
  = map (fun fa => BMatch (MCmp (fst fa) CEq (snd fa))) ps.
Proof. intro ps. unfold kmatches. rewrite combine_fst_snd. reflexivity. Qed.

(** The prefix reconstructs the body. *)
Lemma take_mcmp_prefix_app : forall body ps tl,
  take_mcmp_prefix body = (ps, tl) ->
  body = map (fun fa => BMatch (MCmp (fst fa) CEq (snd fa))) ps ++ tl.
Proof.
  induction body as [| it body IH]; intros ps tl H.
  - cbn in H. inversion H; subst. reflexivity.
  - destruct it as [m | s].
    + destruct m as [ | | | | f op v | | | | | | | | ]; try (cbn in H; inversion H; subst; reflexivity).
      destruct op; try (cbn in H; inversion H; subst; reflexivity).
      cbn in H. destruct (take_mcmp_prefix body) as [ps0 tl0] eqn:E.
      inversion H; subst ps tl. cbn [map app fst snd].
      rewrite (IH ps0 tl0 eq_refl). reflexivity.
    + cbn in H. inversion H; subst. reflexivity.
Qed.

(** A record built from a body [b] and [r1]'s end fields. *)
Definition with_end (b : list body_item) (r1 : rule) : rule :=
  {| r_body := b; r_verdict := r_verdict r1; r_vmap := r_vmap r1; r_nat := r_nat r1;
     r_tproxy := r_tproxy r1; r_fwd := r_fwd r1; r_queue := r_queue r1;
     r_after := r_after r1 |}.

Lemma orig_ruleK_with_end : forall fields row body r1,
  orig_ruleK fields row body r1 = with_end (kmatches fields row ++ body) r1.
Proof. reflexivity. Qed.

(** A rule equals [with_end] of its OWN body and end fields (record eta). *)
Lemma with_end_self : forall r, with_end (r_body r) r = r.
Proof. intro r. unfold with_end. destruct r; reflexivity. Qed.

(** When [rule_end_eqb r1 r2] holds, [with_end b r1 = with_end b r2]. *)
Lemma with_end_end_eqb : forall b r1 r2,
  rule_end_eqb r1 r2 = true -> with_end b r1 = with_end b r2.
Proof.
  intros b r1 r2 H. unfold rule_end_eqb in H.
  rewrite !Bool.andb_true_iff in H. rewrite !sumbool_eqb_true_iff, !opt_eqb_true_iff in H.
  destruct H as [[[[[[Hv Hvm] Hn] Ht] Hf] Hq] Ha].
  unfold with_end. rewrite Hv, Hvm, Hn, Ht, Hf, Hq, Ha. reflexivity.
Qed.

(** If [r1]'s prefix is [(ps, body)] then [r1] is its own [orig_ruleK] shell over
    [fields = map fst ps], [row = map snd ps]. *)
Lemma head_self_orig : forall r1 ps body,
  take_mcmp_prefix (r_body r1) = (ps, body) ->
  r1 = orig_ruleK (map fst ps) (map snd ps) body r1.
Proof.
  intros r1 ps body H. rewrite orig_ruleK_with_end, kmatches_proj.
  rewrite <- (take_mcmp_prefix_app (r_body r1) ps body H).
  symmetry. apply with_end_self.
Qed.

(** Every prefix field is fixed-width and its stored value has that width. *)
Definition fields_fixed (ps : list (field * data)) : bool :=
  forallb (fun fa => match field_fixed_len (fst fa) with
                     | Some l => Nat.eqb l (length (snd fa)) | None => false end) ps.

Lemma fields_fixed_Forall2 : forall ps,
  fields_fixed ps = true ->
  Forall2 (fun f a => field_fixed_len f = Some (length a)) (map fst ps) (map snd ps).
Proof.
  induction ps as [| [f a] ps IH]; intro H; [constructor|].
  cbn [fields_fixed forallb fst snd] in H. apply Bool.andb_true_iff in H as [Hfa Hrest].
  cbn [map fst snd]. constructor.
  - destruct (field_fixed_len f) as [l|] eqn:E; [|discriminate].
    apply Nat.eqb_eq in Hfa. subst l. reflexivity.
  - apply (IH Hrest).
Qed.

(** Two rules form an eligible K-field (K>=3) concat-merge pair: same fields, same
    tail body, same end fields, both fixed-width.  Returns the shared fields, the
    two rows, and the shared body. *)
Definition concat_mergeK_pair (r1 r2 : rule)
  : option (list field * list data * list data * list body_item) :=
  let '(ps1, b1) := take_mcmp_prefix (r_body r1) in
  let '(ps2, b2) := take_mcmp_prefix (r_body r2) in
  if Nat.leb 3 (length ps1) then
  if list_eq_dec field_eq_dec (map fst ps1) (map fst ps2) then
  if list_eq_dec body_item_eq_dec b1 b2 then
  if fields_fixed ps1 then
  if fields_fixed ps2 then
  if rule_end_eqb r1 r2 then
    Some (map fst ps1, map snd ps1, map snd ps2, b1)
  else None else None else None else None else None else None.

Lemma concat_mergeK_pair_shape : forall r1 r2 fields row1 row2 body,
  concat_mergeK_pair r1 r2 = Some (fields, row1, row2, body) ->
  r1 = orig_ruleK fields row1 body r1 /\
  r2 = orig_ruleK fields row2 body r1 /\
  Forall2 (fun f a => field_fixed_len f = Some (length a)) fields row1 /\
  Forall2 (fun f a => field_fixed_len f = Some (length a)) fields row2 /\
  fields <> [] /\ 3 <= length fields.
Proof.
  intros r1 r2 fields row1 row2 body H. unfold concat_mergeK_pair in H.
  destruct (take_mcmp_prefix (r_body r1)) as [ps1 b1] eqn:E1.
  destruct (take_mcmp_prefix (r_body r2)) as [ps2 b2] eqn:E2.
  destruct (Nat.leb 3 (length ps1)) eqn:Hlen3; [|discriminate].
  destruct (list_eq_dec field_eq_dec (map fst ps1) (map fst ps2)) as [Hf|]; [|discriminate].
  destruct (list_eq_dec body_item_eq_dec b1 b2) as [Hb|]; [|discriminate].
  destruct (fields_fixed ps1) eqn:Hx1; [|discriminate].
  destruct (fields_fixed ps2) eqn:Hx2; [|discriminate].
  destruct (rule_end_eqb r1 r2) eqn:Hend; [|discriminate].
  injection H as Hfields Hrow1 Hrow2 Hbody. subst fields row1 row2 body.
  pose proof (head_self_orig r1 ps1 b1 E1) as Hr1.
  pose proof (head_self_orig r2 ps2 b2 E2) as Hr2.
  apply Nat.leb_le in Hlen3.
  repeat split.
  - exact Hr1.
  - rewrite Hr2, <- Hf, <- Hb, !orig_ruleK_with_end.
    symmetry. apply (with_end_end_eqb _ r1 r2 Hend).
  - apply (fields_fixed_Forall2 ps1 Hx1).
  - rewrite Hf. apply (fields_fixed_Forall2 ps2 Hx2).
  - intro Hc. apply (f_equal (@length field)) in Hc. rewrite length_map in Hc. cbn in Hc. lia.
  - rewrite length_map. exact Hlen3.
Qed.

(* ================================================================== *)
(** ** The executable pairwise K-field concat pass.

    On each adjacent eligible K(>=3)-field pair it mints a fresh [setname n],
    prepends the two packed rows to [sd_sets], and rewrites the pair into ONE
    [merged_ruleK] (a single [MConcatSet] head atop the shared body).  Mirrors the
    pairwise 2-field [Optimize_Concat.optimize_rules_concat]; correctness is
    [eval_rules_concat_mergeK] (with two rows). *)
Fixpoint optimize_rules_concatK (n : nat) (d : set_decls) (rs : list rule)
  : nat * set_decls * list rule :=
  match rs with
  | r1 :: ((r2 :: rest) as tl) =>
      match concat_mergeK_pair r1 r2 with
      | Some (fields, row1, row2, body) =>
          let name := setname n in
          let d' := {| sd_sets := (name, map pack_row [row1; row2]) :: sd_sets d;
                       sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
          let merged := merged_ruleK fields name body r1 in
          let '(n'', d'', rest') := optimize_rules_concatK (S n) d' rest in
          (n'', d'', merged :: rest')
      | None =>
          let '(n'', d'', tl') := optimize_rules_concatK n d tl in
          (n'', d'', r1 :: tl')
      end
  | _ => (n, d, rs)
  end.

Lemma optimize_rules_concatK_cons2 : forall n d r1 r2 rest,
  optimize_rules_concatK n d (r1 :: r2 :: rest) =
  match concat_mergeK_pair r1 r2 with
  | Some (fields, row1, row2, body) =>
      let name := setname n in
      let d' := {| sd_sets := (name, map pack_row [row1; row2]) :: sd_sets d;
                   sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
      let merged := merged_ruleK fields name body r1 in
      let '(n'', d'', rest') := optimize_rules_concatK (S n) d' rest in
      (n'', d'', merged :: rest')
  | None =>
      let '(n'', d'', tl') := optimize_rules_concatK n d (r2 :: rest) in
      (n'', d'', r1 :: tl')
  end.
Proof. reflexivity. Qed.

Definition optimize_chain_concatK (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n', d', rs') := optimize_rules_concatK n d (c_rules c) in
  (n', d', {| c_policy := c_policy c; c_rules := rs' |}).

(** The pass only PREPENDS [sd_sets] entries keyed by [setname k], n <= k < n', and
    leaves [sd_vmaps] / [sd_maps] untouched. *)
Lemma optimize_rules_concatK_assoc_stable : forall rs n d n' d' rs' nm X,
  optimize_rules_concatK n d rs = (n', d', rs') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X = assoc_str nm (sd_sets d) X.
Proof.
  induction rs as [rs H0] using (induction_ltof1 _ (@length rule)).
  intros n d n' d' rs' nm X H Hnm.
  destruct rs as [| r1 [| r2 rest] ].
  - cbn in H. inversion H; subst; reflexivity.
  - cbn in H. inversion H; subst; reflexivity.
  - rewrite optimize_rules_concatK_cons2 in H. cbv zeta in H.
    destruct (concat_mergeK_pair r1 r2) as [[[[fields row1] row2] body] |] eqn:Em.
    + destruct (optimize_rules_concatK (S n)
                  {| sd_sets := (setname n, map pack_row [row1; row2]) :: sd_sets d;
                     sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest)
        as [[m'' dd''] rr''] eqn:Erec.
      inversion H; subst n' d' rs'. clear H.
      erewrite (H0 rest); [ | unfold ltof; cbn; lia | exact Erec | ].
      * cbn [sd_sets assoc_str].
        destruct (String.eqb nm (setname n)) eqn:Eqn.
        -- apply String.eqb_eq in Eqn. exfalso. apply (Hnm n); [lia | exact Eqn].
        -- reflexivity.
      * intros k Hk. apply Hnm. lia.
    + destruct (optimize_rules_concatK n d (r2 :: rest)) as [[m'' dd''] rr''] eqn:Erec.
      inversion H. subst n' d' rs'. clear H.
      eapply (H0 (r2 :: rest)); [ unfold ltof; cbn; lia | exact Erec | exact Hnm ].
Qed.

Lemma optimize_rules_concatK_vmaps : forall rs n d n' d' rs',
  optimize_rules_concatK n d rs = (n', d', rs') -> sd_vmaps d' = sd_vmaps d.
Proof.
  induction rs as [rs H0] using (induction_ltof1 _ (@length rule)).
  intros n d n' d' rs' H.
  destruct rs as [| r1 [| r2 rest] ].
  - cbn in H. inversion H; subst; reflexivity.
  - cbn in H. inversion H; subst; reflexivity.
  - rewrite optimize_rules_concatK_cons2 in H. cbv zeta in H.
    destruct (concat_mergeK_pair r1 r2) as [[[[fields row1] row2] body] |] eqn:Em.
    + destruct (optimize_rules_concatK (S n) _ rest) as [[m'' dd''] rr''] eqn:Erec.
      inversion H; subst n' d' rs'. clear H.
      rewrite (H0 rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ Erec). reflexivity.
    + destruct (optimize_rules_concatK n d (r2 :: rest)) as [[m'' dd''] rr''] eqn:Erec.
      inversion H; subst n' d' rs'. clear H.
      exact (H0 (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ Erec).
Qed.

Lemma optimize_rules_concatK_mono : forall rs n d n' d' rs',
  optimize_rules_concatK n d rs = (n', d', rs') -> n <= n'.
Proof.
  induction rs as [rs H0] using (induction_ltof1 _ (@length rule)).
  intros n d n' d' rs' H.
  destruct rs as [| r1 [| r2 rest] ].
  - cbn in H. inversion H; subst; lia.
  - cbn in H. inversion H; subst; lia.
  - rewrite optimize_rules_concatK_cons2 in H. cbv zeta in H.
    destruct (concat_mergeK_pair r1 r2) as [[[[fields row1] row2] body] |] eqn:Em.
    + destruct (optimize_rules_concatK (S n) _ rest) as [[m'' dd''] rr''] eqn:Erec.
      inversion H; subst n' d' rs'. clear H.
      pose proof (H0 rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ Erec). lia.
    + destruct (optimize_rules_concatK n d (r2 :: rest)) as [[m'' dd''] rr''] eqn:Erec.
      inversion H; subst n' d' rs'. clear H.
      exact (H0 (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ Erec).
Qed.

(** The minted set keys lie in [n, n'). *)
Lemma optimize_rules_concatK_keys_bound : forall rs n d n' d' rs' k,
  optimize_rules_concatK n d rs = (n', d', rs') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  induction rs as [rs IHrs] using (induction_ltof1 _ (@length rule)).
  intros n d n' d' rs' k H Hin.
  destruct rs as [| r1 [| r2 rest] ].
  - cbn in H. inversion H; subst. left; exact Hin.
  - cbn in H. inversion H; subst. left; exact Hin.
  - rewrite optimize_rules_concatK_cons2 in H. cbv zeta in H.
    destruct (concat_mergeK_pair r1 r2) as [[[[fields row1] row2] body] |] eqn:Em.
    + remember (optimize_rules_concatK (S n)
                  {| sd_sets := (setname n, map pack_row [row1; row2]) :: sd_sets d;
                     sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest) as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. injection H as Hn' Hd' Hr'. subst n' d' rs'.
      destruct (IHrs rest ltac:(unfold ltof; cbn; lia) (S n) _ m'' dd'' rr'' k (eq_sym Erec) Hin)
        as [Hin_dn | Hlt].
      * cbn [sd_sets map] in Hin_dn. destruct Hin_dn as [Heq | Hin_d].
        -- apply setname_inj in Heq. subst k. right.
           pose proof (optimize_rules_concatK_mono rest (S n) _ m'' dd'' rr'' (eq_sym Erec)). lia.
        -- left; exact Hin_d.
      * right; exact Hlt.
    + remember (optimize_rules_concatK n d (r2 :: rest)) as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. injection H as Hn' Hd' Hr'. subst n' d' rs'.
      eapply (IHrs (r2 :: rest) ltac:(unfold ltof; cbn; lia) n d m'' dd'' rr'' k (eq_sym Erec) Hin).
Qed.

(** *** Chain-level wrappers (mono / vmaps / keys_bound). *)
Lemma optimize_chain_concatK_mono : forall n d c n' d' c',
  optimize_chain_concatK n d c = (n', d', c') -> n <= n'.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_concatK in H.
  destruct (optimize_rules_concatK n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_concatK_mono _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_concatK_vmaps : forall n d c n' d' c',
  optimize_chain_concatK n d c = (n', d', c') -> sd_vmaps d' = sd_vmaps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_concatK in H.
  destruct (optimize_rules_concatK n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_concatK_vmaps _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_concatK_keys_bound : forall n d c n' d' c' k,
  optimize_chain_concatK n d c = (n', d', c') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  intros n d c n' d' c' k H Hin. unfold optimize_chain_concatK in H.
  destruct (optimize_rules_concatK n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  apply (optimize_rules_concatK_keys_bound _ _ _ _ _ _ k E Hin).
Qed.

(** Axiom-freedom guard (build-time): prints "Closed under the global context". *)
Print Assumptions concat_in_iv_pointsN.
Print Assumptions concat_fields_certificate_N.
Print Assumptions eval_rules_concat_mergeK.
