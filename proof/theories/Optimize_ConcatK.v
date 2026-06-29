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

From Stdlib Require Import List PeanoNat Bool Lia.
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

(** Axiom-freedom guard (build-time): prints "Closed under the global context". *)
Print Assumptions concat_in_iv_pointsN.
Print Assumptions concat_fields_certificate_N.
Print Assumptions eval_rules_concat_mergeK.
