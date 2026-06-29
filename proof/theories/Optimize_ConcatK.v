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
From Nft Require Import Bytes Packet Verdict Syntax Semantics Optimize_Concat.
Import ListNotations.
Local Open Scope nat_scope.

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

(** Axiom-freedom guard (build-time): prints "Closed under the global context". *)
Print Assumptions concat_in_iv_pointsN.
