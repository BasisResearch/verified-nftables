(** * Bytes: the value domain shared by the DSL and the bytecode.

    nftables registers and immediates hold byte strings.  A "payload load"
    reads [len] bytes from a header; a "cmp" compares a register's bytes to an
    immediate.  We therefore model a value as a [list byte], with byte = [N]
    (we never need the 0..255 bound for the equivalence proofs; only equality
    of byte strings matters). *)

From Stdlib Require Import List PeanoNat Bool NArith Lia.
Import ListNotations.

(** A byte is modelled as a [nat]; only equality of byte strings matters for the
    proofs, and [nat] extracts cleanly to an OCaml [int] for the glue code. *)
Definition byte := nat.

(** A [data] is a byte string: a loaded register value or a compared immediate. *)
Definition data := list byte.

(** Boolean equality on byte strings (decidable; used by [cmp]). *)
Definition data_eqb (a b : data) : bool :=
  if list_eq_dec Nat.eq_dec a b then true else false.

Lemma data_eqb_refl : forall a, data_eqb a a = true.
Proof. intros a. unfold data_eqb. destruct (list_eq_dec Nat.eq_dec a a); congruence. Qed.

Lemma data_eqb_true_iff : forall a b, data_eqb a b = true <-> a = b.
Proof.
  intros a b. unfold data_eqb. destruct (list_eq_dec Nat.eq_dec a b); split; congruence.
Qed.

(** Membership of a byte string in a set (the semantics of an nftables set
    lookup). *)
Definition data_mem (x : data) (s : list data) : bool :=
  existsb (data_eqb x) s.

(** Map lookup: the data value a key maps to ([] if absent). *)
Fixpoint map_lookup_data (k : data) (entries : list (data * data)) : data :=
  match entries with
  | [] => []
  | (k', v) :: rest => if data_eqb k k' then v else map_lookup_data k rest
  end.

(** Bytewise [(a & mask) ^ xor], the operation an nftables [bitwise] expression
    performs (used to model prefix/masked matches such as a /24). *)
Definition byte_and (a b : byte) : byte := Nat.land a b.
Definition byte_xor (a b : byte) : byte := Nat.lxor a b.
Definition byte_or  (a b : byte) : byte := Nat.lor a b.

(** Bytewise OR of two values, the operation an nftables register-to-register
    [bitwise ... | ...] expression performs (used when a value is composed by
    OR-ing several field sources, e.g. [meta mark | meta iif]). *)
Fixpoint data_or (a b : data) : data :=
  match a, b with
  | x :: xs, y :: ys => byte_or x y :: data_or xs ys
  | _, _ => []
  end.

Fixpoint data_bitops (a mask xor : data) : data :=
  match a, mask, xor with
  | x :: xs, m :: ms, e :: es => byte_xor (byte_and x m) e :: data_bitops xs ms es
  | _, _, _ => []
  end.

(** Byte-string <-> big-endian [N], used to model shifts faithfully. *)
Definition data_to_N (d : data) : N :=
  fold_left (fun acc b => (acc * 256 + N.of_nat b)%N) d 0%N.

Fixpoint N_to_data (len : nat) (n : N) : data :=
  match len with
  | 0 => []
  | S k => N_to_data k (N.div n 256) ++ [N.to_nat (N.modulo n 256)]
  end.

(** Left/right bit shift of a register value (preserving its byte width). *)
Definition data_shift (shl : bool) (amt : nat) (d : data) : data :=
  N_to_data (length d)
    (if shl then N.shiftl (data_to_N d) (N.of_nat amt)
             else N.shiftr (data_to_N d) (N.of_nat amt)).

(** Jenkins-hash transform ([hash ... = jhash(reg, len, seed) % mod offset]).
    The real jhash is a specific mixing function; we model it as a deterministic
    function of the input bytes, seed, modulus and offset, bounded into
    [offset, offset+modulus) — faithful in *structure* (deterministic, input- and
    seed-dependent, mod-bounded), an abstraction of the exact mixing. *)
Definition data_jhash (len seed modulus offset : nat) (d : data) : data :=
  N_to_data 4
    (N.of_nat offset +
     N.modulo (data_to_N d + N.of_nat seed) (N.of_nat (S modulus))).

(** Byte-order conversion (ntoh/hton).  nftables' byteorder expression swaps the
    bytes *within each [len]-byte element* across the [size]-byte value (ntoh and
    hton are the same byte reversal for a single conversion).  We therefore
    reverse each [len]-byte chunk of the register value.  [fuel] (= [length d])
    bounds the recursion so it is structural even when [len = 0]. *)
Fixpoint byteorder_chunks (fuel len : nat) (d : data) : data :=
  match fuel with
  | 0 => d
  | S f =>
      match d with
      | [] => []
      | _ :: _ => rev (firstn len d) ++ byteorder_chunks f len (skipn len d)
      end
  end.

Definition data_byteorder (hton : bool) (size len : nat) (d : data) : data :=
  byteorder_chunks (length d) len d.

(** Big-endian (most-significant-byte-first) lexicographic order on byte
    strings; for equal-length network-order values this is numeric order.
    Used by range matches. *)
Fixpoint data_le (a b : data) : bool :=
  match a, b with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if Nat.eqb x y then data_le xs ys else Nat.leb x y
  end.

(** Antisymmetry: [a <= b] and [b <= a] together are exactly equality.  Used to
    prove that a singleton range [lo <= x <= lo] is the same test as [x = lo]. *)
Lemma data_le_antisym : forall a b, andb (data_le a b) (data_le b a) = data_eqb a b.
Proof.
  induction a as [| x xs IH]; intros [| y ys].
  - reflexivity.
  - reflexivity.
  - cbn [data_le andb]. symmetry.
    destruct (data_eqb (x::xs) nil) eqn:E;
      [apply data_eqb_true_iff in E; discriminate | reflexivity].
  - cbn [data_le]. rewrite (Nat.eqb_sym y x).
    destruct (Nat.eqb x y) eqn:Exy.
    + apply Nat.eqb_eq in Exy; subst y. rewrite IH.
      destruct (data_eqb xs ys) eqn:E.
      * apply data_eqb_true_iff in E; subst ys. symmetry. apply data_eqb_refl.
      * symmetry. apply Bool.not_true_is_false.
        rewrite data_eqb_true_iff. intro Hc. inversion Hc; subst ys.
        rewrite data_eqb_refl in E; discriminate.
    + apply Nat.eqb_neq in Exy.
      assert (data_eqb (x::xs) (y::ys) = false) as ->.
      { apply Bool.not_true_is_false. rewrite data_eqb_true_iff.
        intro Hc; inversion Hc; congruence. }
      destruct (Nat.leb x y) eqn:Lxy, (Nat.leb y x) eqn:Lyx; cbn; try reflexivity.
      apply Nat.leb_le in Lxy, Lyx.
      exfalso. apply Exy. apply Nat.le_antisymm; assumption.
Qed.

(** Set membership over an *interval* set: each element is a closed range
    [lo, hi] (an exact element is the degenerate [x, x]; a prefix/CIDR like
    10.0.0.0/8 is [10.0.0.0, 10.255.255.255]).  Membership is [lo <= x <= hi]
    by big-endian order — so a point set reduces to equality ([data_le_antisym])
    while interval/prefix sets are faithfully expressible. *)
Definition data_in_iv (x : data) (iv : data * data) : bool :=
  andb (data_le (fst iv) x) (data_le x (snd iv)).
Definition set_mem (x : data) (s : list (data * data)) : bool :=
  existsb (data_in_iv x) s.

(** ** Per-field (cross-product) membership for CONCATENATED sets.

    A concatenated set (NFT_SET_CONCAT) is NOT one flat lexicographic interval
    over the concatenated key: the kernel is told each field's length
    (NFTA_SET_FIELD_LEN, nf_tables.h) and the pipapo backend matches EACH FIELD
    against its OWN [lo,hi] independently — the set is the CROSS-PRODUCT of the
    per-field intervals.  So for `ip daddr . tcp dport { 10.0.0.0/8 . 10-23 }`
    the element is {daddr in [10.0.0.0,10.255.255.255]} x {dport in [10,23]},
    and a packet matches iff BOTH hold (a flat lexicographic test over the
    concatenation is an unsound over-approximation).

    The stored element bound [lo] (resp. [hi]) is the per-field concatenation of
    the per-field lower (resp. upper) bounds, laid out with the SAME per-field
    widths as the packet's per-field values [vals].  We split [lo]/[hi] by those
    widths and test each field's slice independently. *)

(** Split [d] into successive chunks of the given byte [widths].  Every chunk
    but the LAST takes exactly its width; the final field takes ALL remaining
    bytes.  Giving the last field the remainder means that for a SINGLE field the
    chunk is the whole bound [d] (no truncation), so the per-field test on one
    field coincides definitionally with the flat [data_in_iv] — single-field
    interval/point sets are byte-for-byte unchanged.  For a well-formed
    multi-field bound (the per-field concatenation) the remainder of the last
    split is exactly that last field's bytes, so this matches the kernel. *)
Fixpoint split_by (widths : list nat) (d : data) : list data :=
  match widths with
  | [] => []
  | [_] => [d]
  | w :: ws => firstn w d :: split_by ws (skipn w d)
  end.

(** One field's interval test: [lo_i <= val_i <= hi_i] in big-endian order. *)
Definition field_in_iv (val : data) (lohi : data * data) : bool :=
  andb (data_le (fst lohi) val) (data_le val (snd lohi)).

(** A list of per-field values matches one concatenated element [iv=(lo,hi)] iff
    every field's value lies in its own per-field interval.  [lo] and [hi] are
    split by the per-field widths (= the lengths of [vals]). *)
Definition concat_in_iv (vals : list data) (iv : data * data) : bool :=
  let widths := map (@length byte) vals in
  let los := split_by widths (fst iv) in
  let his := split_by widths (snd iv) in
  forallb (fun t => field_in_iv (fst t) (snd t))
          (combine vals (combine los his)).

(** Membership of a per-field-decomposed key in a concatenated set: some element
    whose per-field intervals all contain the corresponding field value. *)
Definition concat_set_mem (vals : list data) (s : list (data * data)) : bool :=
  existsb (concat_in_iv vals) s.

(** ** Regression: for a SINGLE field, per-field membership coincides DEFINITIONALLY
    with the old flat [set_mem] — the last (here only) field takes the whole bound,
    so no truncation happens and [concat_in_iv [v] (lo,hi) = data_in_iv v (lo,hi)].
    This guarantees single-field interval/point sets are byte-for-byte unchanged
    (and is what makes the compiled single-register [ILookup] still match the DSL
    [MSetT]/single-field [MConcatSet]). *)
Lemma concat_in_iv_single : forall (v lo hi : data),
  concat_in_iv [v] (lo, hi) = data_in_iv v (lo, hi).
Proof.
  intros v lo hi. unfold concat_in_iv, data_in_iv, field_in_iv.
  cbn [map split_by combine forallb fst snd]. apply Bool.andb_true_r.
Qed.

Lemma concat_set_mem_single : forall (v : data) (s : list (data * data)),
  concat_set_mem [v] s = set_mem v s.
Proof.
  intros v s. unfold concat_set_mem, set_mem.
  induction s as [| [lo hi] s' IH]; cbn [existsb]; [reflexivity|].
  rewrite concat_in_iv_single, IH. reflexivity.
Qed.

Lemma data_eqb_sym : forall a b, data_eqb a b = data_eqb b a.
Proof.
  intros a b. unfold data_eqb.
  destruct (list_eq_dec Nat.eq_dec a b), (list_eq_dec Nat.eq_dec b a); congruence.
Qed.
