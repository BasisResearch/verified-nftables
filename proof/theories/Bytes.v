(** * Bytes: the value domain shared by the DSL and the bytecode.

    nftables registers and immediates hold byte strings.  A "payload load"
    reads [len] bytes from a header; a "cmp" compares a register's bytes to an
    immediate.  We therefore model a value as a [list byte], with byte = [N]
    (we never need the 0..255 bound for the equivalence proofs; only equality
    of byte strings matters). *)

From Stdlib Require Import List PeanoNat Bool NArith.
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

Lemma data_eqb_sym : forall a b, data_eqb a b = data_eqb b a.
Proof.
  intros a b. unfold data_eqb.
  destruct (list_eq_dec Nat.eq_dec a b), (list_eq_dec Nat.eq_dec b a); congruence.
Qed.
