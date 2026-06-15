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

(** Bytewise [(a & mask) ^ xor], the operation an nftables [bitwise] expression
    performs (used to model prefix/masked matches such as a /24). *)
Definition byte_and (a b : byte) : byte := Nat.land a b.
Definition byte_xor (a b : byte) : byte := Nat.lxor a b.

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

(** Byte-order conversion (ntoh/hton); modelled as reversing the byte string. *)
Definition data_byteorder (hton : bool) (size len : nat) (d : data) : data := rev d.

(** Big-endian (most-significant-byte-first) lexicographic order on byte
    strings; for equal-length network-order values this is numeric order.
    Used by range matches. *)
Fixpoint data_le (a b : data) : bool :=
  match a, b with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if Nat.eqb x y then data_le xs ys else Nat.leb x y
  end.

Lemma data_eqb_sym : forall a b, data_eqb a b = data_eqb b a.
Proof.
  intros a b. unfold data_eqb.
  destruct (list_eq_dec Nat.eq_dec a b), (list_eq_dec Nat.eq_dec b a); congruence.
Qed.
