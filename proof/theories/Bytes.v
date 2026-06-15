(** * Bytes: the value domain shared by the DSL and the bytecode.

    nftables registers and immediates hold byte strings.  A "payload load"
    reads [len] bytes from a header; a "cmp" compares a register's bytes to an
    immediate.  We therefore model a value as a [list byte], with byte = [N]
    (we never need the 0..255 bound for the equivalence proofs; only equality
    of byte strings matters). *)

From Stdlib Require Import List PeanoNat Bool.
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

Lemma data_eqb_sym : forall a b, data_eqb a b = data_eqb b a.
Proof.
  intros a b. unfold data_eqb.
  destruct (list_eq_dec Nat.eq_dec a b), (list_eq_dec Nat.eq_dec b a); congruence.
Qed.
