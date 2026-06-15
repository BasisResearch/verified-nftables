(** * Bytecode: the nftables control-plane "bytecode".

    This is the level of the netlink messages [nft] emits: a base chain becomes a
    sequence of NEWRULE messages, and each rule carries a list of expressions
    over a register file.  We model exactly that expression language (a faithful
    subset), abstracting away the netlink wire encoding itself (as instructed).

    Concretely, [nft --debug=netlink] for `tcp dport 22 accept` prints:

      [ payload load 2b @ transport header + 2 => reg 1 ]
      [ cmp eq reg 1 0x00001600 ]
      [ immediate reg 0 accept ]

    which is one [rule_prog] of three [instr]s.  A whole base chain is a
    [program]: an ordered list of such per-rule programs (one NEWRULE each). *)

From Stdlib Require Import List NArith PeanoNat.
From Nft Require Import Bytes Packet Verdict.
Import ListNotations.

(** Comparison operators of a [cmp] expression. *)
Inductive cmpop : Type :=
| CEq
| CNe.

Definition reg := nat.   (* register index; reg 0 is the verdict register *)

Inductive instr : Type :=
| IMetaLoad    (k : meta_key) (dst : reg)
| IPayloadLoad (b : pbase) (off len : nat) (dst : reg)
| ICmp         (op : cmpop) (src : reg) (v : data)
| IImmediate   (v : verdict).            (* immediate reg 0 <verdict> *)

(** Expressions of one rule (one NEWRULE message). *)
Definition rule_prog := list instr.

(** A base chain's bytecode: the ordered per-rule programs. *)
Definition program := list rule_prog.

(** Register file: a total map from register index to its byte string. *)
Definition regfile := reg -> data.
Definition empty_rf : regfile := fun _ => [].
Definition set_reg (rf : regfile) (r : reg) (d : data) : regfile :=
  fun r' => if Nat.eqb r r' then d else rf r'.

Lemma set_reg_same : forall rf r d, set_reg rf r d r = d.
Proof. intros. unfold set_reg. now rewrite Nat.eqb_refl. Qed.

Definition eval_cmp (op : cmpop) (a b : data) : bool :=
  match op with
  | CEq => data_eqb a b
  | CNe => negb (data_eqb a b)
  end.
