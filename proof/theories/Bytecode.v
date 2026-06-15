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

From Stdlib Require Import List NArith PeanoNat String.
From Nft Require Import Bytes Packet Verdict.
Import ListNotations.

(** Comparison operators of a [cmp] expression. *)
Inductive cmpop : Type :=
| CEq
| CNe
| CLt
| CGt
| CLe
| CGe.

Definition reg := nat.   (* register index; reg 0 is the verdict register *)

Inductive instr : Type :=
| IMetaLoad    (k : meta_key) (dst : reg)
| ICtLoad      (k : ct_key) (dst : reg)
| IRtLoad      (k : rt_key) (dst : reg)
| ISocketLoad  (k : socket_key) (dst : reg)
| INumgen      (spec : numgen_spec) (dst : reg)
| IOsf         (dst : reg)
| IExthdrLoad  (ep : exthdr_proto) (htype off len : nat) (present : bool) (dst : reg)
| IFibLoad     (sel : string) (res : fib_result) (dst : reg)
| IPayloadLoad (b : pbase) (off len : nat) (dst : reg)
| ICmp         (op : cmpop) (src : reg) (v : data)
| IRange       (op : cmpop) (src : reg) (lo hi : data)   (* range eq/neq *)
| IBitwise     (dst src : reg) (mask xor : data)         (* dst = (src & mask) ^ xor *)
| IBitShift    (dst src : reg) (shl : bool) (amt : nat) (* dst = src >>/<< amt *)
| IByteorder   (dst src : reg) (hton : bool) (size len : nat)
| IJhash       (dst src : reg) (len seed modulus offset : nat)
| ILookup      (srcs : list reg) (name : string) (neg : bool) (elems : list data)
                                          (* set membership over the concatenation
                                             of [srcs] (one reg per concatenated
                                             field; rendered at [hd srcs]); [elems]
                                             is the set contents, carried for
                                             semantics and not rendered (NEWSET) *)
| IVmap        (srcs : list reg) (name : string) (entries : list (data * verdict))
                                          (* verdict-map lookup (lookup .. dreg 0):
                                             the rule's verdict, or fall-through *)
| IImmediateData (dst : reg) (v : data)   (* immediate into a data register *)
| IPayloadWrite (src : reg) (b : pbase) (off len : nat) (ctype coff cflags : nat)
                                          (* payload mangle (verdict-neutral) *)
| IMetaSet     (k : meta_key) (src : reg)   (* meta set (verdict-neutral) *)
| ICtSet       (k : ct_key) (src : reg)     (* ct set (verdict-neutral) *)
| ILookupVal   (key : reg) (name : string) (dreg : reg) (entries : list (data * data))
                                          (* map lookup (lookup .. dreg N>0):
                                             loads the mapped value into [dreg] *)
| INat         (kind family : string) (amin amax pmin pmax : option reg)
               (flags : nat)   (* terminal NAT / masquerade / redirect *)
| ILimit       (spec : limit_spec)       (* rate limit (can break the rule) *)
| ICounter     (pkts bytes : nat)        (* verdict-neutral statements *)
| INotrack
| ILog         (level : option nat)
| IReject      (typ code : nat)          (* terminal verdicts *)
| IQueue       (lo hi : nat) (bypass fanout : bool)
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

Lemma set_reg_other : forall rf r d r', r <> r' -> set_reg rf r d r' = rf r'.
Proof.
  intros rf r d r' H. unfold set_reg.
  destruct (Nat.eqb r r') eqn:E; [apply Nat.eqb_eq in E; contradiction | reflexivity].
Qed.

Definition eval_cmp (op : cmpop) (a b : data) : bool :=
  match op with
  | CEq => data_eqb a b
  | CNe => negb (data_eqb a b)
  | CLt => andb (data_le a b) (negb (data_eqb a b))
  | CGt => negb (data_le a b)
  | CLe => data_le a b
  | CGe => data_le b a
  end.

(** range eq: [lo <= x <= hi]; range neq: the complement. *)
Definition eval_range (op : cmpop) (x lo hi : data) : bool :=
  let inr := andb (data_le lo x) (data_le x hi) in
  match op with
  | CNe => negb inr
  | _   => inr
  end.
