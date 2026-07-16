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

(** The NAT statement kind ([nft_nat]'s manip selector plus the two
    interface-address forms): source NAT to an operand ([NKsnat]), destination
    NAT to an operand ([NKdnat]), source NAT to the exit interface's address
    ([NKmasq], masquerade), destination NAT to the inbound interface's address
    ([NKredir], redirect).  The netlink/corpus rendering ("snat"/"dnat"/
    "masq"/"redir") is produced only at the rendering boundary
    (extracted/codec.ml, glue.ml). *)
Inductive nat_op : Type := NKsnat | NKdnat | NKmasq | NKredir.

Definition natop_eqb (a b : nat_op) : bool :=
  match a, b with
  | NKsnat, NKsnat | NKdnat, NKdnat | NKmasq, NKmasq | NKredir, NKredir => true
  | _, _ => false
  end.

Lemma natop_eqb_eq : forall a b, natop_eqb a b = true <-> a = b.
Proof. intros [] []; cbn; split; intro H; congruence. Qed.

(** The NAT L3 address family: [NFip4] the 32-bit IPv4 slot, [NFip6] the
    128-bit IPv6 slot (the kernel chooses by family — nat_addrlen,
    netlink_linearize.c:1237), and [NFinet] the RUNTIME-DISPATCHED sentinel: an
    `inet` table has ONE NAT rule that serves BOTH families and the kernel
    dispatches on the PACKET's L3 family at runtime (nft_masq_inet_eval:
    `switch (nft_pf(pkt))`), so no static family is correct and the data-plane
    NAT resolves [NFinet] per-packet ([Semantics.nat_addrfamily_pkt]). *)
Inductive nat_af : Type := NFip4 | NFip6 | NFinet.

Definition nataf_eqb (a b : nat_af) : bool :=
  match a, b with
  | NFip4, NFip4 | NFip6, NFip6 | NFinet, NFinet => true
  | _, _ => false
  end.

Lemma nataf_eqb_eq : forall a b, nataf_eqb a b = true <-> a = b.
Proof. intros [] []; cbn; split; intro H; congruence. Qed.

(** The dynamic-set mutation of a `dynset` statement: [SOadd]/[SOupdate] insert
    the key (update also refreshes its timeout — indistinguishable in this
    timeout-free model), [SOdelete] removes it.  Rendered "add"/"update"/
    "delete" only at the rendering boundary (extracted/codec.ml). *)
Inductive dynset_op : Type := SOadd | SOupdate | SOdelete.

Definition dynsetop_eqb (a b : dynset_op) : bool :=
  match a, b with
  | SOadd, SOadd | SOupdate, SOupdate | SOdelete, SOdelete => true
  | _, _ => false
  end.

Lemma dynsetop_eqb_eq : forall a b, dynsetop_eqb a b = true <-> a = b.
Proof. intros [] []; cbn; split; intro H; congruence. Qed.

Definition reg := nat.   (* register index; reg 0 is the verdict register *)

Inductive instr : Type :=
| IMetaLoad    (k : meta_key) (dst : reg)
| ICtLoad      (k : ct_key) (dst : reg)
| IRtLoad      (k : rt_key) (dst : reg)
| ISocketLoad  (k : socket_key) (dst : reg)
| INumgen      (spec : numgen_spec) (dst : reg)
| IOsf         (dst : reg)
| IExthdrLoad  (ep : exthdr_proto) (htype off len : nat) (present : bool) (dst : reg)
| ITproxy      (family : string) (areg preg : option reg)
| IFwd         (devreg addrreg : option reg) (nfproto : option nat)
| IQueueSreg   (sreg : reg) (bypass fanout : bool)
| IFibLoad     (sel : string) (res : fib_result) (dst : reg)
| IQuota       (spec : quota_spec)
| IConnlimit   (spec : connlimit_spec)
| IObjref      (otype : nat) (oname : string)
| ISynproxy    (mss wscale : nat)
| ILast        (info : string)
| IDynset      (op : dynset_op) (name : string) (keyregs : list reg) (datareg : option reg) (fdata : bool)
                            (* [keyregs] hold the (concatenated) set/map key; [datareg]
                               is the map data register (None = a pure SET dynset).
                               [fdata] distinguishes a data register fed by a packet
                               FIELD ([true], the value is modelled) from one fed by
                               IMMEDIATE constants ([false], a separate SDynsetImm
                               whose value-effect is left out of the model).  [fdata]
                               does not affect rendering — it only guides the
                               mutation semantics. *)
| IExthdrReset (proto : string) (htype : nat)
| IDup         (devreg addrreg : option reg)
| IObjrefMap   (sregs : list reg) (name : string)
| ICtSetDir    (key dir : string) (src : reg)
| IExthdrWrite (proto : string) (htype off len : nat) (src : reg)
| ICtDirLoad   (key dir : string) (dst : reg)
| IXfrmLoad    (dir : string) (spnum : nat) (key : string) (dst : reg)
| ITunnelLoad  (key : string) (dst : reg)
| ISymhash     (modulus offset : nat) (dst : reg)
| IInnerLoad   (typ hdrsize flags : nat) (innerdesc : string) (width : nat) (dst : reg)
| IPayloadLoad (b : pbase) (off len : nat) (dst : reg)
| ICmp         (op : cmpop) (src : reg) (v : data)
| IRange       (op : cmpop) (src : reg) (lo hi : data)   (* range eq/neq *)
| IBitwise     (dst src : reg) (mask xor : data)         (* dst = (src & mask) ^ xor *)
| IBitwiseOr   (dst src1 src2 : reg)                     (* dst = src1 | src2 *)
| IBitShift    (dst src : reg) (shl : bool) (amt : nat) (* dst = src >>/<< amt *)
| IByteorder   (dst src : reg) (hton : bool) (size len : nat)
| IJhash       (dst src : reg) (len seed modulus offset : nat)
| ILookup      (srcs : list reg) (name : string) (neg : bool)
                                          (* set membership over the concatenation
                                             of [srcs] (one reg per concatenated
                                             field; rendered at [hd srcs]); the set
                                             contents are looked up by [name] in the
                                             runtime environment, not inlined here *)
| IVmap        (srcs : list reg) (name : string)
                                          (* verdict-map lookup (lookup .. dreg 0):
                                             the entries are looked up by [name] *)
| IImmediateData (dst : reg) (v : data)   (* immediate into a data register *)
| IPayloadWrite (src : reg) (b : pbase) (off len : nat) (ctype coff cflags : nat)
                                          (* payload mangle (verdict-neutral) *)
| IMetaSet     (k : meta_key) (src : reg)   (* meta set (verdict-neutral) *)
| ICtSet       (k : ct_key) (src : reg)     (* ct set (verdict-neutral) *)
| ILookupVal   (keys : list reg) (name : string) (dreg : reg)
                                          (* map lookup (lookup .. dreg N>0): loads
                                             the value mapped by [name] into [dreg].
                                             Used in VERDICT-NEUTRAL positions (set/
                                             mangle operands): a miss is observable
                                             only as the unwritten side effect, so the
                                             VM keeps running (verdict unchanged). *)
| ILookupValBr (keys : list reg) (name : string) (dreg : reg)
                                          (* map lookup feeding a TERMINAL operand
                                             (`dnat to … map`): a miss BREAKs the rule
                                             (NFT_BREAK) so the terminal does NOT fire
                                             — the verdict-relevant lookup.  Renders to
                                             the same netlink `lookup` as [ILookupVal];
                                             the two differ only in the modelled
                                             miss behaviour at their use site. *)
| INat         (kind : nat_op) (family : nat_af) (amin amax pmin pmax : option reg)
               (flags : nat)   (* terminal NAT / masquerade / redirect *)
| ILimit       (spec : limit_spec)       (* rate limit (can break the rule) *)
| ICounter     (pkts bytes : nat)        (* verdict-neutral statements *)
| INotrack
| ILog         (opts : string)
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

(** Compare register [a] against immediate [b].  The ordered ops use [data_le]
    (big-endian unsigned), which is a total order on EQUAL-LENGTH operands; nft
    only ever emits a [cmp] whose immediate has the loaded field's width, so [a]
    and [b] are always the same length here. *)
(** Equality compares the first [length b] bytes of [a] — the cmp value's width.
    For equal-width values this is exact equality; for a *prefix* pattern (a
    wildcard interface name `iifname "eth*"`, which the kernel emits as a short
    cmp value) it is the prefix match the kernel performs.  (Range comparisons are
    unaffected; the singleton-range→eq optimisation is dropped because it is
    unsound for prefix equality — see Optimize.v.) *)
Definition eval_cmp (op : cmpop) (a b : data) : bool :=
  match op with
  | CEq => data_eqb (List.firstn (List.length b) a) b
  | CNe => negb (data_eqb (List.firstn (List.length b) a) b)
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
