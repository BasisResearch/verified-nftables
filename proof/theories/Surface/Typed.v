(** * Surface.Typed: the typed match-term language and its VERIFIED
    elaboration onto the byte IR.

    [txmatch] covers every SCALAR match shape the frontend produces, so the
    OCaml frontend constructs no byte-level match condition for any scalar
    match.  A typed term carries TYPED immediates ([Nftval.nftval] —
    [VIpv4]/[VPort]/[VIfname]/[VCtState]/[VHostInt]/…), never raw register
    bytes; the per-field byte encoding (endianness, widths) is
    [Nftval.encode], applied only by the elaboration [elab_tx] below:

      [TXEq]/[TXNeq] equality / inequality against a typed immediate.
      [TXPrefix]   CIDR prefixes: the top [plen] bits of the field equal /
                   differ from the network part of the value.  The verified
                   [prefix_expand] owns nft's byte-aligned shortening decision
                   (see its section header below).
      [TXWildcard] trailing-`*` interface-name wildcards / ct-tuple CIDRs:
                   the field's LEADING bytes equal a short prefix (the one
                   surface construct whose meaning is a prefix compare).
      [TXRange]    inclusive ranges, where the selector DATATYPE decides the
                   byte form: the three kernel-adjudicated host-endian range
                   dtypes (mark / ifindex / fib_addrtype) take nft's mandatory
                   `byteorder hton` path ([MRangeT] + big-endian re-encoded
                   bounds); everything else is a plain big-endian [MRange].
      [TXBitmask]  bitmask-basetype forms (ct state / ct status / tcp flags):
                   the 4-operator dispatch (implicit / bang / == / !=) over the
                   OR-fold of one or more bit values (a bare comma list ORs
                   several).
      [TXBitfield] sub-byte header bitfields (ip dscp / ip6 flowlabel / tcp
                   doff / vlan id / frag frag-off / ...): the byte mask and the
                   shifted compare value are COMPUTED here from the numeric
                   bit-width/LSB-position specs of [Selector.bitfield_spec] —
                   the frontend no longer stores or derives any mask bytes.
      [TXBitwise]  explicit bitwise mask matches (`<sel> and|or|xor <m> <op>
                   <v>`), realised exactly as nft does:
                     and m : (field & m) ^ 0        or m : (field & ~m) ^ m
                     xor m : (field & ~0) ^ m
      [TXFlag]     fib/exthdr/tcp-option presence tests: a compare of the
                   1-byte kernel PRESENT flag.

    [elab_tx] is the TOTAL elaboration of a typed term onto [matchcond]; the
    per-shape NON-definitional erasure theorems (the typed numeric semantics of
    Semantics.TypedEval agrees with the byte-level evaluation of the elaborated
    form) live in Surface.Lower_Proofs — [txmatch_erasure] and its per-shape
    lemmas [eq_erasure]/[neq_erasure]/[prefix_erasure]/[wildcard_erasure]/
    [range_erasure_be]/[range_erasure_host]/[bitmask_erasure]/
    [bitfield_erasure]/[bitwise_erasure]/[flag_erasure].  *)

From Stdlib Require Import List PeanoNat Bool NArith String.
From Nft Require Import Bytes Packet Verdict Bytecode Syntax Nftval
  Ast Datatype Selector.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(** ** Numeric views of a typed value (shared by the typed semantics and the
    erasure proofs; defined WITHOUT [encode] so Semantics/TypedEval.v can use
    them under its no-encode independence gate). *)

(** The numeric value a typed value denotes.  Numeric constructors carry it;
    the verbatim byte constructors (addresses / MAC / ifname) denote their
    big-endian byte reading — the order the register compare uses. *)
Definition val_N (v : nftval) : N :=
  match v with
  | VInteger _ n | VHostInt _ n => n
  | VPort n | VVerdict n | VCtState n | VFibType n => n
  | VIpv4 b | VIpv6 b | VEther b => data_to_N b
  | VIfname s => data_to_N s
  end.

(** The register byte width the value's encoding occupies (=
    [length (Nftval.encode v)] — proved as [val_width_encode] in
    Lower_Proofs.v, but stated here without mentioning [encode]). *)
Definition val_width (v : nftval) : nat :=
  match v with
  | VInteger w _ | VHostInt w _ => w
  | VIpv4 b | VIpv6 b | VEther b => List.length b
  | VIfname s => List.length s
  | VPort _ => 2
  | VVerdict _ => Nftval.verdict_width
  | VCtState _ | VFibType _ => 4
  end.

(** Boolean well-formedness: numeric constructors fit their width, verbatim
    byte constructors carry genuine bytes (< 256).  This is [Nftval.wf] minus
    the length pins (lengths are checked against the DATATYPE width by the
    consumers), as a computable bool. *)
Definition bytes_wfb (d : data) : bool := forallb (fun b => b <? 256)%nat d.

Definition val_wfb (v : nftval) : bool :=
  match v with
  | VInteger w n | VHostInt w n => (n <? 256 ^ N.of_nat w)%N
  | VPort n => (n <? 256 ^ 2)%N
  | VVerdict n => (n <? 256 ^ N.of_nat Nftval.verdict_width)%N
  | VCtState n | VFibType n => (n <? 256 ^ 4)%N
  | VIpv4 b | VIpv6 b | VEther b => bytes_wfb b
  | VIfname s => bytes_wfb s
  end.

(** Host-endian-encoded constructors ([Nftval.encode] stores them
    least-significant-byte first) — same set as [Typecheck.host_encoded]. *)
Definition host_val (v : nftval) : bool :=
  match v with VHostInt _ _ | VFibType _ => true | _ => false end.

(* ------------------------------------------------------------------ *)
(** ** Big-endian re-encoding (nft's post-`hton` range/interval bounds).

    A range over a host-endian field is only numerically meaningful after
    nft's mandatory `byteorder reg = hton(reg, w, w)`; the stored bounds are
    then NETWORK order.  [encode_be] is the bound encoder: the host-endian
    constructors big-endian, everything else its ordinary register encoding
    (which is already big-endian / verbatim). *)
Definition encode_be (v : nftval) : data :=
  match v with
  | VHostInt w n => N_to_data w n
  | VFibType n   => N_to_data 4 n
  | _ => encode v
  end.

(** The three HOST-ENDIAN dtypes whose range/ordered path is
    kernel-adjudicated to take the `byteorder hton` conversion (golden
    any/ct.t.payload `ct mark 0x32-0x45`; the byteorder-gate pins mark / iif /
    oif / ct mark / fib type from source).  The OTHER host-endian register
    dtypes ([DThostint w]: meta skuid/length/cpu/..., ct id/zone/expiration)
    keep the frontend's HISTORICAL plain-[MRange] form with host-endian
    bounds — an UNADJUDICATED display-vs-wire class (see byteorder-gate.sh's
    SCOPE note); the typed semantics deliberately gives that form NO meaning
    (evaluation is STUCK on it, Semantics/TypedEval.v), rather than blessing a
    byte-lexicographic compare of little-endian bytes as numeric. *)
Definition range_hton (dt : dtype) : bool :=
  match dt with DTmark | DTifindex | DTfib_addrtype => true | _ => false end.

(* ------------------------------------------------------------------ *)
(** ** The verified CIDR expansion (the alignment decision, in Coq).

    nft shortens a byte-aligned prefix on a plain payload field to a load of
    just the prefix bytes plus a direct cmp (`ip saddr a.b.c.0/24` =>
    `payload load 3b @ network+12 ; cmp eq`), and keeps the full-width
    `load ; bitwise & mask ; cmp` form for every other prefix (golden
    {ip,ip6}.t.payload) — [prefix_expand] makes that decision, verified, not
    the frontend. *)

(** The truncated-load field of a byte-aligned prefix on a plain payload
    address (or the identity for a conntrack-tuple address, whose symbolic
    `ct load` keeps the full-width load and shortens only the compare). *)
Definition payload_prefix_field (f : field) (nbytes : nat) : option field :=
  match f with
  | FIp4Saddr => Some (FPayload PNetwork 12 nbytes)
  | FIp4Daddr => Some (FPayload PNetwork 16 nbytes)
  | FIp6Saddr => Some (FPayload PNetwork 8  nbytes)
  | FIp6Daddr => Some (FPayload PNetwork 24 nbytes)
  | FCtDir k d => Some (FCtDir k d)
  | _ => None
  end.

(** Byte [i] of a big-endian prefix mask: the top [min b 8] bits set. *)
Definition mask_byte (b : nat) : nat := 256 - Nat.pow 2 (8 - Nat.min b 8).

(** The [w]-byte big-endian mask with the top [plen] bits set. *)
Definition prefix_mask (w plen : nat) : data :=
  map (fun i => mask_byte (plen - 8 * i)) (seq 0 w).

(** Pointwise AND (an all-zero xor [data_bitops]). *)
Definition data_and (a mask : data) : data :=
  data_bitops a mask (repeat 0 (List.length a)).

(** Expand a CIDR prefix to the byte IR: a byte-aligned prefix strictly inside
    the field's width on a plain payload address shortens to a truncated-load
    direct compare; every other prefix keeps the full-width masked compare. *)
Definition prefix_expand (f : field) (op : cmpop) (v : nftval) (plen : nat)
  : matchcond :=
  let bytes := encode v in
  let w := List.length bytes in
  let mask := prefix_mask w plen in
  let net := data_and bytes mask in
  if (0 <? plen) && (plen <? 8 * w) && (Nat.eqb (Nat.modulo plen 8) 0)
  then match payload_prefix_field f (Nat.div plen 8) with
       | Some f' =>
           let short := firstn (Nat.div plen 8) net in
           match op with CNe => MNeq f' short | _ => MEq f' short end
       | None => MMasked f op mask (repeat 0 w) net
       end
  else MMasked f op mask (repeat 0 w) net.

(* ------------------------------------------------------------------ *)
(** ** The typed match terms. *)

(** The bitwise operator of an explicit `<sel> and|or|xor <mask>` match. *)
Inductive bitop : Type := BOand | BOor | BOxor.

Inductive txmatch : Type :=
| TXEq       (f : field) (v : nftval)
             (* equality against a typed immediate                        *)
| TXNeq      (f : field) (v : nftval)
             (* inequality against a typed immediate                      *)
| TXPrefix   (f : field) (op : cmpop) (v : nftval) (plen : nat)
             (* CIDR: the top [plen] bits of [f] equal (op = CEq) / differ
                from (op = CNe) the network part of [v]                   *)
| TXWildcard (f : field) (prefix : data)
             (* trailing-`*` interface-name wildcard / ct-tuple CIDR: the
                field's LEADING bytes equal [prefix] (a genuinely SHORT
                compare — the one surface construct whose meaning is a
                prefix match)                                             *)
| TXRange    (f : field) (dt : dtype) (neg : bool) (lo hi : nftval)
| TXBitmask  (f : field) (dt : dtype) (op : srelop) (bits : list N)
| TXBitfield (spec : bitfield_spec) (neg : bool) (v : N)
| TXBitwise  (f : field) (dt : dtype) (bop : bitop) (neg : bool)
             (mask v : nftval)
| TXFlag     (f : field) (neg : bool) (v : N).

(* ------------------------------------------------------------------ *)
(** ** The elaboration. *)

(** Bytewise complement (nft's `~mask` operand of the `or` realisation; the
    register is a byte string, so the complement is per-byte). *)
Definition data_not (d : data) : data := map (fun b => Nat.lxor b 255) d.

(** The OR-fold of a bitmask value list (a bare comma list
    `ct state new,established` ORs all members — evaluate.c:1877 mpz_ior). *)
Definition bm_fold (bits : list N) : N := fold_left N.lor bits 0%N.

(** The byte mask of a sub-byte bitfield: the field's [bf_bits] bits at LSB
    position [bf_shift] of the [bf_bytes]-byte load — `(2^bits - 1) << shift`,
    big-endian over the loaded bytes.  (The frontend's old hand-written byte
    tables are re-derived from the numeric specs; each of the 13 masks is
    pinned by a vm_compute Example in Lower.v.) *)
Definition bf_mask (spec : bitfield_spec) : data :=
  N_to_data (bf_bytes spec)
    (N.shiftl (N.ones (N.of_nat (bf_bits spec))) (N.of_nat (bf_shift spec))).

(** The shifted compare value of a bitfield match (`value << shift`). *)
Definition bf_cmpval (spec : bitfield_spec) (v : N) : data :=
  N_to_data (bf_bytes spec) (N.shiftl v (N.of_nat (bf_shift spec))).

Definition elab_tx (t : txmatch) : matchcond :=
  match t with
  | TXEq f v  => MEq  f (encode v)
  | TXNeq f v => MNeq f (encode v)
  | TXPrefix f op v plen => prefix_expand f op v plen
  | TXWildcard f prefix => MEq f prefix
  | TXRange f dt neg lo hi =>
      if range_hton dt
      then
        (* the hton path: convert the loaded host-endian register to network
           order, compare against big-endian bounds (golden ct.t.payload
           `byteorder reg 1 = hton(reg 1, 4, 4)` ; `range eq ...`) *)
        let w := dt_bytes dt in
        MRangeT f [TByteorder true w w] neg (encode_be lo) (encode_be hi)
      else MRange f neg (encode lo) (encode hi)
  | TXBitmask f dt op bits =>
      let w := dt_bytes dt in
      let mb := N_to_data w (bm_fold bits) in
      let z := repeat 0 w in
      match op with
      | SOpImplicit => MMasked f CNe mb z z    (* (field & m) <> 0          *)
      | SOpBang     => MMasked f CEq mb z z    (* (field & m) == 0          *)
      | SOpEq       => MEq  f mb               (* field == m                *)
      | SOpNe       => MNeq f mb               (* field <> m                *)
      end
  | TXBitfield spec neg v =>
      MMasked (bf_field spec) (if neg then CNe else CEq)
              (bf_mask spec) (repeat 0 (bf_bytes spec)) (bf_cmpval spec v)
  | TXBitwise f dt bop neg mask v =>
      let w := dt_bytes dt in
      let cmp := if neg then CNe else CEq in
      let mb := encode mask in
      let vb := encode v in
      match bop with
      | BOand => MMasked f cmp mb (repeat 0 w) vb
      | BOor  => MMasked f cmp (data_not mb) mb vb
      | BOxor => MMasked f cmp (repeat 255 w) mb vb
      end
  | TXFlag f neg v =>
      if neg then MNeq f (N_to_data 1 v) else MEq f (N_to_data 1 v)
  end.

(* ------------------------------------------------------------------ *)
(** ** Byte-pin witnesses (the elaboration is byte-for-byte the frontend's
    documented lowering; the golden corpus / byteorder-gate re-check the same
    bytes end-to-end). *)

(** `ip saddr 192.168.100.0/24` — byte-aligned: truncated 3-byte load + cmp. *)
Example prefix_aligned_24 :
  elab_tx (TXPrefix FIp4Saddr CEq (VIpv4 [192;168;100;0]) 24)
  = MEq (FPayload PNetwork 12 3) [192;168;100].
Proof. vm_compute. reflexivity. Qed.

(** `ip saddr 10.0.0.0/20` — unaligned: full-width mask + cmp. *)
Example prefix_unaligned_20 :
  elab_tx (TXPrefix FIp4Saddr CEq (VIpv4 [10;0;0;0]) 20)
  = MMasked FIp4Saddr CEq [255;255;240;0] [0;0;0;0] [10;0;0;0].
Proof. vm_compute. reflexivity. Qed.

(** A typed port equality elaborates to the 2-byte big-endian register cmp. *)
Example elab_port_22 : elab_tx (TXEq FThDport (VPort 22)) = MEq FThDport [0;22].
Proof. vm_compute. reflexivity. Qed.

(** A wildcard `iifname "dummy*"` is the short 5-byte prefix compare. *)
Example elab_wildcard :
  elab_tx (TXWildcard FMetaIifname (sbytes "dummy"))
  = MEq FMetaIifname [100;117;109;109;121].
Proof. vm_compute. reflexivity. Qed.

(** `ct state established` (single positive: implicit bitmask, ct.t:35-40). *)
Example elab_ct_state_established :
  elab_tx (TXBitmask FCtState DTct_state SOpImplicit [2%N])
  = MMasked FCtState CNe [0;0;0;2] [0;0;0;0] [0;0;0;0].
Proof. vm_compute. reflexivity. Qed.

(** `ct state new,established` (comma list ORs the bits). *)
Example elab_ct_state_comma :
  elab_tx (TXBitmask FCtState DTct_state SOpImplicit [8%N; 2%N])
  = MMasked FCtState CNe [0;0;0;10] [0;0;0;0] [0;0;0;0].
Proof. vm_compute. reflexivity. Qed.

(** The four written operators of `tcp flags X` (inet/tcp.t:69-74). *)
Example elab_tcpflags_ops :
  (elab_tx (TXBitmask FTcpFlags DTtcp_flag SOpImplicit [2%N]),
   elab_tx (TXBitmask FTcpFlags DTtcp_flag SOpBang     [2%N]),
   elab_tx (TXBitmask FTcpFlags DTtcp_flag SOpEq       [2%N]),
   elab_tx (TXBitmask FTcpFlags DTtcp_flag SOpNe       [2%N]))
  = (MMasked FTcpFlags CNe [2] [0] [0],
     MMasked FTcpFlags CEq [2] [0] [0],
     MEq  FTcpFlags [2],
     MNeq FTcpFlags [2]).
Proof. vm_compute. reflexivity. Qed.

(** `tcp dport 100-200`: plain big-endian range. *)
Example elab_range_port :
  elab_tx (TXRange FThDport DTinet_service false (VPort 100) (VPort 200))
  = MRange FThDport false [0;100] [0;200].
Proof. vm_compute. reflexivity. Qed.

(** `ct mark 0x32-0x45`: the hton path — [TByteorder] transform + big-endian
    bounds (golden any/ct.t.payload), NOT the host-endian eq/membership bytes. *)
Example elab_range_ctmark :
  elab_tx (TXRange FCtMark DTmark false (VHostInt 4 0x32) (VHostInt 4 0x45))
  = MRangeT FCtMark [TByteorder true 4 4] false [0;0;0;0x32] [0;0;0;0x45].
Proof. vm_compute. reflexivity. Qed.

(** `meta mark and 0x3 == 0x1` / `ct mark or 0x23` / xor: the three bitwise
    realisations over the host-endian mark register (any/meta.t, any/ct.t). *)
Example elab_bitwise_and :
  elab_tx (TXBitwise FMetaMark DTmark BOand false (VHostInt 4 3) (VHostInt 4 1))
  = MMasked FMetaMark CEq [3;0;0;0] [0;0;0;0] [1;0;0;0].
Proof. vm_compute. reflexivity. Qed.
Example elab_bitwise_or :
  elab_tx (TXBitwise FCtMark DTmark BOor false (VHostInt 4 0x23) (VHostInt 4 0x23))
  = MMasked FCtMark CEq [0xdc;0xff;0xff;0xff] [0x23;0;0;0] [0x23;0;0;0].
Proof. vm_compute. reflexivity. Qed.
Example elab_bitwise_xor :
  elab_tx (TXBitwise FMetaMark DTmark BOxor false (VHostInt 4 3) (VHostInt 4 1))
  = MMasked FMetaMark CEq [255;255;255;255] [3;0;0;0] [1;0;0;0].
Proof. vm_compute. reflexivity. Qed.

(** `fib daddr type missing` / `exthdr frag exists` / `tcp option sack
    missing`: the 1-byte present-flag compares. *)
Example elab_flag_forms :
  (elab_tx (TXFlag (FFib "daddr" FRpresent) false 0),
   elab_tx (TXFlag (FFib "daddr" FRpresent) true 0),
   elab_tx (TXFlag (FExthdr EPipv6 44 0 1 true) false 1),
   elab_tx (TXFlag (FExthdr EPtcpopt 5 0 1 true) false 0))
  = (MEq  (FFib "daddr" FRpresent) [0],
     MNeq (FFib "daddr" FRpresent) [0],
     MEq (FExthdr EPipv6 44 0 1 true) [1],
     MEq (FExthdr EPtcpopt 5 0 1 true) [0]).
Proof. vm_compute. reflexivity. Qed.

(** `ip dscp cs1`: load 1b @ nh+1 ; & 0xfc ; cmp eq 0x20 (cs1 = 8, 8<<2). *)
Example elab_bitfield_dscp :
  elab_tx (TXBitfield (bf (FPayload PNetwork 1 1) 1 6 2 dep_ip4 true) false 8)
  = MMasked (FPayload PNetwork 1 1) CEq [0xfc] [0] [0x20].
Proof. vm_compute. reflexivity. Qed.
