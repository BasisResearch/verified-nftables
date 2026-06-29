(** * Syntax: the declarative nftables DSL.

    This is the high-level, human-facing surface that [nft] accepts:
    a ruleset is a list of tables, a table a list of named chains, a chain a
    policy plus an ordered list of rules, and a rule a conjunction of match
    conditions terminated by a verdict.

    Each high-level [field] (e.g. "tcp dport") *denotes* a concrete way to read
    the packet, given by [field_load].  This denotation is the single source of
    truth shared by the semantics (which reads the field from the packet) and
    the compiler (which emits a load instruction for it).  The offsets here are
    checked against live [nft] by `make validate` (an INDEPENDENT oracle — see
    [run_validation] in extracted/corpus_test.ml); the corpus round-trip alone
    cannot check them because its parser and renderer share these tables. *)

From Stdlib Require Import List NArith String.
From Nft Require Import Bytes Packet Verdict Bytecode.
Import ListNotations.

(** How to read a field's value out of a packet. *)
Inductive loaddesc : Type :=
| LMeta    (k : meta_key)
| LCt      (k : ct_key)
| LRt      (k : rt_key)
| LSocket  (k : socket_key)
| LNumgen  (spec : numgen_spec)
| LOsf
| LExthdr  (ep : exthdr_proto) (htype off len : nat) (present : bool)
| LFib     (sel : string) (res : fib_result)
| LCtDir   (key dir : string)
| LXfrm    (dir : string) (spnum : nat) (key : string)
| LTunnel  (key : string)
| LSymhash (modulus offset : nat)
| LInner   (typ hdrsize flags : nat) (innerdesc : string) (width : nat)
| LPayload (b : pbase) (off len : nat).

(** The high-level header/metadata fields the DSL can match on.  Offsets/lengths
    mirror the layouts [nft] itself uses; they are validated against the upstream
    [tests/py/*.t.payload] corpus by the round-trip differential test. *)
Inductive field : Type :=
(* metadata *)
| FMetaL4proto | FMetaNfproto | FMetaProtocol | FMetaMark
| FMetaIif | FMetaOif | FMetaIiftype | FMetaOiftype | FMetaIifname | FMetaOifname
| FMetaLen | FMetaPkttype | FMetaCpu | FMetaSkuid | FMetaSkgid | FMetaPriority
(* conntrack *)
| FCtState | FCtStatus | FCtMark | FCtDirection | FCtExpiration | FCtId
(* link header (Ethernet) *)
| FEtherDaddr | FEtherSaddr | FEtherType | FLinkVlan
(* network header (IPv4) *)
| FIp4VerHdrlen | FIp4Word0 | FIp4Tos | FIp4Totlen | FIp4Id | FIp4FragOff
| FIp4Ttl | FIp4Protocol | FIp4Csum | FIp4Saddr | FIp4Daddr
(* network header (IPv6) *)
| FIp6Saddr | FIp6Daddr
(* transport header (TCP/UDP/ICMP) *)
| FThSport | FThDport | FTcpSeq | FTcpAck | FTcpFlags
| FUdpLen | FUdpCsum | FIcmpType | FIcmpCode
(* parametric payload field (any base/offset/length) and exthdr field *)
| FPayload (b : pbase) (off len : nat)
| FExthdr (ep : exthdr_proto) (htype off len : nat) (present : bool)
(* typed oracle-keyed fields: any meta key, routing key, socket key *)
| FMetaGen (k : meta_key)
| FCtGen (k : ct_key)
| FRtGen (k : rt_key)
| FSocketGen (k : socket_key)
| FNumgen (spec : numgen_spec)
| FOsf
| FFib (sel : string) (res : fib_result)
| FCtDir (key dir : string)
| FXfrm (dir : string) (spnum : nat) (key : string)
| FTunnel (key : string)
| FSymhash (modulus offset : nat)
| FInner (typ hdrsize flags : nat) (innerdesc : string) (width : nat).

(** The denotation of each field as a load. *)
Definition field_load (f : field) : loaddesc :=
  match f with
  | FMetaL4proto  => LMeta MKl4proto   | FMetaNfproto  => LMeta MKnfproto
  | FMetaProtocol => LMeta MKprotocol  | FMetaMark     => LMeta MKmark
  | FMetaIif      => LMeta MKiif       | FMetaOif      => LMeta MKoif
  | FMetaIiftype  => LMeta MKiiftype   | FMetaOiftype  => LMeta MKoiftype
  | FMetaLen      => LMeta MKlen       | FMetaPkttype  => LMeta MKpkttype
  | FMetaCpu      => LMeta MKcpu       | FMetaSkuid    => LMeta MKskuid
  | FMetaSkgid    => LMeta MKskgid     | FMetaPriority => LMeta MKpriority
  | FMetaIifname  => LMeta MKiifname   | FMetaOifname  => LMeta MKoifname
  | FCtState      => LCt CKstate       | FCtStatus     => LCt CKstatus
  | FCtMark       => LCt CKmark        | FCtDirection  => LCt CKdirection
  | FCtExpiration => LCt CKexpiration  | FCtId         => LCt CKid
  | FEtherDaddr   => LPayload PLink 0 6   | FEtherSaddr => LPayload PLink 6 6
  | FEtherType    => LPayload PLink 12 2  | FLinkVlan   => LPayload PLink 14 2
  | FIp4VerHdrlen => LPayload PNetwork 0 1  | FIp4Word0   => LPayload PNetwork 0 2
  | FIp4Tos       => LPayload PNetwork 1 1  | FIp4Totlen  => LPayload PNetwork 2 2
  | FIp4Id        => LPayload PNetwork 4 2  | FIp4FragOff => LPayload PNetwork 6 2
  | FIp4Ttl       => LPayload PNetwork 8 1  | FIp4Protocol=> LPayload PNetwork 9 1
  | FIp4Csum      => LPayload PNetwork 10 2 | FIp4Saddr   => LPayload PNetwork 12 4
  | FIp4Daddr     => LPayload PNetwork 16 4
  | FIp6Saddr     => LPayload PNetwork 8 16 | FIp6Daddr   => LPayload PNetwork 24 16
  | FThSport      => LPayload PTransport 0 2 | FThDport   => LPayload PTransport 2 2
  | FTcpSeq       => LPayload PTransport 4 4 | FTcpAck    => LPayload PTransport 8 4
  | FTcpFlags     => LPayload PTransport 13 1
  | FUdpLen       => LPayload PTransport 4 2 | FUdpCsum   => LPayload PTransport 6 2
  | FIcmpType     => LPayload PTransport 0 1 | FIcmpCode  => LPayload PTransport 1 1
  | FPayload b off len => LPayload b off len
  | FExthdr ep htype off len present => LExthdr ep htype off len present
  | FMetaGen k => LMeta k
  | FCtGen k => LCt k
  | FXfrm dir sp key => LXfrm dir sp key
  | FRtGen k => LRt k
  | FSocketGen k => LSocket k
  | FNumgen spec => LNumgen spec
  | FOsf => LOsf
  | FFib sel res => LFib sel res
  | FCtDir key dir => LCtDir key dir
  | FTunnel key => LTunnel key
  | FSymhash m o => LSymhash m o
  | FInner t h fl desc w => LInner t h fl desc w
  end.

(** Enumeration of every field, for the glue's load->field reverse map. *)
Definition all_fields : list field :=
  [ FMetaL4proto; FMetaNfproto; FMetaProtocol; FMetaMark; FMetaIif; FMetaOif;
    FMetaIiftype; FMetaOiftype; FMetaIifname; FMetaOifname;
    FMetaLen; FMetaPkttype; FMetaCpu; FMetaSkuid; FMetaSkgid; FMetaPriority;
    FCtState; FCtStatus; FCtMark; FCtDirection; FCtExpiration; FCtId;
    FEtherDaddr; FEtherSaddr; FEtherType; FLinkVlan;
    FIp4VerHdrlen; FIp4Word0; FIp4Tos; FIp4Totlen; FIp4Id; FIp4FragOff;
    FIp4Ttl; FIp4Protocol; FIp4Csum; FIp4Saddr; FIp4Daddr;
    FIp6Saddr; FIp6Daddr;
    FThSport; FThDport; FTcpSeq; FTcpAck; FTcpFlags;
    FUdpLen; FUdpCsum; FIcmpType; FIcmpCode ].

(** The value a `numgen inc` expression hands to an evaluation, given the SHARED
    counter [c] = the number of evaluations the instance has already performed
    (read from [e_numgen]).  The kernel (nft_numgen.c nft_ng_inc_gen) inits the
    atomic counter to [modulus-1], and each eval computes
    [nval = (oval + 1 < modulus) ? oval + 1 : 0] then returns [nval + offset].
    Numbering evals from 0, the value of eval [c] is therefore
    [(c mod modulus) + offset]: eval 0 -> [0 + offset], eval 1 -> [1 + offset], …,
    wrapping at [modulus] — exactly the round-robin sequence.  Rendered big-endian
    in a 4-byte register slot (NFT_REG32_SIZE), like the kernel's u32 dreg. *)
Definition numgen_inc_value (spec : numgen_spec) (c : nat) : data :=
  N_to_data 4 (N.of_nat (Nat.modulo c (ng_mod spec) + ng_offset spec)).

(** Evaluate a load against a packet. *)
Definition do_load (ld : loaddesc) (p : packet) : data :=
  match ld with
  | LMeta k         => pkt_meta p k
  | LCt k           =>
      (* EVERY conntrack key is read from the SHARED, flow-keyed conntrack table
         [e_ct] at THIS packet's flow ([pkt_flow]) — NOT from a free per-packet
         oracle.  This mirrors the kernel: nft_ct_get_eval first does
         `ct = nf_ct_get(pkt->skb, &ctinfo)` to select the flow's conntrack ENTRY,
         then derives the requested key from THAT entry — both the
         WRITABLE+PERSISTENT keys (mark/label: `*dest = READ_ONCE(ct->mark)`) and the
         READ-ONLY, kernel-computed keys (state/direction/expiration/counters/zone:
         e.g. NFT_CT_STATE `state = NF_CT_STATE_BIT(ctinfo)` where ctinfo is the
         flow's tracking info).  Because the value is a function of the FLOW (not the
         individual skb), two packets of the same connection read CONSISTENT
         conntrack data, the FIRST packet of a flow reads whatever the entry was
         INITIALISED to (the kernel: NEW — established/related bits clear), and a
         fabricated packet can no longer report ESTABLISHED out of thin air: it can
         only read what an entry for [pkt_flow p] holds.  See [ct_wf]/[Ct_Flow.v] for
         the well-formedness invariant that pins the initial state to NEW.

         The sole per-traversal exception is [CKstate] after a `notrack` statement:
         nft_notrack_eval sets the skb's ctinfo to IP_CT_UNTRACKED, so the subsequent
         nft_ct_get_eval NFT_CT_STATE read takes the `else if (ctinfo ==
         IP_CT_UNTRACKED)` branch and returns the constant NF_CT_STATE_UNTRACKED_BIT
         (= [0;0;0;64]); this is modelled by the per-traversal [pkt_untracked] flag
         and overrides the flow-table read.

         [CKdirection] is the OTHER per-packet (not per-flow-entry) exception, and it is
         NOT a free oracle: in the kernel the `ct direction` SELECTOR and the NAT manip
         direction are LITERALLY THE SAME value — both are CTINFO2DIR(ctinfo) of the one
         skb (nft_ct.c:86 `nft_reg_store8(dest, CTINFO2DIR(ctinfo))` for the selector;
         nf_nat_core.c:872 `dir = CTINFO2DIR(ctinfo)` then `if (dir == IP_CT_DIR_REPLY)`
         for the manip).  This model represents CTINFO2DIR(ctinfo) by the single bit
         [pkt_ctdir_orig] (true = IP_CT_DIR_ORIGINAL, false = IP_CT_DIR_REPLY; see
         Packet.v and [apply_nat]).  So the `ct direction` selector is DERIVED from that
         same bit — NOT read as an independent free byte from [e_ct] — guaranteeing that
         the selector and the NAT decision can never disagree, exactly as in the kernel.
         The byte is the kernel's [nft_reg_store8] single byte:
         IP_CT_DIR_ORIGINAL = 0 -> [0], IP_CT_DIR_REPLY = 1 -> [1]. *)
      (* [CKstate] is the ONLY key that yields a value when there is no conntrack
         entry (nft_ct.c:68-76): UNTRACKED packet -> NF_CT_STATE_UNTRACKED_BIT
         ([0;0;0;64]), any other no-entry/INVALID packet -> NF_CT_STATE_INVALID_BIT
         (= 1<<0 = [0;0;0;1]); a tracked packet reads the flow entry's state.  EVERY
         OTHER key is reached only past `if (ct == NULL) goto err` (nft_ct.c:81-82),
         so on a no-entry packet ([pkt_ct_present = false]) the load BREAKs — that
         break is enforced by [load_ok] below, which makes the enclosing match FAIL;
         the value computed here is only ever consumed when [load_ok] held (the entry
         is present), so the [CKdirection]/[_] branches read the live entry/direction. *)
      match k with
      | CKstate => if pkt_untracked p then [0;0;0;64]
                   else if pkt_ct_present p then e_ct (pkt_env p) (pkt_flow p) k
                   else [0;0;0;1]
      | CKdirection => if pkt_ctdir_orig p then [0] else [1]
      | _ => e_ct (pkt_env p) (pkt_flow p) k
      end
  | LRt k           => e_rt (pkt_env p) k
  | LSocket k       => pkt_sock p k
  | LNumgen spec    =>
      (* `numgen inc` reads the SHARED, persistent counter from the env and renders
         the round-robin value [(counter mod modulus) + offset]; the increment that
         makes the NEXT evaluation differ is applied by the write-side threading
         ([set_numgen] in [run_rule_writes]/[body_writes]).  `numgen random`
         (ng_random = true: get_random_u32) is genuinely per-packet, so it stays the
         oracle [pkt_numgen]. *)
      if ng_random spec then pkt_numgen p spec
      else numgen_inc_value spec (e_numgen (pkt_env p) spec)
  | LOsf            => pkt_osf p
  | LExthdr ep h o l pr => pkt_eh p ep h o l pr
  | LFib sel res    => lpm_fib (e_routes (pkt_env p)) (pkt_fibkey p sel) res
  | LCtDir key dir  => pkt_ctdir p key dir
  | LXfrm dir sp key => pkt_xfrm p dir sp key
  | LTunnel key      => pkt_tunnel p key
  | LSymhash m o     => pkt_symhash p m o
  | LInner t h fl desc _ => pkt_inner p t h fl desc
  | LPayload b o l  => read_payload b o l p
  end.

(** The value of a field in a packet. *)
Definition field_value (f : field) (p : packet) : data :=
  do_load (field_load f) p.

(** Whether an extension-header / TCP-option / SCTP-chunk VALUE load finds its
    target present.  Derived from the SAME underlying existence oracle the
    F_PRESENT load reports on ([pkt_eh p ep h 0 0 true]): nonzero <=> present.
    This links the "present?" flag and the "value bytes" so the impossible
    kernel state "option absent yet value=v" is no longer admissible: a VALUE
    load on an absent option is NOT loadable (matches the kernel's NFT_BREAK in
    nft_exthdr_{tcp,ipv6,ipv4}_eval err path, taken when F_PRESENT is unset). *)
Definition exthdr_present (p : packet) (ep : exthdr_proto) (h : nat) : bool :=
  List.existsb (fun b => negb (Nat.eqb b 0)) (pkt_eh p ep h 0 0 true).

(** Whether a load SUCCEEDS on a packet (does not cause the kernel to NFT_BREAK).
    A payload load can fail (a short/fragmented/no-L4/no-L2 header).  An exthdr
    VALUE load (present=false) fails when the requested extension header / TCP
    option / SCTP chunk is ABSENT — kernel nft_exthdr_*_eval `goto err` ->
    NFT_BREAK; an exthdr EXISTENCE load (present=true) NEVER breaks (the kernel
    stores 0 on the err path under F_PRESENT).  Every other load reads
    kernel-computed state or an oracle and always succeeds. *)
Definition load_ok (ld : loaddesc) (p : packet) : bool :=
  match ld with
  | LPayload b off len => read_payload_ok b off len p
  | LExthdr ep h _ _ pr => if pr then true else exthdr_present p ep h
  (* A conntrack load BREAKs when there is NO conntrack entry, for EVERY key
     EXCEPT [CKstate].  Kernel nft_ct.c:81-82 `if (ct == NULL) goto err;` (err sets
     NFT_BREAK, :220-221) — reached for direction/status/mark/expiration/id/zone/...;
     NFT_CT_STATE returns before that guard (:68-76), so it is the lone key that still
     yields a value (UNTRACKED/INVALID bits) on a no-entry packet.  Entry presence is
     [pkt_ct_present]: it is [false] for a packet with NO entry — an UNTRACKED packet
     (`nf_ct_set(skb, NULL, IP_CT_UNTRACKED)`, so [pkt_untracked] implies
     [pkt_ct_present = false] for a well-formed packet, see [ct_present_wf]) or a
     genuinely INVALID / no-entry packet.  On such a packet a non-state ct match must
     FAIL (the rule does not apply), so it can never spuriously match — mirroring the
     kernel's NFT_BREAK. *)
  | LCt CKstate => true
  | LCt _ => pkt_ct_present p
  | _ => true
  end.

(** Whether a field's load succeeds on a packet.  When [false] the corresponding
    match condition must FAIL (the rule does not apply), never compare a
    truncated value — this is the soundness fix. *)
Definition field_loadable (f : field) (p : packet) : bool :=
  load_ok (field_load f) p.

(** A match condition: equality / inequality against an immediate, or a
    (possibly negated) range membership [lo <= field <= hi]. *)
(** A register transform applied between a load and a comparison. *)
Inductive transform : Type :=
| TBitAnd    (mask xor : data)
| TShift     (shl : bool) (amt : nat)
| TByteorder (hton : bool) (size len : nat)
| TJhash     (len seed modulus offset : nat).

Inductive matchcond : Type :=
| MEq     (f : field) (v : data)
| MNeq    (f : field) (v : data)
| MRange  (f : field) (neg : bool) (lo hi : data)
| MMasked (f : field) (neg : bool) (mask xor v : data)   (* (field & mask) ^ xor cmp v *)
| MCmp    (f : field) (op : cmpop) (v : data)            (* ordered comparison field <op> v *)
| MConcatSet (fields : list field) (neg : bool) (name : string)
                            (* (concatenation of [fields]) [!]in the named set/map
                               (contents looked up at runtime, not inlined) *)
| MTransform (f : field) (ts : list transform) (op : cmpop) (v : data) (* cmp after transforms *)
| MSetT (f : field) (ts : list transform) (neg : bool) (name : string)
                            (* set membership of a transformed field value *)
| MRangeT (f : field) (ts : list transform) (neg : bool) (lo hi : data)
                            (* range test of a transformed field value *)
| MLimit  (spec : limit_spec)   (* stateful rate limit; passes per the packet oracle *)
| MQuota  (spec : quota_spec)   (* stateful byte quota; passes per the packet oracle *)
| MConnlimit (spec : connlimit_spec)   (* stateful connection limit; passes per oracle *)
| MConcatSetT (elems : list (field * list transform)) (neg : bool)
              (name : string).
                            (* (concatenation of per-element-transformed fields)
                               [!]in a set/map; each element is loaded into its own
                               register slot and transformed in place *)

(** Verdict-neutral statements: they emit bytecode but do not change the packet's
    verdict (counter accounts; notrack disables conntrack). *)
(** The value written by a set/mangle statement: either an immediate, or a field
    value (optionally transformed) computed into register 1. *)
Inductive vsrc : Type :=
| VImm   (v : data)
| VField (f : field) (ts : list transform)
| VMap   (fields : list field) (ts : list transform) (name : string)
| VHash  (fields : list field) (len seed modulus offset : nat)
                            (* jhash of the concatenation of [fields] (the hashed
                               value is a verdict-neutral set/mangle operand) *)
| VOr    (srcs : list (field * list transform)) (final : list transform)
                            (* a value built by OR-ing several (transformed) field
                               sources: the first is loaded into reg 1, each later
                               one into reg 2 then [bitwise reg1 = reg1 | reg2],
                               then [final] is applied in place on reg 1 *)
| VMapT  (elems : list (field * list transform)) (name : string)
                            (* value looked up by a concatenation key whose
                               elements are each transformed in place (cf.
                               [MConcatSetT]); the looked-up value lands in reg 1 *)
| VHashMap (fields : list field) (len seed modulus offset : nat)
           (name : string).
                            (* jhash of [fields] (into reg 1) used as the key of a
                               map lookup whose value lands in reg 1 — e.g.
                               `dnat to jhash ip saddr mod N map {...}` *)
                            (* value looked up by the concatenation of [fields]
                               (each, if a single field, optionally transformed by
                               [ts]) in a named map *)

Inductive stmt : Type :=
| SCounter (pkts bytes : nat)
| SNotrack
| SLog (opts : string)   (* verbatim log options; verdict-neutral side effect *)
| SMangle (vs : vsrc) (b : pbase) (off len : nat) (ctype coff cflags : nat)
                            (* payload write (verdict-neutral; the packet rewrite
                               is a side effect outside the model) *)
| SMetaSet (k : meta_key) (vs : vsrc)   (* meta set <k> with a value *)
| SCtSet   (k : ct_key) (vs : vsrc)     (* ct set <k> with a value *)
| SCtSetDir (key dir : string) (vs : vsrc)  (* directional ct set (zone, ...) *)
| SObjref  (otype : nat) (oname : string)   (* reference a named stateful object *)
| SSynproxy (mss wscale : nat)              (* SYN-proxy: verdict-BEARING — a
                               non-TCP packet BREAKs the rule (NFT_BREAK), a TCP
                               SYN/ACK STOPS traversal (NF_STOLEN/NF_DROP, modelled
                               as terminal Drop), other TCP packets CONTINUE; see
                               [Semantics.synproxy_stops]/[run_rule]. *)
| SLast    (info : string)                  (* `last used` accounting; verbatim *)
| SDynset  (op name : string) (keyfs dataf : list field)
                            (* add/delete [keyfs] (-> [dataf] for a map) to a set *)
| SExthdrReset (proto : string) (htype : nat)
                            (* reset (clear) a TCP option; verdict-neutral *)
| SDup (imms : list (nat * data)) (devreg addrreg : option nat)
                            (* duplicate the packet to a device/address loaded by
                               [imms]; verdict-neutral (the dup is a side effect) *)
| SObjrefMap (keyfs : list field) (name : string)
| SDynsetImm (op name : string) (keyfs : list field)
             (dimms : list (nat * data)) (datareg : nat)
                            (* dynset whose map data is immediate constants loaded
                               into data registers [dimms]; verdict-neutral *)
| SExthdrWrite (vs : vsrc) (proto : string) (htype off len : nat)
                            (* write a value into a TCP-option exthdr field;
                               verdict-neutral (packet rewrite outside the model) *)
| SDupSrc (src : vsrc) (imms : list (nat * data)) (devreg addrreg : option nat).
                            (* duplicate the packet to a device/address where one
                               operand is computed by a value source [src] (e.g. a
                               map lookup into reg 1) and the rest by [imms];
                               verdict-neutral (the dup is a side effect) *)
                            (* reference a stateful object selected by looking up
                               the concatenation of [keyfs] in a named object map *)
                            (* dynamically add/delete the concatenation of [keyfs]
                               to a set; verdict-neutral (the mutation is a side
                               effect outside the single-packet model) *)

(** A verdict map: the rule's verdict comes from looking up the concatenation of
    [vm_fields] in the named map (entries live in NEWSET; carried for semantics,
    empty in the control-plane round-trip). *)
Record vmap_spec : Type := {
  vm_fields  : list field;
  vm_keyf    : option (field * list transform);
                            (* if [Some (f, ts)] the lookup key is the single
                               transformed field value [apply_transforms ts f]
                               instead of the concatenation of [vm_fields] *)
  vm_name    : string;      (* the verdict map's entries are looked up by name *)
}.

(** A NAT statement (snat/dnat).  The address/port operands are loaded into data
    registers by the immediates in [nat_imms]; the statement then references those
    registers.  NAT is terminal (it accepts with a translation); the packet
    rewrite itself is a side effect outside the single-packet verdict model. *)
Record nat_spec : Type := {
  nat_imms   : list (nat * data);   (* immediate operand loads (reg, value) *)
  nat_field  : option (field * list transform);
                            (* operand straight from a (transformed) packet field,
                               `dnat to ip saddr` (no map lookup) *)
  nat_map    : option (list field * list transform * string);
                            (* alternative operand source: the concatenation of
                               [fields] (after the transforms) looked up in a named
                               map, into register 1 — `dnat to ip saddr map {...}`.
                               The looked-up value is consumed by the terminal NAT,
                               which the single-packet model sees only as Accept. *)
  nat_src    : option vsrc;         (* general operand value source into register 1
                                       (e.g. a jhash-keyed map, [VHashMap]) *)
  nat_kind   : string;              (* "snat" / "dnat" / "masq" / "redir" *)
  nat_family : string;              (* "ip" / "ip6"; "" for masq/redir *)
  nat_amin   : option nat;          (* None for masq/redir *)
  nat_amax   : option nat;
  nat_pmin   : option nat;
  nat_pmax   : option nat;
  nat_flags  : nat;
}.

(** A [tproxy] statement (transparent proxy): terminal, like NAT.  The target
    address/port are loaded into data registers by [tp_imms]; the statement then
    references those registers.  The redirection is a side effect outside the
    single-packet verdict model (which sees a terminal Accept). *)
Record tproxy_spec : Type := {
  tp_imms   : list (nat * data);   (* immediate operand loads (reg, value) *)
  tp_portmap : option (nat * nat * string);
                            (* the target port computed by a symhash (modulus,
                               offset) keyed map lookup into register 2 — e.g.
                               `tproxy to :symhash mod N map {...}`; the map's
                               entries are looked up by name at runtime *)
  tp_family : string;              (* "ip" / "ip6" / "" *)
  tp_areg   : option nat;          (* target-address register, if any *)
  tp_preg   : option nat;          (* target-port register, if any *)
}.

(** A [fwd] statement: terminal (like NAT/tproxy) — forward the packet to a device
    (and optionally address) loaded by [fwd_imms]; the forward is a side effect
    outside the single-packet verdict model (which sees a terminal Accept). *)
Record fwd_spec : Type := {
  fwd_imms    : list (nat * data);
  fwd_src     : option vsrc;       (* the device computed by a value source
                                      (e.g. a map lookup) instead of immediates *)
  fwd_devreg  : option nat;
  fwd_addrreg : option nat;
  fwd_nfproto : option nat;
}.

(** A value-sourced [queue] verdict: terminal (sends the packet to a userspace
    queue whose number is the value [q_num] — e.g. `queue to numgen inc mod 4`);
    the queue hand-off is a side effect outside the single-packet model (a terminal
    Accept).  REGISTER-FREE source: [q_num] names the number EXPRESSION; the
    compiler ([compile_terminal]) loads it into register 1 and emits
    [IQueueSreg 1 …], reproducing nft's fixed register convention. *)
Record queue_spec : Type := {
  q_num    : vsrc;             (* the queue-number value expression *)
  q_bypass : bool;
  q_fanout : bool;
}.

(** A rule body item: either a match condition or a verdict-neutral statement.
    nftables emits matches and statements in source order (a match may follow a
    statement), so the body is an *ordered* list rather than separate match/stmt
    lists — this lets the compiler reproduce nft's instruction order exactly. *)
Inductive body_item : Type :=
| BMatch (m : matchcond)
| BStmt  (s : stmt).

(** The match conditions of a body, in order (statements dropped). *)
Definition body_matches (b : list body_item) : list matchcond :=
  flat_map (fun it => match it with BMatch m => m :: nil | BStmt _ => nil end) b.

(** The [dynset] op string denoting element removal (`delete @s {...}`), vs the
    add/update insertion ops.  Defined here, where [String] notation is in scope,
    so [Semantics.env_set_upd] can branch on it without importing [String]. *)
Definition op_delete : string := "delete".

(** The [nat_kind] strings, branched on by [Semantics.apply_nat] to select the
    data-plane rewrite:
    - [nat_masq_kind] ("masq") source-NATs to the exit interface's address;
    - [nat_snat_kind] ("snat") source-NATs to the operand address (reg 1);
    - [nat_dnat_kind] ("dnat") dest-NATs to the operand address (reg 1);
    - [nat_redir_kind] ("redir") dest-NATs to the inbound interface's address
      (redirect = local DNAT). *)
Definition nat_masq_kind  : string := "masq".
Definition nat_snat_kind  : string := "snat".
Definition nat_dnat_kind  : string := "dnat".
Definition nat_redir_kind : string := "redir".

(** The [nat_family] strings, branched on by [Semantics.apply_nat] to pick the
    address geometry: "ip" = the 32-bit IPv4 slot, "ip6" = the 128-bit IPv6 slot
    (the kernel chooses 32 vs 128 bits by family — [nat_addrlen],
    netlink_linearize.c:1237).  Defined here, where [String] is in scope. *)
Definition nat_fam_ip4 : string := "ip".
Definition nat_fam_ip6 : string := "ip6".

(** The [inet] family is a RUNTIME-DISPATCHED sentinel: an `inet` table has ONE
    NAT rule that processes BOTH IPv4 and IPv6 packets, and the kernel dispatches
    on the PACKET's L3 family at runtime (nft_masq_inet_eval: `switch (nft_pf(pkt))`
    -> NFPROTO_IPV4 -> nf_nat_masquerade_ipv4 (4-byte IPv4 slot) vs NFPROTO_IPV6 ->
    nf_nat_masquerade_ipv6 (16-byte IPv6 slot)).  No STATIC family can be correct,
    so a NAT statement in an inet table carries [nat_fam_inet], which the data-plane
    NAT functions resolve per-packet ([Semantics.nat_addrfamily_pkt]). *)
Definition nat_fam_inet : string := "inet".

(** A rule: an ordered body (matches + verdict-neutral statements) then an
    outcome — a static verdict, a verdict-map lookup ([r_vmap]), or a terminal
    redirect ([r_nat] / [r_tproxy]). *)
Record rule : Type := {
  r_body    : list body_item;
  r_verdict : verdict;
  r_vmap    : option vmap_spec;
  r_nat     : option nat_spec;
  r_tproxy  : option tproxy_spec;
  r_fwd     : option fwd_spec;
  r_queue   : option queue_spec;
  r_after   : list stmt;
                            (* verdict-neutral statements emitted *after* the
                               outcome (e.g. a counter after a verdict map); they
                               run for their side effect but cannot change the
                               verdict, which the terminal outcome already fixed *)
}.

(** A base chain: a default policy and an ordered list of rules. *)
Record chain : Type := {
  c_policy : verdict;
  c_rules  : list rule;
}.

(** Organisational layers (carried through to the control-plane command list;
    the packet-filtering theorem is stated per base chain). *)
Record table : Type := {
  t_name   : string;
  t_chains : list (string * chain);
}.

Definition ruleset := list table.
