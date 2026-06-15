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
| FRtGen (k : rt_key)
| FSocketGen (k : socket_key)
| FNumgen (spec : numgen_spec)
| FOsf
| FFib (sel : string) (res : fib_result)
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
  | FRtGen k => LRt k
  | FSocketGen k => LSocket k
  | FNumgen spec => LNumgen spec
  | FOsf => LOsf
  | FFib sel res => LFib sel res
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

(** Evaluate a load against a packet. *)
Definition do_load (ld : loaddesc) (p : packet) : data :=
  match ld with
  | LMeta k         => pkt_meta p k
  | LCt k           => pkt_ct p k
  | LRt k           => pkt_rt p k
  | LSocket k       => pkt_sock p k
  | LNumgen spec    => pkt_numgen p spec
  | LOsf            => pkt_osf p
  | LExthdr ep h o l pr => pkt_eh p ep h o l pr
  | LFib sel res    => pkt_fib p sel res
  | LInner t h fl desc _ => pkt_inner p t h fl desc
  | LPayload b o l  => read_payload b o l p
  end.

(** The value of a field in a packet. *)
Definition field_value (f : field) (p : packet) : data :=
  do_load (field_load f) p.

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
| MConcatSet (fields : list field) (neg : bool) (name : string) (elems : list data)
                            (* (concatenation of [fields]) [!]in a set/map *)
| MTransform (f : field) (ts : list transform) (neg : bool) (v : data) (* cmp after transforms *)
| MSetT (f : field) (ts : list transform) (neg : bool) (name : string) (elems : list data)
                            (* set membership of a transformed field value *)
| MRangeT (f : field) (ts : list transform) (neg : bool) (lo hi : data)
                            (* range test of a transformed field value *)
| MLimit  (spec : limit_spec).  (* stateful rate limit; passes per the packet oracle *)

(** Verdict-neutral statements: they emit bytecode but do not change the packet's
    verdict (counter accounts; notrack disables conntrack). *)
(** The value written by a set/mangle statement: either an immediate, or a field
    value (optionally transformed) computed into register 1. *)
Inductive vsrc : Type :=
| VImm   (v : data)
| VField (f : field) (ts : list transform)
| VMap   (f : field) (name : string) (entries : list (data * data)).
                            (* value looked up by [field] in a named map *)

Inductive stmt : Type :=
| SCounter (pkts bytes : nat)
| SNotrack
| SLog (level : option nat)
| SMangle (vs : vsrc) (b : pbase) (off len : nat) (ctype coff cflags : nat)
                            (* payload write (verdict-neutral; the packet rewrite
                               is a side effect outside the model) *)
| SMetaSet (k : meta_key) (vs : vsrc)   (* meta set <k> with a value *)
| SCtSet   (k : ct_key) (vs : vsrc).    (* ct set <k> with a value *)

(** A verdict map: the rule's verdict comes from looking up the concatenation of
    [vm_fields] in the named map (entries live in NEWSET; carried for semantics,
    empty in the control-plane round-trip). *)
Record vmap_spec : Type := {
  vm_fields  : list field;
  vm_name    : string;
  vm_entries : list (data * verdict);
}.

(** A NAT statement (snat/dnat).  The address/port operands are loaded into data
    registers by the immediates in [nat_imms]; the statement then references those
    registers.  NAT is terminal (it accepts with a translation); the packet
    rewrite itself is a side effect outside the single-packet verdict model. *)
Record nat_spec : Type := {
  nat_imms   : list (nat * data);   (* immediate operand loads (reg, value) *)
  nat_kind   : string;              (* "snat" / "dnat" / "masq" / "redir" *)
  nat_family : string;              (* "ip" / "ip6"; "" for masq/redir *)
  nat_amin   : option nat;          (* None for masq/redir *)
  nat_amax   : option nat;
  nat_pmin   : option nat;
  nat_pmax   : option nat;
  nat_flags  : nat;
}.

(** A rule: matches, then verdict-neutral statements, then an outcome — a static
    verdict, a verdict-map lookup ([r_vmap]), or a NAT statement ([r_nat]). *)
Record rule : Type := {
  r_matches : list matchcond;
  r_stmts   : list stmt;
  r_verdict : verdict;
  r_vmap    : option vmap_spec;
  r_nat     : option nat_spec;
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
