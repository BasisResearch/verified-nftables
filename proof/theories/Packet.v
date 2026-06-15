(** * Packet: the object both languages observe.

    nftables matches inspect two kinds of data:
      - metadata computed by the kernel (e.g. [l4proto], the L4 protocol number),
        accessed by a [meta] expression keyed by a [meta_key];
      - raw header bytes, accessed by a [payload] expression as
        (base, offset, length) where base is the network or transport header.

    We model a packet as a metadata function plus the network/transport header
    byte strings.  This is faithful to how nft's bytecode reads a packet, and it
    is the *single* packet representation used by BOTH the declarative semantics
    and the bytecode VM, so the equivalence theorem is about real behaviour, not
    an artefact of two different packet models. *)

From Stdlib Require Import List NArith String.
From Nft Require Import Bytes.
Import ListNotations.

(** Metadata keys (numeric kernel metadata).  Adding a key is just a new
    constructor — the compiler proof is generic over [meta_key]. *)
Inductive meta_key : Type :=
| MKl4proto | MKnfproto | MKprotocol | MKmark
| MKiif | MKoif | MKiiftype | MKoiftype | MKiifname | MKoifname
| MKlen | MKpkttype | MKcpu | MKskuid | MKskgid | MKpriority
| MKcgroup | MKday | MKhour | MKiifgroup | MKoifgroup | MKprandom
| MKrtclassid | MKsdif | MKsdifname | MKsecpath | MKtime
| MKbri_iifname | MKbri_oifname | MKbri_iifpvid | MKbri_iifvproto | MKibrhwaddr.

(** Conntrack keys (read by a [ct load] expression). *)
Inductive ct_key : Type :=
| CKstate | CKstatus | CKmark | CKdirection | CKexpiration | CKid
| CKavgpkt | CKbytes | CKhelper | CKl3proto | CKlabel | CKpackets
| CKproto | CKzone | CKevent.

(** Routing-state keys ([rt load]) and socket keys ([socket load]); both read
    external state, modelled as packet oracles. *)
Inductive rt_key : Type :=
| RKclassid | RKnexthop4 | RKnexthop6 | RKtcpmss | RKmtu | RKipsec.
Inductive socket_key : Type :=
| SKtransparent | SKmark | SKwildcard | SKcgroupv2.

(** Protocol an [exthdr load] reads from (IPv6 extension headers / TCP options). *)
Inductive exthdr_proto : Type :=
| EPipv6 | EPtcpopt | EPsctp.

(** The result selector of a `fib` route lookup, which fixes the value width:
    [FRoif]/[FRtype] are 4-byte words, [FRoifname] a 16-byte interface name,
    [FRpresent] a 1-byte existence boolean. *)
Inductive fib_result : Type :=
| FRoif | FRoifname | FRtype | FRpresent.

(** A rate-limit configuration (rate per [ls_unit]: 0=second 1=minute 2=hour
    3=day 4=week; [ls_bytes] = byte-rate vs packet-rate). *)
Record limit_spec : Type := {
  ls_rate : nat; ls_unit : nat; ls_burst : nat; ls_bytes : bool; ls_flags : nat
}.

(** A number generator (`numgen`): [ng_random] inc-vs-random, modulus, offset. *)
Record numgen_spec : Type := {
  ng_random : bool; ng_mod : nat; ng_offset : nat
}.

(** A quota: [q_bytes] the limit, [q_consumed] bytes already used, [q_flags] the
    NFT_QUOTA_F_* bits (bit 0 = "over"/inverted). *)
Record quota_spec : Type := {
  q_bytes : nat; q_consumed : nat; q_flags : nat
}.

(** A connection limit: [cl_count] the threshold, [cl_flags] (bit 0 = "over"). *)
Record connlimit_spec : Type := {
  cl_count : nat; cl_flags : nat
}.

(** Payload bases: which header a [payload load] reads from. *)
Inductive pbase : Type :=
| PLink
| PNetwork
| PTransport
| PInner
| PTunnel.

Record packet : Type := {
  pkt_meta : meta_key -> data;   (* kernel-computed metadata *)
  pkt_ct   : ct_key -> data;     (* conntrack state *)
  pkt_rt   : rt_key -> data;     (* routing-state oracle *)
  pkt_sock : socket_key -> data; (* socket-state oracle *)
  pkt_eh   : exthdr_proto -> nat -> nat -> nat -> bool -> data;
                            (* exthdr: proto htype off len present?  present=true
                               reads the existence flag, false the header bytes *)
  pkt_lh   : list byte;          (* link-header bytes (e.g. Ethernet) *)
  pkt_nh   : list byte;          (* network-header bytes (e.g. IPv4/IPv6) *)
  pkt_th   : list byte;          (* transport-header bytes (e.g. TCP/UDP) *)
  pkt_ih   : list byte;          (* inner-header bytes (tunnelled packet) *)
  pkt_tnl  : list byte;          (* tunnel-header bytes *)
  pkt_limit : limit_spec -> bool; (* oracle: does this packet pass a given limiter? *)
  pkt_quota : quota_spec -> bool; (* oracle: does this packet pass a given quota? *)
  pkt_connlimit : connlimit_spec -> bool;  (* oracle: under the connection limit? *)
  pkt_numgen : numgen_spec -> data;  (* oracle: numgen output (per-packet abstraction
                                        of a global counter; cannot distinguish two
                                        firings of one packet — see DEVELOPMENT.md) *)
  pkt_osf  : data;                   (* oracle: OS-fingerprint value (packet-determined) *)
  pkt_fib  : string -> fib_result -> data;
                            (* oracle: route lookup.  The string is the selector
                               specification (which inputs the lookup uses, e.g.
                               "saddr . iif"); the result selector fixes what the
                               routing table yields. *)
  pkt_tunnel : string -> data;    (* oracle: a tunnel-metadata field by name *)
  pkt_symhash : nat -> nat -> data;  (* oracle: symmetric packet hash (mod, offset) *)
  pkt_xfrm : string -> nat -> string -> data;
                            (* oracle: an IPsec xfrm-state field, keyed by
                               direction ("in"/"out"), SA spnum, and field name. *)
  pkt_ctdir : string -> string -> data;
                            (* oracle: a directional conntrack field (e.g. the
                               original/reply tuple address), keyed by the field
                               name and the direction ("original"/"reply"). *)
  pkt_inner : nat -> nat -> nat -> string -> data;
                            (* oracle: a field read from the decapsulated inner
                               packet of a tunnel.  Keyed by tunnel (type, hdrsize,
                               flags) and a descriptor of the inner field (e.g.
                               "meta load protocol").  The inner packet is a
                               separate packet, so its fields are an independent
                               oracle rather than a function of the outer headers. *)
}.

(** Read [len] bytes at [off] from a header byte string. *)
Definition slice (bs : list byte) (off len : nat) : data :=
  firstn len (skipn off bs).

(** A payload read, shared by the DSL field semantics and the bytecode VM. *)
Definition read_payload (b : pbase) (off len : nat) (p : packet) : data :=
  match b with
  | PLink      => slice (pkt_lh p) off len
  | PNetwork   => slice (pkt_nh p) off len
  | PTransport => slice (pkt_th p) off len
  | PInner     => slice (pkt_ih p) off len
  | PTunnel    => slice (pkt_tnl p) off len
  end.
