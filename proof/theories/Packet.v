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
From Nft Require Import Bytes Verdict.
Import ListNotations.

(** Metadata keys (numeric kernel metadata).  Adding a key is just a new
    constructor — the compiler proof is generic over [meta_key]. *)
Inductive meta_key : Type :=
| MKl4proto | MKnfproto | MKprotocol | MKmark
| MKiif | MKoif | MKiiftype | MKoiftype | MKiifname | MKoifname
| MKlen | MKpkttype | MKcpu | MKskuid | MKskgid | MKpriority
| MKcgroup | MKday | MKhour | MKiifgroup | MKoifgroup | MKprandom
| MKrtclassid | MKsdif | MKsdifname | MKsecpath | MKtime
| MKbri_iifname | MKbri_oifname | MKbri_iifpvid | MKbri_iifvproto | MKibrhwaddr
| MKbroute.

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

(** The named, runtime-mutable table state a ruleset is evaluated against: a
    [lookup @s] does NOT read contents baked into the rule — it reads the current
    contents of the named set/map from this environment.  Modelling it as a
    function of the name keeps it decoupled from the rule AST, so the correctness
    theorem (quantified over the whole evaluation environment) holds for *every*
    set/map state, i.e. as the sets are added to / deleted from at runtime.
    (It is transported alongside the packet here as the per-evaluation
    environment; making it a standalone parameter is a cosmetic refactor that
    does not change the theorem.) *)
Record env : Type := {
  e_set  : string -> list (data * data);    (* a named set's elements as closed
                                               intervals [lo,hi] (exact = [x,x],
                                               CIDR/range = [lo,hi]); see [set_mem] *)
  e_vmap : string -> list (data * verdict);  (* a named verdict map's entries *)
  e_map  : string -> list (data * data);     (* a named value map's entries *)
  e_routes : list (data * data * (fib_result -> data));
                            (* the ROUTING TABLE a `fib` lookup consults: a list of
                               routes, each a destination interval [lo,hi] (a prefix
                               10.0.0.0/8 = [10.0.0.0, 10.255.255.255]) paired with
                               its result function (oif / type / oifname / present).
                               Shared external state.  The fib RESULT is *computed*
                               by [lpm_fib] (first containing route, i.e. the table
                               ordered most-specific-first = longest-prefix-match),
                               not an opaque oracle. *)
  e_rt   : rt_key -> data;                   (* routing-state (rt) keys, likewise
                                                shared external routing state. *)
  e_limit : limit_spec -> nat;               (* a rate limiter's REMAINING tokens;
                                                a `limit` match passes (rule
                                                continues) iff [0 < remaining]. *)
  e_quota : quota_spec -> nat;               (* a quota's remaining bytes. *)
  e_ifaddr : data -> data;                   (* an interface's primary IPv4 source
                                                address, keyed by its name — the
                                                source `masquerade` rewrites an IPv4
                                                packet to (the IP of the interface
                                                it exits).  Shared host config. *)
  e_ifaddr6 : data -> data;                  (* an interface's primary IPv6 source
                                                address (a 16-byte in6_addr), keyed
                                                by its name — what an IPv6
                                                `masquerade` rewrites to.  The kernel
                                                computes it via ipv6_dev_get_saddr
                                                (nf_nat_masquerade_ipv6); it is a
                                                DIFFERENT value from the IPv4
                                                e_ifaddr.  Shared host config. *)
  e_connlimit : connlimit_spec -> nat;       (* a connlimit's remaining slots.
                                                These are shared, mutable limiter
                                                state, threaded across packets by
                                                [eval_seq] (see Semantics) — so the
                                                accumulation that a per-packet
                                                oracle hid is now expressible. *)
}.

Record packet : Type := {
  pkt_env  : env;                (* the named set/map state (see [env] above) *)
  pkt_meta : meta_key -> data;   (* kernel-computed metadata *)
  pkt_ct   : ct_key -> data;     (* conntrack state *)
  pkt_sock : socket_key -> data; (* socket-state oracle *)
  pkt_eh   : exthdr_proto -> nat -> nat -> nat -> bool -> data;
                            (* exthdr: proto htype off len present?  present=true
                               reads the existence flag, false the header bytes *)
  pkt_lh   : list byte;          (* link-header bytes (e.g. Ethernet) *)
  pkt_nh   : list byte;          (* network-header bytes (e.g. IPv4/IPv6) *)
  pkt_th   : list byte;          (* transport-header bytes (e.g. TCP/UDP) *)
  pkt_ih   : list byte;          (* inner-header bytes (tunnelled packet) *)
  pkt_tnl  : list byte;          (* tunnel-header bytes *)
  pkt_fibkey : string -> data;   (* the lookup KEY a fib selector extracts from
                                    this packet (e.g. for "saddr . iif" the source
                                    address): genuinely packet-determined.  The
                                    routing-table LOOKUP on this key is computed by
                                    [lpm_fib] against the shared [e_routes]. *)
  pkt_numgen : numgen_spec -> data;  (* oracle: numgen output (per-packet abstraction
                                        of a global counter; cannot distinguish two
                                        firings of one packet — see DEVELOPMENT.md) *)
  pkt_osf  : data;                   (* oracle: OS-fingerprint value (packet-determined) *)
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
  pkt_have_l4 : bool;       (* whether the kernel set NFT_PKTINFO_L4PROTO for this
                               packet (i.e. a transport/L4 header was parsed).  A
                               TRANSPORT-base payload load on a packet WITHOUT this
                               flag BREAKs the rule (kernel nft_payload.c
                               nft_payload_eval: `if (!(pkt->flags &
                               NFT_PKTINFO_L4PROTO) || pkt->fragoff) goto err;`). *)
  pkt_fragoff : nat;        (* the IP fragment offset; a nonzero offset means this is
                               a non-first fragment with no usable transport header,
                               so a TRANSPORT-base load likewise BREAKs the rule. *)
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

(** The header byte string a base reads from. *)
Definition base_bytes (b : pbase) (p : packet) : list byte :=
  match b with
  | PLink      => pkt_lh p
  | PNetwork   => pkt_nh p
  | PTransport => pkt_th p
  | PInner     => pkt_ih p
  | PTunnel    => pkt_tnl p
  end.

(** Whether a payload read of [len] bytes at [off] from base [b] SUCCEEDS, i.e.
    does NOT cause the kernel's nft_payload_eval to `goto err` (which sets the
    verdict to NFT_BREAK and so makes the rule NOT match).  Faithful to
    linux net/netfilter/nft_payload.c:

      - a TRANSPORT (and decapsulated-INNER) load requires the L4 header was
        parsed and the packet is not an IP fragment:
          `if (!(pkt->flags & NFT_PKTINFO_L4PROTO) || pkt->fragoff) goto err;`
      - ANY load must fit in the header bytes (skb_copy_bits returns <0 / the read
        runs off the end of the header otherwise):
          `if (skb_copy_bits(skb, offset, dest, priv->len) < 0) goto err;`

    A failed read must FAIL the rule's match (return [false] here), never compare a
    truncated/empty value — that silent truncation was the soundness bug. *)
Definition read_payload_ok (b : pbase) (off len : nat) (p : packet) : bool :=
  let l4_ok :=
    match b with
    | PTransport | PInner =>
        andb (pkt_have_l4 p) (Nat.eqb (pkt_fragoff p) 0)
    | _ => true
    end in
  andb l4_ok (negb (Nat.ltb (List.length (base_bytes b p)) (off + len))).

(** Longest-prefix-match routing lookup: return the result-[res] component of the
    first route whose destination interval contains [key] (the table is kept
    most-specific-first, so "first containing route" = longest prefix match); [] if
    no route matches (unreachable).  Used by the `fib` field semantics on both
    sides, so the routing-table lookup is a *computed* function of the shared route
    table, not an opaque per-packet oracle. *)
Fixpoint lpm_fib (routes : list (data * data * (fib_result -> data)))
                 (key : data) (res : fib_result) : data :=
  match routes with
  | [] => []
  | (lo, hi, f) :: rest =>
      if andb (data_le lo key) (data_le key hi) then f res else lpm_fib rest key res
  end.
