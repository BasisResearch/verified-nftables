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

(** Which conntrack keys are WRITABLE *and PERSISTENT* — i.e. a `ct <k> set V`
    stores V into the SHARED per-flow conntrack entry (kernel nft_ct.c
    nft_ct_set_eval: `ct = nf_ct_get(skb,&ctinfo); WRITE_ONCE(ct->mark/secmark, V)`,
    `nf_ct_labels(...)`), so that EVERY later packet of the same flow reads V back
    (nft_ct_get_eval: `ct = nf_ct_get(skb,&ctinfo); *dest = READ_ONCE(ct->mark)`).
    These are [CKmark] (NFT_CT_MARK) and [CKlabel] (NFT_CT_LABELS); the model has no
    separate secmark key (it folds into mark/label coverage).  Every OTHER key
    ([CKstate], [CKdirection], [CKexpiration], counters, [CKzone], …) is computed
    by the kernel PER-skb from the flow's current state and is NOT a value the rule
    can store back, so it stays a per-packet oracle ([pkt_ct]).  [CKevent]
    (NFT_CT_EVENTMASK) is settable but configures event delivery — it is never read
    back by `ct ... get`, so it is not modelled as persistent state either. *)
Definition ct_writable (k : ct_key) : bool :=
  match k with
  | CKmark | CKlabel => true
  | _ => false
  end.

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

(** Structural equality on [numgen_spec], used to key the shared per-instance
    `numgen inc` counter [e_numgen] (each `numgen` expression in a ruleset has its
    OWN atomic counter in the kernel; here we conflate instances with the same
    parameters, which is conservative and sufficient — a ruleset rarely repeats an
    identical numgen). *)
Definition numgen_eqb (a b : numgen_spec) : bool :=
  andb (Bool.eqb (ng_random a) (ng_random b))
       (andb (Nat.eqb (ng_mod a) (ng_mod b)) (Nat.eqb (ng_offset a) (ng_offset b))).

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
  e_vmap : string -> list (data * data * verdict);
                            (* a named verdict map's entries, each a closed-interval
                               KEY [lo,hi] paired with its verdict.  A point key is the
                               degenerate [x,x]; an interval/prefix key (the kernel
                               rbtree set is NFT_SET_INTERVAL | NFT_SET_MAP, so
                               `ip hdrlength vmap { 0-4 : drop, 5 : accept }` and
                               `ip6 saddr vmap { ::/64 : accept }` are valid) is the
                               full [lo,hi].  Lookup ([assoc_verdict]) returns the
                               verdict of the first entry whose interval CONTAINS the
                               key (lo <= key <= hi, big-endian) — an LPM/interval
                               search matching nft_set_rbtree, symmetric with the
                               named-set [set_mem] which already does intervals. *)
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
  e_ct : data -> ct_key -> data;             (* the SHARED, flow-keyed conntrack
                                                table: the writable+persistent
                                                conntrack keys ([ct_writable]: mark,
                                                label) stored in each flow's
                                                conntrack entry, keyed by a flow
                                                identifier ([pkt_flow]).  A
                                                `ct mark set V` on one packet writes
                                                [e_ct flow CKmark := V] here, and a
                                                later packet of the SAME flow reads it
                                                back via [do_load (LCt CKmark)] —
                                                mirroring the kernel's nf_ct_get(skb)
                                                selecting the shared entry by tuple +
                                                WRITE_ONCE/READ_ONCE(ct->mark).  This
                                                is the cross-packet state a per-packet
                                                [pkt_ct] oracle could not express. *)
  e_nat : data -> option (option data * option data * option nat);
                            (* the SHARED, flow-keyed NAT-mapping table: the
                               translation tuple the kernel ESTABLISHES ONCE on the
                               first (unconfirmed) packet of a flow and STORES in the
                               conntrack entry ([nf_nat_setup_info]:
                               get_unique_tuple + nf_conntrack_alter_reply), then
                               REUSES for every later packet WITHOUT re-evaluating the
                               rule operand (confirmed packets return NF_ACCEPT and the
                               rewrite comes from the stored tuple via
                               nf_nat_manip_pkt).  [e_nat flow = None] means no mapping
                               is established for the flow yet (the first packet
                               computes + stores one); [Some (orig_addr_opt, new_addr_opt,
                               port_opt)] is the established translation — the ORIGINAL
                               (pre-NAT) L3 address of the manip slot (needed to apply the
                               INVERSE manip on reply-direction packets, mirroring the
                               kernel storing both tuples of the conntrack entry), the new
                               L3 address (if a NAT_REG_ADDR operand was present), and the
                               new L4 port (if a NAT_REG_PROTO operand was present).  This
                               is the flow-keyed NAT state a per-packet pure [apply_nat]
                               could not express — the exact analogue of [e_ct] for the
                               NAT tuple.  [apply_nat] applies [new_addr_opt] FORWARD on an
                               original-direction packet ([pkt_ctdir_orig = true]) and
                               restores [orig_addr_opt] on the OPPOSITE slot for a reply
                               ([pkt_ctdir_orig = false]) — nf_nat_packet's direction
                               inversion. *)
  e_numgen : numgen_spec -> nat;
                            (* the SHARED, persistent `numgen inc` counter, keyed by the
                               numgen instance ([numgen_spec]) — each `numgen inc`
                               expression has its OWN atomic counter in the kernel
                               (nft_ng_inc: `atomic_t *counter`, allocated per expression
                               in nft_ng_inc_init).  This is the COUNT of evaluations the
                               instance has performed so far (the kernel stores the last
                               returned [nval]; we store the eval count [c], from which the
                               kernel's stored value is recovered as [c mod modulus]).  The
                               value handed to the next evaluation is
                               [(e_numgen spec mod ng_mod spec) + ng_offset spec] (rendered
                               big-endian, 4 bytes), and the counter is then INCREMENTED so
                               the NEXT evaluation (this packet's later firing, or the next
                               packet's firing) gets the successor — i.e. successive evals
                               are round-robin 0,1,...,N-1,0,...  This is the cross-packet
                               state the per-packet [pkt_numgen] oracle could not express
                               (it let two distinct packets both read 0); the increment is
                               threaded across packets by [run_rule_writes]/[body_writes]
                               exactly like the dynset/ct/nat env writes.  ONLY the
                               incremental generator (ng_random = false) uses this; the
                               RANDOM generator (ng_random = true,
                               nft_ng_random_gen: get_random_u32) stays a genuine per-packet
                               oracle [pkt_numgen]. *)
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
  pkt_have_l2 : bool;       (* whether the skb carries a built MAC/link-layer header,
                               i.e. skb_mac_header_was_set(skb) && skb_mac_header_len(skb)
                               != 0.  A LINK-LAYER-base (ether) payload load on a packet
                               WITHOUT this BREAKs the rule (kernel nft_payload.c
                               nft_payload_eval: `case NFT_PAYLOAD_LL_HEADER: if
                               (!skb_mac_header_was_set(skb) || skb_mac_header_len(skb) == 0)
                               goto err;`).  This is the L2 analogue of [pkt_have_l4]: for
                               LOCALLY-GENERATED packets at the output/postrouting hooks the
                               L2 header has not been built, so every `ether saddr/daddr/type`
                               load BREAKs -> the rule is skipped.  Every freshly-built test
                               packet defaults to [true] (an L2-bearing packet); a
                               locally-generated packet sets it [false]. *)
  pkt_have_l4 : bool;       (* whether the kernel set NFT_PKTINFO_L4PROTO for this
                               packet (i.e. a transport/L4 header was parsed).  A
                               TRANSPORT-base payload load on a packet WITHOUT this
                               flag BREAKs the rule (kernel nft_payload.c
                               nft_payload_eval: `if (!(pkt->flags &
                               NFT_PKTINFO_L4PROTO) || pkt->fragoff) goto err;`). *)
  pkt_fragoff : nat;        (* the IP fragment offset; a nonzero offset means this is
                               a non-first fragment with no usable transport header,
                               so a TRANSPORT-base load likewise BREAKs the rule. *)
  pkt_untracked : bool;     (* whether a `notrack` statement has run earlier in THIS
                               packet's traversal, forcing the conntrack state to
                               IP_CT_UNTRACKED for the rest of the traversal (kernel
                               nft_notrack_eval: nf_ct_set(skb, NULL, IP_CT_UNTRACKED)).
                               A SUBSEQUENT `ct state` read then returns
                               NF_CT_STATE_UNTRACKED_BIT (= 64) (nft_ct_get_eval's
                               NFT_CT_STATE `else if (ctinfo == IP_CT_UNTRACKED)` branch),
                               not the per-packet oracle.  Per-packet-traversal state:
                               every packet starts FALSE (tracked); the flag is set by
                               [set_untracked] and read by [do_load (LCt CKstate)].  It is
                               NOT cross-packet — the kernel re-runs conntrack per skb. *)
  pkt_flow : data;          (* the FLOW IDENTIFIER of this packet — the key under which
                               the kernel's nf_ct_get(skb) selects the shared conntrack
                               entry.  Two packets of the same connection (both
                               directions: the kernel normalises by tuple) carry the
                               SAME [pkt_flow], so a `ct mark set V` on one is read back
                               as [e_ct (pkt_env p) (pkt_flow p) CKmark] by the other.
                               Derived from the (direction-normalised) 5-tuple; modelled
                               here as an opaque packet-determined value (the kernel
                               computes the tuple from the headers).

                               NOTE on direction: [pkt_flow] is direction-NORMALISED, so
                               BOTH directions of a connection share it.  This is correct
                               for the conntrack-entry state that is itself
                               direction-INDEPENDENT (ct mark / ct label, stored in
                               [e_ct]).  But the NAT translation tuple [e_nat] is
                               direction-SPECIFIC: the kernel applies it FORWARD on the
                               original-direction packet and the INVERSE on the reply
                               (nf_nat_packet: `if (dir==IP_CT_DIR_REPLY) statusbit ^=
                               IPS_NAT_MASK`).  So consumers of [e_nat] (i.e. [apply_nat])
                               MUST consult [pkt_ctdir_orig] below to decide forward vs
                               inverse — keying by the shared [pkt_flow] alone is not
                               enough. *)
  pkt_ctdir_orig : bool;    (* the conntrack DIRECTION of this packet: [true] on the
                               ORIGINAL-direction packet of the flow (client->server, the
                               direction that ESTABLISHED the connection and the NAT
                               mapping), [false] on a REPLY-direction packet
                               (server->client).  This is the kernel's
                               CTINFO2DIR(ctinfo) (IP_CT_DIR_ORIGINAL vs IP_CT_DIR_REPLY).
                               It is packet-determined (the kernel decides it from which
                               tuple of the conntrack entry the skb matched) and is what
                               [apply_nat] uses to apply a stored NAT tuple FORWARD (orig
                               dir) or INVERTED (reply dir) — see nf_nat_packet in
                               net/netfilter/nf_nat_core.c.  Every freshly-built packet
                               in the proofs defaults to [true]; a reply packet sets it
                               [false]. *)
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
      - a LINK-LAYER (ether) load requires the MAC header was built:
          `case NFT_PAYLOAD_LL_HEADER: if (!skb_mac_header_was_set(skb) ||
             skb_mac_header_len(skb) == 0) goto err;`
        (false for LOCALLY-GENERATED packets at output/postrouting — the L2
        header is not built there, so an `ether ...` match BREAKs.)
      - ANY load must fit in the header bytes (skb_copy_bits returns <0 / the read
        runs off the end of the header otherwise):
          `if (skb_copy_bits(skb, offset, dest, priv->len) < 0) goto err;`

    A failed read must FAIL the rule's match (return [false] here), never compare a
    truncated/empty value — that silent truncation was the soundness bug. *)
Definition read_payload_ok (b : pbase) (off len : nat) (p : packet) : bool :=
  let layer_ok :=
    match b with
    | PTransport | PInner =>
        andb (pkt_have_l4 p) (Nat.eqb (pkt_fragoff p) 0)
    | PLink => pkt_have_l2 p
    | _ => true
    end in
  andb layer_ok (negb (Nat.ltb (List.length (base_bytes b p)) (off + len))).

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
