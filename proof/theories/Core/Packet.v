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
    separate secmark key (it folds into mark/label coverage).

    EVERY conntrack key — writable or not — is read from the SHARED, flow-keyed
    conntrack table [e_ct] at the packet's flow ([Syntax.do_load]'s [LCt] case),
    mirroring the kernel's nf_ct_get(skb) selecting the flow's entry and deriving
    the key from it.  [ct_writable] only gates the WRITE path ([set_ct] in
    Semantics.v): a read-only key ([CKstate], [CKexpiration], counters, [CKzone],
    …) is computed by the kernel from the flow's current state and is NOT a value
    a rule can store back.  [CKevent] (NFT_CT_EVENTMASK) is settable but
    configures event delivery — it is never read back by `ct ... get`, so it is
    not modelled as persistent state either. *)
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

(** Structural equality on [limit_spec], used to key the shared per-instance rate
    limiter [e_limit] (each `limit` expression in a ruleset has its OWN token bucket
    in the kernel; here we conflate instances with identical parameters, which is
    conservative and sufficient — a ruleset rarely repeats an identical limiter). *)
Definition limit_eqb (a b : limit_spec) : bool :=
  andb (Nat.eqb (ls_rate a) (ls_rate b))
       (andb (Nat.eqb (ls_unit a) (ls_unit b))
       (andb (Nat.eqb (ls_burst a) (ls_burst b))
       (andb (Bool.eqb (ls_bytes a) (ls_bytes b))
             (Nat.eqb (ls_flags a) (ls_flags b))))).

(** A quota: [q_bytes] the limit, [q_consumed] bytes already used, [q_flags] the
    NFT_QUOTA_F_* bits (bit 0 = "over"/inverted). *)
Record quota_spec : Type := {
  q_bytes : nat; q_consumed : nat; q_flags : nat
}.

Definition quota_eqb (a b : quota_spec) : bool :=
  andb (Nat.eqb (q_bytes a) (q_bytes b))
       (andb (Nat.eqb (q_consumed a) (q_consumed b))
             (Nat.eqb (q_flags a) (q_flags b))).

(** A connection limit: [cl_count] the threshold, [cl_flags] (bit 0 = "over"). *)
Record connlimit_spec : Type := {
  cl_count : nat; cl_flags : nat
}.

Definition connlimit_eqb (a b : connlimit_spec) : bool :=
  andb (Nat.eqb (cl_count a) (cl_count b)) (Nat.eqb (cl_flags a) (cl_flags b)).

(** Payload bases: which header a [payload load] reads from. *)
Inductive pbase : Type :=
| PLink
| PNetwork
| PTransport
| PInner
| PTunnel.

(** ** Per-interface address state — a faithful multi-address model.

    A real Linux interface does NOT carry a single source address: it carries a
    LIST of addresses (a primary + secondaries, kept in [in_device->ifa_list],
    net/ipv4/devinet.c).  Each [in_ifaddr] records its local address
    ([ifa_local]), whether it is a SECONDARY (the [IFA_F_SECONDARY] flag — only a
    PRIMARY is eligible for source-address selection), and its address SCOPE
    ([ifa_scope]: RT_SCOPE_UNIVERSE=0 global, HOST=254 loopback-only, ...; a
    larger number is a TIGHTER scope).  We model exactly this triple. *)
Record ifaddr : Type := {
  ifa_local     : data;   (* the interface address (4-byte IPv4 / 16-byte IPv6) *)
  ifa_secondary : bool;   (* IFA_F_SECONDARY: secondaries are skipped by selection *)
  ifa_scope     : nat     (* RT_SCOPE_*: 0=UNIVERSE(global) .. 255=NOWHERE; bigger=tighter *)
}.

(** RT_SCOPE_UNIVERSE — the loosest scope, what masquerade asks for
    (nf_nat_masquerade.c: [inet_select_addr(out, nh, RT_SCOPE_UNIVERSE)]). *)
Definition scope_universe : nat := 0.

(** A "primary" interface address in the universal scope — the common case used
    by the test/literal environments (a single global primary). *)
Definition mk_primary (v : data) : ifaddr :=
  {| ifa_local := v; ifa_secondary := false; ifa_scope := scope_universe |}.

(** [inet_select_addr l scope] — the kernel's source-address SELECTION,
    net/ipv4/devinet.c:1359 [inet_select_addr], specialised to the
    destination-less call (masquerade passes the nexthop as [dst], but the
    on-link [inet_ifa_match] preference only REORDERS among equally-eligible
    primaries; the value the kernel returns when no on-link match exists — and the
    NF_DROP condition — is exactly "the first eligible primary", which is what we
    model).  We iterate the device's address list and return the FIRST address
    that is (a) NOT a secondary and (b) in scope, i.e. [ifa_scope <= scope] (the
    kernel's [min(ifa->ifa_scope, ...) > scope] skip, here without the localnet
    refinement).  When NO such address exists the result is [] — the kernel's
    [inet_select_addr] returns 0, which the masquerade core turns into NF_DROP. *)
Fixpoint inet_select_addr (l : list ifaddr) (scope : nat) : data :=
  match l with
  | [] => []
  | ia :: rest =>
      if andb (negb (ifa_secondary ia)) (Nat.leb (ifa_scope ia) scope)
      then ifa_local ia
      else inet_select_addr rest scope
  end.

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
                                                shared external routing state (read
                                                via [Syntax.read_rt], width-
                                                normalised to [Syntax.rt_width]). *)
  e_limit : limit_spec -> nat;               (* a rate limiter's REMAINING tokens —
                                                SHARED, CONSUMING, flow-/instance-keyed
                                                state, NOT a per-packet oracle.  A
                                                `limit` match passes (rule continues)
                                                iff [0 < remaining]; when it passes the
                                                bucket is DECREMENTED by the unit cost
                                                (the kernel nft_limit_eval:
                                                `delta = tokens - cost; if (delta>=0)
                                                tokens = delta; return invert`).  The
                                                consumption is applied AT the limiter's
                                                own position inside the break-aware
                                                per-rule folds ([Semantics.body_step] /
                                                [run_rule_step]) and threaded cross-rule/
                                                cross-packet, exactly like the
                                                `numgen inc` counter — so a later packet
                                                of a traversal reads the depleted bucket
                                                and gets a DIFFERENT verdict, which is
                                                the entire point of a rate limit.  Refill
                                                by elapsed time is abstracted to +0
                                                within a traversal (back-to-back packets
                                                in one ktime). *)
  e_quota : quota_spec -> nat;               (* a quota's remaining bytes — SHARED,
                                                CONSUMING state.  A `quota` match passes
                                                iff [cost <= remaining] (consumed+len
                                                still <= quota; equality still passes);
                                                the bucket is DECREMENTED by the packet's
                                                byte length ([quota_cost], = skb->len) on
                                                EVERY evaluation (the kernel nft_overquota
                                                accumulates skb->len UNCONDITIONALLY,
                                                regardless of pass/fail).  Consumed
                                                in-fold like [e_limit]. *)
  e_ifaddrs : data -> list ifaddr;           (* an interface's FULL IPv4 address LIST
                                                (primary + secondaries), keyed by its
                                                name — the genuine multi-address
                                                per-device [ifa_list] of Linux's
                                                [in_device] (net/ipv4/devinet.c).  The
                                                source `masquerade` SELECTS from this
                                                list via [inet_select_addr] (see the
                                                derived [e_ifaddr] below).  Shared host
                                                config. *)
  e_ifaddrs6 : data -> list ifaddr;          (* an interface's FULL IPv6 address LIST
                                                (each [ifa_local] a 16-byte in6_addr),
                                                keyed by its name — the [inet6_dev]
                                                address list.  An IPv6 `masquerade`
                                                SELECTS from this via [inet_select_addr]
                                                (the kernel's ipv6_dev_get_saddr); the
                                                selected value is a DIFFERENT 128-bit
                                                address, not the IPv4 one.  Shared host
                                                config. *)
  e_connlimit : connlimit_spec -> list data; (* the SHARED, flow-keyed set of DISTINCT
                                                live CONNECTIONS currently counted for a
                                                `connlimit`/`ct count` instance — the
                                                analogue of the kernel's nf_conncount
                                                per-instance `priv->list` (a list of
                                                connection tuples).  Each element is a
                                                [pkt_flow] (a connection identifier),
                                                deduplicated.  `connlimit` is a CONNECTION
                                                limiter, NOT a packet limiter: evaluating
                                                it inserts the packet's [pkt_flow]
                                                IDEMPOTENTLY (nf_conncount_add_skb returns
                                                -EEXIST and does NOT grow the list when the
                                                connection is already counted), so the
                                                count = number of DISTINCT flows.  The rule
                                                BREAKs iff `(count > limit) ^ invert`
                                                (STRICT >, kernel nft_connlimit.c:47), hence
                                                `connlimit count N` permits up to N+1 distinct
                                                connections and ANY number of packets of ONE
                                                connection always read the same count and are
                                                never throttled by the connection itself.
                                                Inserted at the match's own position inside
                                                the break-aware per-rule folds and threaded
                                                across rules and packets (the same pattern
                                                as the flow-keyed [e_ct] and [e_limit]). *)
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
                                                state is genuinely CROSS-packet: it is
                                                keyed by flow, not per packet.  The
                                                table carries no width; EVERY read
                                                goes through [Syntax.ct_load], which
                                                [fit]s the value to the key's kernel
                                                register width ([Syntax.ct_width])
                                                BY CONSTRUCTION. *)
  e_nat : data -> option (option data * option data * option nat * option data);
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
                               new_port_opt, orig_port_opt)] is the established
                               translation — the ORIGINAL
                               (pre-NAT) L3 address of the manip slot (needed to apply the
                               INVERSE manip on reply-direction packets, mirroring the
                               kernel storing both tuples of the conntrack entry), the new
                               L3 address (if a NAT_REG_ADDR operand was present), the
                               new L4 port (if a NAT_REG_PROTO operand was present), and the
                               ORIGINAL (pre-NAT) L4 port of the manip slot (also stored iff
                               a NAT_REG_PROTO operand was present — needed to apply the
                               INVERSE port manip on reply-direction packets, exactly as the
                               kernel stores the original port in the reply tuple so
                               nf_nat_manip_pkt(REPLY) un-rewrites the opposite slot's port).
                               This
                               is the flow-keyed NAT state a per-packet pure [apply_nat]
                               could not express — the exact analogue of [e_ct] for the
                               NAT tuple.  [apply_nat] applies [new_addr_opt] FORWARD on an
                               original-direction packet ([pkt_ctdir_orig = true]) and
                               restores [orig_addr_opt] (and the original port) on the
                               OPPOSITE slot for a reply ([pkt_ctdir_orig = false]) —
                               nf_nat_packet's direction inversion. *)
  e_numgen : numgen_spec -> nat;
                            (* the SHARED, persistent `numgen inc` eval count, keyed by
                               the numgen instance.  Full read/increment semantics:
                               [env_numgen_upd]/[set_numgen] in Semantics.v. *)
}.

(** [e_ifaddr e n] = the primary global-scope IPv4 address [inet_select_addr]
    picks from the interface's full address list [e_ifaddrs e n] at
    RT_SCOPE_UNIVERSE — the first non-secondary, in-scope primary (kernel:
    inet_select_addr, net/ipv4/devinet.c).  This is the address an IPv4
    `masquerade` rewrites to; the masquerade core turns a [] result into NF_DROP
    (nf_nat_masquerade.c). *)
Definition e_ifaddr (e : env) (n : data) : data :=
  inet_select_addr (e_ifaddrs e n) scope_universe.

(** Likewise for IPv6: select the primary in-scope address from the interface's
    IPv6 address list (the kernel's ipv6_dev_get_saddr over the inet6_dev list). *)
Definition e_ifaddr6 (e : env) (n : data) : data :=
  inet_select_addr (e_ifaddrs6 e n) scope_universe.

(** [ifaddrs_of v] = the one-primary-address list: an interface whose ONLY
    address is the global primary [v], or NO address when [v = []].  It is the
    canonical way for a single-address test environment to populate [e_ifaddrs];
    [e_ifaddr] of such a list is exactly [v] ([inet_select_ifaddrs_of]). *)
Definition ifaddrs_of (v : data) : list ifaddr :=
  if data_eqb v [] then [] else [ mk_primary v ].

Lemma inet_select_ifaddrs_of : forall v,
  inet_select_addr (ifaddrs_of v) scope_universe = v.
Proof.
  intro v. unfold ifaddrs_of. destruct (data_eqb v []) eqn:E.
  - apply data_eqb_true_iff in E. now rewrite E.
  - reflexivity.
Qed.

(** A packet is ONE skb's worth of state: wire bytes, kernel-computed metadata,
    per-traversal flags, and the per-packet nondeterminism oracles.  The shared,
    mutable cross-packet world (named sets/maps, conntrack, NAT mappings, routes,
    interface addresses, limiter buckets — the [env] above) is NOT part of a
    packet: every evaluator takes the env as an explicit parameter beside the
    packet, and the mutation evaluators return the env they leave
    ([Semantics.eval_rules_flat_env : list rule -> env -> packet ->
    option verdict * env]), so a type signature shows exactly which state flows
    where. *)
Record packet : Type := {
  pkt_meta : meta_key -> data;   (* kernel-computed metadata.  The oracle carries
                                    no width; EVERY evaluation reads it through
                                    [Syntax.read_meta], which [fit]s the value to
                                    the key's kernel register width
                                    ([Syntax.meta_width]) BY CONSTRUCTION. *)
  pkt_sock : socket_key -> data; (* socket-state oracle (read via
                                    [Syntax.read_socket], width-normalised) *)
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
                                    [lpm_fib] against the shared [e_routes].
                                    Still an ORACLE per selector: only the IPv4
                                    "daddr"/"saddr" (and their ". iif") selectors
                                    are pinned to the real header bytes, by
                                    [Fib_Local.fibkey_wf] — every other selector's
                                    key is un-de-oracled, the same residual class
                                    as [pkt_flow] below (see the rationale
                                    there). *)
  pkt_numgen : numgen_spec -> data;  (* oracle: the output of `numgen random`
                                        (nft_ng_random_gen: get_random_u32 — genuinely
                                        per-packet).  The INCREMENTAL generator does NOT
                                        read this: `numgen inc` reads the shared counter
                                        [e_numgen] (see [Syntax.do_load]'s [LNumgen]
                                        case and [env_numgen_upd] in Semantics.v). *)
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
                               not the flow entry's stored state.  Per-packet-traversal state:
                               every packet starts FALSE (tracked); the flag is set by
                               [set_untracked] and read by [do_load (LCt CKstate)].  It is
                               NOT cross-packet — the kernel re-runs conntrack per skb. *)
  pkt_flow : data;          (* the FLOW IDENTIFIER of this packet — the key under which
                               the kernel's nf_ct_get(skb) selects the shared conntrack
                               entry.  Two packets of the same connection (both
                               directions: the kernel normalises by tuple) carry the
                               SAME [pkt_flow], so a `ct mark set V` on one is read back
                               as [e_ct e (pkt_flow p) CKmark] by the other.
                               Derived from the (direction-normalised) 5-tuple; modelled
                               here as an opaque packet-determined value (the kernel
                               computes the tuple from the headers).

                               WHY OPAQUE, AND WHAT THAT COSTS (design rationale).
                               Every ct/NAT theorem is deliberately PARAMETRIC in flow
                               identity: it is a congruence over this key — packets
                               with the same [pkt_flow] share conntrack/NAT state,
                               packets with different keys don't, whatever the key IS.
                               That was the cheapest sound way to model "shared entry
                               selected by nf_ct_get(skb)" without committing to a
                               tuple-extraction function.  The COST: nothing connects
                               [pkt_flow p] to the header bytes [p] actually carries
                               ([pkt_nh]/[pkt_th] via [read_payload]), so transferring
                               a ct/NAT theorem to a real skb rests on an UNVERIFIED
                               assumption — that the instantiation of [pkt_flow] is an
                               INJECTIVE direction-normalised canonicalisation of
                               (5-tuple + l4proto + zone).  If it is not injective (two
                               distinct real flows mapped to one model key), the
                               theorems are true-but-about-the-wrong-flow: the two real
                               flows would merge their ct marks/NAT tuples in the
                               model.  The fib key had the same shape of gap and earned
                               its pinning layer ([Fib_Local.fibkey_wf] ties
                               [pkt_fibkey p "daddr"] to [read_payload PNetwork 16 4]);
                               the ANALOGOUS, designated de-oracling step here is a
                               [flow_wf] well-formedness tying [pkt_flow] to the header
                               tuple (saddr/daddr/sport/dport from [pkt_nh]/[pkt_th],
                               plus l4proto and zone, normalised so both directions
                               yield the same key — the reply direction is already
                               separately available as [pkt_ctdir_orig] below).  It is
                               an ADDITIVE layer, like [Fib_Local]: no existing theorem
                               changes; [flow_wf] hypotheses strengthen their transfer.
                               Until it exists, [pkt_flow] (like [pkt_fibkey] beyond
                               the four selectors [fibkey_wf] pins, and [pkt_inner]) is a
                               free packet-record oracle — ledgered in DEVELOPMENT.md's
                               honest-gaps list and scoped in THEOREMS.md §1.

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
  pkt_ct_present : bool;    (* whether a conntrack ENTRY exists for this packet, i.e.
                               whether the kernel's `ct = nf_ct_get(skb, &ctinfo)`
                               returns a NON-NULL pointer (net/netfilter/nft_ct.c
                               nft_ct_get_eval).  [true] for a normal TRACKED packet that
                               has a conntrack entry; [false] for a packet with NO entry —
                               an UNTRACKED packet (after `notrack`/loopback: nf_ct_get
                               returns NULL with ctinfo == IP_CT_UNTRACKED) or a genuinely
                               INVALID / no-entry packet (NULL with ctinfo == 0).  In the
                               kernel, NFT_CT_STATE is the ONLY key that yields a value when
                               ct == NULL (UNTRACKED -> NF_CT_STATE_UNTRACKED_BIT, else
                               NF_CT_STATE_INVALID_BIT); EVERY OTHER key does
                               `if (ct == NULL) goto err` -> NFT_BREAK, so the rule does NOT
                               match (nft_ct.c:81-82, 220-221).  This flag therefore gates
                               [load_ok (LCt k)] for every non-state key: a `ct mark` /
                               `ct direction` / `ct status` / `ct expiration` / `ct id` / ...
                               match on a packet with [pkt_ct_present = false] BREAKs, exactly
                               as the kernel does.  The [pkt_untracked] latch (set by
                               `notrack`) is a SPECIAL CASE of no-entry that additionally
                               fixes `ct state` to UNTRACKED; both force a no-entry packet.
                               Every freshly-built test packet defaults to [true] (a tracked
                               packet with an entry). *)
}.

(** ** [pstate]: the bundled (env, packet) pair — the pre-split statement shape.

    Before the state split, [packet] carried the whole mutable world in a
    [pkt_env] field, and every theorem quantified over that bundled record.
    [pstate] is that shape as an explicit pair, kept SOLELY so each pre-split
    headline theorem can be restated verbatim as a corollary over it
    (see Main.v): a pre-split packet value is exactly a [pstate]. *)
Record pstate : Type := {
  ps_env  : env;     (* the shared mutable world the old packet embedded *)
  ps_wire : packet;  (* the per-packet state: wire bytes, flags, oracles *)
}.

(** ** Single-field record-update combinators ("withers").

    [coq-record-update] is not available in-tree, so we provide the handful of
    per-field functional setters the semantics actually mutate, each defined ONCE
    as a full record literal.  Every semantic setter (set_meta / set_ct /
    set_nh_field / set_th_field / set_untracked / ...) is then a thin
    composition over these, instead of re-listing all 25 packet (resp. 13 env)
    fields.  Records are non-primitive, so [pkt_X (with_pkt_Y p v)] reduces by
    [cbn]/[simpl]/[vm_compute] to a projection of a constructor — the same normal
    form as a hand-inlined record literal, so the setters are definitionally
    transparent to every proof.  Adding a field to
    [packet]/[env] now forces editing ONE literal per record (the wither group
    below) rather than ~14 setters. *)

(** Replace just the named env field, copying the other 12. *)
Definition with_e_set (e : env) (v : string -> list (data * data)) : env :=
  {| e_set := v; e_vmap := e_vmap e; e_map := e_map e;
     e_routes := e_routes e; e_rt := e_rt e;
     e_ifaddrs := e_ifaddrs e; e_ifaddrs6 := e_ifaddrs6 e;
     e_limit := e_limit e; e_quota := e_quota e; e_connlimit := e_connlimit e;
     e_ct := e_ct e; e_nat := e_nat e; e_numgen := e_numgen e |}.

Definition with_e_map (e : env) (v : string -> list (data * data)) : env :=
  {| e_set := e_set e; e_vmap := e_vmap e; e_map := v;
     e_routes := e_routes e; e_rt := e_rt e;
     e_ifaddrs := e_ifaddrs e; e_ifaddrs6 := e_ifaddrs6 e;
     e_limit := e_limit e; e_quota := e_quota e; e_connlimit := e_connlimit e;
     e_ct := e_ct e; e_nat := e_nat e; e_numgen := e_numgen e |}.

Definition with_e_limit (e : env) (v : limit_spec -> nat) : env :=
  {| e_set := e_set e; e_vmap := e_vmap e; e_map := e_map e;
     e_routes := e_routes e; e_rt := e_rt e;
     e_ifaddrs := e_ifaddrs e; e_ifaddrs6 := e_ifaddrs6 e;
     e_limit := v; e_quota := e_quota e; e_connlimit := e_connlimit e;
     e_ct := e_ct e; e_nat := e_nat e; e_numgen := e_numgen e |}.

Definition with_e_quota (e : env) (v : quota_spec -> nat) : env :=
  {| e_set := e_set e; e_vmap := e_vmap e; e_map := e_map e;
     e_routes := e_routes e; e_rt := e_rt e;
     e_ifaddrs := e_ifaddrs e; e_ifaddrs6 := e_ifaddrs6 e;
     e_limit := e_limit e; e_quota := v; e_connlimit := e_connlimit e;
     e_ct := e_ct e; e_nat := e_nat e; e_numgen := e_numgen e |}.

Definition with_e_connlimit (e : env) (v : connlimit_spec -> list data) : env :=
  {| e_set := e_set e; e_vmap := e_vmap e; e_map := e_map e;
     e_routes := e_routes e; e_rt := e_rt e;
     e_ifaddrs := e_ifaddrs e; e_ifaddrs6 := e_ifaddrs6 e;
     e_limit := e_limit e; e_quota := e_quota e; e_connlimit := v;
     e_ct := e_ct e; e_nat := e_nat e; e_numgen := e_numgen e |}.

Definition with_e_ct (e : env) (v : data -> ct_key -> data) : env :=
  {| e_set := e_set e; e_vmap := e_vmap e; e_map := e_map e;
     e_routes := e_routes e; e_rt := e_rt e;
     e_ifaddrs := e_ifaddrs e; e_ifaddrs6 := e_ifaddrs6 e;
     e_limit := e_limit e; e_quota := e_quota e; e_connlimit := e_connlimit e;
     e_ct := v; e_nat := e_nat e; e_numgen := e_numgen e |}.

Definition with_e_nat (e : env)
    (v : data -> option (option data * option data * option nat * option data)) : env :=
  {| e_set := e_set e; e_vmap := e_vmap e; e_map := e_map e;
     e_routes := e_routes e; e_rt := e_rt e;
     e_ifaddrs := e_ifaddrs e; e_ifaddrs6 := e_ifaddrs6 e;
     e_limit := e_limit e; e_quota := e_quota e; e_connlimit := e_connlimit e;
     e_ct := e_ct e; e_nat := v; e_numgen := e_numgen e |}.

Definition with_e_numgen (e : env) (v : numgen_spec -> nat) : env :=
  {| e_set := e_set e; e_vmap := e_vmap e; e_map := e_map e;
     e_routes := e_routes e; e_rt := e_rt e;
     e_ifaddrs := e_ifaddrs e; e_ifaddrs6 := e_ifaddrs6 e;
     e_limit := e_limit e; e_quota := e_quota e; e_connlimit := e_connlimit e;
     e_ct := e_ct e; e_nat := e_nat e; e_numgen := v |}.

(** Replace just the named packet field, copying the other 23. *)
Definition with_pkt_meta (p : packet) (v : meta_key -> data) : packet :=
  {| pkt_meta := v; pkt_sock := pkt_sock p;
     pkt_eh := pkt_eh p; pkt_lh := pkt_lh p; pkt_nh := pkt_nh p; pkt_th := pkt_th p;
     pkt_ih := pkt_ih p; pkt_tnl := pkt_tnl p; pkt_fibkey := pkt_fibkey p;
     pkt_numgen := pkt_numgen p; pkt_osf := pkt_osf p;
     pkt_tunnel := pkt_tunnel p; pkt_symhash := pkt_symhash p; pkt_xfrm := pkt_xfrm p;
     pkt_ctdir := pkt_ctdir p; pkt_inner := pkt_inner p;
     pkt_have_l2 := pkt_have_l2 p; pkt_have_l4 := pkt_have_l4 p; pkt_fragoff := pkt_fragoff p;
     pkt_flow := pkt_flow p; pkt_untracked := pkt_untracked p;
     pkt_ctdir_orig := pkt_ctdir_orig p; pkt_ct_present := pkt_ct_present p |}.

Definition with_pkt_nh (p : packet) (v : list byte) : packet :=
  {| pkt_meta := pkt_meta p; pkt_sock := pkt_sock p;
     pkt_eh := pkt_eh p; pkt_lh := pkt_lh p; pkt_nh := v; pkt_th := pkt_th p;
     pkt_ih := pkt_ih p; pkt_tnl := pkt_tnl p; pkt_fibkey := pkt_fibkey p;
     pkt_numgen := pkt_numgen p; pkt_osf := pkt_osf p;
     pkt_tunnel := pkt_tunnel p; pkt_symhash := pkt_symhash p; pkt_xfrm := pkt_xfrm p;
     pkt_ctdir := pkt_ctdir p; pkt_inner := pkt_inner p;
     pkt_have_l2 := pkt_have_l2 p; pkt_have_l4 := pkt_have_l4 p; pkt_fragoff := pkt_fragoff p;
     pkt_flow := pkt_flow p; pkt_untracked := pkt_untracked p;
     pkt_ctdir_orig := pkt_ctdir_orig p; pkt_ct_present := pkt_ct_present p |}.

Definition with_pkt_th (p : packet) (v : list byte) : packet :=
  {| pkt_meta := pkt_meta p; pkt_sock := pkt_sock p;
     pkt_eh := pkt_eh p; pkt_lh := pkt_lh p; pkt_nh := pkt_nh p; pkt_th := v;
     pkt_ih := pkt_ih p; pkt_tnl := pkt_tnl p; pkt_fibkey := pkt_fibkey p;
     pkt_numgen := pkt_numgen p; pkt_osf := pkt_osf p;
     pkt_tunnel := pkt_tunnel p; pkt_symhash := pkt_symhash p; pkt_xfrm := pkt_xfrm p;
     pkt_ctdir := pkt_ctdir p; pkt_inner := pkt_inner p;
     pkt_have_l2 := pkt_have_l2 p; pkt_have_l4 := pkt_have_l4 p; pkt_fragoff := pkt_fragoff p;
     pkt_flow := pkt_flow p; pkt_untracked := pkt_untracked p;
     pkt_ctdir_orig := pkt_ctdir_orig p; pkt_ct_present := pkt_ct_present p |}.

Definition with_pkt_untracked (p : packet) (v : bool) : packet :=
  {| pkt_meta := pkt_meta p; pkt_sock := pkt_sock p;
     pkt_eh := pkt_eh p; pkt_lh := pkt_lh p; pkt_nh := pkt_nh p; pkt_th := pkt_th p;
     pkt_ih := pkt_ih p; pkt_tnl := pkt_tnl p; pkt_fibkey := pkt_fibkey p;
     pkt_numgen := pkt_numgen p; pkt_osf := pkt_osf p;
     pkt_tunnel := pkt_tunnel p; pkt_symhash := pkt_symhash p; pkt_xfrm := pkt_xfrm p;
     pkt_ctdir := pkt_ctdir p; pkt_inner := pkt_inner p;
     pkt_have_l2 := pkt_have_l2 p; pkt_have_l4 := pkt_have_l4 p; pkt_fragoff := pkt_fragoff p;
     pkt_flow := pkt_flow p; pkt_untracked := v;
     pkt_ctdir_orig := pkt_ctdir_orig p; pkt_ct_present := pkt_ct_present p |}.

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
