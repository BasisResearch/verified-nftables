(** * Syntax: the byte-level rule IR (the compiler's internal source).

    A ruleset is a list of tables, a table a list of named chains, a chain a
    policy plus an ordered list of rules, and a rule an ordered body of match
    conditions and statements followed by ONE outcome.  The leaves here are
    byte-level: match values are register bytes, and [transform] records the
    mask/shift/byteorder/jhash operations in front of a compare — this IR
    models exactly what the kernel's expressions evaluate.  The typed->bytes
    boundary, stated precisely: a generated source term ([*_Gen.v]) carries
    the SURFACE ruleset with TYPED immediates ([Nftval.nftval] atoms inside
    [Surface.Typed.txmatch] terms and surface set/statement values), which
    reach this IR only through the VERIFIED lowering
    ([Lower.lower_ruleset] / [Typed.elab_tx]); the per-atom encoding is
    everywhere the verified [Nftval.encode], and the per-shape correctness is
    the [Lower_Proofs.*_erasure] family.  No raw byte list is composed
    outside Coq (`make boundary` enforces this); the same bytes are re-checked
    end-to-end by the untrusted differential gates (corpus 2532/2532,
    validate 28/28, parse-test/e2e vs live nft) — see CONFIG_PROOFS.md
    ("What the Gen bytes rest on").

    Each [field] (e.g. "tcp dport") *denotes* a concrete way to read
    the packet, given by [field_load].  This denotation is the single source of
    truth shared by the semantics (which reads the field from the packet) and
    the compiler (which emits a load instruction for it).  The offsets here are
    checked against live [nft] by `make validate` (an INDEPENDENT oracle — see
    [run_validation] in extracted/corpus_test.ml); the corpus round-trip alone
    cannot check them because its parser and renderer share these tables. *)

From Stdlib Require Import List NArith String PeanoNat.
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

(** *** THE KERNEL WIDTH TABLE: every meta / ct / rt / socket / osf / numgen /
    symhash oracle read is normalised — BY CONSTRUCTION, at the semantics
    boundary — to the exact byte width the kernel eval writes into the
    destination register.

    In the kernel every one of these selectors has a PINNED width: [struct
    nft_regs] is 16 x u32 general registers (include/net/netfilter/
    nf_tables.h), values are explicit-length byte arrays spanning consecutive
    u32 words, and [nft_validate_register_load]/[store]
    (net/netfilter/nf_tables_api.c) bound every access to [reg + len].  The
    abstract oracles ([pkt_meta : meta_key -> data], [e_ct : data -> ct_key ->
    data], [e_rt], [pkt_sock], [pkt_osf], [pkt_numgen], [pkt_symhash];
    Core/Packet.v) carry NO width — they stay oracles — so every read below is
    wrapped in [Bytes.fit] at its kernel width, over [Bytes.octets] (each byte
    clamped to its low 8 bits: a register cell is a u8 lane of the u32 word
    array, so no register byte can exceed 0xff — see the [octets] header in
    Core/Bytes.v).  The width facts ([read_meta_length] & co.) and the octet
    facts ([do_load_bitops_id]) are therefore DEFINITIONAL: no [packet_wf]/
    [env_wf] hypothesis exists anywhere in this development.

    Each entry cites the eval-side WRITE in linux-6.18.33 (the width the
    register actually receives; [nft_reg_store8]/[16] zero the containing u32
    word and write 1/2 low bytes, [nft_reg_store64] and the memcpy cases write
    the full value).  Cross-checked against the frontend datatype table
    (Surface/Selector.v [sel_table] x Surface/Datatype.v [dt_bytes]) by the
    computed check [Selector.selector_widths_agree]; the two tables agree on
    every selector the frontend exposes.

    NOT in this table (deliberately): the OPAQUE abstractions — [pkt_flow],
    [pkt_fibkey] (beyond [Fib_Local.fibkey_wf]), [pkt_ctdir] (ct tuple columns,
    family-dependent 4/16-byte addresses chosen at eval time, nft_ct.c
    NFT_CT_SRC/DST), [pkt_xfrm], [pkt_tunnel], [pkt_inner], connlimit flow
    keys.  Those are abstractions of kernel OBJECTS, not register encodings
    (TODO.md non-negotiable).  Payload/exthdr loads already carry their width
    in the load descriptor ([read_payload] slices exactly [len] bytes); the
    fib result columns are read from the route table [e_routes], whose
    per-column values [Fib_Local]'s route-table constructors build at the
    kernel result widths. *)

(** Register byte width of a `meta` read = the width nft_meta_get_eval
    (net/netfilter/nft_meta.c; bridge keys: net/bridge/netfilter/
    nft_meta_bridge.c) writes into the dreg. *)
Definition meta_width (k : meta_key) : nat :=
  match k with
  (* nft_meta.c:330  nft_reg_store8(dest, pkt->tprot)            — u8       *)
  | MKl4proto => 1
  (* nft_meta.c:325  nft_reg_store8(dest, nft_pf(pkt))           — u8       *)
  | MKnfproto => 1
  (* nft_meta.c:322  nft_reg_store16(dest, skb->protocol)        — u16      *)
  | MKprotocol => 2
  (* nft_meta.c:336  *dest = skb->mark                           — u32      *)
  | MKmark => 4
  (* nft_meta.c:204  *dest = dev->ifindex (nft_meta_store_ifindex) — u32    *)
  | MKiif | MKoif => 4
  (* nft_meta.c:217  nft_reg_store16(dest, dev->type)            — u16      *)
  | MKiiftype | MKoiftype => 2
  (* nft_meta.c:209  strscpy_pad(dest, dev->name, IFNAMSIZ)      — 16 bytes *)
  | MKiifname | MKoifname => 16
  (* nft_meta.c:319  *dest = skb->len                            — u32      *)
  | MKlen => 4
  (* nft_meta.c:367  nft_reg_store8(dest, skb->pkt_type)         — u8       *)
  | MKpkttype => 1
  (* nft_meta.c:375  *dest = raw_smp_processor_id()              — u32      *)
  | MKcpu => 4
  (* nft_meta.c:149/:153  *dest = from_kuid/kgid(...)            — u32      *)
  | MKskuid | MKskgid => 4
  (* nft_meta.c:333  *dest = skb->priority                       — u32      *)
  | MKpriority => 4
  (* nft_meta.c:173  *dest = sock_cgroup_classid(...) — the u32 net_cls
     CLASSID (NFT_META_CGROUP; init pins len = sizeof(u32), :501-503).  NOT
     the u64 cgroupv2 id: that is `socket cgroupv2` (NFT_SOCKET_CGROUPV2,
     [socket_width] below).                                                 *)
  | MKcgroup => 4
  (* nft_meta.c:69   nft_reg_store8(dest, nft_meta_weekday())    — u8       *)
  | MKday => 1
  (* nft_meta.c:72   *dest = nft_meta_hour(...) (secs since 00:00) — u32    *)
  | MKhour => 4
  (* nft_meta.c:66   nft_reg_store64(dest, ktime_get_real_ns())  — u64      *)
  | MKtime => 8
  (* nft_meta.c:226  *dest = dev->group (nft_meta_store_ifgroup) — u32      *)
  | MKiifgroup | MKoifgroup => 4
  (* nft_meta.c:384  *dest = get_random_u32()                    — u32      *)
  | MKprandom => 4
  (* nft_meta.c:282  *dest = dst->tclassid                       — u32      *)
  | MKrtclassid => 4
  (* nft_meta.c:402  *dest = nft_meta_get_eval_sdif(pkt)         — u32      *)
  | MKsdif => 4
  (* nft_meta.c:306  nft_meta_store_ifname (strscpy_pad IFNAMSIZ) — 16 bytes *)
  | MKsdifname => 16
  (* nft_meta.c:388  nft_reg_store8(dest, secpath_exists(skb))   — u8       *)
  | MKsecpath => 1
  (* nft_meta_bridge.c:73  strscpy_pad(dest, br_dev->name, IFNAMSIZ) — 16 B *)
  | MKbri_iifname | MKbri_oifname => 16
  (* nft_meta_bridge.c:48  nft_reg_store16(dest, p_pvid)         — u16      *)
  | MKbri_iifpvid => 2
  (* nft_meta_bridge.c:59  nft_reg_store_be16(dest, htons(p_proto)) — be16  *)
  | MKbri_iifvproto => 2
  (* nft_meta_bridge.c:67  memcpy(dest, br_dev->dev_addr, ETH_ALEN) — 6 B   *)
  | MKibrhwaddr => 6
  (* nft_meta_bridge.c:147-148  NFT_META_BRI_BROUTE reads a 1-byte sreg
     (set path, nft_reg_load8); the matching read register is the same u8.  *)
  | MKbroute => 1
  end.

(** Normalise a meta read to its kernel register width. *)
Definition meta_load (k : meta_key) (d : data) : data :=
  fit (meta_width k) (octets d).

(** THE meta read: what every evaluation (DSL [do_load] and VM [IMetaLoad])
    sees.  Its width is definitional ([read_meta_length]). *)
Definition read_meta (p : packet) (k : meta_key) : data :=
  meta_load k (pkt_meta p k).

Lemma meta_load_length : forall k d,
  List.length (meta_load k d) = meta_width k.
Proof. intros k d. apply fit_length. Qed.

(** The by-construction width fact: EVERY meta read has its kernel register
    width, on EVERY packet — no packet well-formedness anywhere. *)
Lemma read_meta_length : forall p k,
  List.length (read_meta p k) = meta_width k.
Proof. intros p k. apply fit_length. Qed.

(** Register byte width of a `ct` read = the width nft_ct_get_eval
    (net/netfilter/nft_ct.c) writes into the dreg. *)
Definition ct_width (k : ct_key) : nat :=
  match k with
  (* nft_ct.c:75   *dest = state (NF_CT_STATE_BIT bits)          — u32      *)
  | CKstate => 4
  (* nft_ct.c:89   *dest = ct->status                            — u32      *)
  | CKstatus => 4
  (* nft_ct.c:93   *dest = READ_ONCE(ct->mark)                   — u32      *)
  | CKmark => 4
  (* nft_ct.c:86   nft_reg_store8(dest, CTINFO2DIR(ctinfo))      — u8       *)
  | CKdirection => 1
  (* nft_ct.c:102  *dest = jiffies_to_msecs(nf_ct_expires(ct))   — u32 ms   *)
  | CKexpiration => 4
  (* nft_ct.c:174  *dest = nf_ct_get_id(ct)                      — u32      *)
  | CKid => 4
  (* nft_ct.c:150  memcpy(dest, &avgcnt, sizeof(u64))            — u64      *)
  | CKavgpkt => 8
  (* nft_ct.c:134  memcpy(dest, &count, sizeof(u64))             — u64      *)
  | CKbytes | CKpackets => 8
  (* nft_ct.c:113  strscpy_pad(dest, helper->name, NF_CT_HELPER_NAME_LEN);
     NF_CT_HELPER_NAME_LEN = 16 (include/net/netfilter/nf_conntrack_helper.h:30) *)
  | CKhelper => 16
  (* nft_ct.c:154  nft_reg_store8(dest, nf_ct_l3num(ct))         — u8       *)
  | CKl3proto => 1
  (* nft_ct.c:120  memcpy(dest, labels->bits, NF_CT_LABELS_MAX_SIZE);
     NF_CT_LABELS_MAX_SIZE = (XT_CONNLABEL_MAXBIT+1)/8 = 128/8 = 16
     (include/net/netfilter/nf_conntrack_labels.h:14)            — 16 bytes *)
  | CKlabel => 16
  (* nft_ct.c:157  nft_reg_store8(dest, nf_ct_protonum(ct))      — u8       *)
  | CKproto => 1
  (* nft_ct.c:169  nft_reg_store16(dest, zoneid)                 — u16      *)
  | CKzone => 2
  (* NFT_CT_EVENTMASK is SET-only (an event-delivery mask, never read back);
     its sreg value is the u32 mask (nft_ct.c nft_ct_set_init:
     len = sizeof(u32)).  The read register width, were one to exist, is the
     same u32; pinned so the table is total.                                *)
  | CKevent => 4
  end.

(** Normalise a ct read to its kernel register width. *)
Definition ct_load (k : ct_key) (d : data) : data :=
  fit (ct_width k) (octets d).

Lemma ct_load_length : forall k d,
  List.length (ct_load k d) = ct_width k.
Proof. intros k d. apply fit_length. Qed.

(** Register byte width of an `rt` read = the width nft_rt_get_eval
    (net/netfilter/nft_rt.c) writes into the dreg. *)
Definition rt_width (k : rt_key) : nat :=
  match k with
  (* nft_rt.c:69   *dest = dst->tclassid                         — u32      *)
  | RKclassid => 4
  (* nft_rt.c:76   *dest = rt_nexthop(...)                       — u32      *)
  | RKnexthop4 => 4
  (* nft_rt.c:83   memcpy(dest, rt6_nexthop(...), sizeof(struct in6_addr)) — 16 B *)
  | RKnexthop6 => 16
  (* nft_rt.c:88   nft_reg_store16(dest, get_tcpmss(pkt, dst))   — u16.
     [RKmtu] is the SAME kernel key: nftables spells NFT_RT_TCPMSS `rt mtu`
     (nftables src/rt.c rt_template "mtu"); the codec keeps both spellings.  *)
  | RKtcpmss | RKmtu => 2
  (* nft_rt.c:92   nft_reg_store8(dest, !!dst->xfrm)             — u8       *)
  | RKipsec => 1
  end.

Definition rt_load (k : rt_key) (d : data) : data :=
  fit (rt_width k) (octets d).

Lemma rt_load_length : forall k d,
  List.length (rt_load k d) = rt_width k.
Proof. intros k d. apply fit_length. Qed.

(** THE rt read (from the routing-state oracle [e_rt]). *)
Definition read_rt (e : env) (k : rt_key) : data := rt_load k (e_rt e k).

Lemma read_rt_length : forall e k,
  List.length (read_rt e k) = rt_width k.
Proof. intros e k. apply fit_length. Qed.

(** Register byte width of a `socket` read = the width nft_socket_eval
    (net/netfilter/nft_socket.c) writes into the dreg. *)
Definition socket_width (k : socket_key) : nat :=
  match k with
  (* nft_socket.c:129  nft_reg_store8(dest, inet_sk_transparent(sk)) — u8   *)
  | SKtransparent => 1
  (* nft_socket.c:133  *dest = READ_ONCE(sk->sk_mark)            — u32      *)
  | SKmark => 4
  (* nft_socket.c:144  nft_socket_wildcard -> nft_reg_store8     — u8       *)
  | SKwildcard => 1
  (* nft_socket.c:54   memcpy(dest, &cgid, sizeof(u64)) — the u64 cgroupv2
     ID (nft_sock_get_eval_cgroupv2); contrast `meta cgroup` = u32 classid. *)
  | SKcgroupv2 => 8
  end.

Definition socket_load (k : socket_key) (d : data) : data :=
  fit (socket_width k) (octets d).

Lemma socket_load_length : forall k d,
  List.length (socket_load k d) = socket_width k.
Proof. intros k d. apply fit_length. Qed.

(** THE socket read (from the packet's socket oracle [pkt_sock]). *)
Definition read_socket (p : packet) (k : socket_key) : data :=
  socket_load k (pkt_sock p k).

Lemma read_socket_length : forall p k,
  List.length (read_socket p k) = socket_width k.
Proof. intros p k. apply fit_length. Qed.

(** `osf name` writes a fixed 16-byte genre buffer: nft_osf.c:53/:61
    strscpy_pad(dest, ..., NFT_OSF_MAXGENRELEN); NFT_OSF_MAXGENRELEN = 16
    (include/uapi/linux/netfilter/nf_tables.h:11). *)
Definition osf_width : nat := 16.

Definition read_osf (p : packet) : data := fit osf_width (octets (pkt_osf p)).

Lemma read_osf_length : forall p, List.length (read_osf p) = osf_width.
Proof. intros p. apply fit_length. Qed.

(** `numgen` and `symhash` both write a plain u32 dreg:
    nft_numgen.c:42/:149  regs->data[priv->dreg] = nft_ng_inc/random_gen(priv);
    nft_hash.c:57         regs->data[priv->dreg] = h + priv->offset. *)
Definition numgen_width : nat := 4.
Definition symhash_width : nat := 4.

Definition read_numgen (p : packet) (spec : numgen_spec) : data :=
  fit numgen_width (octets (pkt_numgen p spec)).

Lemma read_numgen_length : forall p spec,
  List.length (read_numgen p spec) = numgen_width.
Proof. intros p spec. apply fit_length. Qed.

Definition read_symhash (p : packet) (m o : nat) : data :=
  fit symhash_width (octets (pkt_symhash p m o)).

Lemma read_symhash_length : forall p m o,
  List.length (read_symhash p m o) = symhash_width.
Proof. intros p m o. apply fit_length. Qed.

(** Evaluate a load against a packet. *)
Definition do_load (ld : loaddesc) (e : env) (p : packet) : data :=
  match ld with
  | LMeta k         => read_meta p k
  | LCt k           => ct_load k
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
         only read what an entry for [pkt_flow p] holds.  [Regression/Ct_Flow.v]
         proves these consequences ([ct_state_flow_keyed], [same_flow_same_state])
         and provides [flow_is_new] — an ENTRY-STATE invariant on (env, packet)
         hypotheses ("the table records NEW for this packet's flow"), under which
         `ct state established` provably does not match; there is no global ct
         well-formedness predicate.  Note also that [pkt_flow] itself is an opaque
         packet oracle (no [flow_wf] ties it to the header 5-tuple yet — see the
         rationale on [pkt_flow] in Core/Packet.v).

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
      (match k with
      | CKstate => if pkt_untracked p then [0;0;0;64]
                   else if pkt_ct_present p then e_ct e (pkt_flow p) k
                   else [0;0;0;1]
      | CKdirection => if pkt_ctdir_orig p then [0] else [1]
      | _ => e_ct e (pkt_flow p) k
      end)
  | LRt k           => read_rt e k
  | LSocket k       => read_socket p k
  | LNumgen spec    =>
      (* `numgen inc` reads the SHARED, persistent counter from the env and renders
         the round-robin value [(counter mod modulus) + offset]; the increment that
         makes the NEXT evaluation differ is applied in-fold by
         [Semantics.run_rule_step]'s [INumgen] case (VM-only: the lowering rejects
         incremental numgen fail-loud, [Lower.LEnumgen], so every frontend-emitted
         rule is [rule_numgen_free] and the advance never fires).  `numgen random`
         (ng_random = true: get_random_u32) is genuinely per-packet, so it stays the
         oracle [pkt_numgen]. *)
      if ng_random spec then read_numgen p spec
      else numgen_inc_value spec (e_numgen e spec)
  | LOsf            => read_osf p
  | LExthdr ep h o l pr => pkt_eh p ep h o l pr
  | LFib sel res    => lpm_fib (e_routes e) (pkt_fibkey p sel) res
  | LCtDir key dir  => pkt_ctdir p key dir
  | LXfrm dir sp key => pkt_xfrm p dir sp key
  | LTunnel key      => pkt_tunnel p key
  | LSymhash m o     => read_symhash p m o
  | LInner t h fl desc _ => pkt_inner p t h fl desc
  | LPayload b o l  => read_payload b o l p
  end.

(** The value of a field, read against the shared env [e] and packet [p]. *)
Definition field_value (f : field) (e : env) (p : packet) : data :=
  do_load (field_load f) e p.

(** ** The register-normalised loads and their octet identity.

    [load_octet_width ld = Some w] exactly when [do_load ld] is the width- and
    octet-normalised register read [fit w (octets _)] — the fixed-width oracle
    reads (meta / ct / rt / socket / osf / symhash; the kernel width tables
    above).  [None] for the loads whose width lives elsewhere (payload/exthdr
    descriptors, the fib route-table columns) and for the opaque abstractions
    (ct tuple columns, xfrm/tunnel/inner) — no claim is made about those.
    ([LNumgen] is [None] only because its non-random branch reads the rendered
    round-robin counter, not a [fit]-normalised oracle.) *)
Definition load_octet_width (ld : loaddesc) : option nat :=
  match ld with
  | LMeta k      => Some (meta_width k)
  | LCt k        => Some (ct_width k)
  | LRt k        => Some (rt_width k)
  | LSocket k    => Some (socket_width k)
  | LOsf         => Some osf_width
  | LSymhash _ _ => Some symhash_width
  | _            => None
  end.

(** The octet identity at the load boundary, DEFINITIONAL (no hypothesis on
    [e]/[p]): the all-ones/zero bitwise at a normalised read's own register
    width is the identity on the read value.  In the kernel this is trivially
    true of every register value ([struct nft_regs] holds octets); here it
    holds by construction of [fit]/[octets].  This is the fact that makes
    nft's trivial-binop elision ([Optimize_Elide], evaluate.c
    [binop_transfer_handle_lhs] OP_XOR: the spent binop is replaced by its
    left operand) provable with no side condition. *)
Lemma do_load_bitops_id : forall ld w e p,
  load_octet_width ld = Some w ->
  data_bitops (do_load ld e p) (List.repeat 255 w) (List.repeat 0 w)
  = do_load ld e p.
Proof.
  intros ld w e p H.
  destruct ld; cbn in H; try discriminate; injection H as <-;
    cbn [do_load]; unfold read_meta, meta_load, ct_load, read_rt, rt_load,
      read_socket, socket_load, read_osf, read_symhash;
    apply data_bitops_fit_octets_id.
Qed.

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
| MMasked (f : field) (op : cmpop) (mask xor v : data)   (* (field & mask) ^ xor <op> v *)
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

(** The implicit-bitmask idiom: a positive `tcp flags X` / `ct state X` match
    tests [(field & X) <> 0] (nft evaluate.c keeps OP_IMPLICIT over a
    TYPE_BITMASK basetype as the implicit inequality against zero; golden
    inet/tcp.t.payload `bitwise reg1 = (reg1 & X) ^ 0; cmp neq reg1 0`).  The
    comparison polarity is [CNe] — the surface match is POSITIVE ("some flagged
    bit is set"); [MFlagsSet] names the shape so a source term carries no
    inverted-looking raw [MMasked]. *)
Definition MFlagsSet (f : field) (bits : data) : matchcond :=
  MMasked f CNe bits (List.repeat 0 (List.length bits)) (List.repeat 0 (List.length bits)).

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
| SDynset  (op : dynset_op) (name : string) (keyfs dataf : list field)
                            (* add/delete [keyfs] (-> [dataf] for a map) to a set *)
| SExthdrReset (proto : string) (htype : nat)
                            (* reset (clear) a TCP option; verdict-neutral *)
| SDup (dup_addr : option data) (dup_dev : option data)
                            (* REGISTER-FREE: duplicate to an immediate address
                               (-> reg 1) and/or device (-> reg 2 after an address,
                               else reg 1); compile allocates the registers.
                               Verdict-neutral (the dup is a side effect) *)
| SObjrefMap (keyfs : list field) (name : string)
| SDynsetImm (op : dynset_op) (name : string) (keyfs : list field) (data_vals : list data)
                            (* REGISTER-FREE: dynset whose map data are immediate
                               constants; compile lays them into the registers
                               after the key fields.  Verdict-neutral *)
| SExthdrWrite (vs : vsrc) (proto : string) (htype off len : nat)
                            (* write a value into a TCP-option exthdr field;
                               verdict-neutral (packet rewrite outside the model) *)
| SDupSrc (src : vsrc) (src_is_addr : bool) (dup_dev : option data).
                            (* REGISTER-FREE: duplicate where one operand (the
                               address if [src_is_addr], else the device) is
                               computed by [src] into reg 1, and an optional
                               immediate device lands in reg 2.  Verdict-neutral *)
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

(** A NAT statement (snat/dnat).  REGISTER-FREE: it names the address/port
    operand VALUES; [compile_terminal] loads them into data registers and emits
    the [INat] that references those registers.  NAT is terminal (it accepts with
    a translation); the packet rewrite itself is a side effect outside the
    single-packet verdict model. *)
(** The SECONDARY NAT operand — a range-end address or a port range — REGISTER-FREE:
    it carries operand VALUES, not the netlink register indices
    (NFTNL_EXPR_NAT_REG_ADDR_MAX / _REG_PROTO_MIN / _REG_PROTO_MAX).  The compiler
    ([compile_terminal]) derives the actual registers: a separate immediate lands in
    the next sequential register (reg 2/3), while a value taken from the PRIMARY
    operand's concat-MAP lands in the next slot register (reg 9 = slot 1). *)
Inductive nat_2nd : Type :=
| NXnone                              (* `dnat to a` : no second operand *)
| NXimm (addr_max : option data) (port_min : option data) (port_max : option data)
                                      (* separate immediates for the range-end address
                                         and/or port [range]; allocated to the next
                                         sequential registers (reg 2/3/4) *)
| NXmap_addr_max                      (* `snat to <k> map {k:a-b}` : range-end from the operand concat-map (reg 9) *)
| NXmap_port                          (* `snat to <k> map {k:a.p}` : port from the operand concat-map (reg 9) *)
| NXmap_full.                         (* `dnat to <k> map {k : a1-a2 . p1-p2}` : address range
                                         AND port range from one concat-map value, laid out
                                         addr_min . port_min . addr_max . port_max across
                                         register slots 0/1/2/3 (reg 1/9/10/11) *)

(** A NAT terminal.  REGISTER-FREE source: the operand SOURCE for the primary
    address (into register 1) is exactly one of [nat_addr_imm] (an immediate value),
    [nat_field], [nat_map], or [nat_src]; the secondary operand is [nat_extra]; the
    register allocation (the NFTNL_EXPR_NAT_REG slots) is entirely the compiler's job. *)
Record nat_spec : Type := {
  nat_addr_imm : option data;       (* `… to <imm>` : the immediate address value (reg 1) *)
  nat_field    : option (field * list transform);
                            (* `… to ip saddr` : operand from a (transformed) field *)
  nat_map      : option (list field * list transform * string);
                            (* `… to ip saddr map {…}` : concat of [fields] looked up
                               in a named map (into register 1) *)
  nat_src      : option vsrc;       (* general operand value source (e.g. jhash map) *)
  nat_extra    : nat_2nd;           (* range-end / port (register-free) *)
  nat_kind     : nat_op;            (* NKsnat / NKdnat / NKmasq / NKredir *)
  nat_family   : nat_af;            (* NFip4 / NFip6 / NFinet (runtime-dispatched) *)
  nat_flags    : nat;
}.

(** A [tproxy] statement (transparent proxy): terminal, like NAT.  Register-free:
    it names the target address and/or port values (or a symhash-keyed port map);
    [compile] allocates the registers (address -> reg 1, port -> reg 2 after an
    address else reg 1).  The redirection is a side effect outside the
    single-packet verdict model (which sees a terminal Accept). *)
Record tproxy_spec : Type := {
  tp_addr   : option data;         (* target address (immediate), if any *)
  tp_port   : option data;         (* target port (immediate), if any *)
  tp_portmap : option (nat * nat * string);
                            (* the target port computed by a symhash (modulus,
                               offset) keyed map lookup — e.g.
                               `tproxy to <a>:symhash mod N map {...}`; the map's
                               entries are looked up by name at runtime *)
  tp_family : string;              (* "ip" / "ip6" / "" *)
}.

(** A [fwd] statement: terminal (like NAT/tproxy) — forward the packet to a device
    (and optionally address); the forward is a side effect outside the
    single-packet verdict model (which sees a terminal Accept).
    REGISTER-FREE source: [fwd_dev] names the device EXPRESSION (`fwd to "lo"` /
    `fwd to <map>`), [fwd_addr] the optional target address VALUE, [fwd_family] the
    "ip"/"ip6" qualifier.  The compiler ([compile_terminal]) loads the device into
    register 1, the address (if any) into register 2, derives the numeric nfproto
    from the family, and emits [IFwd (Some 1) …]. *)
Record fwd_spec : Type := {
  fwd_dev    : vsrc;             (* the device value expression (reg 1) *)
  fwd_addr   : option data;      (* the target address immediate (reg 2), if any *)
  fwd_family : string;          (* "ip" / "ip6" — used only when [fwd_addr] present *)
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

(** A SYNTHESIZED protocol-dependency guard (the implicit `meta l4proto`/
    `meta nfproto`/`meta iiftype` match nft inserts before a payload selector),
    as emitted by the frontend.  Definitionally the match it wraps — evaluation,
    loadability and compilation are those of [BMatch] — the name only marks, in
    a generated source term, which conjuncts the frontend synthesized versus
    the user wrote. *)
Definition BDep (m : matchcond) : body_item := BMatch m.

(** The match conditions of a body, in order (statements dropped). *)
Definition body_matches (b : list body_item) : list matchcond :=
  flat_map (fun it => match it with BMatch m => m :: nil | BStmt _ => nil end) b.

(** The [dynset] op denoting element removal (`delete @s {...}`), vs the
    add/update insertion ops ([dynset_op] is defined in Bytecode.v, next to the
    other operator enums). *)
Definition op_delete : dynset_op := SOdelete.

(** The [nat_kind] values, branched on by [Semantics.apply_nat] to select the
    data-plane rewrite:
    - [nat_masq_kind] ([NKmasq]) source-NATs to the exit interface's address;
    - [nat_snat_kind] ([NKsnat]) source-NATs to the operand address (reg 1);
    - [nat_dnat_kind] ([NKdnat]) dest-NATs to the operand address (reg 1);
    - [nat_redir_kind] ([NKredir]) dest-NATs to the inbound interface's address
      (redirect = local DNAT). *)
Definition nat_masq_kind  : nat_op := NKmasq.
Definition nat_snat_kind  : nat_op := NKsnat.
Definition nat_dnat_kind  : nat_op := NKdnat.
Definition nat_redir_kind : nat_op := NKredir.

(** The [nat_family] values, branched on by [Semantics.apply_nat] to pick the
    address geometry: [NFip4] = the 32-bit IPv4 slot, [NFip6] = the 128-bit IPv6
    slot (the kernel chooses 32 vs 128 bits by family — [nat_addrlen],
    netlink_linearize.c:1237); [NFinet] is the runtime-dispatched sentinel (see
    [nat_af] in Bytecode.v and [Semantics.nat_addrfamily_pkt]). *)
Definition nat_fam_ip4 : nat_af := NFip4.
Definition nat_fam_ip6 : nat_af := NFip6.
Definition nat_fam_inet : nat_af := NFinet.

(** The "ip6" family-qualifier STRING of the still-stringly-typed fwd/tproxy
    specs, used by [Compile.nfproto_of_family] (String is in scope here). *)
Definition fam_ip6_str : string := "ip6".

(** A rule's OUTCOME: exactly one of a static verdict, a fall-through, a
    verdict-map lookup, or one of the four terminal side effects
    (nat/tproxy/fwd/queue, each a terminal Accept whose redirect is a side
    effect).  A rule has ONE outcome — the sum replaces the historical product
    of a filler verdict plus five optional terminal slots. *)
Inductive outcome : Type :=
| OVerdict (v : verdict)    (* static terminal verdict (Accept/Drop/Jump/…) *)
| ONone                     (* fall through: no outcome, traversal continues *)
| OVmap   (s : vmap_spec)   (* verdict-map lookup; a miss falls through *)
| OVmapNat (s : vmap_spec) (ns : nat_spec)
                            (* verdict-map lookup whose MISS fires a terminal
                               NAT (`… vmap {…} redirect`): the kernel runs the
                               statements in order, so a map miss reaches the
                               trailing NAT statement.  The miss-only
                               reachability holds in the VERDICT semantics
                               ([Semantics.outcome]/[end_loadable]/[run_rule]);
                               the TRACE evaluator's NAT effect is keyed on
                               [r_nat] and unfaithfully fires on a HIT too — a
                               KNOWN INFIDELITY (see [Semantics.eval_rules_trace]
                               and DEVELOPMENT.md § "Known model infidelities") *)
| ONat    (s : nat_spec)    (* snat/dnat/masquerade/redirect (terminal) *)
| OTproxy (s : tproxy_spec) (* transparent proxy (terminal) *)
| OFwd    (s : fwd_spec)    (* forward to a device (terminal) *)
| OQueue  (s : queue_spec). (* value-sourced userspace queue (terminal) *)

(** A rule: an ordered body (matches + verdict-neutral statements), one
    outcome, and the verdict-neutral statements emitted *after* the outcome
    (e.g. a counter after a verdict map) — they run for their side effect but
    cannot change the verdict, which a terminal outcome already fixed. *)
Record rule : Type := {
  r_body    : list body_item;
  r_outcome : outcome;
  r_after   : list stmt;
}.

(** *** Projection views of the outcome sum.

    The evaluators and the compiler dispatch on the outcome through these
    single-constructor projections (each is [Some] exactly on its constructor).
    [r_verdict] projects the static verdict, with [Continue] for every
    non-[OVerdict] outcome — [ONone] IS the fall-through [Continue]. *)
Definition r_verdict (r : rule) : verdict :=
  match r_outcome r with OVerdict v => v | _ => Continue end.
Definition r_vmap (r : rule) : option vmap_spec :=
  match r_outcome r with OVmap s | OVmapNat s _ => Some s | _ => None end.
Definition r_nat (r : rule) : option nat_spec :=
  match r_outcome r with ONat s | OVmapNat _ s => Some s | _ => None end.
Definition r_tproxy (r : rule) : option tproxy_spec :=
  match r_outcome r with OTproxy s => Some s | _ => None end.
Definition r_fwd (r : rule) : option fwd_spec :=
  match r_outcome r with OFwd s => Some s | _ => None end.
Definition r_queue (r : rule) : option queue_spec :=
  match r_outcome r with OQueue s => Some s | _ => None end.

(** *** The historical product encoding of a rule and its translation.

    A rule used to carry a PRODUCT of one always-present verdict plus five
    optional terminal specs, with dummy fillers ([Continue]/[None]) occupying
    the unused slots.  [rule_prod] is that encoding, kept solely to state the
    representation-change ratchet: [rule_of_prod] translates it into the
    outcome sum along the old evaluation precedence (vmap first; then
    nat > tproxy > fwd > queue; then the static verdict, [Continue] = fall
    through), and [Semantics.run_rule_outcome_eq] proves the translation
    evaluation-equal to the old product semantics for every well-formed
    product ([prod_wf]: at most one populated slot, and a filler [Continue]
    verdict under a vmap — exactly the shapes the frontend ever produced). *)
Record rule_prod : Type := {
  rp_body    : list body_item;
  rp_verdict : verdict;
  rp_vmap    : option vmap_spec;
  rp_nat     : option nat_spec;
  rp_tproxy  : option tproxy_spec;
  rp_fwd     : option fwd_spec;
  rp_queue   : option queue_spec;
  rp_after   : list stmt;
}.

Definition outcome_of_prod (rp : rule_prod) : outcome :=
  match rp_vmap rp with
  | Some s => match rp_nat rp with
              | Some ns => OVmapNat s ns
              | None => OVmap s
              end
  | None =>
  match rp_nat rp with Some s => ONat s | None =>
  match rp_tproxy rp with Some s => OTproxy s | None =>
  match rp_fwd rp with Some s => OFwd s | None =>
  match rp_queue rp with Some s => OQueue s | None =>
  match rp_verdict rp with Continue => ONone | v => OVerdict v end
  end end end end end.

Definition rule_of_prod (rp : rule_prod) : rule :=
  {| r_body := rp_body rp; r_outcome := outcome_of_prod rp; r_after := rp_after rp |}.

(** Well-formed products: at most one outcome slot is populated — except the
    genuine vmap-then-NAT combination ([OVmapNat]) — and a pure vmap rule
    carries the filler [Continue] verdict (its miss falls through). *)
Definition prod_wf (rp : rule_prod) : bool :=
  match rp_vmap rp, rp_nat rp, rp_tproxy rp, rp_fwd rp, rp_queue rp with
  | Some _, Some _, None, None, None => true
  | Some _, None, None, None, None =>
      match rp_verdict rp with Continue => true | _ => false end
  | None, None, None, None, None => true
  | None, Some _, None, None, None => true
  | None, None, Some _, None, None => true
  | None, None, None, Some _, None => true
  | None, None, None, None, Some _ => true
  | _, _, _, _, _ => false
  end.

(** *** Source-side numgen-freedom.

    An incremental `numgen` ([FNumgen] with [ng_random = false]) has no
    parser/DSL surface: the lowering REJECTS any rule carrying one (fail-loud
    [Lower.LEnumgen]), so [Lower_Proofs.lower_ruleset_numgen_free] discharges
    the [rule_numgen_free] hypothesis of the mutation-strand compiler theorems
    over EVERY frontend-emitted program.  The predicate is decidable on the
    source rule — a compiled incremental [INumgen] arises only from a load of
    an incremental [FNumgen] field, and [Correct.numgen_free_compile_rule]
    proves the two agree exactly:
    [numgen_free_prog (compile_rule r) = rule_numgen_free r]. *)
Definition field_ngfree (f : field) : bool :=
  match f with FNumgen spec => ng_random spec | _ => true end.

Definition vsrc_ngfree (vs : vsrc) : bool :=
  match vs with
  | VImm _ => true
  | VField f _ => field_ngfree f
  | VMap fields _ _ | VHash fields _ _ _ _ | VHashMap fields _ _ _ _ _ =>
      forallb field_ngfree fields
  | VOr srcs _ => forallb (fun e => field_ngfree (fst e)) srcs
  | VMapT elems _ => forallb (fun e => field_ngfree (fst e)) elems
  end.

Definition match_ngfree (m : matchcond) : bool :=
  match m with
  | MEq f _ | MNeq f _ | MRange f _ _ _ | MMasked f _ _ _ _
  | MCmp f _ _ | MTransform f _ _ _ | MSetT f _ _ _ | MRangeT f _ _ _ _ =>
      field_ngfree f
  | MConcatSet fields _ _ => forallb field_ngfree fields
  | MConcatSetT elems _ _ => forallb (fun fe => field_ngfree (fst fe)) elems
  | MLimit _ | MQuota _ | MConnlimit _ => true
  end.

Definition stmt_ngfree (s : stmt) : bool :=
  match s with
  | SMangle vs _ _ _ _ _ _ => vsrc_ngfree vs
  | SMetaSet _ vs | SCtSet _ vs => vsrc_ngfree vs
  | SCtSetDir _ _ vs => vsrc_ngfree vs
  | SExthdrWrite vs _ _ _ _ => vsrc_ngfree vs
  | SDupSrc src _ _ => vsrc_ngfree src
  | SDynset _ _ keyfs dataf => forallb field_ngfree (keyfs ++ dataf)
  | SObjrefMap keyfs _ => forallb field_ngfree keyfs
  | SDynsetImm _ _ keyfs _ => forallb field_ngfree keyfs
  | SCounter _ _ | SNotrack | SLog _ | SObjref _ _ | SSynproxy _ _
  | SLast _ | SExthdrReset _ _ | SDup _ _ => true
  end.

Definition body_item_ngfree (it : body_item) : bool :=
  match it with BMatch m => match_ngfree m | BStmt s => stmt_ngfree s end.

Definition vmap_ngfree (ov : option vmap_spec) : bool :=
  match ov with
  | None => true
  | Some vm => match vm_keyf vm with
               | Some (f, _) => field_ngfree f
               | None => forallb field_ngfree (vm_fields vm)
               end
  end.

(** The terminal's field positions, mirroring [Compile.compile_terminal]'s
    dispatch order (nat, then tproxy, then fwd, then queue, then the static
    verdict): only a nat operand / fwd device / queue number can load a field;
    tproxy and a static verdict load none. *)
Definition terminal_ngfree (r : rule) : bool :=
  match r_nat r with
  | Some n => match nat_src n with
              | Some vs => vsrc_ngfree vs
              | None => match nat_map n with
                        | Some (fields, _, _) => forallb field_ngfree fields
                        | None => match nat_field n with
                                  | Some (f, _) => field_ngfree f
                                  | None => true
                                  end
                        end
              end
  | None =>
  match r_tproxy r with
  | Some _ => true
  | None =>
  match r_fwd r with
  | Some w => vsrc_ngfree (fwd_dev w)
  | None =>
  match r_queue r with
  | Some q => vsrc_ngfree (q_num q)
  | None => true
  end end end end.

(** A rule with no incremental `numgen` in ANY field position. *)
Definition rule_numgen_free (r : rule) : bool :=
  forallb body_item_ngfree (r_body r)
  && vmap_ngfree (r_vmap r)
  && terminal_ngfree r
  && forallb stmt_ngfree (r_after r).

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
