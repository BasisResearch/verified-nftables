(** * Surface.Selector: selector key paths -> (IR field, datatype, deps).

    The Coq counterpart of the UNVERIFIED [extracted/nft_lower.ml]
    [key_field]/[bitfield_sel] tables: which IR [field] a surface selector
    loads, at which DATATYPE its right-hand side is typed, and which implicit
    protocol dependencies nft inserts before the load (payload.c
    payload_gen_dependency; family resolution stays in the lowering).

    Two shapes:
      - [selector]  : byte-aligned selectors -> (field, dtype, deps);
      - [bitfield]  : sub-byte header bitfields -> a [bitfield_spec] whose
        mask/shift are NUMBERS (bit width + LSB position), not byte masks —
        the byte-level mask is derived where bytes are made (the verified
        lowering of a later milestone), never stored here.

    Kind assignment is a TYPING decision, so it lives here (in Coq), per the
    typed-source architecture's "typing never in the OCaml frontend".

    Offsets/lengths mirror key_field's, which the golden corpus round-trip
    pins (see the per-family comments in nft_lower.ml for the payload
    citations); [selector_widths_agree] below re-checks every table row's
    dtype width against the IR load width. *)

From Stdlib Require Import List PeanoNat Bool NArith String.
From Nft Require Import Bytes Packet Verdict Bytecode Syntax Ast Datatype Symbols.
Import ListNotations.
Local Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(** ** Implicit-dependency SPECS (numbers; the guard bytes and the
    family-awareness — inet vs L2 vs single-L3 — are lowering decisions). *)
Inductive depspec : Type :=
| DepL4       (proto : nat)   (* `meta l4proto == proto` transport guard      *)
| DepNfproto  (fam : nat)     (* `meta nfproto == fam` network guard (inet)   *)
| DepNetLL    (fam : nat)     (* network guard synthesised UNDER the link
                                 header (payload.c payload_gen_special_dependency,
                                 e.g. `icmp type` in bridge): the guard's SHAPE
                                 differs from [DepNfproto] only in the L2 families
                                 — proto_eth reads the in-frame ethertype with a
                                 `payload load 2b @ link + 12`, where a direct
                                 network selector ([DepNfproto]) reaches the
                                 protocol via proto_netdev's `meta protocol`
                                 (src/proto.c proto_eth vs proto_netdev
                                 protocol_key template).                       *)
| DepEther    (et : N)        (* `ether type == et` VLAN guard                *)
| DepL2proto  (et : N)        (* `meta protocol == et` L2-family net guard    *)
| DepIiftype  (t : nat)       (* `meta iiftype == ARPHRD t` link guard        *)
| DepIcmpType (t : nat).      (* `icmp type == t` union-field guard           *)

(** The transport guard(s) of an L4 protocol: icmp/icmpv6/igmp are
    network-protocol-LINKED and carry the nfproto guard FIRST (payload.c
    proto_icmp/proto_icmp6; golden inet/icmp.t.payload order). *)
Definition dep_l4 (proto : string) : list depspec :=
  if String.eqb proto "tcp" then [DepL4 6]
  else if String.eqb proto "udp" then [DepL4 17]
  else if String.eqb proto "ah" then [DepL4 51]
  else if String.eqb proto "esp" then [DepL4 50]
  else if String.eqb proto "comp" then [DepL4 108]
  else if String.eqb proto "sctp" then [DepL4 132]
  else if String.eqb proto "dccp" then [DepL4 33]
  else if String.eqb proto "udplite" then [DepL4 136]
  else if String.eqb proto "icmp" then [DepNetLL 2; DepL4 1]
  else if String.eqb proto "icmpv6" then [DepNetLL 10; DepL4 58]
  else if String.eqb proto "igmp" then [DepNetLL 2; DepL4 2]
  else [].

Definition dep_ip4 : list depspec := [DepNfproto 2].
Definition dep_ip6 : list depspec := [DepNfproto 10].
Definition dep_arp : list depspec := [DepL2proto 0x0806].   (* ETH_P_ARP    *)
Definition dep_ether : list depspec := [DepIiftype 1].      (* ARPHRD_ETHER *)

(* ------------------------------------------------------------------ *)
(** ** The byte-aligned selector table (mirror of key_field, minus the
    parametric fib/ctdir/tcpopt families handled below). *)

Definition selinfo : Type := field * dtype * list depspec.

Definition sel_table : list (skeypath * selinfo) := [
  (* transport ports *)
  (["tcp"; "dport"], (FThDport, DTinet_service, dep_l4 "tcp"));
  (["udp"; "dport"], (FThDport, DTinet_service, dep_l4 "udp"));
  (["th"; "dport"],  (FThDport, DTinet_service, []));
  (["tcp"; "sport"], (FThSport, DTinet_service, dep_l4 "tcp"));
  (["udp"; "sport"], (FThSport, DTinet_service, dep_l4 "udp"));
  (["th"; "sport"],  (FThSport, DTinet_service, []));
  (["tcp"; "flags"], (FTcpFlags, DTtcp_flag, dep_l4 "tcp"));
  (* IPv4 network header *)
  (["ip"; "saddr"],    (FIp4Saddr,    DTipv4,       dep_ip4));
  (["ip"; "daddr"],    (FIp4Daddr,    DTipv4,       dep_ip4));
  (["ip"; "protocol"], (FIp4Protocol, DTinet_proto, dep_ip4));
  (["ip"; "ttl"],      (FIp4Ttl,      DTinteger 1,  dep_ip4));
  (["ip"; "length"],   (FIp4Totlen,   DTinteger 2,  dep_ip4));
  (["ip"; "id"],       (FIp4Id,       DTinteger 2,  dep_ip4));
  (["ip"; "frag-off"], (FIp4FragOff,  DTinteger 2,  dep_ip4));
  (["ip"; "checksum"], (FIp4Csum,     DTinteger 2,  dep_ip4));
  (* IPv6 network header *)
  (["ip6"; "saddr"],    (FIp6Saddr, DTipv6, dep_ip6));
  (["ip6"; "daddr"],    (FIp6Daddr, DTipv6, dep_ip6));
  (["ip6"; "length"],   (FPayload PNetwork 4 2, DTinteger 2,  dep_ip6));
  (["ip6"; "hoplimit"], (FPayload PNetwork 7 1, DTinteger 1,  dep_ip6));
  (["ip6"; "nexthdr"],  (FPayload PNetwork 6 1, DTinet_proto, dep_ip6));
  (* ICMP / ICMPv6 *)
  (["icmp"; "type"],       (FIcmpType, DTicmp_type,   dep_l4 "icmp"));
  (["icmp"; "code"],       (FIcmpCode, DTicmp_code,   dep_l4 "icmp"));
  (["icmp"; "checksum"],   (FPayload PTransport 2 2, DTinteger 2, dep_l4 "icmp"));
  (["icmp"; "id"],         (FPayload PTransport 4 2, DTinteger 2, dep_l4 "icmp"));
  (["icmp"; "seq"],        (FPayload PTransport 6 2, DTinteger 2, dep_l4 "icmp"));
  (["icmp"; "sequence"],   (FPayload PTransport 6 2, DTinteger 2, dep_l4 "icmp"));
  (["icmp"; "gateway"],    (FPayload PTransport 4 4, DTinteger 4,
                            (dep_l4 "icmp" ++ [DepIcmpType 5])%list));
  (["icmp"; "mtu"],        (FPayload PTransport 6 2, DTinteger 2,
                            (dep_l4 "icmp" ++ [DepIcmpType 3])%list));
  (["icmpv6"; "type"],     (FIcmpType, DTicmpv6_type, dep_l4 "icmpv6"));
  (["icmpv6"; "code"],     (FIcmpCode, DTicmpv6_code, dep_l4 "icmpv6"));
  (["icmpv6"; "checksum"], (FPayload PTransport 2 2, DTinteger 2, dep_l4 "icmpv6"));
  (["icmpv6"; "id"],       (FPayload PTransport 4 2, DTinteger 2, dep_l4 "icmpv6"));
  (["icmpv6"; "seq"],      (FPayload PTransport 6 2, DTinteger 2, dep_l4 "icmpv6"));
  (["icmpv6"; "sequence"], (FPayload PTransport 6 2, DTinteger 2, dep_l4 "icmpv6"));
  (["icmpv6"; "mtu"],      (FPayload PTransport 4 4, DTinteger 4,
                            (dep_l4 "icmpv6" ++ [DepIcmpType 2])%list));
  (* IGMP (transport header; IPv4-linked) *)
  (["igmp"; "type"],     (FPayload PTransport 0 1, DTigmp_type, dep_l4 "igmp"));
  (["igmp"; "mrt"],      (FPayload PTransport 1 1, DTinteger 1, dep_l4 "igmp"));
  (["igmp"; "checksum"], (FPayload PTransport 2 2, DTinteger 2, dep_l4 "igmp"));
  (* additional TCP / UDP header fields *)
  (["tcp"; "sequence"], (FTcpSeq, DTinteger 4, dep_l4 "tcp"));
  (["tcp"; "ackseq"],   (FTcpAck, DTinteger 4, dep_l4 "tcp"));
  (["tcp"; "window"],   (FPayload PTransport 14 2, DTinteger 2, dep_l4 "tcp"));
  (["tcp"; "checksum"], (FPayload PTransport 16 2, DTinteger 2, dep_l4 "tcp"));
  (["tcp"; "urgptr"],   (FPayload PTransport 18 2, DTinteger 2, dep_l4 "tcp"));
  (["udp"; "length"],   (FUdpLen,  DTinteger 2, dep_l4 "udp"));
  (["udp"; "checksum"], (FUdpCsum, DTinteger 2, dep_l4 "udp"));
  (* link layer.  `ether type` / vlan selectors carry the `meta iiftype ==
     ARPHRD_ETHER` link guard so they cannot fire on a non-ethernet device
     (loopback / tunnels) in inet/netdev — nft prepends it (payload.c
     payload_gen_dependency -> proto_dev, ARPHRD_ETHER); [dep_ether] makes it a
     no-op in bridge (an inherently ethernet family).  Historically it was
     attached only to ether ADDRESS selectors, so `ether type`/`vlan` fired on
     loopback (reports/corpus-divergence-bugs class F, packet-proven). *)
  (["ether"; "type"],  (FEtherType,  DTethertype, dep_ether));
  (["ether"; "saddr"], (FEtherSaddr, DTether, dep_ether));
  (["ether"; "daddr"], (FEtherDaddr, DTether, dep_ether));
  (* meta *)
  (["meta"; "l4proto"],  (FMetaL4proto,  DTinet_proto, []));
  (["meta"; "nfproto"],  (FMetaNfproto,  DTnfproto,    []));
  (["meta"; "protocol"], (FMetaProtocol, DTethertype,  []));
  (["meta"; "mark"],     (FMetaMark,     DTmark,       []));
  (["meta"; "iifname"],  (FMetaIifname,  DTifname,     []));
  (["meta"; "oifname"],  (FMetaOifname,  DTifname,     []));
  (["meta"; "iif"],      (FMetaIif,      DTifindex,    []));
  (["meta"; "oif"],      (FMetaOif,      DTifindex,    []));
  (["meta"; "obrname"],  (FMetaGen MKbri_oifname, DTifname, []));
  (["meta"; "ibrname"],  (FMetaGen MKbri_iifname, DTifname, []));
  (["meta"; "pkttype"],  (FMetaPkttype,  DTpkttype,    []));
  (["meta"; "length"],   (FMetaLen,      DThostint 4,  []));
  (["meta"; "len"],      (FMetaLen,      DThostint 4,  []));
  (["meta"; "cpu"],      (FMetaCpu,      DThostint 4,  []));
  (["meta"; "skuid"],    (FMetaSkuid,    DThostint 4,  []));
  (["meta"; "skgid"],    (FMetaSkgid,    DThostint 4,  []));
  (["meta"; "iifgroup"], (FMetaGen MKiifgroup, DThostint 4, []));
  (["meta"; "oifgroup"], (FMetaGen MKoifgroup, DThostint 4, []));
  (["meta"; "cgroup"],   (FMetaGen MKcgroup,   DThostint 4, []));
  (["meta"; "iiftype"],  (FMetaIiftype,  DThostint 2,  []));
  (["meta"; "oiftype"],  (FMetaOiftype,  DThostint 2,  []));
  (* bare meta shorthands *)
  (["mark"],    (FMetaMark,    DTmark,    []));
  (["pkttype"], (FMetaPkttype, DTpkttype, []));
  (["iifname"], (FMetaIifname, DTifname,  []));
  (["oifname"], (FMetaOifname, DTifname,  []));
  (["iif"],     (FMetaIif,     DTifindex, []));
  (["oif"],     (FMetaOif,     DTifindex, []));
  (* conntrack *)
  (["ct"; "state"],      (FCtState,      DTct_state,  []));
  (["ct"; "status"],     (FCtStatus,     DTct_status, []));
  (["ct"; "mark"],       (FCtMark,       DTmark,      []));
  (["ct"; "direction"],  (FCtDirection,  DTct_dir,    []));
  (["ct"; "id"],         (FCtId,         DThostint 4, []));
  (["ct"; "expiration"], (FCtExpiration, DTtime,      []));
  (["ct"; "zone"],       (FCtGen CKzone, DThostint 2, []));
  (* ARP header (network header; L2 families pin `meta protocol == 0x0806`) *)
  (["arp"; "htype"],     (FPayload PNetwork 0 2, DTinteger 2, dep_arp));
  (["arp"; "ptype"],     (FPayload PNetwork 2 2, DTethertype, dep_arp));
  (["arp"; "hlen"],      (FPayload PNetwork 4 1, DTinteger 1, dep_arp));
  (["arp"; "plen"],      (FPayload PNetwork 5 1, DTinteger 1, dep_arp));
  (["arp"; "operation"], (FPayload PNetwork 6 2, DTarp_op,    dep_arp));
  (["arp"; "saddr"; "ether"], (FPayload PNetwork 8 6,  DTether, dep_arp));
  (["arp"; "saddr"; "ip"],    (FPayload PNetwork 14 4, DTipv4,  dep_arp));
  (["arp"; "daddr"; "ether"], (FPayload PNetwork 18 6, DTether, dep_arp));
  (["arp"; "daddr"; "ip"],    (FPayload PNetwork 24 4, DTipv4,  dep_arp));
  (* AH / ESP / COMP / SCTP / DCCP / UDP-Lite (transport header) *)
  (["ah"; "nexthdr"],   (FPayload PTransport 0 1, DTinet_proto, dep_l4 "ah"));
  (["ah"; "hdrlength"], (FPayload PTransport 1 1, DTinteger 1,  dep_l4 "ah"));
  (["ah"; "reserved"],  (FPayload PTransport 2 2, DTinteger 2,  dep_l4 "ah"));
  (["ah"; "spi"],       (FPayload PTransport 4 4, DTinteger 4,  dep_l4 "ah"));
  (["ah"; "sequence"],  (FPayload PTransport 8 4, DTinteger 4,  dep_l4 "ah"));
  (["esp"; "spi"],      (FPayload PTransport 0 4, DTinteger 4,  dep_l4 "esp"));
  (["esp"; "sequence"], (FPayload PTransport 4 4, DTinteger 4,  dep_l4 "esp"));
  (["comp"; "nexthdr"], (FPayload PTransport 0 1, DTinet_proto, dep_l4 "comp"));
  (["comp"; "flags"],   (FPayload PTransport 1 1, DTinteger 1,  dep_l4 "comp"));
  (["comp"; "cpi"],     (FPayload PTransport 2 2, DTinteger 2,  dep_l4 "comp"));
  (["sctp"; "sport"],    (FPayload PTransport 0 2, DTinet_service, dep_l4 "sctp"));
  (["sctp"; "dport"],    (FPayload PTransport 2 2, DTinet_service, dep_l4 "sctp"));
  (["sctp"; "vtag"],     (FPayload PTransport 4 4, DTinteger 4,    dep_l4 "sctp"));
  (["sctp"; "checksum"], (FPayload PTransport 8 4, DTinteger 4,    dep_l4 "sctp"));
  (["dccp"; "sport"],    (FPayload PTransport 0 2, DTinet_service, dep_l4 "dccp"));
  (["dccp"; "dport"],    (FPayload PTransport 2 2, DTinet_service, dep_l4 "dccp"));
  (["udplite"; "sport"],    (FPayload PTransport 0 2, DTinet_service, dep_l4 "udplite"));
  (["udplite"; "dport"],    (FPayload PTransport 2 2, DTinet_service, dep_l4 "udplite"));
  (["udplite"; "cscov"],    (FPayload PTransport 4 2, DTinteger 2,    dep_l4 "udplite"));
  (["udplite"; "csumcov"],  (FPayload PTransport 4 2, DTinteger 2,    dep_l4 "udplite"));
  (["udplite"; "checksum"], (FPayload PTransport 6 2, DTinteger 2,    dep_l4 "udplite"));
  (* IPv6 extension headers (exthdr walker; htype = the exthdr's IPPROTO) *)
  (["hbh"; "nexthdr"],    (FExthdr EPipv6 0   0 1 false, DTinet_proto, dep_ip6));
  (["hbh"; "hdrlength"],  (FExthdr EPipv6 0   1 1 false, DTinteger 1,  dep_ip6));
  (["rt"; "nexthdr"],     (FExthdr EPipv6 43  0 1 false, DTinet_proto, dep_ip6));
  (["rt"; "hdrlength"],   (FExthdr EPipv6 43  1 1 false, DTinteger 1,  dep_ip6));
  (["rt"; "type"],        (FExthdr EPipv6 43  2 1 false, DTinteger 1,  dep_ip6));
  (["rt"; "seg-left"],    (FExthdr EPipv6 43  3 1 false, DTinteger 1,  dep_ip6));
  (["srh"; "last-entry"], (FExthdr EPipv6 43  4 1 false, DTinteger 1,  dep_ip6));
  (["srh"; "flags"],      (FExthdr EPipv6 43  5 1 false, DTinteger 1,  dep_ip6));
  (["srh"; "tag"],        (FExthdr EPipv6 43  6 2 false, DTinteger 2,  dep_ip6));
  (["frag"; "nexthdr"],   (FExthdr EPipv6 44  0 1 false, DTinet_proto, dep_ip6));
  (["frag"; "reserved"],  (FExthdr EPipv6 44  1 1 false, DTinteger 1,  dep_ip6));
  (["frag"; "id"],        (FExthdr EPipv6 44  4 4 false, DTinteger 4,  dep_ip6));
  (["dst"; "nexthdr"],    (FExthdr EPipv6 60  0 1 false, DTinet_proto, dep_ip6));
  (["dst"; "hdrlength"],  (FExthdr EPipv6 60  1 1 false, DTinteger 1,  dep_ip6));
  (["mh"; "nexthdr"],     (FExthdr EPipv6 135 0 1 false, DTinet_proto, dep_ip6));
  (["mh"; "hdrlength"],   (FExthdr EPipv6 135 1 1 false, DTinteger 1,  dep_ip6));
  (["mh"; "type"],        (FExthdr EPipv6 135 2 1 false, DTmh_type,    dep_ip6));
  (["mh"; "reserved"],    (FExthdr EPipv6 135 3 1 false, DTinteger 1,  dep_ip6));
  (["mh"; "checksum"],    (FExthdr EPipv6 135 4 2 false, DTinteger 2,  dep_ip6))
].

Fixpoint keypath_eqb (a b : skeypath) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => String.eqb x y && keypath_eqb a' b'
  | _, _ => false
  end.

Fixpoint assoc_kp {A : Type} (kp : skeypath) (tbl : list (skeypath * A))
  : option A :=
  match tbl with
  | [] => None
  | (k, v) :: rest => if keypath_eqb kp k then Some v else assoc_kp kp rest
  end.

(* ------------------------------------------------------------------ *)
(** ** The parametric selector families. *)

(** fib result columns (`fib <sel> type/oif/oifname`); the selector key list
    [sel] (e.g. "daddr", "daddr.iif") stays an opaque string, exactly as
    [FFib] carries it. *)
Definition sel_fib (rest : list string) : option selinfo :=
  match rest with
  | [sel; res] =>
      if String.eqb res "type" then Some (FFib sel FRtype, DTfib_addrtype, [])
      else if String.eqb res "oifname" then Some (FFib sel FRoifname, DTifname, [])
      else if String.eqb res "oif" then Some (FFib sel FRoif, DTinteger 4, [])
      else None
  | _ => None
  end.

(** Direction-qualified conntrack tuple (`ct original ip saddr`, ...); the
    FCtDir key strings match nft's `ct load <key>` render. *)
Definition sel_ctdir (rest : list string) : option selinfo :=
  match rest with
  | [d; k] =>
      if String.eqb k "zone" then Some (FCtDir "zone" d, DThostint 2, [])
      else if String.eqb k "protocol" then Some (FCtDir "protocol" d, DTinet_proto, [])
      else if String.eqb k "proto-src" then Some (FCtDir "proto_src" d, DTinet_service, [])
      else if String.eqb k "proto-dst" then Some (FCtDir "proto_dst" d, DTinet_service, [])
      else None
  | [d; fam; k] =>
      if String.eqb fam "ip" then
        (if String.eqb k "saddr" then Some (FCtDir "src_ip" d, DTipv4, [])
         else if String.eqb k "daddr" then Some (FCtDir "dst_ip" d, DTipv4, [])
         else None)
      else if String.eqb fam "ip6" then
        (if String.eqb k "saddr" then Some (FCtDir "src_ip6" d, DTipv6, [])
         else if String.eqb k "daddr" then Some (FCtDir "dst_ip6" d, DTipv6, [])
         else None)
      else None
  | _ => None
  end.

(** TCP options (`tcp option <name> <field>`): exthdr tcpopt load positioned
    by Symbols.dt_tcpopt_num/dt_tcpopt_field; byte-aligned integer fields. *)
Definition sel_tcpopt (rest : list string) : option selinfo :=
  match rest with
  | [name; f] =>
      match dt_tcpopt_num name, dt_tcpopt_field name f with
      | Some optnum, Some (off, len) =>
          Some (FExthdr EPtcpopt (N.to_nat optnum) off len false,
                DTinteger len, [])
      | _, _ => None
      end
  | _ => None
  end.

(** The exthdr IPPROTO of a presence test (`exthdr <p> exists|missing`). *)
Definition exthdr_htype (proto : string) : option nat :=
  if String.eqb proto "hbh" then Some 0
  else if String.eqb proto "rt" then Some 43
  else if String.eqb proto "frag" then Some 44
  else if String.eqb proto "dst" then Some 60
  else if String.eqb proto "mh" then Some 135
  else None.

(** The full selector map. *)
Definition selector (kp : skeypath) : option selinfo :=
  match kp with
  | k :: rest =>
      if String.eqb k "fib" then sel_fib rest
      else if String.eqb k "ctdir" then sel_ctdir rest
      else if String.eqb k "tcpopt" then sel_tcpopt rest
      else assoc_kp kp sel_table
  | [] => None
  end.

(* ------------------------------------------------------------------ *)
(** ** Sub-byte header bitfields.

    A field occupying [bf_bits] bits at LSB position [bf_shift] of the
    [bf_bytes]-byte load [bf_field]; nft compiles it to load + `& mask` +
    compare against value<<shift, where mask = (2^bits - 1) << shift over the
    loaded bytes (golden {ip,ip6,bridge}/…t.payload; the mask BYTES are
    derived from these numbers at lowering time). *)
Record bitfield_spec : Type := mkBitfield {
  bf_field : field;
  bf_bytes : nat;
  bf_bits  : nat;
  bf_shift : nat;
  bf_deps  : list depspec;
  bf_dscp  : bool }.          (* rhs symbols come from dt_syms_dscp *)

Definition bf (f : field) (bytes bits shift : nat) (deps : list depspec)
              (dscp : bool) : bitfield_spec :=
  mkBitfield f bytes bits shift deps dscp.

Definition bitfield_table : list (skeypath * bitfield_spec) := [
  (["ip"; "version"],   bf (FPayload PNetwork 0 1) 1 4 4 dep_ip4 false);
  (["ip"; "hdrlength"], bf (FPayload PNetwork 0 1) 1 4 0 dep_ip4 false);
  (["ip"; "dscp"],      bf (FPayload PNetwork 1 1) 1 6 2 dep_ip4 true);
  (["ip6"; "dscp"],     bf (FPayload PNetwork 0 2) 2 6 6 dep_ip6 true);
  (["ip6"; "flowlabel"],bf (FPayload PNetwork 1 3) 3 20 0 dep_ip6 false);
  (["tcp"; "doff"],     bf (FPayload PTransport 12 1) 1 4 4 (dep_l4 "tcp") false);
  (* vlan bitfields: the iiftype link guard (F, no-op in bridge) THEN the
     `ether type 0x8100` in-frame guard (payload.c proto_vlan). *)
  (["vlan"; "id"],      bf (FPayload PLink 14 2) 2 12 0 (dep_ether ++ [DepEther 0x8100]) false);
  (["vlan"; "pcp"],     bf (FPayload PLink 14 1) 1 3 5 (dep_ether ++ [DepEther 0x8100]) false);
  (["vlan"; "dei"],     bf (FPayload PLink 14 1) 1 1 4 (dep_ether ++ [DepEther 0x8100]) false);
  (["vlan"; "cfi"],     bf (FPayload PLink 14 1) 1 1 4 (dep_ether ++ [DepEther 0x8100]) false);
  (["frag"; "frag-off"],       bf (FExthdr EPipv6 44 2 2 false) 2 13 3 dep_ip6 false);
  (["frag"; "reserved2"],      bf (FExthdr EPipv6 44 3 1 false) 1 2 1 dep_ip6 false);
  (["frag"; "more-fragments"], bf (FExthdr EPipv6 44 3 1 false) 1 1 0 dep_ip6 false)
].

Definition bitfield (kp : skeypath) : option bitfield_spec :=
  assoc_kp kp bitfield_table.

(* ------------------------------------------------------------------ *)
(** ** Width agreement: every selector's DATATYPE width equals the byte width
    its IR field LOADS.

    [load_width] reads the width off the load descriptor where the IR fixes
    one (payload/exthdr loads; meta/ct keys with a pinned register width);
    symbolic loads (fib columns, ct tuple keys, unpinned meta/ct) have no
    a-priori width and are skipped.  A row failing this check would mean the
    typed layer admits values at a width the compare will never see — the
    exact class of bug the ip6-length/KNum-2 style typos produce. *)
Definition load_width (l : loaddesc) : option nat :=
  match l with
  | LPayload _ _ len => Some len
  | LExthdr _ _ _ len _ => Some len
  | LMeta k => meta_fixed_len k
  | LCt k => ct_fixed_len k
  | _ => None
  end.

Definition width_agrees (f : field) (dt : dtype) : bool :=
  match load_width (field_load f) with
  | Some w => Nat.eqb w (dt_bytes dt)
  | None => true
  end.

Example selector_widths_agree :
  forallb (fun '(_, (f, dt, _)) => width_agrees f dt) sel_table = true.
Proof. vm_compute. reflexivity. Qed.

Example bitfield_widths_agree :
  forallb (fun '(_, s) =>
             match load_width (field_load (bf_field s)) with
             | Some w => Nat.eqb w (bf_bytes s)
             | None => false        (* every bitfield load has a fixed width *)
             end
           && (bf_bits s + bf_shift s <=? 8 * bf_bytes s)%nat)
          bitfield_table = true.
Proof. vm_compute. reflexivity. Qed.

(** tcpopt fields agree by construction ([sel_tcpopt] types at the load
    width); pinned for the record on every named option field. *)
Example tcpopt_widths_agree :
  forallb (fun '(name, f) =>
             match sel_tcpopt [name; f] with
             | Some (fld, dt, _) => width_agrees fld dt
             | None => false
             end)
          [("maxseg","size"); ("window","count"); ("timestamp","tsval");
           ("timestamp","tsecr"); ("sack","left"); ("sack1","right");
           ("mptcp","kind"); ("fastopen","length")] = true.
Proof. vm_compute. reflexivity. Qed.

(** The map is a real partial map: an unknown selector is refused. *)
Example selector_unknown : selector ["tcp"; "bogus"] = None.
Proof. reflexivity. Qed.
Example selector_tcp_dport :
  selector ["tcp"; "dport"] = Some (FThDport, DTinet_service, [DepL4 6]).
Proof. reflexivity. Qed.
Example selector_icmp_two_deps :
  selector ["icmp"; "type"]
  = Some (FIcmpType, DTicmp_type, [DepNetLL 2; DepL4 1]).
Proof. reflexivity. Qed.
