(* Nft_lower: surface AST (Nft_ast) -> trusted Syntax AST + Packet.env.

   Since the M2 typed-layer milestone this file is a DRIVER, not an encoder:
   every SCALAR match shape (typed atoms, ranges incl. the hton ranges,
   ct-state/status and tcp-flags bitmask forms and comma OR-lists, sub-byte
   bitfields, presence tests, CIDR prefixes, ifname wildcards, explicit
   bitwise masks, and the implicit protocol-dependency guard values) is
   lowered by the extracted VERIFIED Coq lowering (theories/Surface/Lower.v)
   — symbol resolution, coercion, width/byteorder, and byte encoding all
   happen in Coq.  What remains here, in untrusted code:
     - expanding `define` references (`$lan`) and the pure structural
       injection into the Coq surface AST ([Nft_inject]);
     - the per-rule dep-guard DEDUP loop (guard VALUES come from the verified
       [Lower.dep_guard]/[Lower.discharge]);
     - the UNTYPED set/map paths (brace sets, @refs, concatenations, vmaps —
       the M3 milestone) and statement immediates (the M4 milestone), which
       still encode via [typed_atom]/[enc_atom] below;
     - turning named-set/map *declarations* (and inline anonymous `{...}` sets
       and `vmap {...}` maps) into NAMED entries in the evaluation
       environment, which the model looks set/map contents up by name (NOT
       inlined into the rule).

   Everything here is checked downstream (against the Coq proofs' verdicts and
   live `nft`); nothing here is in the proof TCB.  Any construct outside the
   supported subset raises [Unsupported] — we never guess (the verified
   lowering fails LOUD with an [lerr]; there is no OCaml byte fallback for a
   scalar shape).  See TODO 9 in ../DEVELOPMENT.md. *)

module L = Stdlib.List
module S = Stdlib.String

exception Unsupported of string

(* ---------- byte helpers ---------- *)

let bytes_of_int (width : int) (n : int) : Bytes.data =
  if n < 0 then raise (Unsupported "negative numeric literal");
  L.init width (fun i -> (n lsr (8 * (width - 1 - i))) land 0xff)

(* Interface-name -> numeric ifindex resolution.  Real nft resolves this at LOAD
   time via nft_if_nametoindex() against the live host, so it is host-specific.
   We only know the loopback index for certain: the kernel always assigns "lo"
   index 1 (it is the first device registered).  Any other name cannot be
   faithfully resolved without the live interface table, so we raise
   [Unsupported] rather than guess (the same fail-loud discipline an undefined
   `$var` gets; a resolvable-but-non-literal NAT target instead degrades to a bare
   terminal).  A numeric form `iif 2` is always exact. *)
let nametoindex (s : string) : int =
  match s with
  | "lo" -> 1
  | _ -> raise (Unsupported
           ("iif/oif interface name " ^ s ^
            " is resolved to a numeric index at load time against the live "
            ^ "host; use the numeric form (e.g. `iif 2`) or `iifname " ^ s
            ^ "` for the ASCII-name match"))

let ascii (s : string) : Bytes.data =
  L.init (S.length s) (fun i -> Char.code (S.get s i))

(* IFNAMSIZ: the interface-name register is a fixed 16-byte buffer. *)
let ifnamsiz = 16

let zero_pad (b : Bytes.data) (width : int) : Bytes.data =
  let n = Stdlib.List.length b in
  if n >= width then b
  else b @ L.init (width - n) (fun _ -> 0)

(* nft compiles an interface-name match in two DISTINCT ways (golden
   any/meta.t.payload):
     - exact name `iifname "dummy0"`  => full 16-byte zero-padded cmp
       (`0x64756d6d 0x79300000 0x00000000 0x00000000`, payload:198-199);
     - trailing-`*` wildcard `iifname "dummy*"` => a SHORT cmp of just the
       prefix bytes (`0x64756d6d 0x79`, payload:224-225) — the ONLY prefix case.
   The model's byte-level equality is a prefix compare of the stored bytes
   against the field, so a SHORT value gives the wildcard semantics and a
   16-byte zero-padded value gives the exact semantics.  Emitting only the
   unpadded name (the old behaviour) collapsed both into a prefix match,
   unsoundly matching same-prefix interfaces the kernel rejects (e.g.
   `iifname br.20` matching "br.200").

   The lexer keeps a backslash literally, so a trailing `\*` is an ESCAPED star
   (a LITERAL '*' in the name, payload:227-230 `"dummy\*"` => byte 0x2a then
   padded to 16), distinct from an unescaped trailing `*` wildcard. *)
let ifname_bytes (s : string) : Bytes.data =
  let n = S.length s in
  if n >= 2 && S.get s (n - 1) = '*' && S.get s (n - 2) = '\\' then
    (* escaped star: literal '*' at the end, exact name -> pad to 16 *)
    zero_pad (ascii (S.sub s 0 (n - 2) ^ "*")) ifnamsiz
  else if n >= 1 && S.get s (n - 1) = '*' then
    (* trailing unescaped star: wildcard prefix -> short bytes, no pad *)
    ascii (S.sub s 0 (n - 1))
  else
    (* exact name: full 16-byte zero-padded compare *)
    zero_pad (ascii s) ifnamsiz

(* ---------- symbolic-constant tables ---------- *)

let sym_ethertype = [
  "ip",[8;0]; "ip4",[8;0]; "ipv4",[8;0]; "arp",[8;6];
  "ip6",[0x86;0xdd]; "ipv6",[0x86;0xdd]; "vlan",[0x81;0x00];
  "8021q",[0x81;0x00]; "8021ad",[0x88;0xa8];
]
let sym_l4proto = [
  "icmp",[1]; "igmp",[2]; "tcp",[6]; "udp",[17]; "udplite",[136];
  "dccp",[33]; "gre",[47]; "esp",[50]; "ah",[51]; "icmpv6",[58];
  "ipv6-icmp",[58]; "comp",[108]; "sctp",[132];
]
(* meta nfproto is the netfilter L3 FAMILY (NFPROTO family), a distinct 1-byte
   datatype from the L4/IP-protocol space (sym_l4proto).  datatype.c
   nfproto_tbl lists only ipv4/ipv6 as symbols; the rest are the NFPROTO
   family constants from linux/netfilter.h (UNSPEC 0, INET 1, IPV4 2,
   ARP 3, NETDEV 5, BRIDGE 7, IPV6 10).  `meta nfproto ipv4` => cmp 0x02,
   `meta nfproto ipv6` => cmp 0x0a (golden inet/meta.t.payload). *)
let sym_nfproto = [
  "inet",[1]; "ipv4",[2]; "arp",[3]; "netdev",[5];
  "bridge",[7]; "ipv6",[10];
]
let sym_ctstate = [
  "invalid",[0;0;0;1]; "established",[0;0;0;2]; "related",[0;0;0;4];
  "new",[0;0;0;8]; "untracked",[0;0;0;64];
]
(* conntrack status bits (IPS_*, nf_conntrack_common.h; nft ct.c ct_status_tbl).
   A 4-byte big-endian register, matched as a bitmask like ct state (golden
   any/ct.t.payload: `ct status expected` => `bitwise & 0x00000001 ^ 0 ; cmp neq 0`). *)
let sym_ctstatus = [
  "expected",[0;0;0;1]; "seen-reply",[0;0;0;2]; "assured",[0;0;0;4];
  "confirmed",[0;0;0;8]; "snat",[0;0;0;0x10]; "dnat",[0;0;0;0x20];
  "dying",[0;0;2;0];
]
(* TCP flag bits (the single byte at transport header + 13).  proto.c:
   TCPHDR_FIN 0x01 .. TCPHDR_CWR 0x80.  A comma/`|` list ORs the bits. *)
let sym_tcpflag = [
  "fin",0x01; "syn",0x02; "rst",0x04; "psh",0x08;
  "ack",0x10; "urg",0x20; "ecn",0x40; "cwr",0x80;
]
let sym_icmp = [
  "echo-reply",[0]; "destination-unreachable",[3]; "source-quench",[4];
  "redirect",[5];
  "echo-request",[8]; "router-advertisement",[9]; "router-solicitation",[10];
  "time-exceeded",[11]; "parameter-problem",[12]; "timestamp-request",[13];
  "timestamp-reply",[14]; "info-request",[15]; "info-reply",[16];
  "address-mask-request",[17]; "address-mask-reply",[18];
]
let sym_icmpv6 = [
  "destination-unreachable",[1]; "packet-too-big",[2]; "time-exceeded",[3];
  "parameter-problem",[4]; "echo-request",[128]; "echo-reply",[129];
  "mld-listener-query",[130]; "mld-listener-report",[131];
  "mld-listener-done",[132]; "mld-listener-reduction",[132];
  "nd-router-solicit",[133]; "nd-router-advert",[134];
  "nd-neighbor-solicit",[135]; "nd-neighbor-advert",[136]; "nd-redirect",[137];
  "router-renumbering",[138]; "ind-neighbor-solicit",[141];
  "ind-neighbor-advert",[142]; "mld2-listener-report",[143];
]
(* IGMP message types (nft igmp.c igmp_type_tbl), a 1-byte field. *)
let sym_igmptype = [
  "membership-query",[0x11]; "membership-report-v1",[0x12];
  "membership-report-v2",[0x16]; "leave-group",[0x17];
  "membership-report-v3",[0x22];
]
(* ICMP code names (icmp.c icmp_code_tbl), a 1-byte field. *)
let sym_icmpcode = [
  "net-unreachable",[0]; "host-unreachable",[1]; "prot-unreachable",[2];
  "port-unreachable",[3]; "frag-needed",[4]; "net-prohibited",[9];
  "host-prohibited",[10]; "admin-prohibited",[13];
]
(* ICMPv6 code names (icmpv6.c icmpv6_code_tbl), a 1-byte field. *)
let sym_icmp6code = [
  "no-route",[0]; "admin-prohibited",[1]; "addr-unreachable",[3];
  "port-unreachable",[4]; "policy-fail",[5]; "reject-route",[6];
]
(* Mobility-header types (mh.c mh_type_tbl), a 1-byte field. *)
let sym_mhtype = [
  "binding-refresh-request",[0]; "home-test-init",[1]; "careof-test-init",[2];
  "home-test",[3]; "careof-test",[4]; "binding-update",[5];
  "binding-acknowledgement",[6]; "binding-error",[7]; "fast-binding-update",[8];
  "fast-binding-acknowledgement",[9]; "fast-binding-advertisement",[10];
  "experimental-mobility-header",[11]; "home-agent-switch-message",[12];
]
let sym_pkttype = [ "host",[0]; "unicast",[0]; "broadcast",[1]; "multicast",[2];
                    "other",[3]; "otherhost",[3]; ]
(* ARP operation codes (2-byte network-order field at arp header + 6).  arp.c
   arp_op_tbl: request 1, reply 2, rrequest 3, rreply 4, inrequest 8,
   inreply 9, nak 10. *)
let sym_arpop = [
  "request",[0;1]; "reply",[0;2]; "rrequest",[0;3]; "rreply",[0;4];
  "inrequest",[0;8]; "inreply",[0;9]; "nak",[0;10];
]
(* /etc/services subset (extend as corpora demand). *)
let sym_service = [
  "ftp-data",20; "ftp",21; "ssh",22; "telnet",23; "smtp",25; "domain",53;
  "bootps",67; "bootpc",68; "tftp",69; "http",80; "www",80; "pop3",110;
  "ntp",123; "imap",143; "snmp",161; "bgp",179; "https",443; "submission",587;
  "imaps",993; "pop3s",995; "mysql",3306; "rdp",3389; "nfs",2049;
  "syncthing",22000; "wireguard",51820; "openvpn",1194;
  "http-alt",8080; "https-alt",8443; "domain-s",853; "socks",1080;
  "printer",515; "ipp",631; "ldap",389; "ldaps",636; "smtps",465;
  "sip",5060; "kerberos",88; "rsync",873; "irc",6667; "xmpp-client",5222;
]

let lookup ctx tbl s =
  match L.assoc_opt s tbl with
  | Some b -> b
  | None -> raise (Unsupported (Printf.sprintf "symbolic constant %S (%s)" s ctx))

(* ---------- field kinds: how a value is encoded for a given selector ---------- *)

type kind =
  | KIfname | KIfindex | KIp4 | KIp6 | KPort | KL4proto | KNfproto | KEthertype
  | KCtstate | KCtstatus | KMark | KIcmp | KIcmpv6 | KPkttype | KFibType | KTcpflag | KNum of int
  | KIgmp | KIcmpcode | KIcmp6code | KMhtype  (* 1-byte symbolic-or-numeric enums *)
  | KCtdir   (* conntrack direction: original=0 / reply=1, a 1-byte register *)
  | KArpop   (* ARP operation: symbolic (request/reply/...) or numeric, 2-byte NBO *)
  (* host-endian (little-endian on x86) integer of [n] bytes; used for the value
     of `ct <key> set` / `meta <key> set` where the kernel register width is
     key-specific (e.g. ct zone is a u16 -> [KNumLe 2], ct label a 128-bit value
     -> [KNumLe 16]).  [KMark] is the special case [KNumLe 4]. *)
  | KNumLe of int

(* fib route-type symbols (the RTN_ route types), as 4-byte words.
   `fib_addr_type` is BYTEORDER_HOST_ENDIAN (src/fib.c:50) and the kernel stores
   the route type as a NATIVE u32 (`*dst = res.type`, nft_fib_ipv4.c) — i.e. on a
   little-endian host (x86/ARM64-LE, where the validate gate runs) the RTN_LOCAL
   register holds [2;0;0;0].  So we encode the type LITTLE-ENDIAN, exactly like
   `mark`/`ifindex` (the other BYTEORDER_HOST_ENDIAN fields). *)
let sym_fibtype = [
  "unspec",[0;0;0;0]; "unicast",[1;0;0;0]; "local",[2;0;0;0];
  "broadcast",[3;0;0;0]; "anycast",[4;0;0;0]; "multicast",[5;0;0;0];
  "blackhole",[6;0;0;0]; "unreachable",[7;0;0;0]; "prohibit",[8;0;0;0];
  "throw",[9;0;0;0]; "nat",[10;0;0;0]; "xresolve",[11;0;0;0];
]

(* ---- the TYPED value of an atom (Nftval.nftval), per field kind ----
   The byte encoding used EVERYWHERE below is the VERIFIED [Nftval.encode] of
   this typed value ([enc_atom] is literally [encode (typed_atom k v)]), so the
   typed->bytes step is the proved one (Nftval round-trips + Elab agreement),
   not an unverified byte table. *)
let nof = BinNat.N.of_nat
let be_int (b : Bytes.data) : int = L.fold_left (fun a x -> a * 256 + x) 0 b

let typed_atom (k : kind) (v : Nft_ast.value) : Nftval.nftval =
  match k, v with
  | KIfname, (Nft_ast.Vsym s | Nft_ast.Vstr s) -> Nftval.VIfname (ifname_bytes s)
  | KIfindex, Nft_ast.Vnum n -> Nftval.VHostInt (4, nof n)
  | KIfindex, (Nft_ast.Vsym s | Nft_ast.Vstr s) -> Nftval.VHostInt (4, nof (nametoindex s))
  | KIp4, Nft_ast.Vip4 b -> Nftval.VIpv4 b
  | KIp6, Nft_ast.Vip6 b -> Nftval.VIpv6 b
  | KIp6, Nft_ast.Vip4 b -> Nftval.VIpv6 b   (* a v4-mapped literal in a v6 context *)
  | KPort, Nft_ast.Vnum n -> Nftval.VPort (nof n)
  | KPort, Nft_ast.Vsym s ->
      Nftval.VPort (nof (L.assoc_opt s sym_service
        |> function Some p -> p | None -> raise (Unsupported ("service " ^ s))))
  | KL4proto, Nft_ast.Vnum n -> Nftval.VInteger (1, nof (n land 0xff))
  | KL4proto, Nft_ast.Vsym s -> Nftval.VInteger (1, nof (be_int (lookup "l4proto" sym_l4proto s)))
  | KNfproto, Nft_ast.Vnum n -> Nftval.VInteger (1, nof (n land 0xff))
  | KNfproto, Nft_ast.Vsym s -> Nftval.VInteger (1, nof (be_int (lookup "nfproto" sym_nfproto s)))
  | KEthertype, Nft_ast.Vnum n -> Nftval.VInteger (2, nof n)
  | KEthertype, Nft_ast.Vsym s -> Nftval.VInteger (2, nof (be_int (lookup "ethertype" sym_ethertype s)))
  | KCtstate, Nft_ast.Vsym s -> Nftval.VCtState (nof (be_int (lookup "ct state" sym_ctstate s)))
  | KCtstate, Nft_ast.Vnum n -> Nftval.VCtState (nof n)
  | KCtstatus, Nft_ast.Vsym s -> Nftval.VInteger (4, nof (be_int (lookup "ct status" sym_ctstatus s)))
  | KCtstatus, Nft_ast.Vnum n -> Nftval.VInteger (4, nof n)
  | KTcpflag, Nft_ast.Vsym s -> Nftval.VInteger (1, nof (lookup "tcp flag" sym_tcpflag s))
  | KTcpflag, Nft_ast.Vnum n -> Nftval.VInteger (1, nof (n land 0xff))
  | KMark, Nft_ast.Vnum n -> Nftval.VHostInt (4, nof n)
  | KIcmp, Nft_ast.Vnum n -> Nftval.VInteger (1, nof (n land 0xff))
  | KIcmp, Nft_ast.Vsym s -> Nftval.VInteger (1, nof (be_int (lookup "icmp type" sym_icmp s)))
  | KIcmpv6, Nft_ast.Vnum n -> Nftval.VInteger (1, nof (n land 0xff))
  | KIcmpv6, Nft_ast.Vsym s -> Nftval.VInteger (1, nof (be_int (lookup "icmpv6 type" sym_icmpv6 s)))
  | KPkttype, Nft_ast.Vsym s -> Nftval.VInteger (1, nof (be_int (lookup "pkttype" sym_pkttype s)))
  | KPkttype, Nft_ast.Vnum n -> Nftval.VInteger (1, nof (n land 0xff))
  | KIgmp, Nft_ast.Vsym s -> Nftval.VInteger (1, nof (be_int (lookup "igmp type" sym_igmptype s)))
  | KIgmp, Nft_ast.Vnum n -> Nftval.VInteger (1, nof (n land 0xff))
  | KIcmpcode, Nft_ast.Vsym s -> Nftval.VInteger (1, nof (be_int (lookup "icmp code" sym_icmpcode s)))
  | KIcmpcode, Nft_ast.Vnum n -> Nftval.VInteger (1, nof (n land 0xff))
  | KIcmp6code, Nft_ast.Vsym s -> Nftval.VInteger (1, nof (be_int (lookup "icmpv6 code" sym_icmp6code s)))
  | KIcmp6code, Nft_ast.Vnum n -> Nftval.VInteger (1, nof (n land 0xff))
  | KMhtype, Nft_ast.Vsym s -> Nftval.VInteger (1, nof (be_int (lookup "mh type" sym_mhtype s)))
  | KMhtype, Nft_ast.Vnum n -> Nftval.VInteger (1, nof (n land 0xff))
  | KFibType, Nft_ast.Vsym s -> Nftval.VFibType (nof (be_int (L.rev (lookup "fib type" sym_fibtype s))))
  | KFibType, Nft_ast.Vnum n -> Nftval.VFibType (nof n)
  | KNum 6, Nft_ast.Vmac b -> Nftval.VEther b
  | KNum w, Nft_ast.Vnum n -> Nftval.VInteger (w, nof n)
  | KNumLe w, Nft_ast.Vnum n -> Nftval.VHostInt (w, nof n)
  | KArpop, Nft_ast.Vnum n -> Nftval.VInteger (2, nof n)
  | KArpop, Nft_ast.Vsym s -> Nftval.VInteger (2, nof (be_int (lookup "arp operation" sym_arpop s)))
  | KCtdir, Nft_ast.Vnum n -> Nftval.VInteger (1, nof (n land 0xff))
  | KCtdir, Nft_ast.Vsym s ->
      (match s with "original" -> Nftval.VInteger (1, nof 0)
       | "reply" -> Nftval.VInteger (1, nof 1)
       | _ -> raise (Unsupported ("ct direction " ^ s)))
  | _, Nft_ast.Vvar n -> raise (Unsupported ("unresolved $" ^ n))
  | _ -> raise (Unsupported "value/selector type mismatch")

(* encode a single (non-range, non-prefix, non-concat) value for a field kind:
   the VERIFIED encoding of its typed value *)
let enc_atom (k : kind) (v : Nft_ast.value) : Bytes.data =
  Nftval.encode (typed_atom k v)

(* A kind stored HOST-ENDIAN (little-endian on x86) in the register, like the
   kernel holds `meta mark` / `ct mark` (BYTEORDER_HOST_ENDIAN).  For these,
   an ORDERED or RANGE comparison is only numerically meaningful after nft's
   mandatory `byteorder reg = hton(reg, N, N)` conversion, which we model with a
   [TByteorder true w w] transform.  Equality/neq need no conversion (memcmp is
   order-independent), so only the range/ordered path consults this. *)
let host_endian_kind = function KMark | KIfindex | KFibType -> true | _ -> false
(* the host-endian range/interval BOUNDS (network-order re-encoding after nft's
   mandatory `byteorder hton`) are now the verified Coq [Typed.encode_be]. *)

(* NFT_SET_CONCAT register-slot padding and all set/interval byte composition
   now live in the VERIFIED Coq lowering (Surface/Lower.v); this file composes
   no set byte (M3). *)

(* ---------- selector resolution: keypath -> (field, kind) ----------

   The implicit protocol-dependency SPECS of a selector (the guard nft inserts
   before the load) are no longer kept here: they come from the VERIFIED
   selector table (Surface/Selector.v, extracted [Selector.selector]) as
   numeric [Selector.depspec]s, and their guard register VALUES are encoded by
   the verified [Lower.dep_guard] (family-aware: inet nfproto vs L2
   `meta protocol` ethertype vs single-L3 no-op).  [key_field] keeps only the
   byte-composition data the remaining UNTYPED set/concat paths need (their
   migration is the M3 milestone). *)

(* ---------- TCP options (NFT_EXTHDR tcpopt) ----------
   nft reads a TCP option field with `exthdr load tcpopt <len>b @ <optnum> +
   <off>`, where <optnum> is the option KIND number and <off>/<len> position the
   field within that option (golden any/tcpopt.t.payload).  No l4proto dependency
   is emitted (the exthdr walker locates the TCP header itself). *)
let tcpopt_num (name : string) : int =
  match name with
  | "eol" -> 0 | "nop" -> 1 | "maxseg" | "mss" -> 2 | "window" -> 3
  | "sack-perm" -> 4 | "sack" | "sack0" | "sack1" | "sack2" | "sack3" -> 5
  | "timestamp" -> 8 | "md5sig" -> 19 | "mptcp" -> 30 | "fastopen" -> 34
  | _ -> (match int_of_string_opt name with
          | Some n -> n
          | None -> raise (Unsupported ("tcp option " ^ name)))

(* field position (off,len,kind) within a TCP option.  `left`/`right` on a
   multi-block SACK (`sack1`/`sack2`/`sack3`) step by one 8-byte block. *)
let tcpopt_field (name : string) (field : string) : int * int * kind =
  let sackn = match name with
    | "sack1" -> 1 | "sack2" -> 2 | "sack3" -> 3 | _ -> 0 in
  match field with
  | "kind"   -> (0, 1, KNum 1)
  | "length" -> (1, 1, KNum 1)
  | "size"   -> (2, 2, KNum 2)          (* maxseg size *)
  | "count"  -> (2, 1, KNum 1)          (* window count (shift) *)
  | "left"   -> (2 + 8*sackn, 4, KNum 4)
  | "right"  -> (6 + 8*sackn, 4, KNum 4)
  | "tsval"  -> (2, 4, KNum 4)
  | "tsecr"  -> (6, 4, KNum 4)
  | _ -> raise (Unsupported ("tcp option " ^ name ^ " " ^ field))

(* CIDR mask/net/broadcast arithmetic now lives in the VERIFIED Coq lowering
   (Surface/Lower.v [cidr_interval], unified with Elab.prefix_expand). *)

(* ---------- typed-emission side tables ----------
   The lowering constructs every typed-representable match THROUGH the verified
   elaboration ([Elab.elab_m] of an [Elab.tmatch]); these tables remember the
   typed source of each produced byte-level matchcond (keyed by value — equal
   byte terms print the same typed form) and which matchconds were SYNTHESIZED
   protocol-dependency guards, so the emitter (nft_emit.ml) can print the typed
   constructors and the [BDep] tag instead of raw byte lists. *)
let typed_tbl : (Syntax.matchcond * Elab.tmatch) list ref = ref []
let dep_mcs : Syntax.matchcond list ref = ref []
let reg_typed (tm : Elab.tmatch) : Syntax.matchcond =
  let mc = Elab.elab_m tm in
  (if not (L.mem_assoc mc !typed_tbl) then typed_tbl := (mc, tm) :: !typed_tbl);
  mc
let typed_of (mc : Syntax.matchcond) : Elab.tmatch option = L.assoc_opt mc !typed_tbl
let is_dep (mc : Syntax.matchcond) : bool = L.mem mc !dep_mcs

(* ---------- the VERIFIED scalar lowering (extracted Coq) ----------
   Every scalar match shape — typed atoms, ranges (incl. the mark/iif/fib-type
   `byteorder hton` ranges), ct-state/ct-status/tcp-flags bitmask forms and
   comma OR-lists, sub-byte bitfields, presence flags, CIDR prefixes, ifname
   wildcards, and explicit bitwise mask matches — is lowered by the extracted
   [Lower.lower_match]/[Lower.lower_bitmatch] (theories/Surface/Lower.v) into
   a typed term ([Typed.txmatch]) whose byte IR is the verified elaboration
   [Typed.elab_tx].  This file composes NO byte-level match condition for
   them; a construct the verified lowering does not cover is a loud [lerr]
   (surfaced as [Unsupported]), never a silent OCaml byte fallback. *)

let lres_get = function
  | Lower.LOk x -> x
  | Lower.LErr e -> raise (Unsupported (Lower.lerr_message e))

(* the implicit-dependency SPECS of a selector, from the VERIFIED table
   (numbers, not bytes; the guard register values are encoded by the verified
   [Lower.dep_guard] at materialisation time) *)
let sel_deps (kp : Nft_ast.keypath) : Selector.depspec list =
  match Selector.selector kp with
  | Some (_, deps) -> deps
  | None -> []

(* elaborate a Coq-lowered typed term and register its legacy typed view (the
   four Elab shapes) so nft_emit keeps printing `(elab_m (...))` Gen entries
   until the M6 Gen migration *)
let coq_mc (tx : Typed.txmatch) : Syntax.matchcond =
  let mc = Typed.elab_tx tx in
  (match Typed.tx_view tx with
   | Some tm ->
       if not (L.mem_assoc mc !typed_tbl) then typed_tbl := (mc, tm) :: !typed_tbl
   | None -> ());
  mc

(* ---------- mutable lowering state ---------- *)

type state = {
  defines : (string, Nft_ast.value) Hashtbl.t;
  (* the byte-relevant lowering state — the shared fresh-name counter and the
     named set / verdict-map / value-map contents — IS the extracted Coq
     [Lower.lstate].  The OCaml driver only THREADS it and reads back the
     declarations; it composes no set byte and mints no name of its own. *)
  mutable ls : Lower.lstate;
}
(* mint a fresh anonymous verdict-map name through the shared Coq counter *)
let fresh_map st = let (name, ls') = Lower.fresh_map st.ls in st.ls <- ls'; name

(* expand `$name` to its define (recursively), leave other values as-is *)
let rec resolve_var st (v : Nft_ast.value) : Nft_ast.value =
  match v with
  | Nft_ast.Vvar n ->
      (match Hashtbl.find_opt st.defines n with
       | Some v' -> resolve_var st v'
       | None -> raise (Unsupported ("undefined variable $" ^ n)))
  | Nft_ast.Vprefix (v', l) -> Nft_ast.Vprefix (resolve_var st v', l)
  | Nft_ast.Vrange (a, b) -> Nft_ast.Vrange (resolve_var st a, resolve_var st b)
  | Nft_ast.Vconcat vs -> Nft_ast.Vconcat (L.map (resolve_var st) vs)
  | Nft_ast.Vset vs -> Nft_ast.Vset (L.map (resolve_var st) vs)
  | _ -> v

let lower_verdict : Nft_ast.verdict -> Verdict.verdict = function
  | Nft_ast.SVaccept -> Verdict.Accept
  | Nft_ast.SVdrop -> Verdict.Drop
  | Nft_ast.SVcontinue -> Verdict.Continue
  | Nft_ast.SVreturn -> Verdict.Return
  | Nft_ast.SVjump n -> Verdict.Jump n
  | Nft_ast.SVgoto n -> Verdict.Goto n
  | Nft_ast.SVqueue (lo, hi, byp, fan) -> Verdict.Queue (lo, hi, byp, fan)
  | Nft_ast.SVreject _ -> Verdict.Reject (0, 0)

(* ---------- set / map / vmap element encoding: ALL VERIFIED (Coq) ----------
   Every single-field / declared-type / concatenated set element interval, the
   host-endian interval byteorder path, the CIDR net/broadcast expansion, the
   4-byte register-slot padding of concatenated set keys (and the FLAT unpadded
   vmap-key asymmetry), and the content-dedup `__setN` interning are the
   extracted Coq [Lower.*] functions (Surface/Lower.v).  This file no longer
   composes a single set byte; it injects the surface values, calls the verified
   lowering, threads [st.ls], and reads back the declarations. *)

(* ---------- injection into the Coq surface AST ----------
   The values handed to the VERIFIED lowering are the define-expanded surface
   values, injected by the pure structural translation [Nft_inject] (character/
   string/int injection only — no bytes are made here). *)

let inj_value st (v : Nft_ast.value) : Ast.svalue =
  Nft_inject.value (resolve_var st v)

let inj_rhs st (r : Nft_ast.rhs) : Ast.srhs =
  { Ast.sr_op = Nft_inject.relop r.Nft_ast.op;
    sr_neg = r.Nft_ast.neg;
    sr_payload = (match r.Nft_ast.payload with
      | Nft_ast.SEvalue v -> Ast.SSEvalue (inj_value st v)
      | Nft_ast.SElist vs -> Ast.SSElist (L.map (inj_value st) vs)
      | Nft_ast.SEset vs -> Ast.SSEset (L.map (inj_value st) vs)
      | Nft_ast.SEref n -> Ast.SSEref n) }

(* the VERIFIED scalar path: inject the (define-expanded) rhs and run the
   extracted [Lower.lower_match]; the byte IR is the verified elaboration of
   the returned typed term ([coq_mc]) *)
let coq_scalar st (kp : Nft_ast.keypath) (r : Nft_ast.rhs)
    : Selector.depspec list * Syntax.matchcond =
  let (deps, tx) =
    lres_get (Lower.lower_match { Ast.sm_keys = [kp]; sm_rhs = inj_rhs st r }) in
  (deps, coq_mc tx)

(* the VERIFIED (field, datatype) of a selector, from the extracted table *)
let sel_info (kp : Nft_ast.keypath) : Syntax.field * Datatype.dtype =
  match Selector.selector kp with
  | Some ((f, dt), _) -> (f, dt)
  | None -> raise (Unsupported ("selector: " ^ S.concat " " kp))

(* An inline `{...}` set (or a `$var` expanding to one) over a single field: the
   verified Coq [Lower.lower_anon_set] builds every element interval and interns
   the set, choosing the host-endian hton path (a byteorder-transformed lookup
   with big-endian bounds) exactly when the field is host-endian AND the set has
   an interval element, and refusing a tcp-flags brace set (brace-vs-OR
   ambiguity).  This file composes no set byte. *)
let anon_set_match st (kp : Nft_ast.keypath) (neg : bool)
    (elems : Nft_ast.value list) : Selector.depspec list * Syntax.matchcond =
  let (f, dt) = sel_info kp in
  let (ls', mc) =
    lres_get (Lower.lower_anon_set st.ls f dt neg (L.map (inj_value st) elems)) in
  st.ls <- ls';
  (sel_deps kp, mc)

(* lower a single match clause into body items.  EVERY scalar shape (typed
   atoms, ranges incl. the hton ranges, ct-state/status and tcp-flags bitmask
   forms and comma OR-lists, sub-byte bitfields, presence tests, CIDR
   prefixes, ifname wildcards) goes through the extracted VERIFIED
   [Lower.lower_match]; this file composes NO byte-level match condition for
   them.  Only the set-shaped right-hand sides (brace sets, @refs,
   concatenations — the M3 milestone) keep the untyped path.  The implicit
   protocol guards are materialised by the caller from the returned VERIFIED
   dep specs via [Lower.dep_guard]. *)
let lower_match st (m : Nft_ast.smatch)
    : Selector.depspec list * Syntax.matchcond =
  let neg = m.Nft_ast.m_rhs.Nft_ast.neg in
  match m.Nft_ast.m_keys with
  | [kp] ->
      (match m.Nft_ast.m_rhs.Nft_ast.payload with
       | Nft_ast.SEref name ->
           (* `@name` reference: a real lookup against a named set (the
              matchcond is built by the verified [Lower.lower_set_ref]) *)
           let (f, _) = sel_info kp in
           (sel_deps kp, Lower.lower_set_ref [f] neg name)
       | Nft_ast.SEset elems -> anon_set_match st kp neg elems
       | Nft_ast.SEvalue v
         when (match resolve_var st v with
               | Nft_ast.Vset _ -> true | _ -> false) ->
           (* a `$var` that expands to a set *)
           (match resolve_var st v with
            | Nft_ast.Vset elems -> anon_set_match st kp neg elems
            | _ -> assert false)
       | Nft_ast.SEvalue _ | Nft_ast.SElist _ ->
           (* EVERY scalar shape: the verified Coq lowering *)
           coq_scalar st kp m.Nft_ast.m_rhs)
  | kps ->
      (* concatenation: ip daddr . oifname [!=] @set / {set}; the per-field
         intervals, 4-byte register-slot padding, interning, and the matchcond
         are the verified Coq [Lower.lower_concat_set]/[Lower.lower_set_ref] *)
      let infos = L.map sel_info kps in
      let fields = L.map fst infos in
      let dts    = L.map snd infos in
      let dep = L.concat (L.map sel_deps kps) in
      (match m.Nft_ast.m_rhs.Nft_ast.payload with
       | Nft_ast.SEref nm -> (dep, Lower.lower_set_ref fields neg nm)
       | Nft_ast.SEset elems ->
           let (ls', mc) =
             lres_get (Lower.lower_concat_set st.ls fields dts neg
                         (L.map (inj_value st) elems)) in
           st.ls <- ls'; (dep, mc)
       | Nft_ast.SEvalue (Nft_ast.Vconcat _ as v) ->
           let (ls', mc) =
             lres_get (Lower.lower_concat_set st.ls fields dts neg
                         [inj_value st v]) in
           st.ls <- ls'; (dep, mc)
       | Nft_ast.SElist _ -> raise (Unsupported
           "bare comma list is not valid for a concatenated selector; use `{ ... }`")
       | Nft_ast.SEvalue _ -> raise (Unsupported "concatenated match needs a set/ref rhs"))

(* meta/ct key from a name (reuses the codec name tables) *)
let meta_key n = match Codec.meta_of_name n with
  | Some k -> k | None -> raise (Unsupported ("meta key: " ^ n))
let ct_key n = match Codec.ct_of_name n with
  | Some k -> k | None -> raise (Unsupported ("ct key: " ^ n))

(* The register WIDTH (and byteorder) the kernel uses when STORING a value into a
   ct/meta key — decoupled from `mark`'s 4-byte shape.  Mirrors the kernel set-eval
   paths (net/netfilter/nft_ct.c nft_ct_set_eval / nft_ct_set_zone_eval and
   nft_meta.c nft_meta_set_eval):
     ct mark / secmark / eventmask : u32  (nft_ct.c:8 `u32 value = regs->data[..]`)
     ct zone                       : u16  (nft_ct.c nft_reg_load16 -> zone.id)
     ct label                      : 128-bit (16 bytes, nf_connlabels_replace)
     meta mark / priority / secmark: u32  (skb->mark/priority/secmark = value)
     meta pkttype / nftrace        : u8   (nft_reg_load8)
   All are HOST-ENDIAN registers, so we encode little-endian (host order on x86),
   exactly as `mark` (KMark = KNumLe 4) already does. *)
let ct_set_kind (k : Packet.ct_key) : kind =
  match k with
  | Packet.CKzone   -> KNumLe 2
  | Packet.CKlabel  -> KNumLe 16
  | Packet.CKmark | Packet.CKevent -> KNumLe 4
  | _ -> raise (Unsupported "ct key is not settable")

let meta_set_kind (k : Packet.meta_key) : kind =
  match k with
  | Packet.MKmark | Packet.MKpriority -> KNumLe 4
  | Packet.MKpkttype -> KNumLe 1
  | _ -> raise (Unsupported "meta key is not settable")

(* `log level <name>` renders in the golden with the NUMERIC syslog level
   (`[ log level 0 ]` for emerg .. 7 debug, 8 audit), not the symbolic name.  Map
   the bare `level <name>` opts to `level <n>`; other log-option forms (prefix /
   group / snaplen / queue-threshold / flags, which the golden also canonicalises
   with defaults and flag expansion) are left verbatim for a later batch. *)
let syslog_level = function
  | "emerg" -> Some 0 | "alert" -> Some 1 | "crit" -> Some 2 | "err" -> Some 3
  | "warn" | "warning" -> Some 4 | "notice" -> Some 5 | "info" -> Some 6
  | "debug" -> Some 7 | "audit" -> Some 8 | _ -> None
let canon_log_opts (opts : string) : string =
  match Stdlib.String.split_on_char ' ' opts with
  | ["level"; name] ->
      (match syslog_level name with Some n -> "level " ^ string_of_int n | None -> opts)
  | _ -> opts

let lower_stmt st (s : Nft_ast.sstmt) : Syntax.stmt option =
  match s with
  | Nft_ast.StComment _ -> None              (* metadata; no verdict/bytecode effect *)
  | Nft_ast.StCounter -> Some (Syntax.SCounter (0, 0))
  | Nft_ast.StLog opts -> Some (Syntax.SLog (canon_log_opts opts))
  | Nft_ast.StLimit _ ->
      (* `limit` is a matchcond (MLimit), not a statement; lower_rule intercepts
         StLimit before reaching here, so this is unreachable. *)
      raise (Unsupported "limit handled as a match, not a statement")
  | Nft_ast.StMasquerade _ | Nft_ast.StSnat _ | Nft_ast.StDnat _
  | Nft_ast.StRedirect _ | Nft_ast.StTproxy _ ->
      (* terminal NAT/tproxy: the single-packet model treats it as terminal Accept *)
      None
  | Nft_ast.StMetaSet (k, v) ->
      let key = meta_key k in
      Some (Syntax.SMetaSet (key, Syntax.VImm (enc_atom (meta_set_kind key) (resolve_var st v))))
  | Nft_ast.StCtSet (k, v) ->
      let key = ct_key k in
      Some (Syntax.SCtSet (key, Syntax.VImm (enc_atom (ct_set_kind key) (resolve_var st v))))
  | Nft_ast.StNotrack -> Some Syntax.SNotrack

(* does a statement force a terminal Accept (NAT)? *)
let stmt_is_terminal_accept = function
  | Nft_ast.StMasquerade _ | Nft_ast.StSnat _ | Nft_ast.StDnat _
  | Nft_ast.StRedirect _ | Nft_ast.StTproxy _ -> true | _ -> false

let limit_spec rate unit_ over burst bytes : Packet.limit_spec =
  let u = match unit_ with
    | "second"->0 | "minute"->1 | "hour"->2 | "day"->3 | "week"->4
    | _ -> raise (Unsupported ("limit unit " ^ unit_)) in
  (* ExtrOcamlNatInt seam guard (re-check; the parser's [limit_value] bounds
     every grammar path).  ls_rate/ls_burst enter extracted products with
     lim_window <= 604800 (Semantics.lim_cost/lim_max); above 2^40 those
     products can pass 2^62 and WRAP in the extracted 63-bit int — semantics
     the proofs know nothing about.  See theories/Compiler/Extract.v. *)
  let max_limit_value = 1 lsl 40 in
  if rate < 0 || rate > max_limit_value || burst < 0 || burst > max_limit_value then
    raise (Unsupported
      (Printf.sprintf
         "limit rate/burst %d/%d exceeds the extracted-int-safe bound 2^40 \
          (see theories/Compiler/Extract.v)" rate burst));
  (* bit 0 of ls_flags = NFT_LIMIT_F_INV ("over"); the data-plane semantics XOR
     the under/not-exceeded test with this bit (Semantics.v eval_matchcond_body).
     [ls_burst]/[ls_bytes] now carry the parsed burst and packet-vs-byte rate
     (nft: `kbytes`->1024, packet default burst 5, byte default burst 0). *)
  { Packet.ls_rate = rate; ls_unit = u; ls_burst = burst; ls_bytes = bytes;
    ls_flags = (if over then 1 else 0) }

(* The L3 NAT address family for a NAT statement in a chain of table [family].  The
   kernel dispatches masquerade/snat/dnat BY FAMILY (nft_masq.c:113-121:
   NFPROTO_IPV4 -> nf_nat_masquerade_ipv4 vs NFPROTO_IPV6 -> nf_nat_masquerade_ipv6),
   so the address geometry (4-byte IPv4 slot vs 16-byte IPv6 slot) and the source
   value (IPv4 e_ifaddr vs IPv6 e_ifaddr6) must follow the table family.  An ip6
   table -> "ip6"; ip table -> "ip".  An `inet` table has ONE NAT rule serving BOTH
   IPv4 and IPv6 packets, and the kernel dispatches on the PACKET's L3 family at
   RUNTIME (nft_masq_inet_eval: `switch (nft_pf(pkt))` -> NFPROTO_IPV4 vs
   NFPROTO_IPV6); NO static family is correct, so an inet-table NAT carries the
   runtime-dispatched sentinel "inet" (Semantics.nat_addrfamily_pkt resolves it
   per-packet to the packet's L3 family). *)
let nat_l3_family = function "ip6" -> Bytecode.NFip6 | "inet" -> Bytecode.NFinet | _ -> Bytecode.NFip4

(* a `masquerade` NAT spec: source-NAT to the exit interface's address, in the
   address family of the enclosing table ([nat_l3_family]) so an `ip6 masquerade`
   rewrites the 16-byte IPv6 source (nf_nat_masquerade_ipv6), not the IPv4 slot. *)
(* 2-byte big-endian port value (the compiler loads it into the proto register) *)
let port_bytes p = [(p lsr 8) land 0xff; p land 0xff]

(* NAT flag words -> the kernel NF_NAT_RANGE_* bitmask (nf_nat.h):
   PROTO_SPECIFIED 0x2 (a port range is given), PROTO_RANDOM 0x4,
   PERSISTENT 0x8, PROTO_RANDOM_FULLY 0x10.  Verified against golden
   ip/{masquerade,redirect}.t.payload flag values (0x4/0x8/0xc/0x1c). *)
let nat_flag_bit = function
  | "random" -> 0x04 | "persistent" -> 0x08 | "fully-random" -> 0x10
  | s -> raise (Unsupported ("nat flag " ^ s))
let nat_flags_of fs = L.fold_left (fun a f -> a lor nat_flag_bit f) 0 fs

let masq_spec ~family ~flags : Syntax.nat_spec =
  { Syntax.nat_addr_imm = None; nat_field = None; nat_map = None; nat_src = None;
    nat_extra = Syntax.NXnone;
    nat_kind = Bytecode.NKmasq; nat_family = nat_l3_family family; nat_flags = flags }

(* an `snat to <ip>[:<port>]` / `dnat to <ip>[:<port>]` NAT spec: the target
   address goes into register 1 (= NFTNL_EXPR_NAT_REG_ADDR_MIN), which the kernel
   nft_nat applies as NF_NAT_MANIP_SRC / NF_NAT_MANIP_DST.  An optional L4 [port]
   (`addr:port`) populates nat_pmin/nat_pmax (= NFTNL_EXPR_NAT_REG_PROTO_MIN/MAX),
   which the kernel loads into range.min_proto/max_proto (nft_nat.c:57-60) and
   nf_nat_setup_info writes into the TCP/UDP header (nf_nat_proto.c).  Only an
   explicit IPv4 literal target is modelled here; a RESOLVABLE non-literal address
   (a defined symbol/map/concat we don't lower) stays a bare terminal Accept
   (nat = None).  An UNDEFINED `$var` is NOT swallowed: [resolve_var] raises
   [Unsupported] and the parse fails loudly, exactly as `nft -f` rejects an
   unqualified name — we never silently drop a NAT to a dangling define. *)
let addr_nat_spec st kind ?(port=None) ~flags (v : Nft_ast.value) : Syntax.nat_spec option =
  match resolve_var st v with
  | Nft_ast.Vip4 b ->
      (* a specified port range sets NF_NAT_RANGE_PROTO_SPECIFIED (0x2): golden
         `dnat to A:port` renders `... proto_min reg N flags 0x2`. *)
      let (ne, f) = (match port with
                | Some p -> (Syntax.NXimm (None, Some ((port_bytes p)), None), flags lor 0x2)
                | None -> (Syntax.NXnone, flags)) in
      Some { Syntax.nat_addr_imm = Some b; nat_field = None; nat_map = None;
             nat_src = None; nat_extra = ne;
             nat_kind = kind; nat_family = Bytecode.NFip4; nat_flags = f }
  | _ -> None   (* unresolvable / non-literal target: stay a bare terminal Accept *)

(* a PORT-ONLY `snat to :<port>` / `dnat to :<port>` NAT spec: NO address operand
   (nat_imms = [], nat_field/map/src = None), only the L4 proto range.  The kernel
   sets only NFTNL_EXPR_NAT_REG_PROTO_MIN/MAX (not the addr register), so
   nft_nat_eval rewrites ONLY the L4 port and leaves the L3 address unchanged
   (nft_nat.c:114/120 — two independent register guards).  In the model this is a
   nat_spec with nat_has_addr = false, so apply_nat preserves the address and
   apply_nat_port rewrites the port. *)
let portonly_nat_spec ~family kind ~flags (port : int) : Syntax.nat_spec =
  { Syntax.nat_addr_imm = None; nat_field = None; nat_map = None; nat_src = None;
    nat_extra = Syntax.NXimm (None, Some ((port_bytes port)), None);
    nat_kind = kind; nat_family = nat_l3_family family; nat_flags = flags lor 0x2 }

(* `tproxy [ip|ip6] to <addr>[:<port>]` — a terminal transparent-proxy spec.
   tp_family: an explicit ip/ip6 qualifier wins; otherwise the enclosing table's
   L3 family (ip/ip6), or "" for a multi-L3 (inet/bridge/netdev) table — golden
   {ip,inet}/tproxy.t.payload (`tproxy ip addr reg 1` in ip, `tproxy port reg 1`
   in inet).  Only an IPv4 literal target is modelled here; a v6 `[addr]` literal
   needs the bracket lexer (out of scope) and stays a clean Unsupported. *)
let tproxy_spec st ~family qual (addr : Nft_ast.value option) (port : int option)
    : Syntax.tproxy_spec =
  let tp_fam =
    if qual <> "" then qual
    else (match family with "ip" -> "ip" | "ip6" -> "ip6" | _ -> "") in
  let a = match addr with
    | None -> None
    | Some v -> (match resolve_var st v with
        | Nft_ast.Vip4 b -> Some b
        | _ -> raise (Unsupported "tproxy target is not an IPv4 literal")) in
  { Syntax.tp_addr = a;
    tp_port = (match port with Some p -> Some (port_bytes p) | None -> None);
    tp_portmap = None; tp_family = tp_fam }

(* `redirect [to :port] [flags]` — kind "redir" (no address, no family), like
   masquerade; a port range adds PROTO_SPECIFIED (0x2).  Golden ip/redirect.t:
   bare `redirect` -> `[ redir ]`, `redirect to :22` -> `[ redir proto_min reg 1
   flags 0x2 ]`, `redirect random` -> `[ redir flags 0x4 ]`. *)
let redir_spec ~flags (port : int option) : Syntax.nat_spec =
  let (ne, f) = (match port with
    | Some p -> (Syntax.NXimm (None, Some (port_bytes p), None), flags lor 0x2)
    | None -> (Syntax.NXnone, flags)) in
  { Syntax.nat_addr_imm = None; nat_field = None; nat_map = None; nat_src = None;
    nat_extra = ne; nat_kind = Bytecode.NKredir; nat_family = Bytecode.NFip4; nat_flags = f }

(* `reject [with <proto> <name>]` -> the kernel nft_reject (type, code) pair.
   type: NFT_REJECT_ICMP_UNREACH 0 (icmp/icmpv6 code), TCP_RST 1, ICMPX_UNREACH 2.
   A BARE `reject` is family-defaulted (nft evaluate.c stmt_reject_default):
     ip   -> icmp  port-unreach   (0,3)
     ip6  -> icmpv6 port-unreach  (0,4)
     inet/bridge/netdev (L2/dual) -> icmpx port-unreach (2,1).
   Codes verified against {ip,ip6,inet,bridge,netdev}/reject.t.payload. *)
let icmp_reject_code = function
  | "net-unreachable" -> 0 | "host-unreachable" -> 1 | "prot-unreachable" -> 2
  | "port-unreachable" -> 3 | "net-prohibited" -> 9 | "host-prohibited" -> 10
  | "admin-prohibited" -> 13
  | s -> raise (Unsupported ("reject icmp code " ^ s))
let icmpv6_reject_code = function
  | "no-route" -> 0 | "admin-prohibited" -> 1 | "addr-unreachable" -> 3
  | "port-unreachable" -> 4 | "policy-fail" -> 5 | "reject-route" -> 6
  | s -> raise (Unsupported ("reject icmpv6 code " ^ s))
let icmpx_reject_code = function
  | "no-route" -> 0 | "port-unreachable" -> 1 | "host-unreachable" -> 2
  | "admin-prohibited" -> 3
  | s -> raise (Unsupported ("reject icmpx code " ^ s))
let reject_type_code family (opts : string) : int * int =
  (* drop a stray `type` keyword (`reject with icmp type net-unreachable`) *)
  let ws = L.filter (fun w -> w <> "" && w <> "type")
             (Stdlib.String.split_on_char ' ' opts) in
  match ws with
  | [] -> (match family with
           | "ip" -> (0, 3) | "ip6" -> (0, 4) | _ -> (2, 1))
  | ["tcp"; "reset"] -> (1, 0)
  | "icmp" :: name :: _   -> (0, icmp_reject_code name)
  | "icmpv6" :: name :: _ -> (0, icmpv6_reject_code name)
  | "icmpx" :: name :: _  -> (2, icmpx_reject_code name)
  | _ -> raise (Unsupported ("reject with " ^ opts))

let lower_rule st ~family (clauses : Nft_ast.clause list) : Syntax.rule =
  let body = ref [] in
  let deps = ref [] in       (* (field, value) deps already emitted, for dedup *)
  let verdict = ref Verdict.Continue in
  let vmap = ref None in
  let nat = ref None in   (* set for `masquerade` (a source-NAT terminal) *)
  let tproxy = ref None in   (* set for `tproxy` (a transparent-proxy terminal) *)
  let push bi = body := bi :: !body in
  (* Materialise one VERIFIED guard action ([Lower.dep_guard]: which guard a
     dep spec becomes — and its register VALUE — is family-aware Coq).  The
     per-rule DEDUP state stays here: nft keys the network-base dependency on
     the LAYER, not the value ([layer_keyed]: once a `meta nfproto` (inet) /
     `meta protocol` (L2) match exists in the rule, a later selector's
     implicit network guard is suppressed EVEN IF its value differs — golden
     inet/icmp.t.payload `meta nfproto ipv4 icmpv6 type ...` emits nfproto==2
     ONCE); value-keyed guards dedup by (field, value). *)
  let push_guard = function
    | Lower.DAnone -> ()
    | Lower.DAguard (layer_keyed, f, key, tm) ->
        let dup =
          if layer_keyed then L.exists (fun (fk, _) -> fk = f) !deps
          else L.mem (f, key) !deps in
        if not dup then begin
          (* a dependency guard is a small integer compare; construct it
             through the verified elaboration and tag it as SYNTHESIZED *)
          let mc = reg_typed tm in
          dep_mcs := mc :: !dep_mcs;
          push (Syntax.BMatch mc); deps := (f, key) :: !deps
        end
  in
  (* materialise dep specs in order (nfproto guard pushed before l4proto
     guard); an unverifiable guard is a LOUD [lerr] (vlan in netdev) *)
  let ensure_dep ds =
    L.iter (fun d -> push_guard (lres_get (Lower.dep_guard family d))) ds in
  L.iter (fun (cl : Nft_ast.clause) ->
    match cl with
    | Nft_ast.CVerdict (Nft_ast.SVreject opts) ->
        (* `reject with icmp <x>` only applies to IPv4 packets and `icmpv6 <x>`
           only to IPv6, so in a dual-stack family nft prepends the matching
           network guard (`meta nfproto`/`meta protocol == {ipv4|ipv6}`) before the
           reject (golden {inet,bridge,netdev}/reject.t.payload).  ensure_dep makes
           it a no-op in the single-L3 ip/ip6 families.  icmpx/tcp/bare take no
           network guard. *)
        (match L.filter (fun w -> w <> "" && w <> "type")
                 (Stdlib.String.split_on_char ' ' opts) with
         | "icmp" :: _   -> ensure_dep [Selector.DepNfproto 2]
         | "icmpv6" :: _ -> ensure_dep [Selector.DepNfproto 10]
         | _ -> ());
        let (rt, rc) = reject_type_code family opts in
        verdict := Verdict.Reject (rt, rc)
    | Nft_ast.CVerdict v -> verdict := lower_verdict v
    | Nft_ast.CMatch m ->
        let (dep, mc) = lower_match st m in
        ensure_dep dep; push (Syntax.BMatch mc);
        (* An EXPLICIT match on a field nft also uses as an implicit dependency
           (l4proto / nfproto / protocol / iiftype / ethertype) discharges that
           dependency: a later selector's implicit guard for the SAME (field,value)
           must NOT re-emit it.  nft dedups exactly this way, so `meta l4proto 6
           tcp dport 22` and `ether type vlan vlan id 2` emit the guard ONCE.
           WHICH matches discharge WHAT is the VERIFIED [Lower.discharge]
           (including `ip protocol N` fixing the l4proto guard); registering
           the returned (field, value) pairs in the dedup set stays here. *)
        L.iter
          (fun (fk, pv) ->
             if not (L.mem (fk, pv) !deps) then deps := (fk, pv) :: !deps)
          (Lower.discharge mc)
    | Nft_ast.CBitmatch (kp, op, mask, r) ->
        (* `<field> and|or|xor <m> <relop> <v>`: the VERIFIED
           [Lower.lower_bitmatch] — admitted only over an integer-basetype
           selector (`iifname & 0xff` is ill-typed), realised as nft's
           bitwise-then-compare (see Typed.elab_tx's TXBitwise clause for the
           three mask/xor realisations and their golden citations) *)
        let (dep, tx) =
          lres_get
            (Lower.lower_bitmatch kp op (inj_value st mask) (inj_rhs st r)) in
        ensure_dep dep;
        push (Syntax.BMatch (coq_mc tx))
    | Nft_ast.CVmap (kps, entries) ->
        if !vmap <> None then raise (Unsupported "more than one verdict map in a rule");
        let infos = L.map sel_info kps in
        let fields = L.map fst infos in
        let dts    = L.map snd infos in
        ensure_dep (L.concat (L.map sel_deps kps));
        let name = fresh_map st in
        (* the per-key intervals (single-field closed interval, or the FLAT
           unpadded per-field concatenation for a concatenated key — the model's
           assoc_verdict key) are the verified Coq [Lower.vmap_entries_*] *)
        let coq_entries =
          L.map (fun (v, sv) -> (inj_value st v, lower_verdict sv)) entries in
        let ents = lres_get (match dts with
          | [dt] -> Lower.vmap_entries_single dt coq_entries
          | _    -> Lower.vmap_entries_concat dts coq_entries) in
        st.ls <- Lower.add_vmap st.ls name ents;
        (match fields with
         | [f] -> vmap := Some { Syntax.vm_fields = []; vm_keyf = Some (f, []); vm_name = name }
         | _   -> vmap := Some { Syntax.vm_fields = fields; vm_keyf = None; vm_name = name })
    | Nft_ast.CVmapRef (kps, name) ->
        (* `<key>[.<key>...] vmap @name`: entries come from the named map in the env *)
        if !vmap <> None then raise (Unsupported "more than one verdict map in a rule");
        let fields = L.map (fun kp -> fst (sel_info kp)) kps in
        ensure_dep (L.concat (L.map sel_deps kps));
        (match fields with
         | [f] -> vmap := Some { Syntax.vm_fields = []; vm_keyf = Some (f, []); vm_name = name }
         | _   -> vmap := Some { Syntax.vm_fields = fields; vm_keyf = None; vm_name = name })
    | Nft_ast.CStmt (Nft_ast.StLimit (r, u, over, burst, bytes)) ->
        push (Syntax.BMatch (Syntax.MLimit (limit_spec r u over burst bytes)))
    | Nft_ast.CStmt s ->
        if stmt_is_terminal_accept s then verdict := Verdict.Accept;
        (match s with
         | Nft_ast.StMasquerade fs -> nat := Some (masq_spec ~family ~flags:(nat_flags_of fs))
         | Nft_ast.StSnat (Some v, port, fs) -> nat := addr_nat_spec st Bytecode.NKsnat ~port ~flags:(nat_flags_of fs) v
         | Nft_ast.StDnat (Some v, port, fs) -> nat := addr_nat_spec st Bytecode.NKdnat ~port ~flags:(nat_flags_of fs) v
         | Nft_ast.StSnat (None, Some port, fs) -> nat := Some (portonly_nat_spec ~family Bytecode.NKsnat ~flags:(nat_flags_of fs) port)
         | Nft_ast.StDnat (None, Some port, fs) -> nat := Some (portonly_nat_spec ~family Bytecode.NKdnat ~flags:(nat_flags_of fs) port)
         | Nft_ast.StRedirect (port, fs) -> nat := Some (redir_spec ~flags:(nat_flags_of fs) port)
         | Nft_ast.StTproxy (qual, addr, port) ->
             tproxy := Some (tproxy_spec st ~family qual addr port)
         | _ -> ());
        (match lower_stmt st s with Some st' -> push (Syntax.BStmt st') | None -> ()))
    clauses;
  let outc = (match !vmap, !nat, !tproxy with
    | Some _, _, Some _ | _, Some _, Some _ ->
        raise (Unsupported "rule with more than one outcome (vmap/nat/tproxy)")
    | Some vm, Some ns, None ->
        (* `… vmap {…} redirect`: the map miss reaches the trailing NAT *)
        Syntax.OVmapNat (vm, ns)
    | Some vm, None, None ->
        (* a vmap IS the rule's outcome: a static verdict beside it would be
           unreachable-on-hit / outcome-on-miss, a shape nft never emits *)
        if !verdict <> Verdict.Continue then
          raise (Unsupported "verdict map combined with a static verdict");
        Syntax.OVmap vm
    | None, Some ns, None -> Syntax.ONat ns
    | None, None, Some tp -> Syntax.OTproxy tp
    | None, None, None ->
        (match !verdict with
         | Verdict.Continue -> Syntax.ONone
         | v -> Syntax.OVerdict v)) in
  { Syntax.r_body = L.rev !body; r_outcome = outc; r_after = [] }

(* ---------- declarations ---------- *)

let lower_setdecl st (sd : Nft_ast.setdecl) : unit =
  let types = sd.Nft_ast.sd_type in
  if sd.Nft_ast.sd_is_map then begin
    (* a verdict map if its elements carry verdict data; an empty declaration is
       registered as an empty value map (its contents arrive at runtime) *)
    let is_vmap = L.exists (fun (_, d) -> match d with
      | Some _ -> true | None -> false) sd.Nft_ast.sd_elements in
    if is_vmap then
      (* the FULL [lo,hi] interval key (verified Coq [Lower.decl_vmap_ents]) so
         range/prefix vmap keys do an interval lookup, not exact-only *)
      let coq_entries = L.map (fun (key, d) ->
        (inj_value st key,
         match d with Some v -> lower_verdict v | None -> Verdict.Continue))
        sd.Nft_ast.sd_elements in
      let ents = lres_get (Lower.decl_vmap_ents types coq_entries) in
      st.ls <- Lower.add_vmap st.ls sd.Nft_ast.sd_name ents
    else if sd.Nft_ast.sd_elements = [] then
      st.ls <- Lower.add_map st.ls sd.Nft_ast.sd_name []
    else raise (Unsupported "value maps (non-verdict map data) not yet lowered")
  end else begin
    let elems = lres_get (Lower.decl_set_elems types
                            (L.map (fun (v, _) -> inj_value st v) sd.Nft_ast.sd_elements)) in
    st.ls <- Lower.add_set st.ls sd.Nft_ast.sd_name elems
  end

(* the (hook, priority) registration of a base chain, if it has a `type _ hook _
   priority _` declaration; [None] for a regular (jumpable) chain. *)
let lower_chain st ~family (sc : Nft_ast.schain)
  : (string * Syntax.chain) * (string * string * int) option =
  let hookinfo = L.fold_left (fun acc -> function
    | Nft_ast.ITypeHook { ct_type; hook; priority } -> Some (ct_type, hook, priority)
    | _ -> acc) None sc.Nft_ast.sc_items in
  let is_base = hookinfo <> None in
  let policy = ref None and rules = ref [] in
  L.iter (function
    | Nft_ast.ITypeHook _ -> ()
    | Nft_ast.IPolicy v -> policy := Some (lower_verdict v)
    | Nft_ast.IRule cls -> rules := lower_rule st ~family cls :: !rules)
    sc.Nft_ast.sc_items;
  let c_policy = match !policy with
    | Some v -> v | None -> if is_base then Verdict.Accept else Verdict.Continue in
  ((sc.Nft_ast.sc_name, { Syntax.c_policy; c_rules = L.rev !rules }), hookinfo)

(* ---------- top level ---------- *)

type parsed = {
  p_tables : (string * string * (string * Syntax.chain) list) list;
  (* per table: the base-chain hook registrations (chain-name, chain-type, hook,
     priority), in source order.  Empty for tables with no base chains. *)
  p_hooks  : (string * string * (string * string * string * int) list) list;
  p_env    : Packet.env;
  (* the raw declared/anonymous set & map contents, so a Coq emitter can
     serialise them as a [set_decls] record (the env is then [env_with_sets]) *)
  p_sets   : (string * (Bytes.data * Bytes.data) list) list;
  p_vmaps  : (string * ((Bytes.data * Bytes.data) * Verdict.verdict) list) list;
  p_maps   : (string * (Bytes.data * Bytes.data) list) list;
}

let build_env st : Packet.env =
  let sets = st.ls.Lower.ls_sets and vmaps = st.ls.Lower.ls_vmaps
  and maps = st.ls.Lower.ls_maps in
  { Packet.e_set  = (fun n -> match L.assoc_opt n sets  with Some e -> e | None -> []);
    e_vmap        = (fun n -> match L.assoc_opt n vmaps with Some e -> e | None -> []);
    e_map         = (fun n -> match L.assoc_opt n maps  with Some e -> e | None -> []);
    e_routes = []; e_rt = (fun _ -> []); e_ifaddrs = (fun _ -> []); e_ifaddrs6 = (fun _ -> []);
    e_limit = (fun _ -> 1); e_quota = (fun _ -> 1); e_connlimit = (fun _ -> []);
    e_ct = (fun _ _ -> []); e_nat = (fun _ -> None); e_numgen = (fun _ -> 0) }

let lower (f : Nft_ast.sfile) : parsed =
  typed_tbl := []; dep_mcs := [];
  let st = { defines = Hashtbl.create 16; ls = Lower.ls0 } in
  (* pass 1: collect defines *)
  L.iter (function Nft_ast.TopDefine (n, v) -> Hashtbl.replace st.defines n v | _ -> ()) f;
  (* pass 2: declarations (sets/maps) must exist before chains reference them *)
  L.iter (function
    | Nft_ast.TopTable t ->
        L.iter (function Nft_ast.TSet sd -> lower_setdecl st sd | _ -> ()) t.Nft_ast.st_items
    | _ -> ()) f;
  (* pass 3: chains *)
  let tables_with_hooks = L.filter_map (function
    | Nft_ast.TopTable t ->
        let family = t.Nft_ast.st_family in
        let lowered = L.filter_map (function
          | Nft_ast.TChain sc -> Some (lower_chain st ~family sc)
          | Nft_ast.TSet _ | Nft_ast.TObj _ -> None) t.Nft_ast.st_items in
        let chains = L.map fst lowered in
        let hooks = L.filter_map (fun ((cname, _), hi) -> match hi with
          | Some (ctype, hook, prio) -> Some (cname, ctype, hook, prio)
          | None -> None) lowered in
        Some ((t.Nft_ast.st_family, t.Nft_ast.st_name, chains),
              (t.Nft_ast.st_family, t.Nft_ast.st_name, hooks))
    | _ -> None) f
  in
  { p_tables = L.map fst tables_with_hooks;
    p_hooks  = L.map snd tables_with_hooks;
    p_env = build_env st;
    p_sets = L.rev st.ls.Lower.ls_sets; p_vmaps = L.rev st.ls.Lower.ls_vmaps;
    p_maps = L.rev st.ls.Lower.ls_maps }

(* ---------- lookups ---------- *)

let find_table p name = L.find_opt (fun (_, n, _) -> n = name) p.p_tables
let chains_of p ~table = match find_table p table with
  | Some (_, _, chains) -> chains
  | None -> raise (Unsupported ("no such table: " ^ table))
let find_chain p ~table ~chain = match L.assoc_opt chain (chains_of p ~table) with
  | Some c -> c
  | None -> raise (Unsupported (Printf.sprintf "no chain %s in table %s" chain table))
