(* Nft_lower: surface AST (Nft_ast) -> trusted Syntax AST + Packet.env.

   This is where all of nft's frontend behaviour lives, in untrusted code:
     - expanding `define` references (`$lan`);
     - resolving symbolic constants (`established`, `https`, `arp`, `ipv6-icmp`);
     - encoding literals to the byte width of their field / declared set type;
     - inserting the implicit `meta l4proto <proto>` dependency nft puts before an
       L4 (tcp/udp/icmp/...) match;
     - turning named-set/map *declarations* (and inline anonymous `{...}` sets and
       `vmap {...}` maps) into NAMED entries in the evaluation environment, which
       the model looks set/map contents up by name (NOT inlined into the rule).

   Everything here is checked downstream (against the Coq proofs' verdicts and
   live `nft`); nothing here is in the proof TCB.  Any construct outside the
   supported subset raises [Unsupported] — we never guess.  See TODO 9 in
   ../DEVELOPMENT.md. *)

module L = Stdlib.List
module S = Stdlib.String

exception Unsupported of string

(* ---------- byte helpers ---------- *)

let bytes_of_int (width : int) (n : int) : Bytes.data =
  if n < 0 then raise (Unsupported "negative numeric literal");
  L.init width (fun i -> (n lsr (8 * (width - 1 - i))) land 0xff)

(* little-endian (host byte order on x86), least-significant byte first.  This
   is how the kernel stores host-endian integer meta keys such as the interface
   index (meta.c ifindex_type: BYTEORDER_HOST_ENDIAN, 4 bytes). *)
let bytes_of_int_le (width : int) (n : int) : Bytes.data =
  if n < 0 then raise (Unsupported "negative numeric literal");
  L.init width (fun i -> (n lsr (8 * i)) land 0xff)

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
   The model's MEq is a prefix compare (data_eqb (firstn (length v) field) v),
   so a SHORT v gives the wildcard semantics and a 16-byte zero-padded v gives
   the exact semantics.  Emitting only the unpadded name (the old behaviour)
   collapsed both into a prefix match, unsoundly matching same-prefix interfaces
   the kernel rejects (e.g. `iifname br.20` matching "br.200").

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
(* DSCP codepoints (6-bit): class-selector csN = 8N, assured-forwarding afXY,
   expedited-forwarding ef=46, best-effort be=0, lower-effort le=1.  Used as the
   RAW field value for `ip dscp` / `ip6 dscp` (then shifted into the header bits). *)
let sym_dscp = [
  "cs0",0; "cs1",8; "cs2",16; "cs3",24; "cs4",32; "cs5",40; "cs6",48; "cs7",56;
  "af11",10; "af12",12; "af13",14; "af21",18; "af22",20; "af23",22;
  "af31",26; "af32",28; "af33",30; "af41",34; "af42",36; "af43",38;
  "ef",46; "be",0; "le",1;
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

(* encode a single (non-range, non-prefix, non-concat) value for a field kind *)
let enc_atom (k : kind) (v : Nft_ast.value) : Bytes.data =
  match k, v with
  | KIfname, (Nft_ast.Vsym s | Nft_ast.Vstr s) -> ifname_bytes s
  (* iif/oif: the interface INDEX, a 4-byte host-endian integer.  A numeric
     literal is taken verbatim; a name is resolved to its index at load time. *)
  | KIfindex, Nft_ast.Vnum n -> bytes_of_int_le 4 n
  | KIfindex, (Nft_ast.Vsym s | Nft_ast.Vstr s) -> bytes_of_int_le 4 (nametoindex s)
  | KIp4, Nft_ast.Vip4 b -> b
  | KIp6, Nft_ast.Vip6 b -> b
  | KIp6, Nft_ast.Vip4 b -> b           (* a v4-mapped literal in a v6 context *)
  | KPort, Nft_ast.Vnum n -> bytes_of_int 2 n
  | KPort, Nft_ast.Vsym s -> bytes_of_int 2 (L.assoc_opt s sym_service
        |> function Some p -> p | None -> raise (Unsupported ("service " ^ s)))
  | KL4proto, Nft_ast.Vnum n -> [n land 0xff]
  | KL4proto, Nft_ast.Vsym s -> lookup "l4proto" sym_l4proto s
  | KNfproto, Nft_ast.Vnum n -> [n land 0xff]
  | KNfproto, Nft_ast.Vsym s -> lookup "nfproto" sym_nfproto s
  | KEthertype, Nft_ast.Vnum n -> bytes_of_int 2 n
  | KEthertype, Nft_ast.Vsym s -> lookup "ethertype" sym_ethertype s
  | KCtstate, Nft_ast.Vsym s -> lookup "ct state" sym_ctstate s
  | KCtstate, Nft_ast.Vnum n -> bytes_of_int 4 n
  | KCtstatus, Nft_ast.Vsym s -> lookup "ct status" sym_ctstatus s
  | KCtstatus, Nft_ast.Vnum n -> bytes_of_int 4 n
  (* a single tcp-flag symbol / numeric literal -> a 1-byte mask *)
  | KTcpflag, Nft_ast.Vsym s -> [lookup "tcp flag" sym_tcpflag s]
  | KTcpflag, Nft_ast.Vnum n -> [n land 0xff]
  (* `meta mark` / `ct mark` are HOST-ENDIAN (BYTEORDER_HOST_ENDIAN) 4-byte
     integers in the kernel (nft_meta.c `*dest = skb->mark;`; src/ct.c:52 /
     src/meta.c:106).  We store them little-endian (host order on x86) like the
     register actually holds them, exactly as [KIfindex] already does.  For
     equality/neq this is order-agnostic (the kernel uses memcmp); for an ORDERED
     or RANGE match nft inserts a `byteorder hton(4,4)` before the cmp/range so
     the comparison runs over network bytes — see [lower_match], which prepends a
     [TByteorder true 4 4] transform and encodes the bounds network-order. *)
  | KMark, Nft_ast.Vnum n -> bytes_of_int_le 4 n
  | KIcmp, Nft_ast.Vnum n -> [n land 0xff]
  | KIcmp, Nft_ast.Vsym s -> lookup "icmp type" sym_icmp s
  | KIcmpv6, Nft_ast.Vnum n -> [n land 0xff]
  | KIcmpv6, Nft_ast.Vsym s -> lookup "icmpv6 type" sym_icmpv6 s
  | KPkttype, Nft_ast.Vsym s -> lookup "pkttype" sym_pkttype s
  | KPkttype, Nft_ast.Vnum n -> [n land 0xff]
  | KIgmp, Nft_ast.Vsym s -> lookup "igmp type" sym_igmptype s
  | KIgmp, Nft_ast.Vnum n -> [n land 0xff]
  | KIcmpcode, Nft_ast.Vsym s -> lookup "icmp code" sym_icmpcode s
  | KIcmpcode, Nft_ast.Vnum n -> [n land 0xff]
  | KIcmp6code, Nft_ast.Vsym s -> lookup "icmpv6 code" sym_icmp6code s
  | KIcmp6code, Nft_ast.Vnum n -> [n land 0xff]
  | KMhtype, Nft_ast.Vsym s -> lookup "mh type" sym_mhtype s
  | KMhtype, Nft_ast.Vnum n -> [n land 0xff]
  | KFibType, Nft_ast.Vsym s -> lookup "fib type" sym_fibtype s
  | KFibType, Nft_ast.Vnum n -> bytes_of_int_le 4 n
  (* a MAC literal is 6 verbatim big-endian bytes (ether saddr/daddr, arp ether). *)
  | KNum 6, Nft_ast.Vmac b -> b
  | KNum w, Nft_ast.Vnum n -> bytes_of_int w n
  | KNumLe w, Nft_ast.Vnum n -> bytes_of_int_le w n
  | KArpop, Nft_ast.Vnum n -> bytes_of_int 2 n
  | KArpop, Nft_ast.Vsym s -> lookup "arp operation" sym_arpop s
  | KCtdir, Nft_ast.Vnum n -> [n land 0xff]
  | KCtdir, Nft_ast.Vsym s ->
      (match s with "original" -> [0] | "reply" -> [1]
       | _ -> raise (Unsupported ("ct direction " ^ s)))
  | _, Nft_ast.Vvar n -> raise (Unsupported ("unresolved $" ^ n))
  | _ -> raise (Unsupported "value/selector type mismatch")

(* the byte width a kind compares at (for building a prefix mask) *)
let width_of_kind = function
  | KIp4 -> 4 | KIp6 -> 16 | KPort | KEthertype | KArpop -> 2
  | KCtstate | KCtstatus | KMark | KIfindex | KFibType -> 4 | KNum w -> w | KNumLe w -> w
  | KCtdir -> 1 | _ -> 1

(* A kind stored HOST-ENDIAN (little-endian on x86) in the register, like the
   kernel holds `meta mark` / `ct mark` (BYTEORDER_HOST_ENDIAN).  For these,
   an ORDERED or RANGE comparison is only numerically meaningful after nft's
   mandatory `byteorder reg = hton(reg, N, N)` conversion, which we model with a
   [TByteorder true w w] transform.  Equality/neq need no conversion (memcmp is
   order-independent), so only the range/ordered path consults this. *)
let host_endian_kind = function KMark | KIfindex | KFibType -> true | _ -> false

(* Encode a value NETWORK-ORDER (big-endian).  Used for the bounds of a RANGE
   match on a host-endian field: nft stores the range immediates network-order
   (golden `range eq reg 1 0x00000032 0x00000045`) and converts the loaded
   host-endian field to network order with `hton` before the range test, so the
   comparison is numeric.  [enc_atom] (host-endian for [KMark]) is right for the
   eq/membership immediates but wrong for these post-hton range bounds. *)
let enc_atom_be (k : kind) (v : Nft_ast.value) : Bytes.data =
  match k, v with
  | KMark, Nft_ast.Vnum n -> bytes_of_int (width_of_kind k) n
  (* iif/oif (interface INDEX) are BYTEORDER_HOST_ENDIAN like mark (src/meta.c
     NFT_META_IIF/OIF templates), so an ordered/range match on them also goes
     through the hton path; the bounds must be network-order, not the LE form
     [enc_atom] uses for the eq/membership immediates. *)
  | KIfindex, Nft_ast.Vnum n -> bytes_of_int 4 n
  | KIfindex, (Nft_ast.Vsym s | Nft_ast.Vstr s) -> bytes_of_int 4 (nametoindex s)
  (* fib type is BYTEORDER_HOST_ENDIAN too (src/fib.c:50); an ordered/range match
     on it goes through the same hton path, so its bounds are network-order. *)
  | KFibType, Nft_ast.Vnum n -> bytes_of_int 4 n
  | KFibType, Nft_ast.Vsym _ ->
      (match enc_atom k v with b -> Stdlib.List.rev b)
  | _ -> enc_atom k v

(* ---------- concatenated-set register-slot padding ----------

   A concatenated set (NFT_SET_CONCAT) lays each field in its OWN 32-bit register
   slot: each field's contribution to the element key is its byte length ROUNDED
   UP to a multiple of NFT_REG32_SIZE = 4 (include/netlink.h netlink_padded_len /
   netlink_register_space; src/evaluate.c:5192; src/netlink_linearize.c:120-128).
   Within a slot the field's bytes sit at the FRONT, followed by zero padding in
   the trailing bytes (golden corpus: a 2-byte dport=80 displays as 0050 in its
   4-byte slot).  So when we emit a per-field lo/hi bound for a concatenated
   element, each field must be zero-padded on the trailing side to its 4-byte
   slot, matching what nft stores and what [concat_in_iv] (Bytes.v) now expects.
   This mirrors the bytecode/codec layer, which already uses one register slot
   per field (codec.ml:167). *)
let reg_slot (n : int) : int = 4 * ((n + 3) / 4)
let pad_to_slot (b : Bytes.data) : Bytes.data =
  let n = L.length b in
  b @ (L.init (reg_slot n - n) (fun _ -> 0))

(* ---------- selector resolution: keypath -> (field, kind, l4proto-dep) ---------- *)

(* An implicit dependency that nft inserts BEFORE a payload/meta match so the
   compared bytes are only read when they actually belong to the right header.
   - [DL4 pv]: `meta l4proto == pv` (e.g. before a tcp/udp/icmp selector).
   - [DNfproto pv]: `meta nfproto == pv`, the implicit NETWORK-protocol guard
     real nft emits before every `ip`/`ip6` payload match in a chain that can
     see more than one L3 family (inet/bridge/netdev) — see payload.c
     payload_gen_dependency / payload_add_dependency.  In a single-L3 family
     (ip/ip6/arp) nft emits NO such guard, so [DNfproto] is discharged to a
     no-op there (resolved in [ensure_dep], which is family-aware).
   - [DNone]: no dependency. *)
type dep1 = DL4 of Bytes.data | DNfproto of Bytes.data | DEther of Bytes.data
          | DL2proto of Bytes.data | DIiftype of Bytes.data | DIcmpType of int
(* [DIiftype et]: the `meta iiftype == ARPHRD_ETHER (1)` guard nft prepends before
   a LINK-layer (ether address) match in any family whose interfaces are not
   guaranteed ethernet (ip/ip6/inet/netdev) — the ethernet header only exists on an
   ARPHRD_ETHER device (golden {ip,ip6,inet}/ether.t.payload).  A no-op in bridge
   (an inherently-ethernet family).  The compare value is stored BIG-ENDIAN
   ([0x00;0x01]) — the display/corpus convention codec renders as the integer
   0x0001, exactly matching the golden — NOT the host-endian wire order. *)
(* [DL2proto et]: an L2-family (bridge/netdev) network-layer guard `meta protocol
   == <ethertype>` that nft prepends before a network-header (arp) match.  Unlike
   [DNfproto] (which nft emits for ip/ip6 in the *inet* family), the bridge and
   netdev families pin the L3 protocol by the LINK-layer ethertype instead
   (golden arp.t.payload.netdev: `meta load protocol` / `cmp eq 0x0806`).  It is a
   no-op in every single-L3 family (ip/ip6/arp/inet). *)
(* [DEther pv]: the VLAN ether-type guard nft inserts before a `vlan <field>`
   match — `ether type == 0x8100` (payload load 2b @ link+12).  In the netdev
   family nft prepends a `meta iiftype == ARPHRD_ETHER (1)` guard as well
   (golden bridge/vlan.t.payload{,.netdev}). *)
(* A selector may carry SEVERAL implicit deps that nft emits, in order.  Most
   selectors carry zero or one; the L3-specific L4 protocols icmp/icmpv6 carry
   TWO — the network-protocol guard `meta nfproto == {2|10}` AND the transport
   guard `meta l4proto == {1|58}` — because ICMP is IPv4-only and ICMPv6 is
   IPv6-only, so in a multi-L3 family nft pins BOTH (golden inet/icmp.t.payload:
   nfproto THEN l4proto).  tcp/udp are valid over both families and get only the
   l4proto guard. *)
type dep = dep1 list

let dep_l4 = function
  | "tcp" -> [DL4 [6]] | "udp" -> [DL4 [17]]
  (* IP-protocol-numbered transport / auth / compression headers: nft guards each
     payload load with `meta l4proto == <ipproto>` (golden inet/{ah,esp,comp,sctp,
     dccp,udplite}.t.payload).  These carry NO nfproto guard (valid over both L3
     families), exactly like tcp/udp. *)
  | "ah" -> [DL4 [51]] | "esp" -> [DL4 [50]] | "comp" -> [DL4 [108]]
  | "sctp" -> [DL4 [132]] | "dccp" -> [DL4 [33]] | "udplite" -> [DL4 [136]]
  (* icmp/icmpv6 are NETWORK-protocol-LINKED L4 protocols: nft emits the nfproto
     guard BEFORE the l4proto guard (payload.c proto_icmp/proto_icmp6 are linked
     to the IPv4/IPv6 network bases).  Order matches the golden byte sequence. *)
  | "icmp" -> [DNfproto [2]; DL4 [1]]
  | "icmpv6" -> [DNfproto [10]; DL4 [58]]
  (* IGMP (IPPROTO_IGMP 2) is IPv4-only, linked to the network base like icmp. *)
  | "igmp" -> [DNfproto [2]; DL4 [2]]
  | _ -> []

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

let key_field (kp : Nft_ast.keypath) : Syntax.field * kind * dep =
  let none = [] in
  (* arp lives at the network header; in a bridge/netdev L2 chain nft pins it with
     `meta protocol == 0x0806` (ETH_P_ARP), a no-op in the arp family itself. *)
  let arp_dep = [DL2proto [0x08; 0x06]] in
  match kp with
  | ["tcp"; "dport"] | ["udp"; "dport"] | ["th"; "dport"] ->
      (Syntax.FThDport, KPort, dep_l4 (L.hd kp))
  | ["tcp"; "sport"] | ["udp"; "sport"] | ["th"; "sport"] ->
      (Syntax.FThSport, KPort, dep_l4 (L.hd kp))
  | ["tcp"; "flags"] -> (Syntax.FTcpFlags, KTcpflag, dep_l4 "tcp")
  (* `ip`/`ip6` are NETWORK-header (PNetwork) selectors: nft guards them with an
     implicit `meta nfproto == 2` (IPv4) / `== 10` (IPv6) in any multi-L3 family,
     so reading the IPv4 header on an IPv6 packet (or vice versa) can't match.
     [ensure_dep] turns [DNfproto] into a real match only for inet/bridge/netdev. *)
  | ["ip"; "saddr"]    -> (Syntax.FIp4Saddr, KIp4, [DNfproto [2]])
  | ["ip"; "daddr"]    -> (Syntax.FIp4Daddr, KIp4, [DNfproto [2]])
  | ["ip"; "protocol"] -> (Syntax.FIp4Protocol, KL4proto, [DNfproto [2]])
  | ["ip6"; "saddr"]   -> (Syntax.FIp6Saddr, KIp6, [DNfproto [10]])
  | ["ip6"; "daddr"]   -> (Syntax.FIp6Daddr, KIp6, [DNfproto [10]])
  | ["icmp"; "type"]   -> (Syntax.FIcmpType, KIcmp, dep_l4 "icmp")
  | ["icmpv6"; "type"] -> (Syntax.FIcmpType, KIcmpv6, dep_l4 "icmpv6")
  | ["ether"; "type"]  -> (Syntax.FEtherType, KEthertype, none)
  | ["ether"; "saddr"] -> (Syntax.FEtherSaddr, KNum 6, [DIiftype [0x00; 0x01]])
  | ["ether"; "daddr"] -> (Syntax.FEtherDaddr, KNum 6, [DIiftype [0x00; 0x01]])
  | ["meta"; "l4proto"]  -> (Syntax.FMetaL4proto, KL4proto, none)
  | ["meta"; "nfproto"]  -> (Syntax.FMetaNfproto, KNfproto, none)
  | ["meta"; "protocol"] -> (Syntax.FMetaProtocol, KEthertype, none)
  | ["meta"; "mark"]     -> (Syntax.FMetaMark, KMark, none)
  | ["meta"; "iifname"]  -> (Syntax.FMetaIifname, KIfname, none)
  | ["meta"; "oifname"]  -> (Syntax.FMetaOifname, KIfname, none)
  | ["meta"; "iif"]      -> (Syntax.FMetaIif, KIfindex, none)
  | ["meta"; "oif"]      -> (Syntax.FMetaOif, KIfindex, none)
  | ["meta"; "obrname"]  -> (Syntax.FMetaGen Packet.MKbri_oifname, KIfname, none)
  | ["meta"; "ibrname"]  -> (Syntax.FMetaGen Packet.MKbri_iifname, KIfname, none)
  | ["meta"; "pkttype"]  -> (Syntax.FMetaPkttype, KPkttype, none)
  | ["mark"]             -> (Syntax.FMetaMark, KMark, none)
  | ["pkttype"]          -> (Syntax.FMetaPkttype, KPkttype, none)
  | ["iifname"]          -> (Syntax.FMetaIifname, KIfname, none)
  | ["oifname"]          -> (Syntax.FMetaOifname, KIfname, none)
  | ["iif"]              -> (Syntax.FMetaIif, KIfindex, none)
  | ["oif"]              -> (Syntax.FMetaOif, KIfindex, none)
  | ["fib"; sel; "type"]    -> (Syntax.FFib (sel, Packet.FRtype), KFibType, none)
  | ["fib"; sel; "oifname"] -> (Syntax.FFib (sel, Packet.FRoifname), KIfname, none)
  | ["fib"; sel; "oif"]     -> (Syntax.FFib (sel, Packet.FRoif), KNum 4, none)
  | ["ct"; "state"]      -> (Syntax.FCtState, KCtstate, none)
  | ["ct"; "status"]     -> (Syntax.FCtStatus, KCtstatus, none)
  | ["ct"; "mark"]       -> (Syntax.FCtMark, KMark, none)
  (* ---- additional IPv4 header fields (network-order payload loads) ---- *)
  | ["ip"; "ttl"]        -> (Syntax.FIp4Ttl,    KNum 1, [DNfproto [2]])
  | ["ip"; "length"]     -> (Syntax.FIp4Totlen, KNum 2, [DNfproto [2]])
  | ["ip"; "id"]         -> (Syntax.FIp4Id,     KNum 2, [DNfproto [2]])
  | ["ip"; "frag-off"]   -> (Syntax.FIp4FragOff,KNum 2, [DNfproto [2]])
  | ["ip"; "checksum"]   -> (Syntax.FIp4Csum,   KNum 2, [DNfproto [2]])
  (* ---- additional IPv6 header fields ---- *)
  | ["ip6"; "length"]    -> (Syntax.FPayload (Packet.PNetwork, 4, 2), KNum 2, [DNfproto [10]])
  | ["ip6"; "hoplimit"]  -> (Syntax.FPayload (Packet.PNetwork, 7, 1), KNum 1, [DNfproto [10]])
  | ["ip6"; "nexthdr"]   -> (Syntax.FPayload (Packet.PNetwork, 6, 1), KL4proto, [DNfproto [10]])
  (* ---- additional TCP header fields (network-order payload loads) ---- *)
  | ["tcp"; "sequence"]  -> (Syntax.FTcpSeq, KNum 4, dep_l4 "tcp")
  | ["tcp"; "ackseq"]    -> (Syntax.FTcpAck, KNum 4, dep_l4 "tcp")
  | ["tcp"; "window"]    -> (Syntax.FPayload (Packet.PTransport, 14, 2), KNum 2, dep_l4 "tcp")
  | ["tcp"; "checksum"]  -> (Syntax.FPayload (Packet.PTransport, 16, 2), KNum 2, dep_l4 "tcp")
  | ["tcp"; "urgptr"]    -> (Syntax.FPayload (Packet.PTransport, 18, 2), KNum 2, dep_l4 "tcp")
  (* ---- UDP header fields ---- *)
  | ["udp"; "length"]    -> (Syntax.FUdpLen,  KNum 2, dep_l4 "udp")
  | ["udp"; "checksum"]  -> (Syntax.FUdpCsum, KNum 2, dep_l4 "udp")
  (* ---- ICMP / ICMPv6 header fields ---- *)
  | ["icmp"; "code"]     -> (Syntax.FIcmpCode, KIcmpcode, dep_l4 "icmp")
  (* ---- IGMP (IPPROTO_IGMP 2), transport header: type@0 mrt@1 checksum@2
     (golden ip/igmp.t.payload). ---- *)
  | ["igmp"; "type"]     -> (Syntax.FPayload (Packet.PTransport, 0, 1), KIgmp,  dep_l4 "igmp")
  | ["igmp"; "mrt"]      -> (Syntax.FPayload (Packet.PTransport, 1, 1), KNum 1, dep_l4 "igmp")
  | ["igmp"; "checksum"] -> (Syntax.FPayload (Packet.PTransport, 2, 2), KNum 2, dep_l4 "igmp")
  | ["icmp"; "checksum"] -> (Syntax.FPayload (Packet.PTransport, 2, 2), KNum 2, dep_l4 "icmp")
  | ["icmp"; "id"]       -> (Syntax.FPayload (Packet.PTransport, 4, 2), KNum 2, dep_l4 "icmp")
  | ["icmp"; "seq"] | ["icmp"; "sequence"]
                         -> (Syntax.FPayload (Packet.PTransport, 6, 2), KNum 2, dep_l4 "icmp")
  | ["icmp"; "gateway"]  -> (Syntax.FPayload (Packet.PTransport, 4, 4), KNum 4, dep_l4 "icmp" @ [DIcmpType 5])
  | ["icmp"; "mtu"]      -> (Syntax.FPayload (Packet.PTransport, 6, 2), KNum 2, dep_l4 "icmp" @ [DIcmpType 3])
  | ["icmpv6"; "code"]     -> (Syntax.FIcmpCode, KIcmp6code, dep_l4 "icmpv6")
  | ["icmpv6"; "checksum"] -> (Syntax.FPayload (Packet.PTransport, 2, 2), KNum 2, dep_l4 "icmpv6")
  | ["icmpv6"; "id"]       -> (Syntax.FPayload (Packet.PTransport, 4, 2), KNum 2, dep_l4 "icmpv6")
  | ["icmpv6"; "seq"] | ["icmpv6"; "sequence"]
                           -> (Syntax.FPayload (Packet.PTransport, 6, 2), KNum 2, dep_l4 "icmpv6")
  | ["icmpv6"; "mtu"]      -> (Syntax.FPayload (Packet.PTransport, 4, 4), KNum 4, dep_l4 "icmpv6")
  (* ---- host-endian meta register fields (u32/u16 host order) ---- *)
  | ["meta"; "length"] | ["meta"; "len"] -> (Syntax.FMetaLen,   KNumLe 4, none)
  | ["meta"; "cpu"]    -> (Syntax.FMetaCpu,   KNumLe 4, none)
  | ["meta"; "skuid"]  -> (Syntax.FMetaSkuid, KNumLe 4, none)
  | ["meta"; "skgid"]  -> (Syntax.FMetaSkgid, KNumLe 4, none)
  | ["meta"; "iifgroup"] -> (Syntax.FMetaGen Packet.MKiifgroup, KNumLe 4, none)
  | ["meta"; "oifgroup"] -> (Syntax.FMetaGen Packet.MKoifgroup, KNumLe 4, none)
  | ["meta"; "cgroup"]   -> (Syntax.FMetaGen Packet.MKcgroup,   KNumLe 4, none)
  | ["meta"; "iiftype"]  -> (Syntax.FMetaIiftype, KNumLe 2, none)
  | ["meta"; "oiftype"]  -> (Syntax.FMetaOiftype, KNumLe 2, none)
  (* ---- host-endian conntrack register fields ---- *)
  | ["ct"; "direction"]  -> (Syntax.FCtDirection, KCtdir,  none)
  | ["ct"; "id"]         -> (Syntax.FCtId,        KNumLe 4, none)
  | ["ct"; "expiration"] -> (Syntax.FCtExpiration,KNumLe 4, none)
  | ["ct"; "zone"]       -> (Syntax.FCtGen Packet.CKzone, KNumLe 2, none)
  (* ---- direction-qualified conntrack tuple (FCtDir key strings match nft's
     `ct load <key>` render: src_ip/dst_ip/src_ip6/dst_ip6/proto_src/proto_dst/
     zone/protocol) ---- *)
  | ["ctdir"; d; "zone"]         -> (Syntax.FCtDir ("zone", d),      KNumLe 2, none)
  | ["ctdir"; d; "protocol"]     -> (Syntax.FCtDir ("protocol", d),  KL4proto, none)
  | ["ctdir"; d; "proto-src"]    -> (Syntax.FCtDir ("proto_src", d), KPort, none)
  | ["ctdir"; d; "proto-dst"]    -> (Syntax.FCtDir ("proto_dst", d), KPort, none)
  | ["ctdir"; d; "ip"; "saddr"]  -> (Syntax.FCtDir ("src_ip", d),    KIp4, none)
  | ["ctdir"; d; "ip"; "daddr"]  -> (Syntax.FCtDir ("dst_ip", d),    KIp4, none)
  | ["ctdir"; d; "ip6"; "saddr"] -> (Syntax.FCtDir ("src_ip6", d),   KIp6, none)
  | ["ctdir"; d; "ip6"; "daddr"] -> (Syntax.FCtDir ("dst_ip6", d),   KIp6, none)
  (* ---- ARP header (NFT_PAYLOAD_NETWORK_HEADER; arp is a single-L3 family so
     nft emits NO nfproto dependency).  Offsets from arp.c / golden arp.t.payload:
     htype@0 ptype@2 hlen@4 plen@5 operation@6, sender/target hw+proto addrs. ---- *)
  | ["arp"; "htype"]     -> (Syntax.FPayload (Packet.PNetwork, 0, 2), KNum 2, arp_dep)
  | ["arp"; "ptype"]     -> (Syntax.FPayload (Packet.PNetwork, 2, 2), KEthertype, arp_dep)
  | ["arp"; "hlen"]      -> (Syntax.FPayload (Packet.PNetwork, 4, 1), KNum 1, arp_dep)
  | ["arp"; "plen"]      -> (Syntax.FPayload (Packet.PNetwork, 5, 1), KNum 1, arp_dep)
  | ["arp"; "operation"] -> (Syntax.FPayload (Packet.PNetwork, 6, 2), KArpop, arp_dep)
  | ["arp"; "saddr"; "ether"] -> (Syntax.FPayload (Packet.PNetwork, 8, 6),  KNum 6, arp_dep)
  | ["arp"; "saddr"; "ip"]    -> (Syntax.FPayload (Packet.PNetwork, 14, 4), KIp4, arp_dep)
  | ["arp"; "daddr"; "ether"] -> (Syntax.FPayload (Packet.PNetwork, 18, 6), KNum 6, arp_dep)
  | ["arp"; "daddr"; "ip"]    -> (Syntax.FPayload (Packet.PNetwork, 24, 4), KIp4, arp_dep)
  (* ---- AH (IPPROTO_AH 51), transport header.  nexthdr@0 hdrlength@1 reserved@2
     spi@4 sequence@8 (golden inet/ah.t.payload). ---- *)
  | ["ah"; "nexthdr"]    -> (Syntax.FPayload (Packet.PTransport, 0, 1), KL4proto, dep_l4 "ah")
  | ["ah"; "hdrlength"]  -> (Syntax.FPayload (Packet.PTransport, 1, 1), KNum 1, dep_l4 "ah")
  | ["ah"; "reserved"]   -> (Syntax.FPayload (Packet.PTransport, 2, 2), KNum 2, dep_l4 "ah")
  | ["ah"; "spi"]        -> (Syntax.FPayload (Packet.PTransport, 4, 4), KNum 4, dep_l4 "ah")
  | ["ah"; "sequence"]   -> (Syntax.FPayload (Packet.PTransport, 8, 4), KNum 4, dep_l4 "ah")
  (* ---- ESP (IPPROTO_ESP 50), transport header: spi@0 sequence@4. ---- *)
  | ["esp"; "spi"]       -> (Syntax.FPayload (Packet.PTransport, 0, 4), KNum 4, dep_l4 "esp")
  | ["esp"; "sequence"]  -> (Syntax.FPayload (Packet.PTransport, 4, 4), KNum 4, dep_l4 "esp")
  (* ---- COMP (IPPROTO_COMP 108), transport header: nexthdr@0 flags@1 cpi@2. ---- *)
  | ["comp"; "nexthdr"]  -> (Syntax.FPayload (Packet.PTransport, 0, 1), KL4proto, dep_l4 "comp")
  | ["comp"; "flags"]    -> (Syntax.FPayload (Packet.PTransport, 1, 1), KNum 1, dep_l4 "comp")
  | ["comp"; "cpi"]      -> (Syntax.FPayload (Packet.PTransport, 2, 2), KNum 2, dep_l4 "comp")
  (* ---- SCTP (IPPROTO_SCTP 132), transport header: sport@0 dport@2 vtag@4
     checksum@8 (golden inet/sctp.t.payload). ---- *)
  | ["sctp"; "sport"]    -> (Syntax.FPayload (Packet.PTransport, 0, 2), KPort, dep_l4 "sctp")
  | ["sctp"; "dport"]    -> (Syntax.FPayload (Packet.PTransport, 2, 2), KPort, dep_l4 "sctp")
  | ["sctp"; "vtag"]     -> (Syntax.FPayload (Packet.PTransport, 4, 4), KNum 4, dep_l4 "sctp")
  | ["sctp"; "checksum"] -> (Syntax.FPayload (Packet.PTransport, 8, 4), KNum 4, dep_l4 "sctp")
  (* ---- DCCP (IPPROTO_DCCP 33), transport header: sport@0 dport@2. ---- *)
  | ["dccp"; "sport"]    -> (Syntax.FPayload (Packet.PTransport, 0, 2), KPort, dep_l4 "dccp")
  | ["dccp"; "dport"]    -> (Syntax.FPayload (Packet.PTransport, 2, 2), KPort, dep_l4 "dccp")
  (* ---- UDP-Lite (IPPROTO_UDPLITE 136), transport header: sport@0 dport@2
     cscov@4 checksum@6 (golden inet/udplite.t.payload). ---- *)
  | ["udplite"; "sport"]    -> (Syntax.FPayload (Packet.PTransport, 0, 2), KPort, dep_l4 "udplite")
  | ["udplite"; "dport"]    -> (Syntax.FPayload (Packet.PTransport, 2, 2), KPort, dep_l4 "udplite")
  | ["udplite"; "cscov"] | ["udplite"; "csumcov"]
                            -> (Syntax.FPayload (Packet.PTransport, 4, 2), KNum 2, dep_l4 "udplite")
  | ["udplite"; "checksum"] -> (Syntax.FPayload (Packet.PTransport, 6, 2), KNum 2, dep_l4 "udplite")
  (* ---- IPv6 extension-header selectors (NFT_EXTHDR `exthdr load ipv6`).
     The htype is the exthdr's IPPROTO (hbh=0, rt/srh=43, frag=44, dst=60,
     mh=135); off/len are the field's position WITHIN that header.  nft guards
     each with the IPv6 nfproto dependency (golden ip6/{hbh,rt,frag,dst,mh}.t.
     payload: ip6 family emits none, inet/netdev emit `meta nfproto == 0x0a`),
     so dep = [DNfproto [10]] exactly like the ip6 network-header selectors.
     Byte-aligned fields only; the sub-byte bitfields (frag frag-off/reserved2/
     more-fragments, which nft follows with a `bitwise` mask) are left out. ---- *)
  | ["hbh"; "nexthdr"]    -> (Syntax.FExthdr (Packet.EPipv6, 0,   0, 1, false), KL4proto, [DNfproto [10]])
  | ["hbh"; "hdrlength"]  -> (Syntax.FExthdr (Packet.EPipv6, 0,   1, 1, false), KNum 1,   [DNfproto [10]])
  | ["rt"; "nexthdr"]     -> (Syntax.FExthdr (Packet.EPipv6, 43,  0, 1, false), KL4proto, [DNfproto [10]])
  | ["rt"; "hdrlength"]   -> (Syntax.FExthdr (Packet.EPipv6, 43,  1, 1, false), KNum 1,   [DNfproto [10]])
  | ["rt"; "type"]        -> (Syntax.FExthdr (Packet.EPipv6, 43,  2, 1, false), KNum 1,   [DNfproto [10]])
  | ["rt"; "seg-left"]    -> (Syntax.FExthdr (Packet.EPipv6, 43,  3, 1, false), KNum 1,   [DNfproto [10]])
  | ["srh"; "last-entry"] -> (Syntax.FExthdr (Packet.EPipv6, 43,  4, 1, false), KNum 1,   [DNfproto [10]])
  | ["srh"; "flags"]      -> (Syntax.FExthdr (Packet.EPipv6, 43,  5, 1, false), KNum 1,   [DNfproto [10]])
  | ["srh"; "tag"]        -> (Syntax.FExthdr (Packet.EPipv6, 43,  6, 2, false), KNum 2,   [DNfproto [10]])
  | ["frag"; "nexthdr"]   -> (Syntax.FExthdr (Packet.EPipv6, 44,  0, 1, false), KL4proto, [DNfproto [10]])
  | ["frag"; "reserved"]  -> (Syntax.FExthdr (Packet.EPipv6, 44,  1, 1, false), KNum 1,   [DNfproto [10]])
  | ["frag"; "id"]        -> (Syntax.FExthdr (Packet.EPipv6, 44,  4, 4, false), KNum 4,   [DNfproto [10]])
  | ["dst"; "nexthdr"]    -> (Syntax.FExthdr (Packet.EPipv6, 60,  0, 1, false), KL4proto, [DNfproto [10]])
  | ["dst"; "hdrlength"]  -> (Syntax.FExthdr (Packet.EPipv6, 60,  1, 1, false), KNum 1,   [DNfproto [10]])
  | ["mh"; "nexthdr"]     -> (Syntax.FExthdr (Packet.EPipv6, 135, 0, 1, false), KL4proto, [DNfproto [10]])
  | ["mh"; "hdrlength"]   -> (Syntax.FExthdr (Packet.EPipv6, 135, 1, 1, false), KNum 1,   [DNfproto [10]])
  | ["mh"; "type"]        -> (Syntax.FExthdr (Packet.EPipv6, 135, 2, 1, false), KMhtype,  [DNfproto [10]])
  | ["mh"; "reserved"]    -> (Syntax.FExthdr (Packet.EPipv6, 135, 3, 1, false), KNum 1,   [DNfproto [10]])
  | ["mh"; "checksum"]    -> (Syntax.FExthdr (Packet.EPipv6, 135, 4, 2, false), KNum 2,   [DNfproto [10]])
  (* ---- TCP options: `tcp option <name> <field>` (byte-aligned fields). ---- *)
  | ["tcpopt"; name; field] ->
      let optnum = tcpopt_num name in
      let (off, len, k) = tcpopt_field name field in
      (Syntax.FExthdr (Packet.EPtcpopt, optnum, off, len, false), k, [])
  | _ -> raise (Unsupported ("selector: " ^ S.concat " " kp))

(* ---------- sub-byte header bitfields ----------
   A field that occupies only some bits of one or more header bytes: nft loads
   the containing byte(s), masks them (`bitwise reg = (reg & M) ^ 0`), and
   compares against the value SHIFTED into the field's bit position (golden e.g.
   `ip dscp cs1` => load 1b@nh+1 ; bitwise & 0xfc ; cmp eq 0x20, where cs1=8 and
   8<<2=0x20).  We return (field, len, mask, dep, is_dscp); the shift is derived
   from the mask's trailing-zero count.  Byte-aligned fields stay in [key_field]. *)
let bitfield_sel (kp : Nft_ast.keypath)
    : (Syntax.field * int * Bytes.data * dep * bool) option =
  let ip4 = [DNfproto [2]] and ip6 = [DNfproto [10]] in
  match kp with
  | ["ip"; "version"]    -> Some (Syntax.FPayload (Packet.PNetwork, 0, 1), 1, [0xf0], ip4, false)
  | ["ip"; "hdrlength"]  -> Some (Syntax.FPayload (Packet.PNetwork, 0, 1), 1, [0x0f], ip4, false)
  | ["ip"; "dscp"]       -> Some (Syntax.FPayload (Packet.PNetwork, 1, 1), 1, [0xfc], ip4, true)
  | ["ip6"; "dscp"]      -> Some (Syntax.FPayload (Packet.PNetwork, 0, 2), 2, [0x0f;0xc0], ip6, true)
  | ["ip6"; "flowlabel"] -> Some (Syntax.FPayload (Packet.PNetwork, 1, 3), 3, [0x0f;0xff;0xff], ip6, false)
  | ["tcp"; "doff"]      -> Some (Syntax.FPayload (Packet.PTransport, 12, 1), 1, [0xf0], dep_l4 "tcp", false)
  (* VLAN tag fields (802.1Q, at link+14 after the 0x8100 ether type).  The PCP
     (0xe0>>5) and DEI/CFI (0x10>>4) live in the first byte; the 12-bit VID in
     the 2-byte word (golden bridge/vlan.t.payload).  All carry the ether-type
     guard.  Non-stacked forms only (stacked `vlan type` shifts offsets). *)
  | ["vlan"; "id"]       -> Some (Syntax.FPayload (Packet.PLink, 14, 2), 2, [0x0f;0xff], [DEther [0x81;0x00]], false)
  | ["vlan"; "pcp"]      -> Some (Syntax.FPayload (Packet.PLink, 14, 1), 1, [0xe0], [DEther [0x81;0x00]], false)
  | ["vlan"; "dei"] | ["vlan"; "cfi"]
                         -> Some (Syntax.FPayload (Packet.PLink, 14, 1), 1, [0x10], [DEther [0x81;0x00]], false)
  (* IPv6 fragment-header sub-byte fields (exthdr load ipv6 @ 44, then bitwise):
     frag-off (13 bits, 0xfff8>>3), more-fragments (0x01), reserved2 (0x06>>1)
     — golden ip6/frag.t.payload. *)
  | ["frag"; "frag-off"]       -> Some (Syntax.FExthdr (Packet.EPipv6, 44, 2, 2, false), 2, [0xff;0xf8], [DNfproto [10]], false)
  | ["frag"; "reserved2"]      -> Some (Syntax.FExthdr (Packet.EPipv6, 44, 3, 1, false), 1, [0x06], [DNfproto [10]], false)
  | ["frag"; "more-fragments"] -> Some (Syntax.FExthdr (Packet.EPipv6, 44, 3, 1, false), 1, [0x01], [DNfproto [10]], false)
  | _ -> None

(* trailing-zero bit count of a big-endian byte mask = the field's LSB position. *)
let mask_shift (mask : Bytes.data) : int =
  let rec tz_byte b i = if i >= 8 then 8 else if (b lsr i) land 1 = 1 then i else tz_byte b (i+1) in
  let rec go = function
    | [] -> 0
    | b :: rest -> if b = 0 then 8 + go rest else tz_byte b 0
  in go (L.rev mask)

(* ---------- prefix mask ---------- *)

let prefix_mask (width : int) (len : int) : Bytes.data =
  L.init width (fun i ->
    let bit_lo = 8 * i and bit_hi = 8 * (i + 1) in
    let m = ref 0 in
    for b = bit_lo to bit_hi - 1 do
      if b < len then m := !m lor (0x80 lsr (b - bit_lo))
    done; !m)
let band a b = L.map2 (land) a b
let bor  a b = L.map2 (lor)  a b

(* nft shortens a BYTE-ALIGNED CIDR prefix on a plain payload field to a load of
   just the prefix bytes plus a DIRECT compare (no bitwise mask): `ip saddr .../24`
   => `payload load 3b @ network+12 ; cmp eq 0xc0a802` and `ip6 saddr ::/64` =>
   `payload load 8b @ network+8` (golden {ip,ip6}.t.payload).  Only byte-multiple
   prefix lengths strictly inside the field width qualify; every other prefix keeps
   the full-width `load ; bitwise & mask ; cmp` form.  Loading the leading N bytes
   is exactly the masked high-order compare, so this is byte-faithful to nft. *)
let payload_prefix_field (f : Syntax.field) (nbytes : int) : Syntax.field option =
  match f with
  | Syntax.FIp4Saddr -> Some (Syntax.FPayload (Packet.PNetwork, 12, nbytes))
  | Syntax.FIp4Daddr -> Some (Syntax.FPayload (Packet.PNetwork, 16, nbytes))
  | Syntax.FIp6Saddr -> Some (Syntax.FPayload (Packet.PNetwork, 8,  nbytes))
  | Syntax.FIp6Daddr -> Some (Syntax.FPayload (Packet.PNetwork, 24, nbytes))
  | _ -> None

(* ---------- mutable lowering state ---------- *)

type state = {
  defines : (string, Nft_ast.value) Hashtbl.t;
  mutable sets  : (string * (Bytes.data * Bytes.data) list) list;
  mutable vmaps : (string * ((Bytes.data * Bytes.data) * Verdict.verdict) list) list;
  mutable maps  : (string * (Bytes.data * Bytes.data) list) list;
  mutable counter : int;
}
let fresh st pfx = let n = st.counter in st.counter <- n + 1; Printf.sprintf "%s%d" pfx n

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

(* ---------- element encoding (single field & declared concat type) ---------- *)

(* encode a value into one interval [lo,hi] for a single-field set *)
let interval_of_value st (k : kind) (v : Nft_ast.value) : Bytes.data * Bytes.data =
  match resolve_var st v with
  | Nft_ast.Vrange (a, b) -> (enc_atom k a, enc_atom k b)
  | Nft_ast.Vprefix ((Nft_ast.Vip4 b | Nft_ast.Vip6 b), len) ->
      let w = width_of_kind k in let mask = prefix_mask w len in
      let net = band b mask in
      let bcast = L.map2 (fun n m -> n lor (m lxor 0xff)) net mask in
      (net, bcast)
  | v' -> let b = enc_atom k v' in (b, b)

(* Like [interval_of_value] but encode the bounds NETWORK-ORDER (big-endian),
   used for an INTERVAL set over a HOST-ENDIAN field (e.g. `ct mark { 0x100-0x200 }`).
   Such a set is an ORDERED comparison: the kernel compares register bytes with
   memcmp (byte-lexicographic), so nft userspace ALWAYS inserts a
   `byteorder reg = hton(reg,4,4)` before the `lookup` and stores the interval
   immediates network-order — exactly the same conversion it emits for a DIRECT
   `ct mark 0x32-0x45` range (golden any/ct.t.payload: interval mark set forces
   the hton, an exact-element set does not).  We mirror that: the loaded
   host-endian field gets a [TByteorder true w w] transform (see the SEset branch
   in [lower_match]) and the stored bounds are big-endian via [enc_atom_be].
   EXACT (degenerate point) elements are still encoded as a degenerate [b,b]
   interval, but in big-endian so they remain consistent with the hton'd field
   under [set_mem] (equality via [data_le] antisymmetry is order-independent). *)
let interval_of_value_be st (k : kind) (v : Nft_ast.value) : Bytes.data * Bytes.data =
  match resolve_var st v with
  | Nft_ast.Vrange (a, b) -> (enc_atom_be k a, enc_atom_be k b)
  | Nft_ast.Vprefix ((Nft_ast.Vip4 b | Nft_ast.Vip6 b), len) ->
      let w = width_of_kind k in let mask = prefix_mask w len in
      let net = band b mask in
      let bcast = L.map2 (fun n m -> n lor (m lxor 0xff)) net mask in
      (net, bcast)
  | v' -> let b = enc_atom_be k v' in (b, b)

(* Does a single-field set contain at least one INTERVAL (range or prefix)
   element?  An interval set is an ORDERED comparison and so forces nft's
   `byteorder hton` on a host-endian field; an exact-only set (all point
   elements) is an unordered memcmp-equality lookup and emits NO hton.  We only
   take the byteorder path when BOTH the field is host-endian AND the set has an
   interval element (matching the golden corpus: exact mark sets emit no hton). *)
let set_has_interval st (elems : Nft_ast.value list) : bool =
  L.exists
    (fun v -> match resolve_var st v with
       | Nft_ast.Vrange _ | Nft_ast.Vprefix _ -> true
       | _ -> false)
    elems

(* byte width / encoder for a declared set TYPE atom (e.g. `ipv4_addr . ifname`) *)
let bytes_of_typeatom st (atom : string) (v : Nft_ast.value) : Bytes.data =
  let v = resolve_var st v in
  match atom with
  | "ipv4_addr"    -> enc_atom KIp4 v
  | "ipv6_addr"    -> enc_atom KIp6 v
  | "ifname"       -> enc_atom KIfname v
  | "iface_index"  -> enc_atom KIfindex v
  | "inet_service" -> enc_atom KPort v
  | "inet_proto"   -> enc_atom KL4proto v
  | "ether_addr"   -> enc_atom (KNum 6) v
  | "mark"         -> enc_atom KMark v
  | _ -> raise (Unsupported ("set element type: " ^ atom))

(* encode one declared-set element (possibly a concatenation) to an interval *)
let interval_of_decl_elem st (types : string list) (v : Nft_ast.value)
    : Bytes.data * Bytes.data =
  match types, resolve_var st v with
  | [t], v' ->
      (* single-typed: allow range / prefix on ipv4 *)
      (match v' with
       | Nft_ast.Vrange (a, b) -> (bytes_of_typeatom st t a, bytes_of_typeatom st t b)
       | Nft_ast.Vprefix _ when t = "ipv4_addr" -> interval_of_value st KIp4 v'
       | Nft_ast.Vprefix _ when t = "ipv6_addr" -> interval_of_value st KIp6 v'
       | _ -> let b = bytes_of_typeatom st t v' in (b, b))
  | _, Nft_ast.Vconcat vs when L.length vs = L.length types ->
      (* CONCATENATED element (NFT_SET_CONCAT): the kernel ranges EACH field
         independently, so an element is the per-field cross-product of intervals.
         We emit lo = concat of per-field lows, hi = concat of per-field highs;
         a per-field range/CIDR therefore becomes faithfully expressible (it used
         to be refused / silently flattened).  See [concat_set_mem] in Bytes.v. *)
      let iv_of_typeatom t v =
        match resolve_var st v with
        | Nft_ast.Vrange (a, b) -> (bytes_of_typeatom st t a, bytes_of_typeatom st t b)
        | Nft_ast.Vprefix (Nft_ast.Vip4 _, _) when t = "ipv4_addr" ->
            interval_of_value st KIp4 v
        | Nft_ast.Vprefix (Nft_ast.Vip6 _, _) when t = "ipv6_addr" ->
            interval_of_value st KIp6 v
        | Nft_ast.Vprefix _ ->
            raise (Unsupported "CIDR/prefix in concatenated set element for non-ipv4 field")
        | v' -> let b = bytes_of_typeatom st t v' in (b, b) in
      let ivs = L.map2 iv_of_typeatom types vs in
      (* per-field register-slot padding (NFT_SET_CONCAT): each field occupies a
         whole 4-byte slot, field bytes at the front + trailing zero padding. *)
      (L.concat (L.map (fun (lo,_) -> pad_to_slot lo) ivs),
       L.concat (L.map (fun (_,hi) -> pad_to_slot hi) ivs))
  | _ -> raise (Unsupported "set element arity does not match declared type")

(* ---------- match lowering ---------- *)

(* build the anonymous-set env entry for an inline `{...}` set over a single
   field kind, returning its fresh name *)
let intern_anon_set st (k : kind) (elems : Nft_ast.value list) : string =
  let name = fresh st "__set" in
  st.sets <- (name, L.map (interval_of_value st k) elems) :: st.sets;
  name

(* As [intern_anon_set] but encode the elements NETWORK-ORDER (big-endian): used
   for an INTERVAL set over a host-endian field, whose lookup is preceded by a
   `byteorder hton` (see the SEset branch in [lower_match]). *)
let intern_anon_set_be st (k : kind) (elems : Nft_ast.value list) : string =
  let name = fresh st "__set" in
  st.sets <- (name, L.map (interval_of_value_be st k) elems) :: st.sets;
  name

(* build the anonymous-set env entry for a CONCATENATED inline set, where each
   element is a Vconcat matched against [kinds] *)
let intern_anon_concat st (kinds : kind list) (elems : Nft_ast.value list) : string =
  let name = fresh st "__set" in
  (* per-field cross-product element (NFT_SET_CONCAT): lo = concat of per-field
     lows, hi = concat of per-field highs.  A per-field range/CIDR is now
     faithfully expressible (was previously refused). *)
  let enc1 v = match resolve_var st v with
    | Nft_ast.Vconcat vs when L.length vs = L.length kinds ->
        let ivs = L.map2 (fun k v -> interval_of_value st k v) kinds vs in
        (* per-field register-slot padding (NFT_SET_CONCAT); see [pad_to_slot]. *)
        (L.concat (L.map (fun (lo,_) -> pad_to_slot lo) ivs),
         L.concat (L.map (fun (_,hi) -> pad_to_slot hi) ivs))
    | _ -> raise (Unsupported "concatenated set element arity mismatch") in
  st.sets <- (name, L.map enc1 elems) :: st.sets;
  name

(* lower a single match clause into body items (the l4proto dep is handled by the
   caller via the returned dep) *)
let lower_match st (m : Nft_ast.smatch) : dep * Syntax.matchcond =
  let neg = m.Nft_ast.m_rhs.Nft_ast.neg in
  let op  = m.Nft_ast.m_rhs.Nft_ast.op in
  match m.Nft_ast.m_keys with
  | [ (["fib"; sel; _res]) ]
    when (match m.Nft_ast.m_rhs.Nft_ast.payload with
          | Nft_ast.SEvalue (Nft_ast.Vsym ("missing" | "exists")) -> true
          | _ -> false) ->
      (* `fib <sel> <result> missing|exists`: nft loads the fib result with the
         PRESENT flag (a 0/1 boolean) and tests it against 0 —
         `fib ... present => reg ; cmp eq reg 0` for `missing`,
         `cmp neq reg 0` for `exists` (nft --debug=netlink).  The chosen result
         column is irrelevant under the present flag, so we use [FRpresent]. *)
      let exists = (match m.Nft_ast.m_rhs.Nft_ast.payload with
                    | Nft_ast.SEvalue (Nft_ast.Vsym "exists") -> true | _ -> false) in
      let f = Syntax.FFib (sel, Packet.FRpresent) in
      let zero = [0] in   (* FRpresent load_width = 1 byte *)
      let mc = if exists then Syntax.MNeq (f, zero) else Syntax.MEq (f, zero) in
      ([], mc)
  | [ ["exthdr"; proto] ]
    when (match m.Nft_ast.m_rhs.Nft_ast.payload with
          | Nft_ast.SEvalue (Nft_ast.Vsym ("missing" | "exists")) -> true
          | _ -> false) ->
      (* `exthdr <proto> exists|missing`: nft loads the exthdr with the PRESENT
         flag (a 1-byte 0/1) and compares it (golden ip6/exthdr.t.payload:
         `exthdr load ipv6 1b @ H + 0 present => reg 1 ; cmp eq reg 1 0x01`
         for exists, `0x00` for missing).  htype is the exthdr's IPPROTO. *)
      let htype = (match proto with
        | "hbh"  -> 0   | "rt"  -> 43 | "frag" -> 44
        | "dst"  -> 60  | "mh"  -> 135
        | _ -> raise (Unsupported ("exthdr " ^ proto))) in
      let exists = (match m.Nft_ast.m_rhs.Nft_ast.payload with
                    | Nft_ast.SEvalue (Nft_ast.Vsym "exists") -> true | _ -> false) in
      let f = Syntax.FExthdr (Packet.EPipv6, htype, 0, 1, true) in
      let mc = if exists then Syntax.MEq (f, [1]) else Syntax.MEq (f, [0]) in
      ([DNfproto [10]], mc)
  | [ ["tcpopt"; name] ]
    when (match m.Nft_ast.m_rhs.Nft_ast.payload with
          | Nft_ast.SEvalue (Nft_ast.Vsym ("missing" | "exists")) -> true
          | _ -> false) ->
      (* `tcp option <name> exists|missing`: exthdr tcpopt present flag, a 1-byte
         0/1 compared to 1 (exists) / 0 (missing) — golden any/tcpopt.t.payload
         `exthdr load tcpopt 1b @ <optnum> + 0 present => reg 1 ; cmp eq reg 1 0x01`. *)
      let optnum = tcpopt_num name in
      let exists = (match m.Nft_ast.m_rhs.Nft_ast.payload with
                    | Nft_ast.SEvalue (Nft_ast.Vsym "exists") -> true | _ -> false) in
      let f = Syntax.FExthdr (Packet.EPtcpopt, optnum, 0, 1, true) in
      let mc = if exists then Syntax.MEq (f, [1]) else Syntax.MEq (f, [0]) in
      ([], mc)
  | [kp] when (match bitfield_sel kp with Some _ -> true | None -> false) ->
      (* a sub-byte header bitfield (ip dscp / ip6 flowlabel / tcp doff / ...):
         load the byte(s), `& mask`, and compare against value<<shift. *)
      let (f, len, mask, dep, is_dscp) =
        (match bitfield_sel kp with Some x -> x | None -> assert false) in
      let shift = mask_shift mask in
      let raw v = match resolve_var st v with
        | Nft_ast.Vnum n -> n
        | Nft_ast.Vsym s when is_dscp ->
            (match L.assoc_opt s sym_dscp with Some n -> n
             | None -> raise (Unsupported ("dscp value " ^ s)))
        | _ -> raise (Unsupported ("bitfield selector value: " ^ S.concat " " kp)) in
      let zeros = L.init len (fun _ -> 0) in
      let mc = (match m.Nft_ast.m_rhs.Nft_ast.payload with
        | Nft_ast.SEvalue v ->
            let cmpval = bytes_of_int len ((raw v) lsl shift) in
            Syntax.MMasked (f, neg, mask, zeros, cmpval)
        | _ ->
            (* a set/range over a bitfield needs a bitwise-then-lookup/range that
               we do not model faithfully yet; refuse rather than mis-encode. *)
            raise (Unsupported ("bitfield selector set/range: " ^ S.concat " " kp))) in
      (dep, mc)
  | [kp] ->
      let (f, k, dep) = key_field kp in
      let mc = match m.Nft_ast.m_rhs.Nft_ast.payload with
        | Nft_ast.SEset _ when k = KTcpflag ->
            (* `tcp flags { fin, syn, ... }` is a genuine set-membership lookup
               (golden inet/tcp.t.payload:66 `lookup reg 1 set`), distinct from
               the bare comma OR-mask form `tcp flags syn,ack`.  The surface AST
               does not record whether braces were written, so the two are
               ambiguous here; rather than silently pick the wrong encoding we
               refuse the brace/comma set form for tcp flags (the single-value
               bitmask forms below cover the infidelity this guards against). *)
            raise (Unsupported
              "tcp flags set/list form is ambiguous (brace-set vs OR-mask); \
               use a single `tcp flags X` / `tcp flags ! X` / `tcp flags == X`")
        | Nft_ast.SEref name -> Syntax.MConcatSet ([f], neg, name)
        | Nft_ast.SElist elems ->
            (* A BARE COMMA list `ct state new,established,...` is NOT a set: nft's
               expr_evaluate_list (evaluate.c:1854-1888) requires every member to
               have a TYPE_BITMASK basetype (line 1871) and OR-folds them all into a
               single constant (line 1877 mpz_ior), then emits the implicit-bitmask
               test `(field & orMask) != 0` — exactly the single-value KCtstate /
               KTcpflag encoding below, just with the OR of all members.  A BRACE set
               `{ ... }` (SEset) is a different expression -> real lookup.  We refuse
               the list form for non-bitmask selectors, mirroring nft's error. *)
            (match k with
             | KCtstate | KCtstatus | KTcpflag ->
                 let w = width_of_kind k in
                 let zero = L.init w (fun _ -> 0) in
                 let orMask =
                   L.fold_left
                     (fun acc v -> bor acc (enc_atom k (resolve_var st v)))
                     zero elems in
                 (match op with
                  | Nft_ast.Op_implicit -> Syntax.MMasked (f, true,  orMask, zero, zero)
                  | Nft_ast.Op_bang     -> Syntax.MMasked (f, false, orMask, zero, zero)
                  | Nft_ast.Op_eq       -> Syntax.MEq  (f, orMask)
                  | Nft_ast.Op_ne       -> Syntax.MNeq (f, orMask))
             | _ ->
                 raise (Unsupported
                   "comma list rhs is only valid for bitmask selectors \
                    (ct state / tcp flags); use a `{ ... }` set instead"))
        | Nft_ast.SEset elems when host_endian_kind k && set_has_interval st elems ->
            (* INTERVAL set over a HOST-ENDIAN field (e.g. `ct mark { 0x100-0x200 }`):
               this is an ORDERED comparison, so nft inserts a mandatory
               `byteorder reg = hton(reg,4,4)` before the `lookup` and stores the
               interval bounds network-order (golden any/ct.t.payload: an interval
               mark set forces the hton, an exact-element set does not).  We mirror
               the Round-7 direct-range fix on the set path: emit [MSetT] with a
               [TByteorder true w w] transform on the loaded host-endian field and
               big-endian set bounds, so [set_mem] (big-endian lexicographic via
               [data_le]) tests numeric containment.  Without this the LE-stored
               bounds would be compared big-endian -> wrong byte order, wrong verdict. *)
            let w = width_of_kind k in
            Syntax.MSetT (f, [Syntax.TByteorder (true, w, w)], neg,
                          intern_anon_set_be st k elems)
        | Nft_ast.SEset elems -> Syntax.MConcatSet ([f], neg, intern_anon_set st k elems)
        | Nft_ast.SEvalue v when k = KTcpflag ->
            (* tcp_flag_type has .basetype = bitmask_type (proto.c:583-591), and
               the OP_IMPLICIT->OP_EQ rewrite (evaluate.c:2792-2797) does NOT fire
               for it, so a single positive `tcp flags X` stays an implicit
               bitmask test, emitted (golden inet/tcp.t.payload:331-337) as
               `bitwise reg1 = (reg1 & X) ^ 0; cmp neq reg1 0`, i.e. (flags & X)
               != 0 — NOT flags == X.  The four written operators differ:
                 implicit `tcp flags X`   -> (flags & X) != 0   MMasked neg:=true
                 bang     `tcp flags ! X` -> (flags & X) == 0   MMasked neg:=false
                                              (tcp.t:74 `& X == 0`)
                 explicit `tcp flags == X`-> flags == X         MEq  (tcp.t:70)
                 explicit `tcp flags != X`-> flags != X         MNeq (tcp.t:69) *)
            let bits = enc_atom k (resolve_var st v) in
            let zero = [0] in
            (match op with
             | Nft_ast.Op_implicit -> Syntax.MMasked (f, true,  bits, zero, zero)
             | Nft_ast.Op_bang     -> Syntax.MMasked (f, false, bits, zero, zero)
             | Nft_ast.Op_eq       -> Syntax.MEq  (f, bits)
             | Nft_ast.Op_ne       -> Syntax.MNeq (f, bits))
        | Nft_ast.SEvalue v ->
            (match resolve_var st v with
             | Nft_ast.Vrange (a, b) when host_endian_kind k ->
                 (* host-endian field range: nft loads the host-endian value, then
                    `byteorder reg = hton(reg, w, w)` to network order, then a
                    network-order `range eq` (golden ct.t.payload `ct mark
                    0x32-0x45` -> `byteorder hton(4,4)` ; `range eq ...`).  Model
                    it with the hton transform + network-order bounds so the range
                    test is numeric (not a host-endian-byte lexicographic compare). *)
                 let w = width_of_kind k in
                 Syntax.MRangeT (f, [Syntax.TByteorder (true, w, w)], neg,
                                 enc_atom_be k a, enc_atom_be k b)
             | Nft_ast.Vrange (a, b) -> Syntax.MRange (f, neg, enc_atom k a, enc_atom k b)
             | Nft_ast.Vprefix ((Nft_ast.Vip4 bs | Nft_ast.Vip6 bs), len) ->
                 let w = width_of_kind k in let mask = prefix_mask w len in
                 let net = band bs mask in
                 (match (if len > 0 && len < 8 * w && len mod 8 = 0
                         then payload_prefix_field f (len / 8) else None) with
                  | Some f' ->
                      let nb = len / 8 in
                      let bytes = L.filteri (fun i _ -> i < nb) net in
                      if neg then Syntax.MNeq (f', bytes) else Syntax.MEq (f', bytes)
                  | None ->
                      Syntax.MMasked (f, neg, mask, L.init w (fun _ -> 0), net))
             | Nft_ast.Vset elems
               when host_endian_kind k && set_has_interval st elems ->
                 (* a `$var` expanding to an INTERVAL set over a host-endian field:
                    same hton-before-lookup as the inline SEset branch above. *)
                 let w = width_of_kind k in
                 Syntax.MSetT (f, [Syntax.TByteorder (true, w, w)], neg,
                               intern_anon_set_be st k elems)
             | Nft_ast.Vset elems ->        (* a `$var` that expands to a set *)
                 Syntax.MConcatSet ([f], neg, intern_anon_set st k elems)
             | v' when k = KCtstate || k = KCtstatus ->
                 (* ct_state has .basetype = bitmask_type, and the relational
                    evaluator (evaluate.c:2792-2797) rewrites OP_IMPLICIT over a
                    TYPE_BITMASK basetype to OP_EQ for EVERY bitmask type EXCEPT
                    TYPE_CT_STATE.  So a single positive `ct state X` stays an
                    implicit bitmask test, emitted (golden ct.t.payload:35-40) as
                    `bitwise reg1 = (reg1 & X) ^ 0; cmp neq reg1 0`, i.e. it
                    matches iff (state & X) != 0, NOT state == X.  The negated
                    form `ct state != X` is a plain cmp neq (golden
                    ct.t.payload:7-10), which is exactly MNeq. *)
                 let bits = enc_atom k v' in
                 let w = width_of_kind k in
                 let zero = L.init w (fun _ -> 0) in
                 if neg
                 then Syntax.MNeq (f, bits)
                 else Syntax.MMasked (f, true (* CNe vs 0 *), bits, zero, zero)
             | v' -> if neg then Syntax.MNeq (f, enc_atom k v')
                     else Syntax.MEq (f, enc_atom k v'))
      in (dep, mc)
  | kps ->
      (* concatenation: ip daddr . oifname [!=] @set / {set} *)
      let triples = L.map key_field kps in
      let fields = L.map (fun (f,_,_) -> f) triples in
      let kinds  = L.map (fun (_,k,_) -> k) triples in
      let dep = L.concat (L.map (fun (_,_,d) -> d) triples) in
      let name = match m.Nft_ast.m_rhs.Nft_ast.payload with
        | Nft_ast.SEref nm -> nm
        | Nft_ast.SEset elems -> intern_anon_concat st kinds elems
        | Nft_ast.SEvalue (Nft_ast.Vconcat _ as v) -> intern_anon_concat st kinds [v]
        | Nft_ast.SElist _ -> raise (Unsupported
            "bare comma list is not valid for a concatenated selector; use `{ ... }`")
        | Nft_ast.SEvalue _ -> raise (Unsupported "concatenated match needs a set/ref rhs")
      in (dep, Syntax.MConcatSet (fields, neg, name))

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
let nat_l3_family = function "ip6" -> "ip6" | "inet" -> "inet" | _ -> "ip"

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
    nat_kind = "masq"; nat_family = nat_l3_family family; nat_flags = flags }

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
             nat_kind = kind; nat_family = "ip"; nat_flags = f }
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
    nat_extra = ne; nat_kind = "redir"; nat_family = ""; nat_flags = f }

(* In a multi-L3 family an inet chain sees both IPv4 and IPv6 packets, so nft
   guards every `ip`/`ip6` payload match with `meta nfproto == {2|10}`.  A
   single-L3 family (ip/ip6/arp) sees only one network protocol, so nft emits no
   such guard.  (bridge/netdev guard the network layer with `meta protocol`
   (ethertype) instead and are out of scope of this nfproto fix.) *)
let family_is_inet = function "inet" -> true | _ -> false

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

(* A bridge/netdev chain is an L2 chain that can see any ethertype, so nft pins an
   ip/ip6 network match with the LINK-layer ethertype (`meta protocol ==`) rather
   than the NFPROTO nfproto guard it uses in inet.  Map the nfproto byte carried by
   [DNfproto] to that ethertype: IPv4 (2) -> 0x0800, IPv6 (10) -> 0x86dd. *)
let family_is_l2 = function "bridge" | "netdev" -> true | _ -> false
let nfproto_ethertype = function
  | [2]  -> Some [0x08; 0x00]      (* ETH_P_IP   *)
  | [10] -> Some [0x86; 0xdd]      (* ETH_P_IPV6 *)
  | _    -> None

let lower_rule st ~family (clauses : Nft_ast.clause list) : Syntax.rule =
  let body = ref [] in
  let deps = ref [] in       (* (field, value) deps already emitted, for dedup *)
  let verdict = ref Verdict.Continue in
  let vmap = ref None in
  let nat = ref None in   (* set for `masquerade` (a source-NAT terminal) *)
  let tproxy = ref None in   (* set for `tproxy` (a transparent-proxy terminal) *)
  let push bi = body := bi :: !body in
  let push_dep fld pv =
    if not (L.mem (fld, pv) !deps) then
      (push (Syntax.BMatch (Syntax.MEq (fld, pv))); deps := (fld, pv) :: !deps)
  in
  let ensure_dep1 = function
    | DL4 pv -> push_dep Syntax.FMetaL4proto pv
    | DNfproto pv ->
        if family_is_inet family then push_dep Syntax.FMetaNfproto pv
        else if family_is_l2 family then
          (match nfproto_ethertype pv with
           | Some et -> push_dep Syntax.FMetaProtocol et
           | None -> ())
    | DL2proto et -> if family_is_l2 family then push_dep Syntax.FMetaProtocol et
    | DIiftype et -> if family <> "bridge" then push_dep Syntax.FMetaIiftype et
    | DIcmpType ty ->
        (* ICMP `mtu`/`gateway` are union members only valid for a particular
           icmp type; nft prepends an implicit `icmp type == <ty>` guard (payload
           load 1b @ transport+0 ; cmp eq <ty>) before the union-field load
           (golden ip/icmp.t.payload: `icmp mtu` => type 3, `icmp gateway` => 5). *)
        push_dep Syntax.FIcmpType [ty]
    | DEther pv ->
        (* In netdev nft prepends a `meta iiftype == ARPHRD_ETHER` guard, but the
           frontend's host-endian iiftype immediate renders in the wrong byte
           order vs the golden (0x0100 not 0x0001), so rather than emit an
           unverified guard we honestly refuse vlan matches in netdev; bridge
           (the tested family) needs only the ether-type guard. *)
        if family = "netdev" then
          raise (Unsupported "vlan match in netdev family (iiftype guard byte-order)");
        push_dep Syntax.FEtherType pv
  in
  (* materialise deps in order (nfproto guard pushed before l4proto guard) *)
  let ensure_dep ds = L.iter ensure_dep1 ds in
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
         | "icmp" :: _   -> ensure_dep [DNfproto [2]]
         | "icmpv6" :: _ -> ensure_dep [DNfproto [10]]
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
           Register the explicit (field,value) in the dedup set. *)
        let reg fk pv = if not (L.mem (fk, pv) !deps) then deps := (fk, pv) :: !deps in
        (match mc with
         | Syntax.MEq (fld, pv) ->
             (match fld with
              | Syntax.FMetaL4proto | Syntax.FMetaNfproto | Syntax.FMetaProtocol
              | Syntax.FMetaIiftype | Syntax.FEtherType -> reg fld pv
              (* `ip protocol N` fixes the packet's L4 protocol to N, so nft does
                 NOT re-emit the `meta l4proto == N` guard a later tcp/udp/icmp
                 selector would otherwise carry (golden icmpX.t: `ip protocol icmp
                 icmp type ...` has no l4proto load).  Discharge that dep. *)
              | Syntax.FIp4Protocol -> reg Syntax.FMetaL4proto pv
              | _ -> ())
         | _ -> ())
    | Nft_ast.CBitmatch (kp, op, mask, r) ->
        (* `<field> and|or|xor <m> <relop> <v>` -> nft's `bitwise reg =
           (reg & mask) ^ xor` then a compare (Syntax.MMasked semantics:
           `((field & mask) ^ xor) cmp v`).  nft realises the three ops as:
             and m : mask=m,   xor=0        or m : mask=~m, xor=m
             xor m : mask=~0,  xor=m
           (golden any/meta.t.payload `meta mark and 0x3`, any/ct.t.payload
           `ct mark or 0x23`).  All bytes are in the field's own byte order
           ([enc_atom]), so the byte-wise complement matches nft's register
           display (host-endian mark: ~0x23 -> 0xffffffdc). *)
        let (f, k, dep) = key_field kp in
        ensure_dep dep;
        let w = width_of_kind k in
        let mbytes = enc_atom k (resolve_var st mask) in
        let vbytes = (match r.Nft_ast.payload with
          | Nft_ast.SEvalue v -> enc_atom k (resolve_var st v)
          | _ -> raise (Unsupported "bitwise mask match needs a single-value rhs")) in
        let comp = L.map (fun x -> x lxor 0xff) in
        let ones = L.init w (fun _ -> 0xff) and zeros = L.init w (fun _ -> 0) in
        let (mask', xorb) = match op with
          | "and" -> (mbytes, zeros)
          | "or"  -> (comp mbytes, mbytes)
          | "xor" -> (ones, mbytes)
          | _ -> raise (Unsupported ("bitwise op " ^ op)) in
        push (Syntax.BMatch (Syntax.MMasked (f, r.Nft_ast.neg, mask', xorb, vbytes)))
    | Nft_ast.CVmap (kps, entries) ->
        if !vmap <> None then raise (Unsupported "more than one verdict map in a rule");
        let triples = L.map key_field kps in
        let fields = L.map (fun (f,_,_) -> f) triples in
        let kinds  = L.map (fun (_,k,_) -> k) triples in
        ensure_dep (L.concat (L.map (fun (_,_,d) -> d) triples));
        let name = fresh st "__map" in
        let ents = (match kinds with
          | [k] ->
              (* single-field vmap key: a range/prefix becomes a closed interval
                 [lo,hi] (a point key is the degenerate [b,b]); the kernel rbtree
                 set is NFT_SET_INTERVAL | NFT_SET_MAP. *)
              L.map (fun (v, sv) ->
                (interval_of_value st k v, lower_verdict sv)) entries
          | _ ->
              (* CONCATENATED-key vmap (`ip protocol . th dport vmap {tcp.22:...}`):
                 the lookup key the model builds is the FLAT byte concatenation of
                 the per-field values [List.concat (map field_value vm_fields)] —
                 raw field bytes, NOT register-slot padded (assoc_verdict tests the
                 flat key with data_in_iv).  So each element's stored [lo,hi] bound
                 is the FLAT concatenation of the per-field encodings, matching the
                 model's key byte-for-byte. *)
              L.map (fun (v, sv) ->
                let per_field = match resolve_var st v with
                  | Nft_ast.Vconcat vs when L.length vs = L.length kinds ->
                      L.map2 (fun k v -> interval_of_value st k v) kinds vs
                  | _ -> raise (Unsupported
                           "concatenated vmap element arity does not match the key") in
                let lo = L.concat (L.map fst per_field) in
                let hi = L.concat (L.map snd per_field) in
                ((lo, hi), lower_verdict sv)) entries) in
        st.vmaps <- (name, ents) :: st.vmaps;
        (match fields with
         | [f] -> vmap := Some { Syntax.vm_fields = []; vm_keyf = Some (f, []); vm_name = name }
         | _   -> vmap := Some { Syntax.vm_fields = fields; vm_keyf = None; vm_name = name })
    | Nft_ast.CVmapRef (kps, name) ->
        (* `<key>[.<key>...] vmap @name`: entries come from the named map in the env *)
        if !vmap <> None then raise (Unsupported "more than one verdict map in a rule");
        let triples = L.map key_field kps in
        let fields = L.map (fun (f,_,_) -> f) triples in
        ensure_dep (L.concat (L.map (fun (_,_,d) -> d) triples));
        (match fields with
         | [f] -> vmap := Some { Syntax.vm_fields = []; vm_keyf = Some (f, []); vm_name = name }
         | _   -> vmap := Some { Syntax.vm_fields = fields; vm_keyf = None; vm_name = name })
    | Nft_ast.CStmt (Nft_ast.StLimit (r, u, over, burst, bytes)) ->
        push (Syntax.BMatch (Syntax.MLimit (limit_spec r u over burst bytes)))
    | Nft_ast.CStmt s ->
        if stmt_is_terminal_accept s then verdict := Verdict.Accept;
        (match s with
         | Nft_ast.StMasquerade fs -> nat := Some (masq_spec ~family ~flags:(nat_flags_of fs))
         | Nft_ast.StSnat (Some v, port, fs) -> nat := addr_nat_spec st "snat" ~port ~flags:(nat_flags_of fs) v
         | Nft_ast.StDnat (Some v, port, fs) -> nat := addr_nat_spec st "dnat" ~port ~flags:(nat_flags_of fs) v
         | Nft_ast.StSnat (None, Some port, fs) -> nat := Some (portonly_nat_spec ~family "snat" ~flags:(nat_flags_of fs) port)
         | Nft_ast.StDnat (None, Some port, fs) -> nat := Some (portonly_nat_spec ~family "dnat" ~flags:(nat_flags_of fs) port)
         | Nft_ast.StRedirect (port, fs) -> nat := Some (redir_spec ~flags:(nat_flags_of fs) port)
         | Nft_ast.StTproxy (qual, addr, port) ->
             tproxy := Some (tproxy_spec st ~family qual addr port)
         | _ -> ());
        (match lower_stmt st s with Some st' -> push (Syntax.BStmt st') | None -> ()))
    clauses;
  { Syntax.r_body = L.rev !body; r_verdict = !verdict; r_vmap = !vmap;
    r_nat = !nat; r_tproxy = !tproxy; r_fwd = None; r_queue = None; r_after = [] }

(* ---------- declarations ---------- *)

let lower_setdecl st (sd : Nft_ast.setdecl) : unit =
  if sd.Nft_ast.sd_is_map then begin
    (* a verdict map if its elements carry verdict data; an empty declaration is
       registered as an empty value map (its contents arrive at runtime) *)
    let is_vmap = L.exists (fun (_, d) -> match d with
      | Some _ -> true | None -> false) sd.Nft_ast.sd_elements in
    if is_vmap then
      let ents = L.map (fun (key, d) ->
        (* keep the FULL [lo,hi] interval key so range/prefix vmap keys do an
           interval lookup (NFT_SET_INTERVAL | NFT_SET_MAP), not exact-only. *)
        (interval_of_decl_elem st sd.Nft_ast.sd_type key,
         match d with Some v -> lower_verdict v | None -> Verdict.Continue))
        sd.Nft_ast.sd_elements in
      st.vmaps <- (sd.Nft_ast.sd_name, ents) :: st.vmaps
    else if sd.Nft_ast.sd_elements = [] then
      st.maps <- (sd.Nft_ast.sd_name, []) :: st.maps
    else raise (Unsupported "value maps (non-verdict map data) not yet lowered")
  end else begin
    let elems = L.map (fun (v, _) -> interval_of_decl_elem st sd.Nft_ast.sd_type v)
                  sd.Nft_ast.sd_elements in
    st.sets <- (sd.Nft_ast.sd_name, elems) :: st.sets
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
  let sets = st.sets and vmaps = st.vmaps and maps = st.maps in
  { Packet.e_set  = (fun n -> match L.assoc_opt n sets  with Some e -> e | None -> []);
    e_vmap        = (fun n -> match L.assoc_opt n vmaps with Some e -> e | None -> []);
    e_map         = (fun n -> match L.assoc_opt n maps  with Some e -> e | None -> []);
    e_routes = []; e_rt = (fun _ -> []); e_ifaddrs = (fun _ -> []); e_ifaddrs6 = (fun _ -> []);
    e_limit = (fun _ -> 1); e_quota = (fun _ -> 1); e_connlimit = (fun _ -> []);
    e_ct = (fun _ _ -> []); e_nat = (fun _ -> None); e_numgen = (fun _ -> 0) }

let lower (f : Nft_ast.sfile) : parsed =
  let st = { defines = Hashtbl.create 16; sets = []; vmaps = []; maps = [];
             counter = 0 } in
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
    p_sets = L.rev st.sets; p_vmaps = L.rev st.vmaps; p_maps = L.rev st.maps }

(* ---------- lookups ---------- *)

let find_table p name = L.find_opt (fun (_, n, _) -> n = name) p.p_tables
let chains_of p ~table = match find_table p table with
  | Some (_, _, chains) -> chains
  | None -> raise (Unsupported ("no such table: " ^ table))
let find_chain p ~table ~chain = match L.assoc_opt chain (chains_of p ~table) with
  | Some c -> c
  | None -> raise (Unsupported (Printf.sprintf "no chain %s in table %s" chain table))
