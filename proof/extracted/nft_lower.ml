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
(* TCP flag bits (the single byte at transport header + 13).  proto.c:
   TCPHDR_FIN 0x01 .. TCPHDR_CWR 0x80.  A comma/`|` list ORs the bits. *)
let sym_tcpflag = [
  "fin",0x01; "syn",0x02; "rst",0x04; "psh",0x08;
  "ack",0x10; "urg",0x20; "ecn",0x40; "cwr",0x80;
]
let sym_icmp = [
  "echo-reply",[0]; "destination-unreachable",[3]; "redirect",[5];
  "echo-request",[8]; "router-advertisement",[9]; "router-solicitation",[10];
  "time-exceeded",[11]; "parameter-problem",[12]; "timestamp-request",[13];
  "timestamp-reply",[14];
]
let sym_icmpv6 = [
  "destination-unreachable",[1]; "packet-too-big",[2]; "time-exceeded",[3];
  "parameter-problem",[4]; "echo-request",[128]; "echo-reply",[129];
  "mld-listener-query",[130]; "mld-listener-report",[131];
  "nd-router-solicit",[133]; "nd-router-advert",[134];
  "nd-neighbor-solicit",[135]; "nd-neighbor-advert",[136]; "nd-redirect",[137];
]
let sym_pkttype = [ "host",[0]; "unicast",[0]; "broadcast",[1]; "multicast",[2];
                    "other",[3]; "otherhost",[3]; ]
(* /etc/services subset (extend as corpora demand). *)
let sym_service = [
  "ftp-data",20; "ftp",21; "ssh",22; "telnet",23; "smtp",25; "domain",53;
  "bootps",67; "bootpc",68; "tftp",69; "http",80; "www",80; "pop3",110;
  "ntp",123; "imap",143; "snmp",161; "bgp",179; "https",443; "submission",587;
  "imaps",993; "pop3s",995; "mysql",3306; "rdp",3389; "nfs",2049;
  "syncthing",22000; "wireguard",51820; "openvpn",1194;
]

let lookup ctx tbl s =
  match L.assoc_opt s tbl with
  | Some b -> b
  | None -> raise (Unsupported (Printf.sprintf "symbolic constant %S (%s)" s ctx))

(* ---------- field kinds: how a value is encoded for a given selector ---------- *)

type kind =
  | KIfname | KIfindex | KIp4 | KIp6 | KPort | KL4proto | KNfproto | KEthertype
  | KCtstate | KMark | KIcmp | KIcmpv6 | KPkttype | KFibType | KTcpflag | KNum of int
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
  | KFibType, Nft_ast.Vsym s -> lookup "fib type" sym_fibtype s
  | KFibType, Nft_ast.Vnum n -> bytes_of_int_le 4 n
  | KNum w, Nft_ast.Vnum n -> bytes_of_int w n
  | KNumLe w, Nft_ast.Vnum n -> bytes_of_int_le w n
  | _, Nft_ast.Vvar n -> raise (Unsupported ("unresolved $" ^ n))
  | _ -> raise (Unsupported "value/selector type mismatch")

(* the byte width a kind compares at (for building a prefix mask) *)
let width_of_kind = function
  | KIp4 -> 4 | KIp6 -> 16 | KPort | KEthertype -> 2
  | KCtstate | KMark | KIfindex | KFibType -> 4 | KNum w -> w | KNumLe w -> w | _ -> 1

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
type dep1 = DL4 of Bytes.data | DNfproto of Bytes.data
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
  (* icmp/icmpv6 are NETWORK-protocol-LINKED L4 protocols: nft emits the nfproto
     guard BEFORE the l4proto guard (payload.c proto_icmp/proto_icmp6 are linked
     to the IPv4/IPv6 network bases).  Order matches the golden byte sequence. *)
  | "icmp" -> [DNfproto [2]; DL4 [1]]
  | "icmpv6" -> [DNfproto [10]; DL4 [58]]
  | _ -> []

let key_field (kp : Nft_ast.keypath) : Syntax.field * kind * dep =
  let none = [] in
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
  | ["ether"; "saddr"] -> (Syntax.FEtherSaddr, KNum 6, none)
  | ["ether"; "daddr"] -> (Syntax.FEtherDaddr, KNum 6, none)
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
  | ["ct"; "mark"]       -> (Syntax.FCtMark, KMark, none)
  | _ -> raise (Unsupported ("selector: " ^ S.concat " " kp))

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
  | Nft_ast.SVqueue -> Verdict.Queue (0, 0, false, false)
  | Nft_ast.SVreject _ -> Verdict.Reject (0, 0)

(* ---------- element encoding (single field & declared concat type) ---------- *)

(* encode a value into one interval [lo,hi] for a single-field set *)
let interval_of_value st (k : kind) (v : Nft_ast.value) : Bytes.data * Bytes.data =
  match resolve_var st v with
  | Nft_ast.Vrange (a, b) -> (enc_atom k a, enc_atom k b)
  | Nft_ast.Vprefix (Nft_ast.Vip4 b, len) ->
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
  | Nft_ast.Vprefix (Nft_ast.Vip4 b, len) ->
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
             | KCtstate | KTcpflag ->
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
             | Nft_ast.Vprefix (Nft_ast.Vip4 bs, len) ->
                 let w = width_of_kind k in let mask = prefix_mask w len in
                 Syntax.MMasked (f, neg, mask, L.init w (fun _ -> 0), band bs mask)
             | Nft_ast.Vset elems
               when host_endian_kind k && set_has_interval st elems ->
                 (* a `$var` expanding to an INTERVAL set over a host-endian field:
                    same hton-before-lookup as the inline SEset branch above. *)
                 let w = width_of_kind k in
                 Syntax.MSetT (f, [Syntax.TByteorder (true, w, w)], neg,
                               intern_anon_set_be st k elems)
             | Nft_ast.Vset elems ->        (* a `$var` that expands to a set *)
                 Syntax.MConcatSet ([f], neg, intern_anon_set st k elems)
             | v' when k = KCtstate ->
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

let lower_stmt st (s : Nft_ast.sstmt) : Syntax.stmt option =
  match s with
  | Nft_ast.StComment _ -> None              (* metadata; no verdict/bytecode effect *)
  | Nft_ast.StCounter -> Some (Syntax.SCounter (0, 0))
  | Nft_ast.StLog opts -> Some (Syntax.SLog opts)
  | Nft_ast.StLimit _ ->
      (* `limit` is a matchcond (MLimit), not a statement; lower_rule intercepts
         StLimit before reaching here, so this is unreachable. *)
      raise (Unsupported "limit handled as a match, not a statement")
  | Nft_ast.StMasquerade | Nft_ast.StSnat _ | Nft_ast.StDnat _ ->
      (* terminal NAT: the single-packet model treats it as a terminal Accept *)
      None
  | Nft_ast.StMetaSet (k, v) ->
      let key = meta_key k in
      Some (Syntax.SMetaSet (key, Syntax.VImm (enc_atom (meta_set_kind key) (resolve_var st v))))
  | Nft_ast.StCtSet (k, v) ->
      let key = ct_key k in
      Some (Syntax.SCtSet (key, Syntax.VImm (enc_atom (ct_set_kind key) (resolve_var st v))))

(* does a statement force a terminal Accept (NAT)? *)
let stmt_is_terminal_accept = function
  | Nft_ast.StMasquerade | Nft_ast.StSnat _ | Nft_ast.StDnat _ -> true | _ -> false

let limit_spec rate unit_ over : Packet.limit_spec =
  let u = match unit_ with
    | "second"->0 | "minute"->1 | "hour"->2 | "day"->3 | "week"->4
    | _ -> raise (Unsupported ("limit unit " ^ unit_)) in
  (* bit 0 of ls_flags = NFT_LIMIT_F_INV ("over"); the data-plane semantics XOR
     the under/not-exceeded test with this bit (Semantics.v eval_matchcond_body). *)
  { Packet.ls_rate = rate; ls_unit = u; ls_burst = 5; ls_bytes = false;
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
let masq_spec ~family : Syntax.nat_spec =
  { Syntax.nat_imms = []; nat_field = None; nat_map = None; nat_src = None;
    nat_kind = "masq"; nat_family = nat_l3_family family; nat_amin = None;
    nat_amax = None; nat_pmin = None; nat_pmax = None; nat_flags = 0 }

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
let addr_nat_spec st kind ?(port=None) (v : Nft_ast.value) : Syntax.nat_spec option =
  match resolve_var st v with
  | Nft_ast.Vip4 b ->
      Some { Syntax.nat_imms = [(1, b)]; nat_field = None; nat_map = None;
             nat_src = None; nat_kind = kind; nat_family = "ip";
             nat_amin = None; nat_amax = None; nat_pmin = port; nat_pmax = port;
             nat_flags = 0 }
  | _ -> None   (* unresolvable / non-literal target: stay a bare terminal Accept *)

(* a PORT-ONLY `snat to :<port>` / `dnat to :<port>` NAT spec: NO address operand
   (nat_imms = [], nat_field/map/src = None), only the L4 proto range.  The kernel
   sets only NFTNL_EXPR_NAT_REG_PROTO_MIN/MAX (not the addr register), so
   nft_nat_eval rewrites ONLY the L4 port and leaves the L3 address unchanged
   (nft_nat.c:114/120 — two independent register guards).  In the model this is a
   nat_spec with nat_has_addr = false, so apply_nat preserves the address and
   apply_nat_port rewrites the port. *)
let portonly_nat_spec ~family kind (port : int) : Syntax.nat_spec =
  { Syntax.nat_imms = []; nat_field = None; nat_map = None; nat_src = None;
    nat_kind = kind; nat_family = nat_l3_family family; nat_amin = None;
    nat_amax = None; nat_pmin = Some port; nat_pmax = Some port; nat_flags = 0 }

(* In a multi-L3 family an inet chain sees both IPv4 and IPv6 packets, so nft
   guards every `ip`/`ip6` payload match with `meta nfproto == {2|10}`.  A
   single-L3 family (ip/ip6/arp) sees only one network protocol, so nft emits no
   such guard.  (bridge/netdev guard the network layer with `meta protocol`
   (ethertype) instead and are out of scope of this nfproto fix.) *)
let family_is_inet = function "inet" -> true | _ -> false

let lower_rule st ~family (clauses : Nft_ast.clause list) : Syntax.rule =
  let body = ref [] in
  let deps = ref [] in       (* (field, value) deps already emitted, for dedup *)
  let verdict = ref Verdict.Continue in
  let vmap = ref None in
  let nat = ref None in   (* set for `masquerade` (a source-NAT terminal) *)
  let push bi = body := bi :: !body in
  let push_dep fld pv =
    if not (L.mem (fld, pv) !deps) then
      (push (Syntax.BMatch (Syntax.MEq (fld, pv))); deps := (fld, pv) :: !deps)
  in
  let ensure_dep1 = function
    | DL4 pv -> push_dep Syntax.FMetaL4proto pv
    | DNfproto pv -> if family_is_inet family then push_dep Syntax.FMetaNfproto pv
  in
  (* materialise deps in order (nfproto guard pushed before l4proto guard) *)
  let ensure_dep ds = L.iter ensure_dep1 ds in
  L.iter (fun (cl : Nft_ast.clause) ->
    match cl with
    | Nft_ast.CVerdict v -> verdict := lower_verdict v
    | Nft_ast.CMatch m ->
        let (dep, mc) = lower_match st m in
        ensure_dep dep; push (Syntax.BMatch mc)
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
    | Nft_ast.CStmt (Nft_ast.StLimit (r, u, over)) ->
        push (Syntax.BMatch (Syntax.MLimit (limit_spec r u over)))
    | Nft_ast.CStmt s ->
        if stmt_is_terminal_accept s then verdict := Verdict.Accept;
        (match s with
         | Nft_ast.StMasquerade -> nat := Some (masq_spec ~family)
         | Nft_ast.StSnat (Some v, port) -> nat := addr_nat_spec st "snat" ~port v
         | Nft_ast.StDnat (Some v, port) -> nat := addr_nat_spec st "dnat" ~port v
         | Nft_ast.StSnat (None, Some port) -> nat := Some (portonly_nat_spec ~family "snat" port)
         | Nft_ast.StDnat (None, Some port) -> nat := Some (portonly_nat_spec ~family "dnat" port)
         | _ -> ());
        (match lower_stmt st s with Some st' -> push (Syntax.BStmt st') | None -> ()))
    clauses;
  { Syntax.r_body = L.rev !body; r_verdict = !verdict; r_vmap = !vmap;
    r_nat = !nat; r_tproxy = None; r_fwd = None; r_queue = None; r_after = [] }

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
  : (string * Syntax.chain) * (string * int) option =
  let hookinfo = L.fold_left (fun acc -> function
    | Nft_ast.ITypeHook { hook; priority; _ } -> Some (hook, priority)
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
  (* per table: the base-chain hook registrations (chain-name, hook, priority),
     in source order.  Empty for tables with no base chains. *)
  p_hooks  : (string * string * (string * string * int) list) list;
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
          | Some (hook, prio) -> Some (cname, hook, prio)
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
