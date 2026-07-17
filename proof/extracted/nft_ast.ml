(* Nft_ast: the SURFACE syntax tree produced by the Menhir parser.

   An untrusted, faithful mirror of the `.nft` text — close to what the user
   wrote, before nft's lowering (define expansion, implicit-dependency insertion,
   anonymous-set allocation, symbolic-constant resolution).  Nft_inject turns it
   into the *trusted* Syntax AST (`Syntax.chain` + `Packet.env`) the proofs are
   stated about; keeping the two apart isolates all the divergence-prone
   "act like nft's frontend" logic in one untrusted place (see TODO 9 in
   ../DEVELOPMENT.md).

   The grammar parses the real structure — named-set declarations, defines,
   concatenations, named-set references, ranges/prefixes, negation, the common
   statement vocabulary — WITHOUT inlining or pre-substituting anything: defines
   stay symbolic (`Vvar`), named sets stay references (`SEref`), set contents stay
   in their declarations.  All of that resolution happens, explicitly, in
   Nft_inject. *)

(* An IPv6 literal, carried UN-expanded: its colon groups, split at the single
   `::` zero-run (if any).  A group is a 16-bit hex value ([Ip6_g16], 0..0xffff)
   or an embedded trailing IPv4 tail ([Ip6_g4], its already-grouped octets from
   `::ffff:1.2.3.4`).  The lexer does only numeral parsing + octet grouping; the
   big-endian 16-bit split and the `::` zero-fill are done in verified Coq
   ([Surface.Ast.sip6_bytes]), never here — see nft_inject.ml. *)
type ip6grp = Ip6_g16 of int | Ip6_g4 of int list
type ip6lit = { il_left : ip6grp list; il_right : ip6grp list option }

(* A literal/expression value as written.  Resolution of its *bytes* is deferred
   to Nft_inject because it depends on the selector it appears under (a port is 2
   bytes, an ifname is ASCII, `established` is a 4-byte conntrack-state word). *)
type value =
  | Vnum    of int                 (* decimal or 0x-hex integer literal *)
  | Vsym    of string              (* a bareword: symbolic constant / service / ifname *)
  | Vstr    of string              (* a double-quoted string, e.g. "eth0" *)
  | Vip4    of int list            (* a dotted IPv4 literal, already 4 bytes *)
  | Vip6    of ip6lit              (* an IPv6 literal, UN-expanded groups (see above) *)
  | Vmac    of int list            (* a MAC literal, 6 bytes, e.g. aa:bb:cc:dd:ee:ff *)
  | Vvar    of string              (* a `$name` reference to a `define` *)
  | Vprefix of value * int         (* a CIDR prefix, e.g. 192.168.50.0/24 *)
  | Vrange  of value * value       (* an inclusive range, e.g. 29811-29814 *)
  | Vconcat of value list          (* a concatenated value, e.g. 192.168.51.20 . inc-budge *)
  | Vset    of value list          (* a `define`d set value, e.g. { $a, $b } *)

type verdict =
  | SVaccept
  | SVdrop
  | SVcontinue
  | SVreturn
  | SVjump of string
  | SVgoto of string
  | SVqueue of int * int * bool * bool  (* `queue [num lo[-hi]] [bypass] [fanout]` *)
  | SVreject of string             (* `reject [with ...]`; opts kept verbatim *)

(* The right-hand side of a match: a single value/range/prefix, an inline
   (anonymous) set, or a reference to a named set/map (`@name`). *)
type setexpr =
  | SEvalue of value
  | SEset   of value list          (* `{ a, b, ... }` braces: real set-membership lookup *)
  | SElist  of value list          (* `a, b, ...` bare commas: OR-fold for bitmask selectors *)
  | SEref   of string              (* @name *)

(* The relational operator a match was WRITTEN with.  nftables treats these
   differently for bitmask-basetype selectors (tcp flags, ct state): an IMPLICIT
   comparison stays a bitmask test `(field & X) != 0`, an explicit `==`/`!=` is an
   exact equality/inequality, and a leading `!` (Op_bang) is `(field & X) == 0`.
   For non-bitmask selectors all four collapse to the [neg] flag (eq vs neq). *)
type relop = Op_implicit | Op_eq | Op_ne | Op_bang

(* a match's rhs: the operator it was written with, an optional negation (derived
   from the operator: `!=` or a leading `!`), and the value/set payload. *)
type rhs = { op : relop; neg : bool; payload : setexpr }

(* A selector key path, e.g. ["tcp";"dport"], ["meta";"obrname"], ["oifname"]. *)
type keypath = string list

(* A match condition as written: a concatenation of one or more selector keys
   (`ip daddr . oifname` is two), then its right-hand side. *)
type smatch = { m_keys : keypath list; m_rhs : rhs }

(* Named stateful objects (mirror of Coq Ast.sobjkind).  A rule references one
   by name (`counter name X`); the injection carries the kind so the verified
   typechecker can check declared-existence + kind agreement. *)
type sobjkind =
  | OKcounter | OKquota | OKlimit | OKcthelper
  | OKcttimeout | OKctexpect | OKsecmark | OKsynproxy

(* Verdict-neutral / terminal action statements that are not plain verdicts. *)
type sstmt =
  | StComment   of string
  | StCounter   of int * int       (* `counter [packets N bytes N]`; initial values *)
  | StObjref    of sobjkind * string
                          (* `counter name X` / `quota name X` / `ct helper set X`
                             / `limit name X` / `synproxy name X` *)
  | StLog       of string          (* options string (e.g. the prefix), verbatim *)
  | StLimit     of int * string * bool * int * bool
                          (* rate, time-unit, over/invert, burst, is-byte-rate;
                             byte-rate values are already scaled to bytes *)
  | StMasquerade of string list                (* `masquerade [random,...]` *)
  | StSnat      of value option * int option * string list  (* `snat to <addr>[:<port>] [flags]` *)
  | StDnat      of value option * int option * string list  (* `dnat to <addr>[:<port>] [flags]` *)
  | StRedirect  of int option * string list    (* `redirect [to :<port>] [flags]` *)
  | StTproxy    of string * value option * int option
                          (* `tproxy [ip|ip6] to <addr>[:<port>]` (fam, addr, port) *)
  | StMetaSet   of string * value  (* `meta <k> set v` / `mark set v` (k="mark") *)
  | StCtSet     of string * value  (* `ct <k> set v` *)
  | StNotrack                      (* `notrack` (disable conntrack for the packet) *)

type clause =
  | CMatch   of smatch
  | CVmap    of keypath list * (value * verdict) list
                          (* `<key> [. <key> ...] vmap { v : verdict, ... }`; the
                             keys list has length >1 for a CONCATENATED-key vmap
                             (`ip protocol . th dport vmap {tcp.22:accept,...}`) *)
  | CVmapRef of keypath list * string              (* `<key>[.<key>...] vmap @named_map` *)
  | CVerdict of verdict
  | CStmt    of sstmt
  | CObjrefMap of sobjkind * keypath list * (value * string) list
                          (* `counter name <key> map { v : "obj" }` *)
  | CBitmatch of keypath * string * value * rhs
                          (* `<sel> and|or|xor <mask> <relop> <val>`, e.g.
                             `meta mark and 0x3 == 0x1`; nft lowers this to a
                             bitwise `(field & m) ^ x` then a compare *)

type srule = clause list

(* A named-set / named-map declaration inside a table. *)
type setdecl = {
  sd_name     : string;
  sd_is_map   : bool;              (* `map` (key:value) vs `set` *)
  sd_type     : string list;       (* the concatenated key type, e.g. ["ipv4_addr";"ifname"] *)
  sd_flags    : string list;       (* `flags constant`, `flags interval`, ... *)
  sd_elements : (value * verdict option) list;
                                   (* element, and (for a map/vmap) its data/verdict *)
}

type chain_item =
  | ITypeHook of { ct_type : string; hook : string; priority : int }
  | IPolicy   of verdict
  | IRule     of srule

type schain = { sc_name : string; sc_items : chain_item list }

type table_item =
  | TChain of schain
  | TSet   of setdecl
  | TObj   of string * sobjkind    (* a named stateful object (ct helper / secmark /
                                       counter / limit / quota ...): its contents are
                                       parsed structurally; the injection retains the
                                       name+kind for reference checking *)

type stable = { st_family : string; st_name : string; st_items : table_item list }

(* Configuration-management operations (delete / destroy / flush).  These are
   applied, in file order, by the UNVERIFIED driver (Nft_config) to the parsed
   config BEFORE it is handed to the verified injection/lowering — nft evaluates
   them as imperative ruleset edits, not as installed rules.  `delete` errors on
   a missing entity; `destroy` is delete-if-exists; `flush` empties. *)
type config_target =
  | CTtable   of string                  (* table NAME (family folded for our model) *)
  | CTchain   of string * string         (* table, chain *)
  | CTruleset                            (* the whole ruleset *)

type config_op =
  | OpDelete  of config_target
  | OpDestroy of config_target
  | OpFlush   of config_target

(* A whole file: defines (collected), the tables, and config ops. *)
type toplevel =
  | TopDefine  of string * value
  | TopTable   of stable
  | TopInclude of string           (* `include "path"` — expanded by the driver *)
  | TopOp      of config_op        (* delete/destroy/flush — driver-applied *)

type sfile = toplevel list
