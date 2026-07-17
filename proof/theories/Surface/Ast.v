(** * Surface.Ast: the UNTYPED surface tree, in Coq.

    A constructor-for-constructor mirror of the Menhir parser's output type
    ([extracted/nft_ast.ml]) — the `.nft` text as written, BEFORE any of nft's
    frontend behaviour (define expansion, symbol resolution, byte encoding,
    implicit-dependency insertion).  This is the tree the OCaml frontend hands
    to the verified side: after the typed-layer migration the OCaml boundary is
    lexer+grammar -> [sruleset] (via the pure structural injection
    [extracted/nft_inject.ml]) and EVERY value->byte decision happens in Coq.

    Mirroring rules (see nft_inject.ml, the single translation site):
      - OCaml [int]    -> [nat] over the ExtrOcamlNatInt seam.  The injection
        rejects negative literals and literals >= 2^40 (the same seam bound the
        `limit` guard enforces — see theories/Compiler/Extract.v), so every
        [nat] here is a genuine natural far below the 63-bit wrap.
      - OCaml [string] -> [string] over ExtrOcamlNativeString.
      - IP/MAC literals arrive as the lexer's byte-group lists ([data]); the
        grouping is textual grammar work (dotted quad, colon-hex), NOT a
        byteorder decision — byteorder is decided only by the Coq datatype
        layer (Surface.Datatype / IR.Nftval).
      - The base-chain priority is an OCaml [int] that can be negative
        (`priority -100`); it crosses the seam in SIGN-MAGNITUDE form
        ([prio_neg], [priority]) so no negative number meets [nat].

    NO functions and NO bytes-with-meaning live here: this file is pure syntax. *)

From Stdlib Require Import List String.
From Nft Require Import Bytes.
Import ListNotations.
Local Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(** ** Values as written (mirror of [Nft_ast.value]).

    Resolution of a value's BYTES is deferred to the typed layer because it
    depends on the datatype of the selector it appears under (a port is 2
    big-endian bytes, an ifname is a 16-byte NUL-padded buffer, `established`
    is a 4-byte conntrack-state word). *)
Inductive svalue : Type :=
| SVNum    (n : nat)                   (* decimal or 0x-hex integer literal    *)
| SVSym    (s : string)                (* bareword: symbolic constant / ifname *)
| SVStr    (s : string)                (* double-quoted string, e.g. "eth0"    *)
| SVIp4    (b : data)                  (* dotted IPv4 literal, 4 bytes         *)
| SVIp6    (b : data)                  (* IPv6 literal, 16 bytes (big-endian)  *)
| SVMac    (b : data)                  (* MAC literal, 6 bytes                 *)
| SVVar    (s : string)                (* `$name` reference to a `define`      *)
| SVPrefix (v : svalue) (len : nat)    (* CIDR prefix, e.g. 192.168.50.0/24    *)
| SVRange  (lo hi : svalue)            (* inclusive range, e.g. 29811-29814    *)
| SVConcat (vs : list svalue)          (* concatenation, e.g. 1.2.3.4 . eth0   *)
| SVSet    (vs : list svalue).         (* a `define`d set value, `{ $a, $b }`  *)

(** Smart constructor for a dotted-quad IPv4 literal: the emitter prints
    `sip4 192 168 100 0` for [SVIp4 [192;168;100;0]] so the generated Gen file
    carries the address as decimal octets (the textual grammar view), never a
    raw byte list.  This is grouping only — no byteorder decision. *)
Definition sip4 (a b c d : nat) : svalue := SVIp4 [a; b; c; d].

(** Verdicts as written (mirror of [Nft_ast.verdict]). *)
Inductive sverdict : Type :=
| SVaccept
| SVdrop
| SVcontinue
| SVreturn
| SVjump  (chain : string)
| SVgoto  (chain : string)
| SVqueue (lo hi : nat) (bypass fanout : bool)  (* `queue [num lo[-hi]] [...]` *)
| SVreject (opts : string).            (* `reject [with ...]`; opts verbatim   *)

(** The right-hand side of a match: a single value/range/prefix, an inline
    (anonymous) set, a bare comma list, or a named-set reference (`@name`). *)
Inductive ssetexpr : Type :=
| SSEvalue (v : svalue)
| SSEset   (vs : list svalue)          (* `{ a, b, ... }`: real set membership *)
| SSElist  (vs : list svalue)          (* `a, b, ...` bare commas: OR-fold,
                                          bitmask selectors only (evaluate.c
                                          expr_evaluate_list)                  *)
| SSEref   (name : string).            (* @name                                *)

(** The relational operator a match was WRITTEN with (bitmask-basetype
    selectors treat implicit / == / != / ! differently). *)
Inductive srelop : Type := SOpImplicit | SOpEq | SOpNe | SOpBang.

Record srhs : Type := mkSrhs {
  sr_op      : srelop;
  sr_neg     : bool;
  sr_payload : ssetexpr }.

(** A selector key path, e.g. ["tcp";"dport"], ["meta";"obrname"], ["oifname"]. *)
Definition skeypath : Type := list string.

(** A match condition as written: one or more concatenated selector keys, then
    its right-hand side. *)
Record smatch : Type := mkSmatch {
  sm_keys : list skeypath;
  sm_rhs  : srhs }.

(** Verdict-neutral / terminal action statements (mirror of [Nft_ast.sstmt]). *)
Inductive sstmt : Type :=
| StComment    (c : string)
| StCounter
| StLog        (opts : string)         (* options verbatim                     *)
| StLimit      (rate : nat) (unit : string) (over : bool)
               (burst : nat) (byte_rate : bool)
| StMasquerade (flags : list string)
| StSnat       (addr : option svalue) (port : option nat) (flags : list string)
| StDnat       (addr : option svalue) (port : option nat) (flags : list string)
| StRedirect   (port : option nat) (flags : list string)
| StTproxy     (fam : string) (addr : option svalue) (port : option nat)
| StMetaSet    (key : string) (v : svalue)   (* `meta <k> set v` / `mark set v` *)
| StCtSet      (key : string) (v : svalue)   (* `ct <k> set v`                  *)
| StNotrack.

Inductive sclause : Type :=
| CMatch    (m : smatch)
| CVmap     (keys : list skeypath) (entries : list (svalue * sverdict))
                                       (* `<key>[.<key>...] vmap { v : verdict }` *)
| CVmapRef  (keys : list skeypath) (name : string)   (* `... vmap @named_map`  *)
| CVerdict  (v : sverdict)
| CStmt     (s : sstmt)
| CBitmatch (kp : skeypath) (op : string) (mask : svalue) (r : srhs).
                                       (* `<sel> and|or|xor <mask> <relop> <v>` *)

Definition srule : Type := list sclause.

(** A named-set / named-map declaration inside a table. *)
Record ssetdecl : Type := mkSsetdecl {
  sd_name     : string;
  sd_is_map   : bool;                  (* `map` (key:value) vs `set`           *)
  sd_type     : list string;           (* concatenated key type atoms          *)
  sd_flags    : list string;           (* `flags constant`, `flags interval`   *)
  sd_elements : list (svalue * option sverdict) }.

Inductive schain_item : Type :=
| ITypeHook (ctype hook : string) (prio_neg : bool) (priority : nat)
                                       (* sign-magnitude: -100 = (true, 100)   *)
| IPolicy   (v : sverdict)
| IRule     (r : srule).

Record schain : Type := mkSchain {
  sc_name  : string;
  sc_items : list schain_item }.

Inductive stable_item : Type :=
| TChain (c : schain)
| TSet   (sd : ssetdecl)
| TObj   (name : string).              (* named stateful object: parsed, skipped *)

Record stable : Type := mkStable {
  st_family : string;
  st_name   : string;
  st_items  : list stable_item }.

(** A whole file: defines (collected), and the tables.  `flush`/`destroy`
    lines parse to [TopNop]; `include` is expanded by the OCaml driver BEFORE
    injection, so a [TopInclude] never reaches the typechecker. *)
Inductive stoplevel : Type :=
| TopDefine  (name : string) (v : svalue)
| TopTable   (t : stable)
| TopInclude (path : string)
| TopNop.

Definition sruleset : Type := list stoplevel.
