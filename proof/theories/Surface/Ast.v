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
      - IPv4/MAC literals arrive as the lexer's byte-group lists ([data]): a
        dotted-quad octet or a colon-hex byte pair is exactly ONE byte, so the
        grouping is textual grammar work, NOT a byteorder decision.  An IPv6
        literal is DIFFERENT — each colon group is a 16-bit value that must be
        split into two big-endian bytes, and `::` expands to a zero run — so it
        arrives UN-expanded, as [ip6grp] groups, and [sip6_bytes] below performs
        the big-endian split and `::` expansion IN COQ (failing loud on a
        literal that cannot be 16 bytes).  Byteorder is decided only on the
        verified side (here + Surface.Datatype / IR.Nftval), never in OCaml.
      - The base-chain priority is an OCaml [int] that can be negative
        (`priority -100`); it crosses the seam in SIGN-MAGNITUDE form
        ([prio_neg], [priority]) so no negative number meets [nat].

    NO functions and NO bytes-with-meaning live here: this file is pure syntax. *)

From Stdlib Require Import List String PeanoNat Lia.
From Nft Require Import Bytes.
Import ListNotations.
Local Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(** ** Values as written (mirror of [Nft_ast.value]).

    Resolution of a value's BYTES is deferred to the typed layer because it
    depends on the datatype of the selector it appears under (a port is 2
    big-endian bytes, an ifname is a 16-byte NUL-padded buffer, `established`
    is a 4-byte conntrack-state word). *)
(* ------------------------------------------------------------------ *)
(** ** IPv6 literal groups (un-expanded).

    An IPv6 literal is carried as its colon-separated groups, split at the
    single `::` zero-run (if any).  A group is either a 16-bit hex value
    ([G16], 0..65535) or an embedded trailing IPv4 tail ([G4], its already-
    grouped octets, one byte each, from `::ffff:1.2.3.4`).  The lexer does the
    numeral parsing and octet grouping (residue (b): int/grouping only); the
    big-endian 16-bit split and the `::` zero-fill are done here, in Coq. *)
Inductive ip6grp : Type :=
| G16 (n : nat)      (* a 1-4 hex-digit colon group, value 0..65535 *)
| G4  (os : data).   (* an embedded IPv4 tail: octets, one byte each *)

Definition ip6grp_bytes (g : ip6grp) : data :=
  match g with
  (* the big-endian 16-bit split — the byteorder decision, made HERE in Coq *)
  | G16 n => [Nat.div n 256; Nat.modulo n 256]
  | G4 os => os
  end.

Definition ip6grps_bytes (gs : list ip6grp) : data :=
  List.concat (List.map ip6grp_bytes gs).

(** [front ++ zero-fill ++ back] is exactly 16 bytes when the two ends fit.
    Stated over abstract [data] and proved cleanly (so the subtraction is a real
    [Nat.sub], not the giant nested match a concrete literal [16] iota-reduces
    to inside the caller's pipeline); the caller discharges its goal by [apply],
    whose up-to-conversion unification bridges the two forms. *)
Lemma ip6_fill_len : forall (x y : data),
  (List.length x + List.length y <= 16)%nat ->
  List.length (x ++ List.repeat 0 (16 - (List.length x + List.length y)) ++ y)%list
    = 16%nat.
Proof.
  intros x y H. unfold data, byte in *.
  rewrite !length_app, repeat_length. lia.
Qed.

(** Expand a textual IPv6 literal to its 16 network-order bytes.
    [r = None]  : no `::`; the groups must already total 16 bytes.
    [r = Some rs]: the `::` zero-run sits between [l] and [rs], filled with as
    many zero bytes as needed to reach 16.  Fails loud ([None]) on any literal
    that cannot form exactly 16 bytes. *)
Definition sip6_bytes (l : list ip6grp) (r : option (list ip6grp)) : option data :=
  match r with
  | None =>
      let b := ip6grps_bytes l in
      if Nat.eqb (List.length b) 16 then Some b else None
  | Some rs =>
      let lb := ip6grps_bytes l in
      let rb := ip6grps_bytes rs in
      let have := (List.length lb + List.length rb)%nat in
      if Nat.leb have 16
      then Some (lb ++ List.repeat 0 (16 - have) ++ rb)%list
      else None
  end.

(** The expansion, when it succeeds, always yields exactly a 16-byte register. *)
Lemma sip6_bytes_len : forall l r b,
  sip6_bytes l r = Some b -> List.length b = 16%nat.
Proof.
  intros l r b H. unfold sip6_bytes in H. destruct r as [rs|]; cbv zeta in H.
  - destruct (Nat.leb (List.length (ip6grps_bytes l)
                       + List.length (ip6grps_bytes rs)) 16) eqn:E;
      [|discriminate H].
    injection H as <-. apply ip6_fill_len. apply Nat.leb_le, E.
  - destruct (Nat.eqb (List.length (ip6grps_bytes l)) 16) eqn:E;
      [|discriminate H].
    injection H as <-. apply Nat.eqb_eq, E.
Qed.

Inductive svalue : Type :=
| SVNum    (n : nat)                   (* decimal or 0x-hex integer literal    *)
| SVSym    (s : string)                (* bareword: symbolic constant / ifname *)
| SVStr    (s : string)                (* double-quoted string, e.g. "eth0"    *)
| SVIp4    (b : data)                  (* dotted IPv4 literal, 4 bytes         *)
| SVIp6    (l : list ip6grp) (r : option (list ip6grp))
                                       (* IPv6 literal groups; -> 16 BE bytes  *)
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

(** ** Named stateful objects.

    A table declares objects (counter, quota, limit, ct helper/timeout/
    expectation, secmark, synproxy) that rules later reference by name.  The
    [sobjkind] tags the object's kind; [objkind_otype] maps it to the kernel's
    NFT_OBJECT_* number (include/linux/netfilter/nf_tables.h) that the objref
    statement/verdict carries.  Object-body validation beyond kind agreement
    (helper protocol modules, timeout policy state names, l3proto) is kernel-
    module behaviour outside this model — the declaration carries its kind, and
    a rule reference is checked for declared-existence + kind agreement. *)
Inductive sobjkind : Type :=
| OKcounter | OKquota | OKlimit | OKcthelper
| OKcttimeout | OKctexpect | OKsecmark | OKsynproxy.

(** The NFT_OBJECT_* type number a reference to an object of this kind carries
    (include/linux/netfilter/nf_tables.h: COUNTER=1, QUOTA=2, CT_HELPER=3,
    LIMIT=4, CT_TIMEOUT=7, SECMARK=8, CT_EXPECT=9, SYNPROXY=10). *)
Definition objkind_otype (k : sobjkind) : nat :=
  match k with
  | OKcounter => 1 | OKquota => 2 | OKcthelper => 3 | OKlimit => 4
  | OKcttimeout => 7 | OKsecmark => 8 | OKctexpect => 9 | OKsynproxy => 10
  end.

(** Verdict-neutral / terminal action statements (mirror of [Nft_ast.sstmt]). *)
Inductive sstmt : Type :=
| StComment    (c : string)
| StCounter    (pkts bytes : nat)      (* `counter [packets N bytes N]` — the
                                          initial values reach the compiled
                                          [SCounter], not silently dropped      *)
| StObjref     (kind : sobjkind) (name : string)
                                       (* `counter name X` / `quota name X` /
                                          `limit name X` / `ct helper set X` /
                                          `synproxy name X`: reference a declared
                                          object; verdict-neutral (a named
                                          quota's over-limit drop is a documented
                                          model boundary, see DEVELOPMENT.md)   *)
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
| CObjrefMap (kind : sobjkind) (keys : list skeypath)
             (entries : list (svalue * string))
                                       (* `counter name <key> map { v : "obj" }`
                                          objref verdict-map: the looked-up datum
                                          is a named object of [kind]           *)
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
| TObj   (name : string) (kind : sobjkind).
                                       (* named stateful object declaration:
                                          its kind is retained so a rule's
                                          `counter name X` etc. can be checked
                                          for existence + kind agreement        *)

Record stable : Type := mkStable {
  st_family : string;
  st_name   : string;
  st_items  : list stable_item }.

(** A whole file: defines (collected), and the tables.  `include` is expanded by
    the OCaml driver BEFORE injection, so a [TopInclude] never reaches the
    typechecker; `delete`/`destroy`/`flush` are structured [TopOp]s the OCaml
    config driver (nft_config.ml) applies before injection, so no config-op node
    reaches this surface AST either. *)
Inductive stoplevel : Type :=
| TopDefine  (name : string) (v : svalue)
| TopTable   (t : stable)
| TopInclude (path : string).

Definition sruleset : Type := list stoplevel.
