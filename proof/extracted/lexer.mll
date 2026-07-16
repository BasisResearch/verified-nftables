(* ocamllex lexer for the nftables DSL surface syntax.
   Feeds Parser; see TODO 9 in ../DEVELOPMENT.md. Untrusted glue. *)

{
  open Parser

  exception Lex_error of string

  (* keyword table: a bareword equal to one of these lexes as the keyword token,
     otherwise as IDENT.  Several of these words are *also* usable as symbolic
     values (e.g. `ip` in a verdict map, `tcp` in an l4proto set); the grammar's
     `value` rule accepts the keyword tokens too, so that overlap is handled
     there, not here. *)
  let keywords = [
    "flush", FLUSH; "ruleset", RULESET; "destroy", DESTROY; "delete", DELETE;
    "table", TABLE; "chain", CHAIN; "set", SET; "map", MAP;
    "define", DEFINE; "include", INCLUDE; "elements", ELEMENTS; "flags", FLAGS;
    "type", TYPE; "hook", HOOK; "priority", PRIORITY; "policy", POLICY;
    "comment", COMMENT; "vmap", VMAP;
    (* verdicts *)
    "accept", ACCEPT; "drop", DROP; "continue", CONTINUE; "return", RETURN;
    "jump", JUMP; "goto", GOTO; "queue", QUEUE; "reject", REJECT;
    (* statements *)
    "counter", COUNTER; "log", LOG; "prefix", PREFIX; "limit", LIMIT;
    "rate", RATE; "over", OVER; "with", WITH; "to", TO; "masquerade", MASQUERADE;
    "snat", SNAT; "dnat", DNAT; "redirect", REDIRECT; "tproxy", TPROXY;
    "notrack", NOTRACK;
    (* selectors *)
    "meta", META; "ct", CT; "ip", IP; "ip6", IP6; "tcp", TCP; "udp", UDP;
    "th", TH; "icmp", ICMP; "icmpv6", ICMPV6; "ether", ETHER; "fib", FIB;
    "option", OPTION; "exists", EXISTS; "missing", MISSING;
    "iif", IIF; "oif", OIF; "iifname", IIFNAME; "oifname", OIFNAME;
    "pkttype", PKTTYPE; "mark", MARK;
    (* bitwise binary operators (nft `meta mark and 0x3`, `ct mark or 0x1`) *)
    "and", AND; "or", OR; "xor", XOR;
    (* conntrack tuple direction (`ct original ip saddr`, `ct reply proto-src`);
       also usable as a symbolic VALUE (`ct direction original`), handled in the
       grammar's `value` rule. *)
    "original", ORIGINAL; "reply", REPLY;
  ]

  let ident_or_kw (s : string) : token =
    match Stdlib.List.assoc_opt s keywords with
    | Some t -> t
    | None -> IDENT s

  let ipv4_bytes (s : string) : int list =
    let parts = Stdlib.String.split_on_char '.' s in
    Stdlib.List.map (fun p ->
      let n = int_of_string p in
      if n < 0 || n > 255 then raise (Lex_error ("bad IPv4 octet: " ^ p));
      n) parts

  (* Expand an IPv6 textual literal (`dead::beef`, `::1`, `fe80::`, a full
     8-group form, optionally with an embedded trailing IPv4 `::ffff:1.2.3.4`)
     to its 16 network-order bytes.  `::` marks the single run of zero groups. *)
  let ipv6_bytes (s : string) : int list =
    let module S = Stdlib.String in
    let module L = Stdlib.List in
    (* a group is 1-4 hex digits -> 2 bytes big-endian; an embedded IPv4 tail
       (the last group contains a '.') contributes its 4 bytes directly. *)
    let group_bytes (g : string) : int list =
      if S.contains g '.' then ipv4_bytes g
      else let n = int_of_string ("0x" ^ g) in [ (n lsr 8) land 0xff; n land 0xff ] in
    let groups (part : string) : int list list =
      if part = "" then []
      else L.map group_bytes (S.split_on_char ':' part) in
    let idx =
      (* locate the "::" zero-run split, if any *)
      let rec find i =
        if i + 1 >= S.length s then -1
        else if S.get s i = ':' && S.get s (i+1) = ':' then i
        else find (i+1) in
      find 0 in
    let bytes =
      if idx < 0 then
        (* no ::, must be a full 8-group address *)
        L.concat (groups s)
      else begin
        let left  = groups (S.sub s 0 idx) in
        let right = groups (S.sub s (idx+2) (S.length s - idx - 2)) in
        let have = L.length left + L.length right in
        let zeros = L.init (8 - have) (fun _ -> [0;0]) in
        L.concat (left @ zeros @ right)
      end in
    (* pad/truncate defensively to 16 bytes *)
    let b = bytes in
    let n = L.length b in
    if n = 16 then b
    else if n < 16 then b @ L.init (16 - n) (fun _ -> 0)
    else raise (Lex_error ("malformed IPv6 literal: " ^ s))
}

let digit   = ['0'-'9']
let hex     = ['0'-'9' 'a'-'f' 'A'-'F']
let alpha   = ['a'-'z' 'A'-'Z' '_']
let word    = ['a'-'z' 'A'-'Z' '0'-'9' '_']
(* an interface/identifier may contain internal dash- or dot-joined segments:
   `nd-neighbor-solicit`, `br.20`, `vlan.25`, `inc-budge`; optional trailing `*`
   wildcard (`podman*`).  An IPv4 literal (all-digit dotted) is matched first by
   the rule order below, so `192.168.51.20` never reaches this. *)
let seg     = (alpha | digit) word*
let ident   = alpha word* (('-' | '.') seg)* '*'?
let ws      = [' ' '\t']
(* IPv6 literals.  A group is 1-4 hex digits.  We recognise either a full
   8-group form (>=3 groups so a lone map `key : value` colon never matches) or
   any form containing the `::` zero-run compression.  An optional embedded IPv4
   tail (`::ffff:1.2.3.4`) is allowed in the last group. *)
let hh      = hex hex
(* a MAC address literal: exactly six colon-separated 2-hex-digit groups.
   Matched BEFORE the IPv6 rules so `aa:bb:cc:dd:ee:ff` (which would otherwise
   lex as a 6-group IPv6 fragment) is recognised as an Ethernet address. *)
let mac     = hh ':' hh ':' hh ':' hh ':' hh ':' hh
let h16     = hex hex? hex? hex?
let v4tail  = digit+ '.' digit+ '.' digit+ '.' digit+
let g6      = h16 | v4tail
let ip6full = g6 (':' g6) (':' g6)+
let ip6comp = (h16 (':' h16)* )? "::" (g6 (':' g6)* )?

rule token = parse
  | ws+              { token lexbuf }
  | '#' [^ '\n']*    { token lexbuf }                 (* line comment *)
  | ('\r')? '\n'     { Lexing.new_line lexbuf; NEWLINE }
  | ';'              { SEMI }
  | '{'              { LBRACE }
  | '}'              { RBRACE }
  | ':'              { COLON }
  | ','              { COMMA }
  | '.'              { DOT }
  | '/'              { SLASH }
  | '='              { EQUALS }
  | "!="             { NE }
  | "=="             { EQ }
  | '!'              { BANG }
  | '-'              { DASH }
  | '&'              { AMP }
  | '|'              { PIPE }
  | '^'              { CARET }
  | '$' (ident as s) { VAR s }
  | '@' (ident as s) { AT s }
  | digit+ ('.' digit+)+ as s   { IPV4 (ipv4_bytes s) }
  | mac as s                    { MAC (Stdlib.List.map (fun g -> int_of_string ("0x" ^ g))
                                        (Stdlib.String.split_on_char ':' s)) }
  | (ip6full | ip6comp) as s    { IPV6 (ipv6_bytes s) }
  (* An integer literal beyond OCaml's native int (2^62-1) cannot be
     represented by the extracted [nat] realisation (ExtrOcamlNatInt, see
     theories/Compiler/Extract.v): reject it as a clean lexical error rather
     than letting int_of_string's Failure escape as a crash. *)
  | "0x" hex+ as s              { match int_of_string_opt s with
                                  | Some n -> INT n
                                  | None -> raise (Lex_error ("integer literal out of range: " ^ s)) }
  | digit+ as s                 { match int_of_string_opt s with
                                  | Some n -> INT n
                                  | None -> raise (Lex_error ("integer literal out of range: " ^ s)) }
  | '"' ([^ '"']* as s) '"'     { STRING s }
  | ident as s                  { ident_or_kw s }
  | eof              { EOF }
  | _ as c           { raise (Lex_error (Printf.sprintf "unexpected character %C" c)) }
