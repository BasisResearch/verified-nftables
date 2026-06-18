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
    "snat", SNAT; "dnat", DNAT;
    (* selectors *)
    "meta", META; "ct", CT; "ip", IP; "ip6", IP6; "tcp", TCP; "udp", UDP;
    "th", TH; "icmp", ICMP; "icmpv6", ICMPV6; "ether", ETHER; "fib", FIB;
    "iif", IIF; "oif", OIF; "iifname", IIFNAME; "oifname", OIFNAME;
    "pkttype", PKTTYPE; "mark", MARK;
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
  | '$' (ident as s) { VAR s }
  | '@' (ident as s) { AT s }
  | digit+ ('.' digit+)+ as s   { IPV4 (ipv4_bytes s) }
  | "0x" hex+ as s              { INT (int_of_string s) }
  | digit+ as s                 { INT (int_of_string s) }
  | '"' ([^ '"']* as s) '"'     { STRING s }
  | ident as s                  { ident_or_kw s }
  | eof              { EOF }
  | _ as c           { raise (Lex_error (Printf.sprintf "unexpected character %C" c)) }
