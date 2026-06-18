/* Menhir grammar for the nftables DSL surface syntax.

   Produces the untrusted Nft_ast surface tree; Nft_lower turns that into the
   trusted Syntax AST.  The grammar parses real structure faithfully — defines,
   named-set/map declarations, concatenations, named-set references, ranges,
   CIDR prefixes, negation, the common statement vocabulary — without inlining or
   pre-substituting anything (defines stay `Vvar`, named sets stay `SEref`).
   See TODO 9 in ../DEVELOPMENT.md.

   Newline handling: rules and block items are newline/semicolon separated.
   Inside a *value* brace-group (`{ ... }` for a set / map / elements list)
   newlines are insignificant — the `nls` nonterminal swallows them there. */

%{
  open Nft_ast

  (* named base-chain priorities -> their integer value (only ordering matters,
     and our per-chain proofs don't use it; map the common names, default 0). *)
  let prio_of_name = function
    | "raw" -> -300 | "mangle" -> -150 | "dstnat" -> -100 | "filter" -> 0
    | "security" -> 50 | "srcnat" -> 100 | "out" -> 100 | _ -> 0
%}

/* structural keywords */
%token FLUSH RULESET DESTROY DELETE TABLE CHAIN SET MAP DEFINE INCLUDE ELEMENTS FLAGS
%token TYPE HOOK PRIORITY POLICY COMMENT VMAP
/* verdicts */
%token ACCEPT DROP CONTINUE RETURN JUMP GOTO QUEUE REJECT
/* statements */
%token COUNTER LOG PREFIX LIMIT RATE WITH TO MASQUERADE SNAT DNAT
/* match selectors */
%token META CT IP IP6 TCP UDP TH ICMP ICMPV6 ETHER FIB
%token IIF OIF IIFNAME OIFNAME PKTTYPE MARK
/* operators / punctuation */
%token LBRACE RBRACE COLON COMMA DOT SLASH EQUALS NE EQ BANG DASH
/* separators */
%token NEWLINE SEMI
/* literals */
%token <int> INT
%token <int list> IPV4
%token <string> IDENT
%token <string> STRING
%token <string> VAR
%token <string> AT
%token EOF

%start <Nft_ast.sfile> file

%%

(* ---- separators ---- *)
sep: NEWLINE {} | SEMI {}
seps: sep {} | seps sep {}
optseps: /* empty */ {} | seps {}
(* a (possibly empty) run of NEWLINEs, used to make value braces newline-blind *)
nls: /* empty */ {} | nls NEWLINE {}

(* ---- file ---- *)
file: optseps toplevels optseps EOF { $2 }

toplevels:
  | /* empty */              { [] }
  | toplevel                 { [$1] }
  | toplevels seps toplevel  { $1 @ [$3] }

toplevel:
  | FLUSH RULESET                 { TopNop }
  | DESTROY TABLE family IDENT    { TopNop }
  | DESTROY TABLE IDENT           { TopNop }   (* `destroy table NAME` (no family) *)
  | DELETE TABLE family IDENT     { TopNop }
  | DELETE TABLE IDENT            { TopNop }
  | INCLUDE STRING                { TopInclude $2 }
  | DEFINE IDENT EQUALS value     { TopDefine ($2, $4) }
  | DEFINE IDENT EQUALS LBRACE nls valueseq nls RBRACE
      { TopDefine ($2, Vset $6) }   (* define X = { a, b, ... } *)
  | TABLE family IDENT LBRACE optseps table_items optseps RBRACE
      { TopTable { st_family = $2; st_name = $3; st_items = $6 } }
  | TABLE IDENT LBRACE optseps table_items optseps RBRACE
      { TopTable { st_family = "ip"; st_name = $2; st_items = $5 } }

family:
  | IDENT { $1 } | IP { "ip" } | IP6 { "ip6" }

table_items:
  | /* empty */                  { [] }
  | table_item                   { [$1] }
  | table_items seps table_item  { $1 @ [$3] }

table_item:
  | chain   { TChain $1 }
  | setdecl { TSet $1 }
  | objdecl { $1 }

(* Named stateful objects (ct helper/timeout/expectation, secmark, counter,
   limit, quota, synproxy ...).  They declare state referenced elsewhere but carry
   no verdict logic, so we parse their block (whatever it contains) and skip it.
   The body is an arbitrary token soup up to the matching brace. *)
objdecl:
  | CT IDENT IDENT LBRACE junk RBRACE { TObj $3 }   (* ct helper NAME { ... } *)
  | IDENT IDENT LBRACE junk RBRACE    { TObj $2 }   (* secmark/quota/... NAME { ... } *)
  | COUNTER IDENT LBRACE junk RBRACE  { TObj $2 }
  | LIMIT IDENT LBRACE junk RBRACE    { TObj $2 }

junk:
  | /* empty */          { () }
  | junk junktok         { () }
  | junk LBRACE junk RBRACE { () }   (* nested braces *)

junktok:
  | INT {} | IPV4 {} | IDENT {} | STRING {} | VAR {} | AT {}
  | COLON {} | COMMA {} | DOT {} | SLASH {} | EQUALS {} | NE {} | EQ {} | BANG {}
  | DASH {} | SEMI {} | NEWLINE {}
  | TYPE {} | HOOK {} | PRIORITY {} | POLICY {} | COMMENT {} | VMAP {} | FLAGS {}
  | ELEMENTS {} | SET {} | MAP {} | TABLE {} | CHAIN {} | DEFINE {} | INCLUDE {}
  | ACCEPT {} | DROP {} | CONTINUE {} | RETURN {} | JUMP {} | GOTO {} | QUEUE {}
  | REJECT {} | COUNTER {} | LOG {} | PREFIX {} | LIMIT {} | RATE {} | WITH {}
  | TO {} | MASQUERADE {} | SNAT {} | DNAT {} | META {} | CT {} | IP {} | IP6 {}
  | TCP {} | UDP {} | TH {} | ICMP {} | ICMPV6 {} | ETHER {} | FIB {} | IIF {}
  | OIF {} | IIFNAME {} | OIFNAME {} | PKTTYPE {} | MARK {} | FLUSH {} | RULESET {}
  | DESTROY {} | DELETE {}

(* ---- named set / map declarations ---- *)
setdecl:
  | SET IDENT LBRACE optseps set_body optseps RBRACE
      { let (ty,fl,el) = $5 in
        { sd_name=$2; sd_is_map=false; sd_type=ty; sd_flags=fl; sd_elements=el } }
  | MAP IDENT LBRACE optseps set_body optseps RBRACE
      { let (ty,fl,el) = $5 in
        { sd_name=$2; sd_is_map=true; sd_type=ty; sd_flags=fl; sd_elements=el } }

(* set body = type / flags / elements lines, in any order; gather them *)
set_body:
  | /* empty */               { ([],[],[]) }
  | set_body_item             { $1 }
  | set_body seps set_body_item
      { let (a,b,c)=$1 and (d,e,f)=$3 in (a@d, b@e, c@f) }

set_body_item:
  | TYPE typespec                 { ($2, [], []) }
  | TYPE typespec COLON typespec  { ($2, [], []) }  (* map key:value; keep key type *)
  | FLAGS flaglist                { ([], $2, []) }
  | ELEMENTS EQUALS elemset       { ([], [], $3) }

typespec:
  | typeatom                   { [$1] }
  | typespec DOT typeatom      { $1 @ [$3] }
typeatom: IDENT { $1 }

flaglist:
  | IDENT                   { [$1] }
  | flaglist COMMA IDENT    { $1 @ [$3] }

(* elements = { e , e , ... }  (each optionally `: data` for a map) *)
elemset:
  | LBRACE nls RBRACE                  { [] }
  | LBRACE nls elemseq nls RBRACE      { $3 }
elemseq:
  | element                         { [$1] }
  | elemseq nls COMMA nls element   { $1 @ [$5] }
element:
  | elem               { ($1, None) }
  | elem COLON verdict { ($1, Some $3) }

(* ---- chains ---- *)
chain:
  | CHAIN IDENT LBRACE optseps chain_items optseps RBRACE
      { { sc_name = $2; sc_items = $5 } }

chain_items:
  | /* empty */                  { [] }
  | chain_item                   { [$1] }
  | chain_items seps chain_item  { $1 @ [$3] }

chain_item:
  | TYPE IDENT HOOK IDENT PRIORITY prio
      { ITypeHook { ct_type = $2; hook = $4; priority = $6 } }
  | TYPE IDENT HOOK IDENT IDENT devspec PRIORITY prio
      { ITypeHook { ct_type = $2; hook = $4; priority = $8 } }  (* `... device DEV ...` *)
  | POLICY verdict { IPolicy $2 }
  | rule           { IRule $1 }

(* a netdev hook's bound device(s): `device lo` or `devices = { eth0, eth1 }` *)
devspec:
  | IDENT                                  { () }
  | EQUALS LBRACE nls valueseq nls RBRACE  { () }

prio:
  | INT       { $1 }
  | DASH INT  { - $2 }
  | IDENT     { prio_of_name $1 }

(* ---- a rule = a non-empty sequence of clauses ---- *)
rule:
  | clauses { $1 }
clauses:
  | clause          { [$1] }
  | clauses clause  { $1 @ [$2] }

clause:
  | matchc                       { CMatch $1 }
  | keyatom VMAP vmapset         { CVmap ($1, $3) }
  | keyatom VMAP AT              { CVmapRef ($1, $3) }   (* vmap @named_map *)
  | verdict                      { CVerdict $1 }
  | stmt                         { CStmt $1 }

(* ---- match conditions ---- *)
matchc:
  | concat_keys rhs { { m_keys = $1; m_rhs = $2 } }

concat_keys:
  | keyatom                  { [$1] }
  | concat_keys DOT keyatom  { $1 @ [$3] }

keyatom:
  | TCP FLAGS     { ["tcp"; "flags"] }   (* `flags` lexes as the FLAGS keyword *)
  | TCP IDENT     { ["tcp"; $2] }
  | UDP IDENT     { ["udp"; $2] }
  | TH IDENT      { ["th"; $2] }
  | IP IDENT      { ["ip"; $2] }
  | IP6 IDENT     { ["ip6"; $2] }
  | ICMP TYPE     { ["icmp"; "type"] }
  | ICMP IDENT    { ["icmp"; $2] }
  | ICMPV6 TYPE   { ["icmpv6"; "type"] }
  | ICMPV6 IDENT  { ["icmpv6"; $2] }
  | ETHER TYPE    { ["ether"; "type"] }
  | ETHER IDENT   { ["ether"; $2] }
  | META IDENT    { ["meta"; $2] }
  (* `meta <kw>` where the sub-selector is itself a keyword token *)
  | META IIF      { ["meta"; "iif"] }
  | META OIF      { ["meta"; "oif"] }
  | META IIFNAME  { ["meta"; "iifname"] }
  | META OIFNAME  { ["meta"; "oifname"] }
  | META MARK     { ["meta"; "mark"] }
  | META PKTTYPE  { ["meta"; "pkttype"] }
  | CT IDENT      { ["ct"; $2] }
  (* fib (routing-table) lookup: `fib <key> <result>`, e.g. `fib daddr type` *)
  | FIB IDENT TYPE  { ["fib"; $2; "type"] }
  | FIB IDENT IDENT { ["fib"; $2; $3] }
  | IIF           { ["iif"] }
  | OIF           { ["oif"] }
  | IIFNAME       { ["iifname"] }
  | OIFNAME       { ["oifname"] }
  | PKTTYPE       { ["pkttype"] }
  | MARK          { ["mark"] }

rhs:
  | payload     { { op = Op_implicit; neg = false; payload = $1 } }
  | NE payload  { { op = Op_ne;       neg = true;  payload = $2 } }
  | EQ payload  { { op = Op_eq;       neg = false; payload = $2 } }
  | BANG payload { { op = Op_bang;    neg = true;  payload = $2 } }

payload:
  | elem                             { SEvalue $1 }
  | elem COMMA bareset               { SElist ($1 :: $3) }  (* `ct state a,b` (no braces): OR-fold list *)
  | AT                               { SEref $1 }
  | LBRACE nls RBRACE                { SEset [] }
  | LBRACE nls valueseq nls RBRACE   { SEset $3 }

bareset:
  | elem                  { [$1] }
  | bareset COMMA elem    { $1 @ [$3] }

valueseq:
  | elem                          { [$1] }
  | valueseq nls COMMA nls elem   { $1 @ [$5] }

(* an element value: a base value, a range, a prefix, or a concatenation *)
elem:
  | concat_val { match $1 with [v] -> v | vs -> Vconcat vs }
concat_val:
  | rangeval                  { [$1] }
  | concat_val DOT rangeval   { $1 @ [$3] }
rangeval:
  | value             { $1 }
  | value DASH value  { Vrange ($1, $3) }

value:
  | INT             { Vnum $1 }
  | IPV4            { Vip4 $1 }
  | IPV4 SLASH INT  { Vprefix (Vip4 $1, $3) }
  | STRING          { Vstr $1 }
  | IDENT           { Vsym $1 }
  | VAR             { Vvar $1 }
  (* selector keywords usable as symbolic VALUES (e.g. `ip`/`ip6` map keys,
     `tcp`/`udp` in an l4proto set) *)
  | IP     { Vsym "ip" }
  | IP6    { Vsym "ip6" }
  | TCP    { Vsym "tcp" }
  | UDP    { Vsym "udp" }
  | ICMP   { Vsym "icmp" }
  | ICMPV6 { Vsym "icmpv6" }

(* ---- verdict-map (`vmap { k : verdict, ... }`) ---- *)
vmapset:
  | LBRACE nls vmapseq nls RBRACE { $3 }
vmapseq:
  | vmapentry                          { [$1] }
  | vmapseq nls COMMA nls vmapentry    { $1 @ [$5] }
vmapentry:
  | value COLON verdict { ($1, $3) }

(* ---- verdicts ---- *)
verdict:
  | ACCEPT      { SVaccept }
  | DROP        { SVdrop }
  | CONTINUE    { SVcontinue }
  | RETURN      { SVreturn }
  | QUEUE       { SVqueue }
  | JUMP IDENT  { SVjump $2 }
  | GOTO IDENT  { SVgoto $2 }
  | REJECT reject_opt { SVreject $2 }

reject_opt:
  | /* empty */            { "" }
  | WITH IDENT             { $2 }
  | WITH IDENT IDENT       { $2 ^ " " ^ $3 }
  | WITH IDENT TYPE IDENT  { $2 ^ " type " ^ $4 }

(* ---- statements ---- *)
stmt:
  | COMMENT STRING            { StComment $2 }
  | COUNTER                   { StCounter }
  | LOG log_opts              { StLog $2 }
  | LIMIT RATE INT SLASH IDENT { StLimit ($3, $5) }
  | MASQUERADE                { StMasquerade }
  | SNAT nat_to               { StSnat $2 }
  | DNAT nat_to               { StDnat $2 }
  | DNAT IP nat_to            { StDnat $3 }
  | DNAT IP6 nat_to           { StDnat $3 }
  | MARK SET value            { StMetaSet ("mark", $3) }
  | META IDENT SET value      { StMetaSet ($2, $4) }
  | CT IDENT SET value        { StCtSet ($2, $4) }

log_opts:
  | /* empty */        { "" }
  | PREFIX STRING      { $2 }

nat_to:
  | /* empty */ { None }
  | TO value    { Some $2 }
