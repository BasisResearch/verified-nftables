(** Nftc — a formally-verified nftables DSL -> control-plane bytecode compiler.

    [compile] and [optimize] are extracted from machine-checked Rocq proofs:
    - [compile] preserves the packet->verdict meaning of the rule set;
    - [optimize] never changes any packet's verdict.
    [to_netlink_text] is untrusted rendering, differentially tested byte-identical
    against upstream [nft --debug=netlink]. *)

module Verdict : module type of Verdict
module Packet : module type of Packet
module Syntax : module type of Syntax
module Bytecode : module type of Bytecode
module Semantics : module type of Semantics

type field = Syntax.field
type matchcond = Syntax.matchcond
type rule = Syntax.rule
type chain = Syntax.chain
type program = Bytecode.program
type verdict = Verdict.verdict

(** {2 DSL builders} (byte strings are big-endian [int list], e.g. port 22 = [[0;22]]) *)

val eq : field -> Bytes.data -> matchcond
val neq : field -> Bytes.data -> matchcond
val range : ?neg:bool -> field -> Bytes.data -> Bytes.data -> matchcond

(** [cmp f op v] — an ordered comparison [field <op> v] (op : {!Bytecode.cmpop}). *)
val cmp : field -> Bytecode.cmpop -> Bytes.data -> matchcond

(** [masked ?neg f mask xor v] — match [(field & mask) ^ xor] against [v]
    (e.g. an address-prefix test). *)
val masked : ?neg:bool -> field -> Bytes.data -> Bytes.data -> Bytes.data -> matchcond

(** {2 Verdict-neutral statement builders} (for [rule ~stmts]) *)

val counter : Syntax.stmt   (** a zeroed packet/byte counter *)
val notrack : Syntax.stmt   (** disable connection tracking *)
val log : string -> Syntax.stmt  (** log with the given option string *)

(** [rule ?stmts matches verdict] — a rule is a conjunction of matches then a verdict. *)
val rule : ?stmts:Syntax.stmt list -> matchcond list -> verdict -> rule

(** [chain policy rules] — a base chain: default policy + ordered rules. *)
val chain : verdict -> rule list -> chain

(** {2 The verified pipeline} *)

(** Compile a chain to control-plane bytecode (proved semantics-preserving). *)
val compile : chain -> program

(** Verified DSL optimizer: dedup duplicate matches, simplify singleton ranges,
    drop rules shadowed by an accept/drop-all (proved verdict-preserving). *)
val optimize : chain -> chain

(** [optimize] then [compile]. *)
val compile_optimized : chain -> program

(** The FULL verified consolidation pipeline (the [nft -o] supersetting passes):
    base dedup/DCE, then the N-way value->set, two-selector->concat, and
    value+verdict->vmap merges, via the UNCONDITIONAL extracted entry
    [Optimize_Uncond.optimize_table_uncond] — whole-pipeline verdict preservation
    holds for ANY input chain with no precondition. Returns the synthesised set/map
    declarations the merges minted (anonymous `__setN`/`__vmapN`) alongside the
    rewritten chain. *)
val optimize_table : chain -> Semantics.set_decls * chain

(** {2 Rendering (untrusted glue)} *)

(** Render a program as `nft --debug=netlink` expression lines. *)
val to_netlink_text : program -> string

(** Render a single instruction. *)
val render_instr : Bytecode.instr -> string

(** {2 The .nft text frontend (untrusted parser)}

    Parse nftables DSL text into the {!Syntax} AST plus the {!Packet.env} its
    set/map lookups read.  The parser is untrusted glue — like the renderer it is
    validated externally (against {!module:Example_Ruleset}'s proven verdicts and
    live [nft]), not part of the proof TCB.  Once parsed, properties proved of the
    AST hold of the compiled bytecode via [compile_table_correct]. *)

(** A parsed ruleset: the tables' chains and the environment their lookups read. *)
type parsed = Nft_inject.parsed

(** Parse a ruleset from a string. @raise Nft_parse.Parse_error on a lex/parse
    error; @raise Nft_inject.Lower_error on a construct outside the supported
    subset (never a silent mis-parse). *)
val parse_string : string -> parsed

(** Parse a ruleset from a file. *)
val parse_file : string -> parsed

(** All chains of the named table, in source order (jump targets + base chains). *)
val table_chains : parsed -> table:string -> (string * chain) list

(** The named chain of the named table. *)
val find_chain : parsed -> table:string -> chain:string -> chain
