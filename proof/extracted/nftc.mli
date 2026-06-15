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

(** {2 Rendering (untrusted glue)} *)

(** Render a program as `nft --debug=netlink` expression lines. *)
val to_netlink_text : program -> string

(** Render a single instruction. *)
val render_instr : Bytecode.instr -> string
