(* Nftc: a reusable, formally-verified nftables compiler.

   `compile` and `optimize` are EXTRACTED from machine-checked Rocq proofs
   (compile_chain_correct: the emitted bytecode filters every packet exactly as
   the DSL says; optimize_chain_correct: the optimizer never changes a verdict).
   Only `to_netlink_text` is untrusted glue, and it is itself differentially
   tested byte-identical against upstream `nft --debug=netlink`. *)

module Verdict = Verdict
module Packet = Packet
module Syntax = Syntax
module Bytecode = Bytecode

type field   = Syntax.field
type matchcond = Syntax.matchcond
type rule    = Syntax.rule
type chain   = Syntax.chain
type program = Bytecode.program
type verdict = Verdict.verdict

(* ---- DSL builders ---- *)
let eq  (f : field) (v : Bytes.data) : matchcond = Syntax.MEq (f, v)
let neq (f : field) (v : Bytes.data) : matchcond = Syntax.MNeq (f, v)
let range ?(neg = false) (f : field) (lo : Bytes.data) (hi : Bytes.data) : matchcond =
  Syntax.MRange (f, neg, lo, hi)
(* ordered comparison `field <op> v` (op : Bytecode.cmpop, e.g. Bytecode.CLt) *)
let cmp (f : field) (op : Bytecode.cmpop) (v : Bytes.data) : matchcond = Syntax.MCmp (f, op, v)
(* masked match `(field & mask) ^ xor {==,!=} v`, e.g. an address prefix *)
let masked ?(neg = false) (f : field) (mask : Bytes.data) (xor : Bytes.data)
    (v : Bytes.data) : matchcond = Syntax.MMasked (f, neg, mask, xor, v)

(* ---- verdict-neutral statement builders ---- *)
let counter : Syntax.stmt = Syntax.SCounter (0, 0)
let notrack : Syntax.stmt = Syntax.SNotrack
let log (opts : string) : Syntax.stmt = Syntax.SLog opts

let rule ?(stmts = []) (matches : matchcond list) (verdict : verdict) : rule =
  { Syntax.r_body =
      Stdlib.List.map (fun m -> Syntax.BMatch m) matches
      @ Stdlib.List.map (fun s -> Syntax.BStmt s) stmts;
    r_verdict = verdict; r_vmap = None; r_nat = None; r_tproxy = None; r_fwd = None;
    r_queue = None; r_after = [] }

let chain (policy : verdict) (rules : rule list) : chain =
  { Syntax.c_policy = policy; c_rules = rules }

(* ---- the verified pipeline ---- *)
let compile : chain -> program = Compile.compile_chain
let optimize : chain -> chain = Optimize.optimize_chain
let compile_optimized (c : chain) : program = compile (optimize c)

(* ---- rendering (untrusted, corpus-tested) ---- *)
let to_netlink_text : program -> string = Codec.render_program
let render_instr : Bytecode.instr -> string = Codec.render_instr

(* ---- the .nft text frontend (untrusted parser; see Nft_parse) ----
   parse a ruleset file/string into the Syntax AST + the set/map environment its
   lookups read, so properties can be proved about it (and, via the verified
   compiler, of the installed bytecode). *)
type parsed = Nft_lower.parsed
let parse_string : string -> parsed = Nft_parse.parse_string
let parse_file   : string -> parsed = Nft_parse.parse_file
(* all chains of the named table (for jump resolution by eval_table) *)
let table_chains (p : parsed) ~(table : string) : (string * chain) list =
  Nft_lower.chains_of p ~table
let find_chain (p : parsed) ~(table : string) ~(chain : string) : chain =
  Nft_lower.find_chain p ~table ~chain
