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

let rule ?(stmts = []) (matches : matchcond list) (verdict : verdict) : rule =
  { Syntax.r_body =
      Stdlib.List.map (fun m -> Syntax.BMatch m) matches
      @ Stdlib.List.map (fun s -> Syntax.BStmt s) stmts;
    r_verdict = verdict; r_vmap = None; r_nat = None; r_tproxy = None }

let chain (policy : verdict) (rules : rule list) : chain =
  { Syntax.c_policy = policy; c_rules = rules }

(* ---- the verified pipeline ---- *)
let compile : chain -> program = Compile.compile_chain
let optimize : chain -> chain = Optimize.optimize_chain
let compile_optimized (c : chain) : program = compile (optimize c)

(* ---- rendering (untrusted, corpus-tested) ---- *)
let to_netlink_text : program -> string = Codec.render_program
let render_instr : Bytecode.instr -> string = Codec.render_instr
