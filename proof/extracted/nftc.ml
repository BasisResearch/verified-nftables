(* Nftc: a reusable, formally-verified nftables compiler.

   `compile` and `optimize` are EXTRACTED from machine-checked Rocq proofs
   (compile_chain_correct: the emitted bytecode filters every packet exactly as
   the DSL says; optimize_chain_correct: the optimizer never changes a verdict).

   The only untrusted step of this verified compile/optimize/render pipeline is
   the renderer `to_netlink_text`, differentially tested byte-identical against
   upstream `nft --debug=netlink`. The DSL builders below (eq/neq/range/cmp/
   masked/rule/chain) are trivial structural wrappers around the `Syntax`
   constructors the proof reasons about. The optional `.nft` text frontend
   (parse_string/parse_file, see below) is likewise untrusted glue, validated
   externally against live `nft` rather than part of the proof TCB. See nftc.mli
   for the per-symbol trust labels. *)

module Verdict = Verdict
module Packet = Packet
module Syntax = Syntax
module Bytecode = Bytecode
module Semantics = Semantics

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
    (v : Bytes.data) : matchcond =
  Syntax.MMasked (f, (if neg then Bytecode.CNe else Bytecode.CEq), mask, xor, v)

(* ---- verdict-neutral statement builders ---- *)
let counter : Syntax.stmt = Syntax.SCounter (0, 0)
let notrack : Syntax.stmt = Syntax.SNotrack
let log (opts : string) : Syntax.stmt = Syntax.SLog opts

let rule ?(stmts = []) (matches : matchcond list) (verdict : verdict) : rule =
  { Syntax.r_body =
      Stdlib.List.map (fun m -> Syntax.BMatch m) matches
      @ Stdlib.List.map (fun s -> Syntax.BStmt s) stmts;
    r_outcome = (match verdict with
                 | Verdict.Continue -> Syntax.ONone
                 | _ -> Syntax.OVerdict verdict);
    r_after = [] }

let chain (policy : verdict) (rules : rule list) : chain =
  { Syntax.c_policy = policy; c_rules = rules }

(* ---- the verified pipeline ---- *)
let compile : chain -> program = Compile.compile_chain
let optimize : chain -> chain = Optimize.optimize_chain
let compile_optimized (c : chain) : program = compile (optimize c)

(* the full verified consolidation pipeline, via the unconditional extracted entry
   [Optimize_Uncond.optimize_table_uncond : chain -> (nat * set_decls) * chain] *)
let optimize_table (c : chain) : Semantics.set_decls * chain =
  let (nd, c') = Optimize_Uncond.optimize_table_uncond c in
  (snd nd, c')

(* ---- rendering (untrusted, corpus-tested) ---- *)
let to_netlink_text : program -> string = Codec.render_program
(* NB: context-free single-instruction render (host-endian fields render in the
   corpus big-endian layout).  Use [to_netlink_text]/[Codec.render_rule] for the
   field-aware, corpus-faithful rendering of a whole rule. *)
let render_instr (i : Bytecode.instr) : string = Codec.render_instr i

(* ---- the .nft text frontend (untrusted parser; see Nft_parse) ----
   parse a ruleset file/string into the Syntax AST + the set/map environment its
   lookups read, so properties can be proved about it (and, via the verified
   compiler, of the installed bytecode). *)
type parsed = Nft_inject.parsed
let parse_string : string -> parsed = Nft_parse.parse_string
let parse_file   : string -> parsed = Nft_parse.parse_file
(* all chains of the named table (for jump resolution by eval_table) *)
let table_chains (p : parsed) ~(table : string) : (string * chain) list =
  Nft_inject.chains_of p ~table
let find_chain (p : parsed) ~(table : string) ~(chain : string) : chain =
  Nft_inject.find_chain p ~table ~chain
