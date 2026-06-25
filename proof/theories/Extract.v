(** * Extract: extract the verified compiler and optimizer to OCaml.

    We extract the datatypes plus [compile_chain] and [optimize_chain].  A thin,
    untrusted OCaml wrapper (see [extracted/glue.ml]) builds concrete chains,
    runs the verified [optimize_chain]/[compile_chain], and renders the result
    in the exact textual format of [nft --debug=netlink] for differential
    testing against the real tool. *)

From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlNativeString.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics Compile Optimize.
From Nft Require Import Optimize_Merge Optimize_Vmap Optimize_Concat Optimize_Table Optimize_Uncond.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".

(* [string_of_nat n] is, by definition, the [n]-fold repetition of the char 'I'
   (see [Optimize_Merge.string_of_nat]).  The default [ExtrOcamlNativeString]
   realisation of the per-char [String.String] constructor emits [String.make 1 c
   ^ s], which resolves [String] to the (empty) extracted [String] module rather
   than [Stdlib.String], breaking the build.  We realise it directly and
   faithfully with the native equivalent — this is the SAME string value, used
   only to mint the fresh `__setN`/`__vmapN` names (whose only proved property is
   injectivity), so the realisation does not enter any trusted proof. *)
Extract Constant Optimize_Merge.string_of_nat =>
  "(fun n -> Stdlib.String.make n 'I')".

(* The control-plane compiler/optimizer and the field table are what the glue
   needs; we also extract the packet semantics ([eval_chain] and the bytecode VM
   [run_chain]) so an executable test can witness [compile_chain_correct] on
   concrete packets (semtest.ml). *)
Separate Extraction
  compile_chain
  optimize_chain
  optimize_table
  optimize_table_uncond
  optimize_chain_setsN
  optimize_chain_vmapN
  optimize_chain_concatN
  field_load
  all_fields
  eval_chain
  run_chain
  compile_env
  eval_table
  run_table
  eval_chain_mut
  run_chain_mut
  eval_chain_mut_env
  run_chain_mut_env
  eval_chain_trace
  chain_out
  seq_eval_env
  eval_ruleset
  run_ruleset
  set_env
  seq_eval
  env_with_sets.
