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

Extraction Language OCaml.
Set Extraction Output Directory "extracted".

(* The control-plane compiler/optimizer and the field table are what the glue
   needs; we also extract the packet semantics ([eval_chain] and the bytecode VM
   [run_chain]) so an executable test can witness [compile_chain_correct] on
   concrete packets (semtest.ml). *)
Separate Extraction
  compile_chain
  optimize_chain
  field_load
  all_fields
  eval_chain
  run_chain
  compile_env
  eval_table
  run_table
  eval_chain_mut
  run_chain_mut
  eval_ruleset
  run_ruleset
  set_env
  seq_eval
  env_with_sets.
