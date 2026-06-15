(** * Extract: extract the verified compiler and optimizer to OCaml.

    We extract the datatypes plus [compile_chain] and [optimize_chain].  A thin,
    untrusted OCaml wrapper (see [extracted/glue.ml]) builds concrete chains,
    runs the verified [optimize_chain]/[compile_chain], and renders the result
    in the exact textual format of [nft --debug=netlink] for differential
    testing against the real tool. *)

From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics Compile Optimize.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".

Separate Extraction
  compile_chain
  optimize_chain
  eval_chain.
