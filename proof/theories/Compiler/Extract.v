(** * Extract: extract the verified compiler and optimizer to OCaml.

    We extract the datatypes plus [compile_chain] and [optimize_chain].  A thin,
    untrusted OCaml wrapper (see [extracted/glue.ml]) builds concrete chains,
    runs the verified [optimize_chain]/[compile_chain], and renders the result
    in the exact textual format of [nft --debug=netlink] for differential
    testing against the real tool. *)

From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
(* ExtrOcamlNatInt realises Rocq's unbounded [nat] as OCaml's 63-bit native
   int, whose arithmetic WRAPS — a semantics the proofs know nothing about.
   This is sound only while no extracted [nat] computation can reach 2^62.
   Classification of the [nat]s that flow through the extracted term:

   - STRUCTURALLY BOUNDED (no guard needed): individual bytes are [mod 256]
     by construction ([data] is [list nat] of bytes); addresses/hashes travel
     as [N] or byte lists, not [nat]; register/slot indices, field widths and
     offsets are small compiler constants; [seed_start] (the optimizer's
     fresh-name seed) is a MAX over the input chain's set-name LENGTHS
     (Optimize_Table.v), so it is bounded by the longest name in the file.

   - USER-CONTROLLED (guarded in the untrusted frontend): [ls_rate]/[ls_burst]
     of a `limit` spec come from `limit rate N <unit>/<time>` literals, scaled
     by up to 2^20 (`mbytes`), and the semantics multiplies them by
     [lim_window] <= 604800 ([lim_cost]/[lim_max], Semantics.v) — so a raw
     rate near 2^43 already overflows the extracted product.  The frontend
     REJECTS scaled rates/bursts above 2^40 (`scaled_or_reject`, parser.mly;
     re-checked in nft_lower.ml limit_spec), keeping the largest extracted
     product below 604800 * 2^41 < 2^62.  Oversized integer LITERALS
     (> OCaml max_int) are a clean lexer error, not an int_of_string crash.
     `quota` has no parser surface today; if one is added, its byte count is
     the same class and needs the same guard.

   The TCB paragraph in DEVELOPMENT.md ("Trust story") carries this argument;
   `make parse-test` pins the oversized-rate rejection. *)
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlNativeString.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics Compile Optimize Nftval Elab.
From Nft Require Import Optimize_ValueSet Optimize_Vmap Optimize_Concat Optimize_Table Optimize_Uncond.
(* The typed-layer surface (T1): the Coq surface AST, datatype/coercion
   lattice, symbol tables, selector map and typechecker.  Extracted so the
   OCaml frontend can hand its untyped tree (via the pure structural
   injection extracted/nft_inject.ml) to the VERIFIED checker — parse-test
   gates all four rulesets and the tests/illtyped suite through it. *)
From Nft Require Import Ast Datatype Symbols Selector Typecheck.
(* The typed-layer scalar lowering (M2): typed match terms + verified
   elaboration ([Typed]), the scalar-match lowering / dep-guard encoding /
   guard discharge ([Lower]), and the independent typed semantics
   ([TypedEval], extracted so a harness can execute the typed evaluator).
   With these the OCaml frontend constructs NO byte-level match condition for
   any scalar match shape — see extracted/nft_lower.ml (driver only). *)
From Nft Require Import Typed Lower TypedEval.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".

(* [string_of_nat n] is, by definition, the [n]-fold repetition of the char 'I'
   (see [Optimize_ValueSet.string_of_nat]).  The default [ExtrOcamlNativeString]
   realisation of the per-char [String.String] constructor emits [String.make 1 c
   ^ s], which resolves [String] to the (empty) extracted [String] module rather
   than [Stdlib.String], breaking the build.  We realise it directly and
   faithfully with the native equivalent — this is the SAME string value, used
   only to mint the fresh `__setN`/`__vmapN` names (whose only proved property is
   injectivity), so the realisation does not enter any trusted proof. *)
Extract Constant Optimize_ValueSet.string_of_nat =>
  "(fun n -> Stdlib.String.make n 'I')".

(* [String.length] is the one Stdlib.Strings.String CONSTANT in the extracted
   closure (Optimize_Uncond's fresh-name seed measures set-name lengths).
   Left alone, extraction emits a String.ml for it whose presence inside the
   (wrapped false) nftc library SHADOWS Stdlib.String — breaking the
   `String.get`/`String.sub` calls in ExtrOcamlNativeString's inline
   string-match realizer (Nftval.sbytes, Symbols.parse_dec destructure
   strings) and any unqualified Stdlib.String use in hand-written glue.
   Realise it natively instead: under ExtrOcamlNativeString (string = native
   string) + ExtrOcamlNatInt (nat = int), Stdlib.String.length IS Coq's
   String.length — same int on the same value.  Same seam class as
   [string_of_nat] above; extracted/dune additionally excludes any stray
   String module from the library. *)
Extract Inlined Constant String.length => "Stdlib.String.length".

(* The control-plane compiler/optimizer and the field table are what the glue
   needs; we also extract the packet semantics ([eval_chain] and the bytecode VM
   [run_chain]) so an executable test can witness [compile_chain_correct] on
   concrete packets (semtest.ml). *)
Separate Extraction
  compile_chain
  optimize_chain
  optimize_table
  optimize_table_uncond
  optimize_chain_valueset
  optimize_chain_vmap
  optimize_chain_concat
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
  seq_eval
  env_with_sets
  mut_wf
  Nftval.encode
  Elab.elab_m
  Typed.elab_tx
  Typed.tx_view
  Lower.lower_match
  Lower.lower_bitmatch
  Lower.dep_guard
  Lower.discharge
  Lower.lerr_message
  TypedEval.eval_txm
  Selector.dep_ip4
  Selector.dep_ip6
  Typecheck.typecheck_ruleset
  Typecheck.typecheck_rule
  Typecheck.typecheck_clause
  Typecheck.resolve_value
  Typecheck.resolve_num
  Symbols.lookup_symbol
  Selector.selector
  Selector.bitfield
  Datatype.dt_width
  Datatype.dt_bytes
  Datatype.dt_byteorder
  Datatype.basetype_of
  Datatype.coercible
  Datatype.int_basetype
  Datatype.lit_fits.
