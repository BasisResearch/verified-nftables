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
From Stdlib Require Import BinNat.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics Compile Optimize Nftval.
(* The kernel register-file validator (W2): extracted so the corpus round-trip
   asserts [regs_valid] on every compiled rule at runtime (corpus_test.ml) —
   the executable twin of RegsValid_Proofs.lower_ruleset_default_regs_valid. *)
From Nft Require Import RegsValid.
From Nft Require Import Optimize_ValueSet Optimize_Vmap Optimize_Concat Optimize_Table Optimize_Uncond.
(* The named, composable pass system: the two intra-rule passes plus the
   chain-level pipeline stages, each bundled with its eval-preservation proof,
   and the ONE generic composition theorem [run_passes_correct].  Extracted so
   the CLI's [-O p1,p2,...] parses names into a pass list and folds them
   ([resolve_passes]/[run_passes]) with no proof of its own. *)
From Nft Require Import Optimize_PayMerge Optimize_XorFold Optimize_Elide
  Optimize_Registry.
(* The DEFAULT compile pipeline (nft's always-on linearization: payload merge +
   xor fold, then compile) — what `nftc compile` and the final compile step of
   `nftc optimize`/`nftc send` emit
   ([Optimize_Linearize_MutSt.compile_chain_default_mut_st_correct]). *)
From Nft Require Import Optimize_Linearize.
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

(* [Lower.nat_dec] mints the DECIMAL suffix of the interned `__setN`/`__mapN`
   names (byte-identical to the historical OCaml `Printf.sprintf "%s%d"`).  Its
   Coq body is a faithful decimal renderer used only by vm_compute witnesses;
   the extracted binary uses the native [string_of_int] — the SAME string value,
   same seam class as [string_of_nat] above (only injectivity/decimalness is
   relied on, and the golden corpus/gen-check re-check every produced name). *)
Extract Constant Lower.nat_dec => "Stdlib.string_of_int".

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

(* [N.of_nat] converts a literal int (nat = OCaml int under ExtrOcamlNatInt) to
   the binary [N] a register value is built from ([Typecheck.resolve_num]
   receives `N.of_nat n` for every `SVNum n`).  Coq's [N.of_nat] runs through
   [Pos.of_succ_nat], which recurses ONCE PER UNIT — O(n), non-tail — so a
   real literal like `meta mark 0x80000000` (2^31, well within the frontend's
   2^40 seam bound) exhausts the OCaml stack before it ever reaches the range
   check.  Realise it in log(n) by reading the int's bits directly; the value
   is identical to Coq's [N.of_nat] (XH=1, XO p=2p, XI p=2p+1), so no proof or
   corpus round-trip observes a difference — only the recursion depth changes.
   Placed in [BinNat]'s scope (open BinNums), so [N0]/[Npos]/[Coq_x*] resolve. *)
Extract Constant N.of_nat =>
  "(fun n ->
      if n <= 0 then N0
      else
        let rec pos_of_int m =
          if m <= 1 then Coq_xH
          else if m land 1 = 1 then Coq_xI (pos_of_int (m asr 1))
          else Coq_xO (pos_of_int (m asr 1)) in
        Npos (pos_of_int n))".

(* The control-plane compiler/optimizer and the field table are what the glue
   needs; we also extract the effect-threading packet semantics
   ([eval_chain_mut]) and the bytecode VM ([run_chain_mut]) so an executable test
   can witness [compile_chain_mut_correct] on concrete packets (semtest.ml). *)
Separate Extraction
  compile_chain
  RegsValid.regs_valid
  RegsValid.regs_valid_prog
  RegsValid.instr_regs_ok
  optimize_chain
  optimize_table
  optimize_table_uncond
  paymerge_chain
  xorfold_chain
  elide_chain
  linearize_chain
  compile_chain_default
  run_passes
  resolve_passes
  registry
  registry_names
  optimize_chain_valueset
  optimize_chain_vmap
  optimize_chain_concat
  field_load
  all_fields
  compile_env
  eval_chain_mut
  run_chain_mut
  eval_chain_mut_env
  run_chain_mut_env
  eval_chain
  chain_out
  chain_out_env
  eval_table
  run_table
  eval_ruleset
  run_ruleset
  eval_hook
  apply_nat
  nat_drops
  seq_eval_env
  env_with_sets
  rule_numgen_free
  dsl_step dsl_writes rule_step body_step
  Nftval.encode
  Typed.elab_tx
  Lower.lower_match
  Lower.lower_bitmatch
  Lower.dep_guard
  Lower.discharge
  Lower.lerr_message
  Lower.ls0
  Lower.fresh_map
  Lower.add_set
  Lower.add_vmap
  Lower.add_map
  Lower.lower_anon_set
  Lower.lower_set_ref
  Lower.lower_concat_set
  Lower.vmap_entries_single
  Lower.vmap_entries_concat
  Lower.decl_set_elems
  Lower.decl_vmap_ents
  Lower.lower_ruleset
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
