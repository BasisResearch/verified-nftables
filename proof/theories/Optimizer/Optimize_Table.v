(** * Optimize_Table: COMPOSE the verified nft -o consolidation passes into a
    single runnable optimizer, with a whole-pipeline correctness theorem.

    This file composes the base dedup/DCE pass with the N-WAY value->set /
    value+verdict->vmap / two-selector->concat passes into [optimize_table],
    threading a fresh counter and a [set_decls] accumulator across the table
    semantics, and provides the pipeline-composition seam lemmas the
    UNCONDITIONAL correctness proofs build on.

    The whole-pipeline correctness of [optimize_table] is proved — with NO
    [rules_clean] and NO freshness precondition on the input — over the state fold
    in [Optimize_MutEnv.v] ([optimize_table_uncond_mut_st_correct]) and composed
    to the bytecode in
    [Optimize_Linearize_MutSt.optimize_table_uncond_compile_mut_st_correct].  That
    UNCONDITIONAL optimizer ([optimize_table_uncond], defined in [Optimize_Uncond.v])
    is what [Extract.v] extracts and what the [glue.ml] CLI invokes, so the shipped
    tool RUNS the verified term. *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Correct Optimize Optimize_ValueSet Optimize_Vmap Optimize_VmapGuarded Optimize_Concat Optimize_ConcatMulti
  Optimize_ConcatGuarded Optimize_SetGuarded Optimize_IntervalSet Optimize_IntervalSetGuarded Optimize_MixedPointRangeGuarded Optimize_Absorb Optimize_CtMask Optimize_Dscp Optimize_DscpVmap Optimize_IntervalSetHostOrder Optimize_DataMap Optimize_Dnat Optimize_Snat Optimize_Table_Inv.

(** ** Step 2 (first rung): compose base [optimize_chain] then the N-WAY value->set
    pass.  Step 1 supplies the [rules_clean] hypothesis the [valueset] theorem needs. *)


(** *** First-rung whole-pipeline correctness, axiom-free. *)

(** ** Step 3: the FULL four-stage pipeline and its whole-pipeline correctness.

    [optimize_table] runs the base dedup/DCE pass, then the N-way value->set
    merge, the two-selector->concat merge, and finally the value+verdict->vmap
    merge, threading the fresh-name counter and [set_decls] accumulator across the
    table semantics.  Its whole-pipeline correctness — preserving the state fold
    over the synthesised declarations, UNCONDITIONALLY — is proved in
    [Optimize_MutEnv.v]; this file provides the composition seam lemmas it builds on.

    The seam between passes is the crux: each pass runs on the PREVIOUS pass's output,
    which is no longer [rules_clean] (it carries merged [MConcatSet] lookup rules).
    [Optimize_Uncond.v] discharges this without any input precondition — a
    passed-through rule stays env-stable because the synthesised names are minted
    fresh past every name the input declares/reads (read-freshness), and fresh-name
    discipline is threaded by [optimize_chain_valueset_fresh_setname] and the
    cross-namespace stability lemmas (valueset/concat leave [sd_vmaps] fixed) — the
    seam lemmas this file provides.

    *** `nft -o` FIDELITY CONTRACT (precise; see [Optimize_DataMap] D1 note + [e2e.sh]).

    All stages EXCEPT [datamap] emit output that `nft --optimize` (nft v1.1.6) also
    emits (differentially confirmed, netns): the bare NAT maps ([dnat]/[snat],
    NFT_BREAK-on-miss), the anonymous value sets ([valueset]), the concat sets
    ([concatmulti]/[concat]/[concatguarded]), the interval sets ([intervalset]) and the verdict
    maps ([vmap]).  The [datamap] stage (`meta mark set … map`) is DIFFERENT: `nft -o`
    does NOT merge `meta mark set` rules at all, so [datamap] is a LABELLED SOUND
    SUPERSET with no `nft -o` counterpart — NOT part of the byte-fidelity claim, and
    NOT an nft bug (nft is merely conservative; the merge is verdict/state-preserving
    per [Optimize_DataMap.eval_rules_mut_map_merge], and its effect-level shape
    certificate [Optimize_MutEnv.eval_rules_mut_st_map_merge] — full state:
    verdict + (env, packet) out — IS composed through [optimize_table]: the
    pipeline-level effect guarantee is
    [Optimize_MutEnv.optimize_table_uncond_mut_st_correct]).  [datamap] emits the HEAD-GUARDED
    form (a synthesised key set in front of the map) because our model loads a
    default on a statement value-map miss rather than NFT_BREAKing; the guard makes
    the lookup always hit, recovering exact equivalence.  Why the guard cannot just
    be dropped — and why doing so would touch the [compile_chain_correct] headline
    with no fidelity payoff — is pinned axiom-free in
    [Optimize_DataMap.mapn_bare_diverges_offkey]. *)
Definition optimize_table (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(nA, dA, cA) := optimize_chain_absorb n d (optimize_chain c) in
  let '(nT, dT, cT) := optimize_chain_ctmask nA dA cA in
  let '(nD, dD, cD) := optimize_chain_dnat nT dT cT in
  let '(nS, dS, cS) := optimize_chain_snat nD dD cD in
  let '(n1, d1, c1) := optimize_chain_valueset nS dS cS in
  let '(nK, dK, cK) := optimize_chain_concatmulti n1 d1 c1 in
  let '(nM, dM, cM) := optimize_chain_datamap nK dK cK in
  let '(n2, d2, c2) := optimize_chain_concat nM dM cM in
  let '(nG, dG, cG) := optimize_chain_concatguarded n2 d2 c2 in
  let '(nGs, dGs, cGs) := optimize_chain_setguarded nG dG cG in
  let '(nI, dI, cI) := optimize_chain_intervalset nGs dGs cGs in
  let '(nIt, dIt, cIt) := optimize_chain_intervalsethostorder nI dI cI in
  let '(nDs, dDs, cDs) := optimize_chain_dscp nIt dIt cIt in
  let '(nIg, dIg, cIg) := optimize_chain_intervalsetguarded nDs dDs cDs in
  let '(nMx, dMx, cMx) := optimize_chain_mixedpointrangeguarded nIg dIg cIg in
  let '(nVg, dVg, cVg) := optimize_chain_vmapguarded nMx dMx cMx in
  let '(nDv, dDv, cDv) := optimize_chain_dscpvmap nVg dVg cVg in
  optimize_chain_vmap nDv dDv cDv.

(** ** Correctness of [optimize_table] is proved UNCONDITIONALLY over the state
    fold — with NO [rules_clean] and NO caller-supplied freshness side-condition on
    the input chain:

      [Optimize_MutEnv.optimize_table_mut_st_correct_uncond_gen] : general (n,d)
        form, freshness obligations only (which a clean input would also satisfy —
        [rules_clean] is subsumed);
      [Optimize_MutEnv.optimize_table_uncond_mut_st_correct] /
      [Optimize_Linearize_MutSt.optimize_table_uncond_compile_mut_st_correct] :
        the fresh-table entry [optimize_table_uncond c], with NO hypothesis on [c]
        beyond numgen-freedom.

    The freshness is discharged internally by seeding the fresh-name counter past
    every name the input declares/reads (see [seed_start], [Optimize_Uncond.v]). *)

