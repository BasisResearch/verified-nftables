(** * Optimize_Linearize: nft's ALWAYS-ON single-rule linearization, composed
    into the DEFAULT compile pipeline.

    nftables applies two single-rule rewrites UNCONDITIONALLY when it
    linearizes a rule to netlink — no `nft -o` involved:

      - the adjacent-payload-load merge (src/payload.c [payload_can_merge] /
        [payload_expr_join]: `tcp sport 1 tcp dport 2` emits ONE 4-byte load) —
        corpus class I, [Optimize_PayMerge];
      - the bitwise-xor constant fold (src/evaluate.c [binop_transfer], OP_XOR:
        the register-side `^ C` moves onto the compare value) — corpus class L,
        [Optimize_XorFold].

    Both passes are SELF-GUARDING and their eval-preservation theorems are
    UNCONDITIONAL ([paymerge_chain_eval] / [xorfold_chain_eval]: no hypothesis
    on the chain, env or packet).  This file composes them into
    [linearize_chain] and defines the DEFAULT compile pipeline

        [compile_chain_default c = compile_chain (linearize_chain c)]

    — what `nftc compile` (and the final compile step of `nftc optimize`/
    `nftc send`) actually emits, so the shipped default output matches nft's
    default linearization.  The composed HEADLINE
    [compile_chain_default_correct] carries [compile_chain_correct] through the
    two stages, axiom-free.

    Placement mirrors nft: linearization happens AT EMISSION, after any `-o`
    consolidation — so the stage lives at the compile boundary (applied to
    whatever chain reaches the compiler), NOT inside
    [Optimize_Uncond.optimize_table_uncond]; the optimize path's composed
    headline is [Optimize_Uncond.optimize_table_uncond_compile_correct], which
    is stated over THIS pipeline.  The `-O paymerge` / `-O xorfold` registry
    passes remain (an explicit second application is idempotent in effect:
    both passes only rewrite where their guard still fires). *)

From Stdlib Require Import List.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Correct Optimize_PayMerge Optimize_XorFold.

(** The always-on single-rule linearization: payload merge, then xor fold.
    (The two rewrite disjoint shapes — payload equalities vs masked
    meta/ct compares — so the order is immaterial; nft folds the xor at
    evaluate time and merges payloads at linearize time, hence merge-then-fold
    matches composing "what reaches the wire".) *)
Definition linearize_chain (c : chain) : chain :=
  xorfold_chain (paymerge_chain c).

(** Verdict preservation, UNCONDITIONAL — the two stage theorems composed. *)
Theorem linearize_chain_eval : forall c e p,
  eval_chain (linearize_chain c) e p = eval_chain c e p.
Proof.
  intros c e p. unfold linearize_chain.
  rewrite xorfold_chain_eval. apply paymerge_chain_eval.
Qed.

(** Both stages copy the policy verbatim. *)
Lemma linearize_chain_policy : forall c,
  c_policy (linearize_chain c) = c_policy c.
Proof. reflexivity. Qed.

(** ** The DEFAULT compile pipeline: linearize, then compile.
    This is the term `nftc compile` emits (and the final compile of
    `nftc optimize` / `nftc send`). *)
Definition compile_chain_default (c : chain) : program :=
  compile_chain (linearize_chain c).

(** HEADLINE (default-pipeline axis): the DEFAULT pipeline's bytecode, run on
    the VM, yields EXACTLY the DSL verdict of the source chain — for every
    chain, environment and packet.  [compile_chain_correct] carried through the
    two always-on stages.  Axiom-free (gated in `make axioms`). *)
Theorem compile_chain_default_correct : forall c e p,
  run_chain (compile_chain_default c) (c_policy c) e p = eval_chain c e p.
Proof.
  intros c e p.
  change (c_policy c) with (c_policy (linearize_chain c)).
  unfold compile_chain_default.
  rewrite compile_chain_correct. apply linearize_chain_eval.
Qed.

(** Sets/maps-as-declared-objects corollary, the [compile_chain_sets_correct]
    mirror — the form [Optimize_Uncond]'s optimize-then-compile headline
    composes with. *)
Corollary compile_chain_default_sets_correct : forall c base d p,
  run_chain (compile_chain_default c) (c_policy c) (env_with_sets base d) p
  = eval_chain c (env_with_sets base d) p.
Proof. intros. apply compile_chain_default_correct. Qed.

(* ================================================================== *)
(** ** Non-vacuity: the DEFAULT pipeline genuinely merges (mirrors the
    [Optimize_Dnat] Compute-witness style).

    Class I: `tcp sport 1 tcp dport 2` — plain [compile_chain] emits TWO
    2-byte transport loads; the default pipeline emits ONE 4-byte load with
    the concatenated compare value (exactly nft's default emission,
    inet/payloadmerge.t.payload:1). *)
Definition linz_demo_chain : chain :=
  {| c_policy := Accept;
     c_rules := [ {| r_body := [BMatch (MEq FThSport [0;1]);
                                BMatch (MEq FThDport [0;2])];
                     r_outcome := ONone; r_after := [] |} ] |}.

Example default_pipeline_merges_payload_loads :
  compile_chain_default linz_demo_chain
  = [[IPayloadLoad PTransport 0 4 1; ICmp CEq 1 [0;1;0;2]]].
Proof. vm_compute. reflexivity. Qed.

Example plain_compile_emits_two_loads :
  compile_chain linz_demo_chain
  = [[IPayloadLoad PTransport 0 2 1; ICmp CEq 1 [0;1];
      IPayloadLoad PTransport 2 2 1; ICmp CEq 1 [0;2]]].
Proof. vm_compute. reflexivity. Qed.

(** Class L: `meta mark xor 0x23 == 0x11` — the default pipeline emits the
    xor operand FOLDED into the compare value (0x11 ^ 0x23 = 0x32), xor slot
    zeroed, exactly nft's default emission (any/meta.t.payload:174; mark
    register bytes little-endian). *)
Definition linz_xor_chain : chain :=
  {| c_policy := Accept;
     c_rules := [ {| r_body := [BMatch (MMasked FMetaMark CEq
                                          (repeat 255 4) [35;0;0;0] [17;0;0;0])];
                     r_outcome := ONone; r_after := [] |} ] |}.

Example default_pipeline_folds_xor :
  compile_chain_default linz_xor_chain
  = [[IMetaLoad MKmark 1; IBitwise 1 1 (repeat 255 4) [0;0;0;0];
      ICmp CEq 1 [50;0;0;0]]].
Proof. vm_compute. reflexivity. Qed.

(** Axiom-freedom audit (build-time guard; enforcement is `make axioms`). *)
Print Assumptions linearize_chain_eval.
Print Assumptions compile_chain_default_correct.
