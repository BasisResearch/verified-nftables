(** * Optimize_Registry: a named, composable pass system with ONE generic
    composition theorem, over the STATE-THREADING fold.

    The three intra-rule passes ([Optimize_PayMerge.paymerge_chain],
    [Optimize_XorFold.xorfold_chain], [Optimize_Elide.elide_chain]) plus the
    chain-level stages of the shipped pipeline ([Optimize_Normalize.normalize_chain]
    head normalisation and [Optimize.optimize_chain] the base absorb/DCE pass) are
    each an [opt_pass]: a NAMED [chain -> chain] transform BUNDLED with its
    [eval_chain_mut_st]-preservation proof.  The certificate is over the full
    observable of the effect-threading fold — verdict AND the resulting (env,
    packet) — so a registered pass can alter neither a `meta mark` write nor a
    dynset-learned element, on any hook.

    An [opt_pass] is state-preserving BY CONSTRUCTION (the proof is a field), so
    folding ANY list of passes preserves [eval_chain_mut_st] — [run_passes_correct],
    proved ONCE by induction over the list, quantified over every pass list and
    every hook.  The CLI ([-O p1,p2,...]) only parses names into a pass list via
    [resolve_passes] (a lookup into [registry]); it composes NO byte and carries
    NO proof.  The whole-pipeline `default` (the set-synthesising
    [Optimize_Uncond.optimize_table_uncond], whose correctness changes the
    environment with the synthesised declarations) is NOT a pure [chain -> chain]
    pass and is handled by the CLI's existing table path — see
    [Optimize_MutEnv.optimize_table_uncond_mut_st_correct].  Axiom-free. *)

From Stdlib Require Import List String Bool.
From Nft Require Import Syntax Semantics
     Optimize Optimize_Normalize Optimize_PayMerge Optimize_XorFold
     Optimize_Elide Optimize_MutEnv Optimize_Linearize_MutSt.
Import ListNotations.

(** A registered optimizer pass: a name, a chain transform, and the PROOF that
    it preserves every chain's threaded (verdict, env, packet) on every hook, env
    and packet. *)
Record opt_pass : Type := {
  op_name    : string;
  op_fn      : chain -> chain;
  op_correct : forall h c e p,
    eval_chain_mut_st h (op_fn c) e p = eval_chain_mut_st h c e p
}.

Definition pass_normalize : opt_pass :=
  {| op_name := "normalize"; op_fn := normalize_chain;
     op_correct := normalize_chain_mut_st |}.

Definition pass_base : opt_pass :=
  {| op_name := "base"; op_fn := optimize_chain;
     op_correct := optimize_chain_mut_st |}.

Definition pass_paymerge : opt_pass :=
  {| op_name := "paymerge"; op_fn := paymerge_chain;
     op_correct := paymerge_chain_mut_st |}.

Definition pass_xorfold : opt_pass :=
  {| op_name := "xorfold"; op_fn := xorfold_chain;
     op_correct := xorfold_chain_mut_st |}.

Definition pass_elide : opt_pass :=
  {| op_name := "elide"; op_fn := elide_chain;
     op_correct := elide_chain_mut_st |}.

(** The registry: every pass exposed by name to [-O]. *)
Definition registry : list opt_pass :=
  [pass_normalize; pass_base; pass_paymerge; pass_xorfold; pass_elide].

(** Apply a pass list to a chain, LEFT TO RIGHT (the user's [-O] order). *)
Definition run_passes (ps : list opt_pass) (c : chain) : chain :=
  fold_left (fun acc p => op_fn p acc) ps c.

(** THE generic composition theorem: folding ANY pass list preserves the threaded
    (verdict, env, packet) — proved once, over an arbitrary list and hook, using
    each entry's bundled [op_correct].  No hypothesis on the passes beyond being
    [opt_pass]es. *)
Theorem run_passes_correct : forall ps h c e p,
  eval_chain_mut_st h (run_passes ps c) e p = eval_chain_mut_st h c e p.
Proof.
  unfold run_passes.
  induction ps as [| pss ps IH]; intros h c e p; [reflexivity|].
  cbn [fold_left]. rewrite IH. apply op_correct.
Qed.

(** Look a pass up by name in a list. *)
Fixpoint lookup_pass (nm : string) (ps : list opt_pass) : option opt_pass :=
  match ps with
  | [] => None
  | p :: rest => if String.eqb (op_name p) nm then Some p else lookup_pass nm rest
  end.

(** Resolve a list of names to a pass list against the registry, ORDER
    PRESERVED; [None] if any name is unknown (the CLI reports it). *)
Definition resolve_passes (names : list string) : option (list opt_pass) :=
  fold_right (fun nm acc =>
                match acc, lookup_pass nm registry with
                | Some ps, Some p => Some (p :: ps)
                | _, _ => None
                end) (Some []) names.

(** Corollary at the resolution boundary: whatever names resolve to, running
    them preserves the threaded state — the CLI needs no separate proof. *)
Theorem resolve_run_correct : forall names ps h c e p,
  resolve_passes names = Some ps ->
  eval_chain_mut_st h (run_passes ps c) e p = eval_chain_mut_st h c e p.
Proof. intros. apply run_passes_correct. Qed.

(** The list of registered names, for [--list-passes]. *)
Definition registry_names : list string := map op_name registry.

Print Assumptions run_passes_correct.
