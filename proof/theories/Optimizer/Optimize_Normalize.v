(** * Optimize_Normalize: a verdict-preserving head normalisation that lets the
    [nft -o] consolidation passes fire on PARSER output.

    The merge recognisers ([Optimize_ValueSet.head_value], [Optimize_Concat.head_value2],
    [Optimize_Vmap]) match a leading ordered comparison [MCmp f CEq v].  But the
    [.nft] frontend lowers an equality match (`ip saddr 10.0.0.1`) to [MEq f v], NOT
    [MCmp f CEq v].  These two matchconds are EXTENSIONALLY EQUAL — same
    [match_loadable] (both [field_loadable f]) and same [eval_matchcond_body]
    (both [data_eqb (firstn (length v) (field_value f e p)) v]; see [eval_cmp]'s [CEq]
    clause) — so rewriting [MEq f v] to [MCmp f CEq v] changes no packet's verdict,
    yet exposes the head to the value->set / concat / vmap merges.

    This pass ([normalize_chain]) does exactly that rewrite over every rule body;
    its state-fold preservation is [Optimize_MutEnv.normalize_chain_flat].
    [Optimize_Uncond.optimize_table_uncond] runs it FIRST, so the SHIPPED optimizer
    consolidates real parsed rulesets (e.g. three adjacent `ip saddr <a>` rules ->
    one `ip saddr { … }`).  The [normalize_mc_*] extensional-equality lemmas here are
    the substrate that state proof threads through.  Axiom-free. *)

From Stdlib Require Import List Bool.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics.
Import ListNotations.

(** Rewrite an equality match to the ordered-comparison form the merges recognise.
    Every other matchcond is left untouched. *)
Definition normalize_mc (m : matchcond) : matchcond :=
  match m with
  | MEq f v => MCmp f CEq v
  | _ => m
  end.

Definition normalize_bi (it : body_item) : body_item :=
  match it with
  | BMatch m => BMatch (normalize_mc m)
  | BStmt s => BStmt s
  end.

Definition normalize_rule (r : rule) : rule :=
  {| r_body := map normalize_bi (r_body r);
     r_outcome := r_outcome r; r_after := r_after r |}.

Definition normalize_chain (c : chain) : chain :=
  {| c_policy := c_policy c; c_rules := map normalize_rule (c_rules c) |}.

(** *** Per-matchcond extensional equality (the load-bearing fact). *)
Lemma normalize_mc_eval : forall m e p,
  eval_matchcond_body (normalize_mc m) e p = eval_matchcond_body m e p.
Proof. intros [f v|f v|f neg lo hi|f neg msk xr v|f op v| | | | | | | | ] e p; reflexivity. Qed.

Lemma normalize_mc_loadable : forall m p,
  match_loadable (normalize_mc m) p = match_loadable m p.
Proof. intros [f v|f v|f neg lo hi|f neg msk xr v|f op v| | | | | | | | ] p; reflexivity. Qed.

Lemma normalize_mc_matchcond : forall m e p,
  eval_matchcond (normalize_mc m) e p = eval_matchcond m e p.
Proof.
  intros m e p. unfold eval_matchcond.
  rewrite normalize_mc_loadable, normalize_mc_eval. reflexivity.
Qed.

(** [r_body (normalize_rule r)] is [map normalize_bi (r_body r)] — kept as an
    equation so [normalize_rule] stays FOLDED (the [normalize_mc_*] lemmas are
    stated about [normalize_rule r], so unfolding it would un-match them). *)
Lemma normalize_r_body : forall r, r_body (normalize_rule r) = map normalize_bi (r_body r).
Proof. reflexivity. Qed.

