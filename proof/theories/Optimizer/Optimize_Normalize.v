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

    This pass ([normalize_chain]) does exactly that rewrite over every rule body and
    is proved [eval_chain]-preserving.  [Optimize_Uncond.optimize_table_uncond] runs
    it FIRST, so the SHIPPED optimizer consolidates real parsed rulesets (e.g. three
    adjacent `ip saddr <a>` rules -> one `ip saddr { … }`).  Axiom-free. *)

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

(** *** Body-scan predicates are invariant (they only read the [BStmt] structure,
    which [normalize_bi] preserves verbatim). *)
Lemma normalize_body_has_notrack : forall body,
  body_has_notrack (map normalize_bi body) = body_has_notrack body.
Proof.
  induction body as [| it b IH]; [reflexivity|].
  unfold body_has_notrack in *. cbn [map existsb]. rewrite IH.
  destruct it as [m | s]; [reflexivity | destruct s; reflexivity].
Qed.

Lemma normalize_body_synproxy_stops : forall body p,
  body_synproxy_stops (map normalize_bi body) p = body_synproxy_stops body p.
Proof.
  induction body as [| it b IH]; intro p; [reflexivity|].
  unfold body_synproxy_stops in *. cbn [map existsb]. rewrite IH.
  destruct it as [m | s]; [reflexivity | destruct s; reflexivity].
Qed.

Lemma normalize_body_thread : forall body p,
  body_thread (map normalize_bi body) p = body_thread body p.
Proof.
  intros body p. unfold body_thread. rewrite normalize_body_has_notrack. reflexivity.
Qed.

(** *** Applicability / loadability walks are invariant. *)
Lemma normalize_rule_applies_walk : forall body e p,
  rule_applies_walk (map normalize_bi body) e p = rule_applies_walk body e p.
Proof.
  induction body as [| it b IH]; intros e p; [reflexivity|].
  destruct it as [m | s]; cbn [map normalize_bi rule_applies_walk].
  - rewrite normalize_mc_matchcond, IH. reflexivity.
  - destruct s; cbn [rule_applies_walk]; rewrite IH; reflexivity.
Qed.

Lemma normalize_body_item_loadable : forall it p,
  body_item_loadable (normalize_bi it) p = body_item_loadable it p.
Proof.
  intros [m | s] p; cbn [normalize_bi body_item_loadable].
  - apply normalize_mc_loadable.
  - reflexivity.
Qed.

Lemma normalize_body_loadable_walk : forall body p,
  body_loadable_walk (map normalize_bi body) p = body_loadable_walk body p.
Proof.
  induction body as [| it b IH]; intro p; [reflexivity|].
  destruct it as [m | s]; cbn [map normalize_bi body_loadable_walk body_item_loadable].
  - rewrite normalize_mc_loadable, IH. reflexivity.
  - destruct s; cbn [body_loadable_walk body_item_loadable stmt_loadable];
      rewrite IH; reflexivity.
Qed.

(** [end_loadable] reads only the verdict-map / terminal end fields, which
    [normalize_rule] copies verbatim — so it is unchanged. *)
Lemma normalize_end_loadable : forall r e p,
  end_loadable (normalize_rule r) e p = end_loadable r e p.
Proof. intros r e p. reflexivity. Qed.

(** [r_body (normalize_rule r)] is [map normalize_bi (r_body r)] — kept as an
    equation so [normalize_rule] stays FOLDED (the [normalize_*] lemmas are stated
    about [normalize_rule r], so unfolding it would un-match them). *)
Lemma normalize_r_body : forall r, r_body (normalize_rule r) = map normalize_bi (r_body r).
Proof. reflexivity. Qed.

Lemma normalize_rule_loadable : forall r e p,
  rule_loadable (normalize_rule r) e p = rule_loadable r e p.
Proof.
  intros r e p. unfold rule_loadable. rewrite normalize_r_body.
  rewrite normalize_body_loadable_walk, normalize_body_synproxy_stops, normalize_body_thread.
  destruct (body_synproxy_stops (r_body r) p); [reflexivity|].
  rewrite normalize_end_loadable. reflexivity.
Qed.

Lemma normalize_rule_applies : forall r e p,
  rule_applies (normalize_rule r) e p = rule_applies r e p.
Proof.
  intros r e p. unfold rule_applies. rewrite normalize_r_body.
  apply normalize_rule_applies_walk.
Qed.

(** [outcome_core] reads only [r_vmap] / [terminal_outcome] (the end fields),
    copied verbatim by [normalize_rule]. *)
Lemma normalize_outcome_core : forall r e p,
  outcome_core (normalize_rule r) e p = outcome_core r e p.
Proof. intros r e p. reflexivity. Qed.

Lemma normalize_outcome : forall r e p,
  outcome (normalize_rule r) e p = outcome r e p.
Proof.
  intros r e p. unfold outcome. rewrite normalize_r_body.
  rewrite normalize_body_synproxy_stops, normalize_body_thread.
  destruct (body_synproxy_stops (r_body r) p); [reflexivity|].
  apply normalize_outcome_core.
Qed.

(** *** The pass preserves [eval_rules] on every rule list, hence [eval_chain]. *)
Lemma normalize_eval_rules : forall rs e p,
  eval_rules (map normalize_rule rs) e p = eval_rules rs e p.
Proof.
  induction rs as [| r rs IH]; intros e p; [reflexivity|].
  cbn [map eval_rules].
  rewrite normalize_rule_loadable, normalize_rule_applies, normalize_outcome.
  destruct (rule_loadable r e p && rule_applies r e p); [| apply IH].
  destruct (outcome r e p) as [v|]; [destruct v|]; rewrite ?IH; reflexivity.
Qed.

Theorem normalize_chain_eval : forall c e p,
  eval_chain (normalize_chain c) e p = eval_chain c e p.
Proof.
  intros c e p. unfold eval_chain, normalize_chain. cbn [c_rules c_policy].
  rewrite normalize_eval_rules. reflexivity.
Qed.
