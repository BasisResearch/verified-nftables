(** * Optimize_Table_Inv: SEAM invariants for composing the verified nft -o passes.

    Each individual pass theorem ([optimize_chain_setsN/vmapN/concatN_correct])
    requires its INPUT chain to be [rules_clean].  But every merge pass EMITS a
    non-clean rule (an [MConcatSet] head, or an [r_vmap] verdict-map rule), so
    stage k's output is NOT [rules_clean] and cannot be fed to stage k+1's theorem
    directly.

    This file builds the two ingredients that bridge the seam:

      1. ENV-AGREEMENT: a rule's verdict depends on the set/vmap environment ONLY
         through the set names its body matchconds read ([MConcatSet]/[MSetT]/
         [MConcatSetT]) and the verdict-map name it carries ([r_vmap]).  Two
         declaration sets that AGREE on exactly those names give the SAME verdict.
         A later pass only PREPENDS entries keyed by FRESH names, so it agrees with
         the earlier [d] on every name the earlier output reads.

      2. OUTPUT INVARIANTS: each pass's counter is monotone, minted names lie in
         [n, n'), and a pass leaves the OTHER namespace's declarations untouched
         (setsN/concatN do not touch [sd_vmaps]; vmapN does not touch [sd_sets]).

    Together with the per-pass [_assoc_stable] lemmas these discharge the freshness
    and clean-input obligations at every seam of the composed [optimize_table]. *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import String.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Optimize Optimize_Merge Optimize_Vmap Optimize_Concat.

(** ** Part 1: env-agreement on the set/vmap names a rule reads. *)

(** The single set name a matchcond reads from the runtime environment ([None] for
    the value-only conds, which never touch [e_set]). *)
Definition mc_set_name (m : matchcond) : option string :=
  match m with
  | MConcatSet _ _ name | MSetT _ _ _ name | MConcatSetT _ _ name => Some name
  | _ => None
  end.

(** A matchcond eval AGREES across two decls that agree on the read set name. *)
Lemma eval_matchcond_agree : forall m p base d1 d2,
  (forall nm, mc_set_name m = Some nm ->
     e_set (env_with_sets base d1) nm = e_set (env_with_sets base d2) nm) ->
  eval_matchcond m (set_env p (env_with_sets base d1))
  = eval_matchcond m (set_env p (env_with_sets base d2)).
Proof.
  intros m p base d1 d2 Hag.
  unfold eval_matchcond, eval_matchcond_body, match_loadable.
  destruct m; cbn [mc_set_name] in Hag;
    rewrite ?field_value_env_with_sets;
    repeat (match goal with
            | |- context[field_value ?f (set_env p (env_with_sets base d1))] =>
                rewrite (field_value_env_with_sets f p base d1 d2)
            end);
    try reflexivity.
  - (* MConcatSet *) cbn [set_env with_pkt_env pkt_env].
    rewrite (Hag _ eq_refl). reflexivity.
  - (* MSetT *) cbn [set_env with_pkt_env pkt_env].
    rewrite (Hag _ eq_refl). reflexivity.
  - (* MConcatSetT *) cbn [set_env with_pkt_env pkt_env].
    rewrite (Hag _ eq_refl). reflexivity.
Qed.

(** Set names read by a body (its matchconds). *)
Definition body_set_names (b : list body_item) : list string :=
  flat_map (fun m => match mc_set_name m with Some nm => [nm] | None => [] end)
           (body_matches b).

(** Pointwise-equal predicates give equal [forallb]. *)
Lemma forallb_ext_in {A} : forall (f g : A -> bool) (l : list A),
  (forall x, In x l -> f x = g x) -> forallb f l = forallb g l.
Proof.
  induction l as [| x l IH]; intro H; [reflexivity|].
  cbn [forallb]. rewrite (H x (or_introl eq_refl)).
  rewrite (IH (fun y Hy => H y (or_intror Hy))). reflexivity.
Qed.

(** A matchcond in [body_matches] reads a set name listed in [body_set_names]. *)
Lemma mc_in_body_read : forall body m nm,
  In m (body_matches body) -> mc_set_name m = Some nm ->
  In nm (body_set_names body).
Proof.
  intros body m nm Hm Hnm. unfold body_set_names.
  apply in_flat_map. exists m. split; [exact Hm |]. rewrite Hnm. left; reflexivity.
Qed.

(** The loadability of a matchcond is env-stable (it only ever consults
    [field_value], never [e_set]/[e_vmap]). *)
Lemma match_loadable_env : forall m p base d1 d2,
  match_loadable m (set_env p (env_with_sets base d1))
  = match_loadable m (set_env p (env_with_sets base d2)).
Proof.
  intros m p base d1 d2. unfold match_loadable.
  destruct m; rewrite ?field_value_env_with_sets;
    repeat (match goal with
            | |- context[field_value ?f (set_env p (env_with_sets base d1))] =>
                rewrite (field_value_env_with_sets f p base d1 d2)
            end);
    try reflexivity;
    unfold fields_loadable;
    repeat (match goal with
            | |- context[field_value ?f (set_env p (env_with_sets base d1))] =>
                rewrite (field_value_env_with_sets f p base d1 d2)
            end);
    reflexivity.
Qed.

(** A body all of whose items are matchconds (no statements).  Every lookup rule a
    merge pass emits ([MConcatSet] head + clean match tail, or a vmap rule whose
    body is the clean match tail) has such a body. *)
Definition body_only_matches (b : list body_item) : bool :=
  forallb (fun it => match it with BMatch _ => true | BStmt _ => false end) b.

(** On a matches-only body, [rule_applies_walk = forallb eval_matchcond]. *)
Lemma rule_applies_walk_only_matches : forall body p,
  body_only_matches body = true ->
  rule_applies_walk body p
  = forallb (fun m => eval_matchcond m p) (body_matches body).
Proof.
  induction body as [| it body IH]; intros p Hb; [reflexivity|].
  cbn [body_only_matches forallb] in Hb. apply Bool.andb_true_iff in Hb as [Hit Hrest].
  destruct it as [m | s]; [| discriminate].
  cbn [rule_applies_walk body_matches flat_map forallb].
  rewrite (IH p Hrest). reflexivity.
Qed.

(** [rule_applies_walk] AGREES across two decls that agree on every set name a
    matches-only body reads. *)
Lemma rule_applies_walk_agree : forall body p base d1 d2,
  body_only_matches body = true ->
  (forall nm, In nm (body_set_names body) ->
     e_set (env_with_sets base d1) nm = e_set (env_with_sets base d2) nm) ->
  rule_applies_walk body (set_env p (env_with_sets base d1))
  = rule_applies_walk body (set_env p (env_with_sets base d2)).
Proof.
  intros body p base d1 d2 Hb Hag.
  rewrite !(rule_applies_walk_only_matches body _ Hb).
  apply forallb_ext_in. intros m Hm.
  apply (eval_matchcond_agree m p base d1 d2).
  intros nm Hnm. apply Hag.
  unfold body_set_names. apply in_flat_map. exists m. split; [exact Hm |].
  rewrite Hnm. left; reflexivity.
Qed.

(** A matches-only body has no [notrack] and no stopping synproxy. *)
Lemma body_only_matches_no_notrack : forall body,
  body_only_matches body = true -> body_has_notrack body = false.
Proof.
  induction body as [| it body IH]; intro Hb; [reflexivity|].
  cbn [body_only_matches forallb] in Hb. apply Bool.andb_true_iff in Hb as [Hit Hrest].
  destruct it as [m | s]; [| discriminate].
  cbn [body_has_notrack existsb]. apply (IH Hrest).
Qed.

Lemma body_only_matches_no_synproxy : forall body p,
  body_only_matches body = true -> body_synproxy_stops body p = false.
Proof.
  induction body as [| it body IH]; intros p Hb; [reflexivity|].
  cbn [body_only_matches forallb] in Hb. apply Bool.andb_true_iff in Hb as [Hit Hrest].
  destruct it as [m | s]; [| discriminate].
  unfold body_synproxy_stops in *. cbn [existsb]. apply (IH p Hrest).
Qed.

(** The (single) verdict-map name a rule carries (empty if it has none). *)
Definition rule_vmap_name (r : rule) : list string :=
  match r_vmap r with Some vm => [vm_name vm] | None => [] end.

(** All set/vmap names a rule reads from the environment. *)
Definition rule_read_names (r : rule) : list string :=
  body_set_names (r_body r) ++ rule_vmap_name r.

(** Two decls AGREE for a rule [r] iff they give the same [e_set]/[e_vmap] lookup at
    every name [r] reads. *)
Definition decls_agree_rule (base : env) (d1 d2 : set_decls) (r : rule) : Prop :=
  (forall nm, In nm (body_set_names (r_body r)) ->
     e_set (env_with_sets base d1) nm = e_set (env_with_sets base d2) nm) /\
  (forall nm, In nm (rule_vmap_name r) ->
     e_vmap (env_with_sets base d1) nm = e_vmap (env_with_sets base d2) nm).

(** Env-stability of the load primitives: they read only the packet's payload /
    conntrack / exthdr geometry — fields [with_pkt_env] copies verbatim — never the
    set/vmap environment. *)
Lemma load_ok_env : forall ld p base d1 d2,
  load_ok ld (set_env p (env_with_sets base d1))
  = load_ok ld (set_env p (env_with_sets base d2)).
Proof.
  intros ld p base d1 d2. unfold load_ok, set_env, with_pkt_env.
  destruct ld; try reflexivity; try (destruct k; reflexivity).
Qed.

Lemma field_loadable_env : forall f p base d1 d2,
  field_loadable f (set_env p (env_with_sets base d1))
  = field_loadable f (set_env p (env_with_sets base d2)).
Proof. intros. unfold field_loadable. apply load_ok_env. Qed.

Lemma fields_loadable_env : forall fs p base d1 d2,
  fields_loadable fs (set_env p (env_with_sets base d1))
  = fields_loadable fs (set_env p (env_with_sets base d2)).
Proof.
  intros fs p base d1 d2. unfold fields_loadable.
  apply forallb_ext_in. intros f _. apply field_loadable_env.
Qed.

Lemma vsrc_loadable_env : forall vs p base d1 d2,
  vsrc_loadable vs (set_env p (env_with_sets base d1))
  = vsrc_loadable vs (set_env p (env_with_sets base d2)).
Proof.
  intros vs p base d1 d2. destruct vs; cbn [vsrc_loadable];
    try reflexivity;
    try apply field_loadable_env; apply fields_loadable_env.
Qed.

(** [terminal_loadable]/[terminal_outcome] of a matches-only rule read only the
    packet/static end fields (never [e_set]/[e_vmap]), so they are env-stable. *)
Lemma terminal_loadable_env : forall r p base d1 d2,
  terminal_loadable r (set_env p (env_with_sets base d1))
  = terminal_loadable r (set_env p (env_with_sets base d2)).
Proof.
  intros r p base d1 d2. unfold terminal_loadable.
  destruct (r_nat r) as [n |].
  { destruct (nat_src n) as [vs |]; [apply vsrc_loadable_env|].
    destruct (nat_map n) as [[[fields ?] ?] |]; [apply fields_loadable_env|].
    destruct (nat_field n) as [[f ?] |]; [apply field_loadable_env| reflexivity]. }
  destruct (r_tproxy r); [reflexivity|].
  destruct (r_fwd r) as [w |].
  { destruct (fwd_src w) as [vs |]; [apply vsrc_loadable_env | reflexivity]. }
  destruct (r_queue r) as [q |].
  { destruct (q_src q) as [vs |]; [apply vsrc_loadable_env | reflexivity]. }
  reflexivity.
Qed.
