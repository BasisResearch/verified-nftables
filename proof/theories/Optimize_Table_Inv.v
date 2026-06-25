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

Lemma synproxy_loadable_env : forall p base d1 d2,
  synproxy_loadable (set_env p (env_with_sets base d1))
  = synproxy_loadable (set_env p (env_with_sets base d2)).
Proof.
  intros. unfold synproxy_loadable, read_payload_ok, set_env, with_pkt_env. reflexivity.
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

Lemma stmt_loadable_env : forall s p base d1 d2,
  stmt_loadable s (set_env p (env_with_sets base d1))
  = stmt_loadable s (set_env p (env_with_sets base d2)).
Proof.
  intros s p base d1 d2. destruct s; cbn [stmt_loadable];
    try reflexivity;
    try apply vsrc_loadable_env; try apply fields_loadable_env;
    apply synproxy_loadable_env.
Qed.

Lemma synproxy_stops_env : forall p base d1 d2,
  synproxy_stops (set_env p (env_with_sets base d1))
  = synproxy_stops (set_env p (env_with_sets base d2)).
Proof.
  intros. unfold synproxy_stops, synproxy_flags, read_payload, set_env, with_pkt_env.
  reflexivity.
Qed.

(** [terminal_outcome] of a matches-only rule is env-stable: it reads only static
    end fields and (on a [Continue] fall-through) the [r_after] statements, which
    consult only the packet. *)
Lemma stmts_after_outcome_env : forall ss p base d1 d2,
  stmts_after_outcome ss (set_env p (env_with_sets base d1))
  = stmts_after_outcome ss (set_env p (env_with_sets base d2)).
Proof.
  induction ss as [| s ss IH]; intros p base d1 d2; [reflexivity|].
  destruct s; cbn [stmts_after_outcome];
    try (rewrite (stmt_loadable_env _ p base d1 d2);
         match goal with
         | |- context[if ?b then _ else _] => destruct b
         end; [apply IH | reflexivity]).
  - (* SSynproxy *)
    rewrite (synproxy_loadable_env p base d1 d2).
    destruct (synproxy_loadable (set_env p (env_with_sets base d2))); [| reflexivity].
    rewrite (synproxy_stops_env p base d1 d2).
    match goal with |- context[if ?b then _ else _] => destruct b end;
      [reflexivity | apply IH].
Qed.

Lemma terminal_outcome_env : forall r p base d1 d2,
  terminal_outcome r (set_env p (env_with_sets base d1))
  = terminal_outcome r (set_env p (env_with_sets base d2)).
Proof.
  intros r p base d1 d2. unfold terminal_outcome.
  destruct (r_nat r); [reflexivity|].
  destruct (r_tproxy r); [reflexivity|].
  destruct (r_fwd r); [reflexivity|].
  destruct (r_queue r); [reflexivity|].
  destruct (r_verdict r); try reflexivity.
  apply stmts_after_outcome_env.
Qed.

Lemma tail_loadable_env : forall r p base d1 d2,
  tail_loadable r (set_env p (env_with_sets base d1))
  = tail_loadable r (set_env p (env_with_sets base d2)).
Proof.
  intros r p base d1 d2. unfold tail_loadable.
  rewrite (terminal_loadable_env r p base d1 d2).
  rewrite (terminal_outcome_env r p base d1 d2).
  rewrite (forallb_ext_in
             (fun s => stmt_loadable s (set_env p (env_with_sets base d1)))
             (fun s => stmt_loadable s (set_env p (env_with_sets base d2)))
             (r_after r) (fun s _ => stmt_loadable_env s p base d1 d2)).
  reflexivity.
Qed.

(** [vmap_loadable] reads only [field_value], so it is env-stable. *)
Lemma vmap_loadable_env : forall ov p base d1 d2,
  vmap_loadable ov (set_env p (env_with_sets base d1))
  = vmap_loadable ov (set_env p (env_with_sets base d2)).
Proof.
  intros ov p base d1 d2. unfold vmap_loadable.
  destruct ov as [vm |]; [| reflexivity].
  destruct (vm_keyf vm) as [[f ?] |];
    [apply field_loadable_env | apply fields_loadable_env].
Qed.

(** [end_loadable] AGREES across two decls that agree on the rule's vmap name. *)
Lemma end_loadable_agree : forall r p base d1 d2,
  (forall nm, In nm (rule_vmap_name r) ->
     e_vmap (env_with_sets base d1) nm = e_vmap (env_with_sets base d2) nm) ->
  end_loadable r (set_env p (env_with_sets base d1))
  = end_loadable r (set_env p (env_with_sets base d2)).
Proof.
  intros r p base d1 d2 Hag. unfold end_loadable.
  destruct (r_vmap r) as [vm |] eqn:Ev; [| apply tail_loadable_env].
  rewrite (vmap_loadable_env (Some vm) p base d1 d2).
  assert (Hk : (let key := match vm_keyf vm with
                 | Some (f, ts) => apply_transforms ts (field_value f (set_env p (env_with_sets base d1)))
                 | None => List.concat (map (fun f => field_value f (set_env p (env_with_sets base d1))) (vm_fields vm))
                 end in key)
             = (let key := match vm_keyf vm with
                 | Some (f, ts) => apply_transforms ts (field_value f (set_env p (env_with_sets base d2)))
                 | None => List.concat (map (fun f => field_value f (set_env p (env_with_sets base d2))) (vm_fields vm))
                 end in key)).
  { cbn zeta. destruct (vm_keyf vm) as [[f ts] |].
    - rewrite (field_value_env_with_sets f p base d1 d2). reflexivity.
    - rewrite (map_ext _ _ (fun f => field_value_env_with_sets f p base d1 d2)).
      reflexivity. }
  cbn zeta. cbn zeta in Hk. rewrite Hk.
  cbn [set_env with_pkt_env pkt_env].
  rewrite (Hag (vm_name vm)) by (unfold rule_vmap_name; rewrite Ev; left; reflexivity).
  destruct (assoc_verdict _ (e_vmap (env_with_sets base d2) (vm_name vm)));
    [reflexivity |].
  f_equal. apply tail_loadable_env.
Qed.

(** Whole-rule agreement for a matches-only rule across two decls that agree on the
    names it reads. *)
Lemma rule_loadable_agree : forall r p base d1 d2,
  body_only_matches (r_body r) = true ->
  decls_agree_rule base d1 d2 r ->
  rule_loadable r (set_env p (env_with_sets base d1))
  = rule_loadable r (set_env p (env_with_sets base d2)).
Proof.
  intros r p base d1 d2 Hb [Hset Hvmap]. unfold rule_loadable.
  rewrite !(body_only_matches_no_synproxy (r_body r) _ Hb).
  rewrite !body_loadable_walk_no_synproxy
    by (apply (body_only_matches_no_synproxy (r_body r) _ Hb)).
  unfold body_thread. rewrite !(body_only_matches_no_notrack (r_body r) Hb).
  assert (Hbl : forallb (fun it => body_item_loadable it (set_env p (env_with_sets base d1))) (r_body r)
              = forallb (fun it => body_item_loadable it (set_env p (env_with_sets base d2))) (r_body r)).
  { apply forallb_ext_in. intros it Hit.
    destruct it as [m | s].
    - cbn [body_item_loadable]. apply match_loadable_env.
    - exfalso. unfold body_only_matches in Hb. rewrite forallb_forall in Hb.
      specialize (Hb _ Hit). discriminate. }
  rewrite Hbl. rewrite (end_loadable_agree r p base d1 d2 Hvmap). reflexivity.
Qed.

Lemma rule_applies_agree : forall r p base d1 d2,
  body_only_matches (r_body r) = true ->
  decls_agree_rule base d1 d2 r ->
  rule_applies r (set_env p (env_with_sets base d1))
  = rule_applies r (set_env p (env_with_sets base d2)).
Proof.
  intros r p base d1 d2 Hb [Hset _]. unfold rule_applies.
  apply (rule_applies_walk_agree (r_body r) p base d1 d2 Hb Hset).
Qed.

Lemma outcome_agree : forall r p base d1 d2,
  body_only_matches (r_body r) = true ->
  decls_agree_rule base d1 d2 r ->
  outcome r (set_env p (env_with_sets base d1))
  = outcome r (set_env p (env_with_sets base d2)).
Proof.
  intros r p base d1 d2 Hb [_ Hvmap]. unfold outcome.
  rewrite !(body_only_matches_no_synproxy (r_body r) _ Hb).
  unfold body_thread. rewrite !(body_only_matches_no_notrack (r_body r) Hb).
  unfold outcome_core.
  destruct (r_vmap r) as [vm |] eqn:Ev; [| apply terminal_outcome_env].
  assert (Hk : match vm_keyf vm with
                 | Some (f, ts) => apply_transforms ts (field_value f (set_env p (env_with_sets base d1)))
                 | None => List.concat (map (fun f => field_value f (set_env p (env_with_sets base d1))) (vm_fields vm))
                 end
             = match vm_keyf vm with
                 | Some (f, ts) => apply_transforms ts (field_value f (set_env p (env_with_sets base d2)))
                 | None => List.concat (map (fun f => field_value f (set_env p (env_with_sets base d2))) (vm_fields vm))
                 end).
  { destruct (vm_keyf vm) as [[f ts] |].
    - rewrite (field_value_env_with_sets f p base d1 d2). reflexivity.
    - rewrite (map_ext _ _ (fun f => field_value_env_with_sets f p base d1 d2)).
      reflexivity. }
  rewrite Hk. cbn [set_env with_pkt_env pkt_env].
  rewrite (Hvmap (vm_name vm)) by (unfold rule_vmap_name; rewrite Ev; left; reflexivity).
  destruct (assoc_verdict _ (e_vmap (env_with_sets base d2) (vm_name vm)));
    [reflexivity | apply terminal_outcome_env].
Qed.

(** ** [eval_rules] AGREES across two decls that agree on every rule's read names.

    This is the seam tool: a partially-merged chain (matches-only lookup rules whose
    set/vmap names are already present in [d]) evaluates identically under [d] and
    under [d] extended with the NEXT pass's FRESH names. *)

(** A whole rule-list is matches-only and reads only names on which [d1],[d2] agree. *)
Definition rules_agree (base : env) (d1 d2 : set_decls) (rs : list rule) : Prop :=
  forall r, In r rs ->
    body_only_matches (r_body r) = true /\ decls_agree_rule base d1 d2 r.

Lemma eval_rules_agree : forall rs p base d1 d2,
  rules_agree base d1 d2 rs ->
  eval_rules rs (set_env p (env_with_sets base d1))
  = eval_rules rs (set_env p (env_with_sets base d2)).
Proof.
  induction rs as [| r rs IH]; intros p base d1 d2 Hag; [reflexivity|].
  destruct (Hag r (or_introl eq_refl)) as [Hb Hda].
  cbn [eval_rules].
  rewrite (rule_loadable_agree r p base d1 d2 Hb Hda).
  rewrite (rule_applies_agree r p base d1 d2 Hb Hda).
  rewrite (outcome_agree r p base d1 d2 Hb Hda).
  rewrite (IH p base d1 d2 (fun r' Hr' => Hag r' (or_intror Hr'))).
  reflexivity.
Qed.
