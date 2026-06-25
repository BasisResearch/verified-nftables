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

(** ** Part 2: pass output invariants (counter monotone, cross-namespace stable). *)

(** *** setsN. *)
Lemma optimize_rules_setsN_mono : forall fuel n d rs n' d' rs',
  optimize_rules_setsN fuel n d rs = (n', d', rs') -> n <= n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; lia.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; lia.
    + cbn in H. inversion H; subst; lia.
    + rewrite optimize_rules_setsN_consSS in H.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_value_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct vs as [| v vs'].
        -- remember (optimize_rules_setsN fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_setsN fuel (S n)
                       {| sd_sets := (setname n, map (fun w => (w,w)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n'.
           assert (S n <= m'')
             by (eapply (IH (S n) _ rest'); symmetry; exact Erec). lia.
      * remember (optimize_rules_setsN fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_setsN_vmaps : forall fuel n d rs n' d' rs',
  optimize_rules_setsN fuel n d rs = (n', d', rs') -> sd_vmaps d' = sd_vmaps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_setsN_consSS in H.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_value_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct vs as [| v vs'].
        -- remember (optimize_rules_setsN fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_setsN fuel (S n)
                       {| sd_sets := (setname n, map (fun w => (w,w)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_setsN fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_chain_setsN_mono : forall n d c n' d' c',
  optimize_chain_setsN n d c = (n', d', c') -> n <= n'.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_setsN in H.
  destruct (optimize_rules_setsN (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_setsN_mono _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_setsN_vmaps : forall n d c n' d' c',
  optimize_chain_setsN n d c = (n', d', c') -> sd_vmaps d' = sd_vmaps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_setsN in H.
  destruct (optimize_rules_setsN (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_setsN_vmaps _ _ _ _ _ _ _ E).
Qed.

(** *** vmapN. *)
Lemma optimize_rules_vmapN_mono : forall fuel n d rs n' d' rs',
  optimize_rules_vmapN fuel n d rs = (n', d', rs') -> n <= n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; lia.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; lia.
    + cbn in H. inversion H; subst; lia.
    + rewrite optimize_rules_vmapN_consSS in H.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_vmap_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_vmapN fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- destruct (has_distinct_verdict (r_verdict r1) (e :: es')) eqn:Hdv.
           ++ cbv zeta in H.
              remember (optimize_rules_vmapN fuel (S n) _ rest') as t eqn:Erec.
              destruct t as [[m'' dd''] rr'']. cbv zeta in H.
              injection H as Hn' Hd' Hr'. subst n'.
              assert (S n <= m'')
                by (eapply (IH (S n) _ rest'); symmetry; exact Erec). lia.
           ++ remember (optimize_rules_vmapN fuel n d (r2 :: rest)) as t eqn:Erec.
              destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
              eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
      * remember (optimize_rules_vmapN fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_vmapN_sets : forall fuel n d rs n' d' rs',
  optimize_rules_vmapN fuel n d rs = (n', d', rs') -> sd_sets d' = sd_sets d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_vmapN_consSS in H.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * destruct (take_vmap_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_vmapN fuel n d (r2 :: rest)) as t eqn:Erec.
           destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- destruct (has_distinct_verdict (r_verdict r1) (e :: es')) eqn:Hdv.
           ++ cbv zeta in H.
              remember (optimize_rules_vmapN fuel (S n)
                          {| sd_sets := sd_sets d;
                             sd_vmaps := (vmapname n,
                               map vmap_pt ((v1, r_verdict r1) :: e :: es')) :: sd_vmaps d;
                             sd_maps := sd_maps d |} rest') as t eqn:Erec.
              destruct t as [[m'' dd''] rr'']. cbv zeta in H.
              injection H as Hn' Hd' Hr'. subst d'.
              rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
           ++ remember (optimize_rules_vmapN fuel n d (r2 :: rest)) as t eqn:Erec.
              destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
              eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
      * remember (optimize_rules_vmapN fuel n d (r2 :: rest)) as t eqn:Erec.
        destruct t as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_chain_vmapN_mono : forall n d c n' d' c',
  optimize_chain_vmapN n d c = (n', d', c') -> n <= n'.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_vmapN in H.
  destruct (optimize_rules_vmapN (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_vmapN_mono _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_vmapN_sets : forall n d c n' d' c',
  optimize_chain_vmapN n d c = (n', d', c') -> sd_sets d' = sd_sets d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_vmapN in H.
  destruct (optimize_rules_vmapN (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_vmapN_sets _ _ _ _ _ _ _ E).
Qed.

(** *** concatN. *)
Lemma optimize_rules_concatN_mono : forall fuel n d rs n' d' rs',
  optimize_rules_concatN fuel n d rs = (n', d', rs') -> n <= n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; lia.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; lia.
    + cbn in H. inversion H; subst; lia.
    + rewrite optimize_rules_concatN_consSS in H.
      destruct (head_value2 r1) as [[[[[f1 a1] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concat_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concatN fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_concatN fuel (S n) _ rest') as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n'.
           assert (S n <= m'')
             by (eapply (IH (S n) _ rest'); symmetry; exact Erec). lia.
      * remember (optimize_rules_concatN fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_concatN_vmaps : forall fuel n d rs n' d' rs',
  optimize_rules_concatN fuel n d rs = (n', d', rs') -> sd_vmaps d' = sd_vmaps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_concatN_consSS in H.
      destruct (head_value2 r1) as [[[[[f1 a1] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concat_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concatN fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_concatN fuel (S n)
                       {| sd_sets := (setname n, map pack_tuple ((a1, b1) :: t :: ts'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_concatN fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_chain_concatN_mono : forall n d c n' d' c',
  optimize_chain_concatN n d c = (n', d', c') -> n <= n'.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_concatN in H.
  destruct (optimize_rules_concatN (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_concatN_mono _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_concatN_vmaps : forall n d c n' d' c',
  optimize_chain_concatN n d c = (n', d', c') -> sd_vmaps d' = sd_vmaps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_concatN in H.
  destruct (optimize_rules_concatN (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_concatN_vmaps _ _ _ _ _ _ _ E).
Qed.

(** ** Part 3: generalized vmapN / concatN correctness (weaker-than-[rules_clean]
    precondition true of a PARTIALLY-MERGED chain).

    A merge pass emits two kinds of rules: CLEAN (untouched) rules with a value head
    [MCmp f CEq v] ([head_value/head_value2 = Some]), and LOOKUP rules ([MConcatSet]
    head / vmap rule) which are NOT clean but whose body is matches-only and which —
    for the NEXT pass — are non-mergeable ([head_value/head_value2 = None]) and read
    only set names (no vmap name).  [rule_lookup_ok] captures exactly this. *)

Definition rule_lookup_vmapN_ok (r : rule) : Prop :=
  rule_clean r = true
  \/ (head_value r = None
      /\ body_only_matches (r_body r) = true
      /\ rule_vmap_name r = []).

Definition rs_vmapN_ok (rs : list rule) : Prop := Forall rule_lookup_vmapN_ok rs.

(** A run-head rule ([head_value = Some]) under the ok-predicate is CLEAN. *)
Lemma rule_lookup_vmapN_ok_head_clean : forall r f v body,
  rule_lookup_vmapN_ok r -> head_value r = Some (f, v, body) -> rule_clean r = true.
Proof.
  intros r f v body [Hcl | [Hnone _]] Hhd; [exact Hcl |].
  rewrite Hhd in Hnone; discriminate.
Qed.

(** Two decls with the SAME [sd_sets] give the same lookup at every set name. *)
Lemma e_set_eq_of_sd_sets_eq : forall base d1 d2 nm,
  sd_sets d1 = sd_sets d2 ->
  e_set (env_with_sets base d1) nm = e_set (env_with_sets base d2) nm.
Proof.
  intros base d1 d2 nm Hs. rewrite !e_set_declared. rewrite Hs. reflexivity.
Qed.

(** A single ok-rule evaluates IDENTICALLY under two decls with equal [sd_sets]:
    clean rules are env-stable everywhere; lookup rules read only [e_set]. *)
Lemma rule_lookup_vmapN_ok_agree : forall r p base d1 d2,
  rule_lookup_vmapN_ok r -> sd_sets d1 = sd_sets d2 ->
  rule_loadable r (set_env p (env_with_sets base d1))
    = rule_loadable r (set_env p (env_with_sets base d2))
  /\ rule_applies r (set_env p (env_with_sets base d1))
    = rule_applies r (set_env p (env_with_sets base d2))
  /\ outcome r (set_env p (env_with_sets base d1))
    = outcome r (set_env p (env_with_sets base d2)).
Proof.
  intros r p base d1 d2 [Hcl | [Hnone [Hbm Hvn]]] Hs.
  - apply (rule_clean_env r p base d1 d2 Hcl).
  - assert (Hda : decls_agree_rule base d1 d2 r).
    { split.
      - intros nm _. apply e_set_eq_of_sd_sets_eq; exact Hs.
      - intros nm Hnm. rewrite Hvn in Hnm. destruct Hnm. }
    repeat split.
    + apply (rule_loadable_agree r p base d1 d2 Hbm Hda).
    + apply (rule_applies_agree r p base d1 d2 Hbm Hda).
    + apply (outcome_agree r p base d1 d2 Hbm Hda).
Qed.

Lemma eval_rules_vmapN_ok_env : forall rs p base d1 d2,
  rs_vmapN_ok rs -> sd_sets d1 = sd_sets d2 ->
  eval_rules rs (set_env p (env_with_sets base d1))
  = eval_rules rs (set_env p (env_with_sets base d2)).
Proof.
  induction rs as [| r rs IH]; intros p base d1 d2 Hok Hs; [reflexivity|].
  inversion Hok as [| ? ? Hr Hrest]; subst.
  destruct (rule_lookup_vmapN_ok_agree r p base d1 d2 Hr Hs) as [Hl [Ha Ho]].
  cbn [eval_rules]. rewrite Hl, Ha, Ho.
  rewrite (IH p base d1 d2 Hrest Hs). reflexivity.
Qed.

(** ok-ness of a suffix and of [take_vmap_run]'s leftover. *)
Lemma rs_vmapN_ok_tl : forall r rs, rs_vmapN_ok (r :: rs) -> rs_vmapN_ok rs.
Proof. intros r rs H. inversion H; assumption. Qed.

(** *** GENERALIZED N-WAY vmap merge correctness: precondition [rs_vmapN_ok]
    (clean cmp-rules merge; pre-existing matches-only lookup rules eval-stable). *)
Theorem optimize_rules_vmapN_correct_gen : forall fuel rs n d n' d' rs' base p,
  optimize_rules_vmapN fuel n d rs = (n', d', rs') ->
  rs_vmapN_ok rs ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  eval_rules rs' (set_env p (env_with_sets base d'))
  = eval_rules rs  (set_env p (env_with_sets base d)).
Proof.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base p H Hok Hfresh.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_vmapN_consSS in H.
      pose proof Hok as Hok0.
      inversion Hok as [| ? ? Hr1ok Hrest_ok]; subst.
      destruct (head_value r1) as [[[f v1] body] |] eqn:Ehd.
      * pose proof (rule_lookup_vmapN_ok_head_clean r1 f v1 body Hr1ok Ehd) as Hc1.
        destruct (take_vmap_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct (take_vmap_run_shape r1 f v1 body (r2 :: rest) es rest' Ehd Erun)
          as [Hsplit [HwK HwT]].
        (* rest' is ok: it is a suffix of (r2 :: rest) via Hsplit *)
        assert (Hokrest' : rs_vmapN_ok rest').
        { unfold rs_vmapN_ok in *. rewrite Hsplit in Hrest_ok.
          apply Forall_app in Hrest_ok. exact (proj2 Hrest_ok). }
        destruct es as [| e es'].
        -- remember (optimize_rules_vmapN fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           cbn [eval_rules].
           rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hrest_ok Hfresh).
           destruct (rule_clean_env r1 p base dd'' d Hc1) as [Hl [Ha Ho]].
           rewrite Hl, Ha, Ho. reflexivity.
        -- destruct (take_vmap_run_head r1 f v1 body r2 rest (e :: es') rest' Ehd Erun
                       ltac:(discriminate)) as [Hr1eq [HwK1 HwT1]].
           destruct (has_distinct_verdict (r_verdict r1) (e :: es')) eqn:Hdv.
           2:{ remember (optimize_rules_vmapN fuel n d (r2 :: rest)) as tt eqn:Erec.
               destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
               injection H as Hn' Hd' Hr'. subst n' d' rs'.
               cbn [eval_rules].
               rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hrest_ok Hfresh).
               destruct (rule_clean_env r1 p base dd'' d Hc1) as [Hl [Ha Ho]].
               rewrite Hl, Ha, Ho. reflexivity. }
           cbv zeta in H.
           remember (optimize_rules_vmapN fuel (S n)
                       {| sd_sets := sd_sets d;
                          sd_vmaps := (vmapname n,
                            map vmap_pt ((v1, r_verdict r1) :: e :: es')) :: sd_vmaps d;
                          sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (entries := (v1, r_verdict r1) :: e :: es') in *.
           set (dn := {| sd_sets := sd_sets d;
                         sd_vmaps := (vmapname n, map vmap_pt entries) :: sd_vmaps d;
                         sd_maps := sd_maps d |}) in *.
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun vw => orig_rule f (fst vw) body (snd vw)) entries ++ rest').
           { subst entries. cbn [map app fst snd]. f_equal; [exact Hr1eq | exact Hsplit]. }
           (* sd_sets unchanged across the whole vmap recursion *)
           assert (Hsets_dd : sd_sets dd'' = sd_sets dn)
             by (apply (optimize_rules_vmapN_sets _ _ _ _ _ _ _ (eq_sym Erec))).
           assert (Hsets_dn : sd_sets dn = sd_sets d) by (subst dn; reflexivity).
           assert (Htail : eval_rules rr'' (set_env p (env_with_sets base dd''))
                           = eval_rules rest' (set_env p (env_with_sets base dn))).
           { eapply (IH rest' (S n) dn m'' dd'' rr'' base p (eq_sym Erec) Hokrest').
             intros k Hk Hin. subst dn; cbn [sd_vmaps map] in Hin.
             destruct Hin as [Heq | Hin].
             - apply vmapname_inj in Heq. lia.
             - apply (Hfresh k); [lia | exact Hin]. }
           assert (Hlook : e_vmap (pkt_env (set_env p (env_with_sets base dd'')))
                             (vmapname n) = map vmap_pt entries).
           { cbn [set_env with_pkt_env pkt_env]. rewrite e_vmap_env_with_sets.
             erewrite (optimize_rules_vmapN_assoc_stable fuel (S n) dn _ _ _ _
                         (vmapname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_vmaps assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply vmapname_inj in Heq. lia. }
           set (qd := set_env p (env_with_sets base dd'')) in *.
           transitivity (eval_rules
             (map (fun vw => orig_rule f (fst vw) body (snd vw)) entries ++ rr'') qd).
           { unfold qd. apply (eval_rules_vmap_mergeN f (vmapname n) entries body rr''
                                 (set_env p (env_with_sets base dd''))).
             - exact Hlook.
             - intros v w Hin. subst entries. destruct Hin as [Hvw | Hin];
                 [ inversion Hvw; subst; exact HwK1 | apply (HwK v w Hin) ].
             - intros v w Hin. subst entries. destruct Hin as [Hvw | Hin];
                 [ inversion Hvw; subst; exact HwT1 | apply (HwT v w Hin) ].
             - apply body_synproxy_stops_clean.
               clear -Hc1 Ehd. unfold head_value in Ehd.
               destruct (r_body r1) as [| [m | s] bb] eqn:Eb; try discriminate.
               destruct m as [ | | | | g op u | | | | | | | | ]; try discriminate.
               destruct op; try discriminate. inversion Ehd; subst g u bb.
               unfold rule_clean in Hc1. rewrite Eb in Hc1.
               cbn [forallb bi_clean] in Hc1.
               repeat (apply Bool.andb_true_iff in Hc1 as [Hc1 ?]).
               match goal with H : forallb bi_clean body = true |- _ => exact H end.
             - apply body_has_notrack_clean.
               clear -Hc1 Ehd. unfold head_value in Ehd.
               destruct (r_body r1) as [| [m | s] bb] eqn:Eb; try discriminate.
               destruct m as [ | | | | g op u | | | | | | | | ]; try discriminate.
               destruct op; try discriminate. inversion Ehd; subst g u bb.
               unfold rule_clean in Hc1. rewrite Eb in Hc1.
               cbn [forallb bi_clean] in Hc1.
               repeat (apply Bool.andb_true_iff in Hc1 as [Hc1 ?]).
               match goal with H : forallb bi_clean body = true |- _ => exact H end. }
           assert (Htail' : eval_rules rr'' qd = eval_rules rest' qd).
           { rewrite Htail. unfold qd.
             apply (eval_rules_vmapN_ok_env rest' p base dn dd'' Hokrest').
             rewrite Hsets_dd. reflexivity. }
           rewrite (eval_rules_app_cong
                      (map (fun vw => orig_rule f (fst vw) body (snd vw)) entries)
                      rr'' rest' qd Htail').
           rewrite <- Hrun_eq.
           unfold qd. apply (eval_rules_vmapN_ok_env (r1 :: r2 :: rest) p base dd'' d Hok0).
           rewrite Hsets_dd, Hsets_dn. reflexivity.
      * remember (optimize_rules_vmapN fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        cbn [eval_rules].
        rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hrest_ok Hfresh).
        (* r1 is a no-op lookup rule (head_value = None): env-stable via ok-agree *)
        destruct (rule_lookup_vmapN_ok_agree r1 p base dd'' d Hr1ok
                    (optimize_rules_vmapN_sets _ _ _ _ _ _ _ (eq_sym Erec)))
          as [Hl [Ha Ho]].
        rewrite Hl, Ha, Ho. reflexivity.
Qed.

(** Chain-level generalized vmap correctness. *)
Theorem optimize_chain_vmapN_correct_gen : forall n d c n' d' c' base p,
  optimize_chain_vmapN n d c = (n', d', c') ->
  rs_vmapN_ok (c_rules c) ->
  (forall k, n <= k -> ~ In (vmapname k) (map fst (sd_vmaps d))) ->
  eval_chain c' (set_env p (env_with_sets base d'))
  = eval_chain c  (set_env p (env_with_sets base d)).
Proof.
  intros n d c n' d' c' base p H Hok Hfresh.
  unfold optimize_chain_vmapN in H.
  destruct (optimize_rules_vmapN (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:Erec.
  inversion H; subst n' d' c'. cbn [c_rules c_policy].
  unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_vmapN_correct_gen (List.length (c_rules c)) (c_rules c) n d
             m'' dd'' rr'' base p Erec Hok Hfresh).
  reflexivity.
Qed.

(** *** concatN.  Lookup rules here ([MConcatSet] from the set/concat passes) are
    matches-only, non-mergeable ([head_value2 = None]), carry no vmap, and reference
    only DECLARED set names — so a later concat extension (which only prepends FRESH
    [setname]s absent from [sd_sets d]) agrees with [d] on every name they read. *)

Definition rule_lookup_concatN_ok (r : rule) : Prop :=
  rule_clean r = true
  \/ (head_value2 r = None
      /\ body_only_matches (r_body r) = true
      /\ rule_vmap_name r = []).

(** A rule reads only set names that are KEYS of [sd_sets d]. *)
Definition rule_reads_declared (d : set_decls) (r : rule) : Prop :=
  forall nm, In nm (body_set_names (r_body r)) -> In nm (map fst (sd_sets d)).

Definition rs_concatN_ok (d : set_decls) (rs : list rule) : Prop :=
  Forall (fun r => rule_lookup_concatN_ok r /\ rule_reads_declared d r) rs.

Lemma rule_lookup_concatN_ok_head_clean : forall r f1 a1 f2 b1 body,
  rule_lookup_concatN_ok r ->
  head_value2 r = Some (f1, a1, f2, b1, body) -> rule_clean r = true.
Proof.
  intros r f1 a1 f2 b1 body [Hcl | [Hnone _]] Hhd; [exact Hcl |].
  rewrite Hhd in Hnone; discriminate.
Qed.

(** Per-rule agreement across [d1],[d2] when they agree (as [e_set] lookups) on the
    set names the rule reads. *)
Lemma rule_lookup_concatN_ok_agree : forall r p base d1 d2,
  rule_lookup_concatN_ok r ->
  (forall nm, In nm (body_set_names (r_body r)) ->
     e_set (env_with_sets base d1) nm = e_set (env_with_sets base d2) nm) ->
  rule_loadable r (set_env p (env_with_sets base d1))
    = rule_loadable r (set_env p (env_with_sets base d2))
  /\ rule_applies r (set_env p (env_with_sets base d1))
    = rule_applies r (set_env p (env_with_sets base d2))
  /\ outcome r (set_env p (env_with_sets base d1))
    = outcome r (set_env p (env_with_sets base d2)).
Proof.
  intros r p base d1 d2 [Hcl | [Hnone [Hbm Hvn]]] Hag.
  - apply (rule_clean_env r p base d1 d2 Hcl).
  - assert (Hda : decls_agree_rule base d1 d2 r).
    { split; [exact Hag |].
      intros nm Hnm. rewrite Hvn in Hnm. destruct Hnm. }
    repeat split.
    + apply (rule_loadable_agree r p base d1 d2 Hbm Hda).
    + apply (rule_applies_agree r p base d1 d2 Hbm Hda).
    + apply (outcome_agree r p base d1 d2 Hbm Hda).
Qed.

(** The seam env-agreement for concatN: between an EXTENDED decl set [d'] and [d]
    that agree (as [assoc_str] over [sd_sets]) on every name declared in [d], on a
    list of ok rules that read only names declared in [d].  The agreement hypothesis
    is discharged at each call site by [optimize_rules_concatN_assoc_stable] +
    [Hfresh] (the extension's fresh [setname]s are absent from [sd_sets d]). *)
Lemma eval_rules_concatN_seam_env : forall d d' rs p base,
  (forall nm X, In nm (map fst (sd_sets d)) ->
     assoc_str nm (sd_sets d') X = assoc_str nm (sd_sets d) X) ->
  rs_concatN_ok d rs ->
  eval_rules rs (set_env p (env_with_sets base d'))
  = eval_rules rs (set_env p (env_with_sets base d)).
Proof.
  intros d d' rs p base Hassoc Hok.
  induction rs as [| r rs IH]; [reflexivity|].
  inversion Hok as [| ? ? [Hrok Hrdecl] Hrest]; subst.
  assert (Hag : forall nm, In nm (body_set_names (r_body r)) ->
            e_set (env_with_sets base d') nm = e_set (env_with_sets base d) nm).
  { intros nm Hnm. rewrite !e_set_declared.
    apply Hassoc. apply (Hrdecl _ Hnm). }
  destruct (rule_lookup_concatN_ok_agree r p base d' d Hrok Hag) as [Hl [Ha Ho]].
  cbn [eval_rules]. rewrite Hl, Ha, Ho.
  rewrite (IH Hrest). reflexivity.
Qed.

(** ok-ness of a suffix and of [take_concat_run]'s leftover. *)
Lemma rs_concatN_ok_tl : forall d r rs, rs_concatN_ok d (r :: rs) -> rs_concatN_ok d rs.
Proof. intros d r rs H. inversion H; assumption. Qed.

(** *** GENERALIZED N-WAY concat correctness, precondition [rs_concatN_ok]. *)
Theorem optimize_rules_concatN_correct_gen : forall fuel rs n d n' d' rs' base p,
  optimize_rules_concatN fuel n d rs = (n', d', rs') ->
  rs_concatN_ok d rs ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  eval_rules rs' (set_env p (env_with_sets base d'))
  = eval_rules rs  (set_env p (env_with_sets base d)).
Proof.
  induction fuel as [| fuel IH]; intros rs n d n' d' rs' base p H Hok Hfresh.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_concatN_consSS in H.
      pose proof Hok as Hok0.
      inversion Hok as [| ? ? [Hr1ok Hr1decl] Hrest_ok]; subst.
      destruct (head_value2 r1) as [[[[[f1 a1] f2] b1] body] |] eqn:Ehd.
      * pose proof (rule_lookup_concatN_ok_head_clean r1 f1 a1 f2 b1 body Hr1ok Ehd) as Hc1.
        destruct (take_concat_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct (take_concat_run_shape r1 f1 a1 f2 b1 body (r2 :: rest) ts rest' Ehd Erun)
          as [Hsplit [HwA HwB]].
        assert (Hokrest' : rs_concatN_ok d rest').
        { unfold rs_concatN_ok in *. rewrite Hsplit in Hrest_ok.
          apply Forall_app in Hrest_ok. exact (proj2 Hrest_ok). }
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concatN fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           cbn [eval_rules].
           rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hrest_ok Hfresh).
           destruct (rule_clean_env r1 p base dd'' d Hc1) as [Hl [Ha Ho]].
           rewrite Hl, Ha, Ho. reflexivity.
        -- cbv zeta in H.
           remember (optimize_rules_concatN fuel (S n)
                       {| sd_sets := (setname n, map pack_tuple ((a1,b1) :: t :: ts'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n' d' rs'.
           set (tuples := (a1, b1) :: t :: ts') in *.
           set (dn := {| sd_sets := (setname n, map pack_tuple tuples) :: sd_sets d;
                         sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |}) in *.
           assert (Hrun_eq : r1 :: r2 :: rest
                   = map (fun ab => orig_rule2 f1 f2 (fst ab) (snd ab) body r1) tuples
                     ++ rest').
           { subst tuples. cbn [map app fst snd]. f_equal.
             - apply (head_value2_canon r1 f1 a1 f2 b1 body Ehd).
             - exact Hsplit. }
           (* combined assoc-stability: dd'' agrees with d on every name declared in d *)
           assert (Hassoc_dd : forall nm X, In nm (map fst (sd_sets d)) ->
                     assoc_str nm (sd_sets dd'') X = assoc_str nm (sd_sets d) X).
           { intros nm X Hnmd.
             assert (Hne : forall k, n <= k -> nm <> setname k)
               by (intros k Hk Heq; subst nm; apply (Hfresh k Hk Hnmd)).
             rewrite (optimize_rules_concatN_assoc_stable fuel (S n) dn _ _ _ _ nm X
                        (eq_sym Erec) (fun k Hk => Hne k ltac:(lia))).
             subst dn; cbn [sd_sets assoc_str].
             destruct (String.eqb nm (setname n)) eqn:Eq.
             - apply String.eqb_eq in Eq. exfalso. apply (Hne n (Nat.le_refl n) Eq).
             - reflexivity. }
           assert (Htail : eval_rules rr'' (set_env p (env_with_sets base dd''))
                           = eval_rules rest' (set_env p (env_with_sets base dn))).
           { eapply (IH rest' (S n) dn m'' dd'' rr'' base p (eq_sym Erec)).
             - (* rest' is ok against dn: it reads declared-in-d names, still declared in dn *)
               unfold rs_concatN_ok in *. apply Forall_forall.
               intros r Hr. rewrite Forall_forall in Hokrest'.
               destruct (Hokrest' r Hr) as [Hrok Hrdecl]. split; [exact Hrok |].
               intros nm Hnm. subst dn; cbn [sd_sets map]. right. apply (Hrdecl _ Hnm).
             - intros k Hk Hin. subst dn; cbn [sd_sets map] in Hin.
               destruct Hin as [Heq | Hin].
               + apply setname_inj in Heq. lia.
               + apply (Hfresh k); [lia | exact Hin]. }
           assert (Hlook : e_set (pkt_env (set_env p (env_with_sets base dd'')))
                             (setname n) = map pack_tuple tuples).
           { cbn [set_env with_pkt_env pkt_env]. rewrite e_set_declared.
             erewrite (optimize_rules_concatN_assoc_stable fuel (S n) dn _ _ _ _
                         (setname n) _ (eq_sym Erec)).
             - subst dn; cbn [sd_sets assoc_str]. rewrite String.eqb_refl. reflexivity.
             - intros k Hk Heq. apply setname_inj in Heq. lia. }
           set (qd := set_env p (env_with_sets base dd'')) in *.
           assert (Hcert : eval_matchcond (MConcatSet [f1; f2] false (setname n)) qd
                   = existsb (fun ab => andb (eval_matchcond (MCmp f1 CEq (fst ab)) qd)
                                             (eval_matchcond (MCmp f2 CEq (snd ab)) qd))
                             tuples).
           { apply (concat_two_fields_certificate_N f1 f2 tuples (setname n) qd).
             - exact Hlook.
             - intros a b Hin Hld.
               assert (Hfx : field_fixed_len f1 = Some (Datatypes.length a)).
               { destruct (take_concat_run_head_width r1 f1 a1 f2 b1 body r2 rest
                             (t :: ts') rest' Ehd Erun ltac:(discriminate)) as [Hh1 _].
                 subst tuples. destruct Hin as [Hab | Hin].
                 - injection Hab as -> ->. exact Hh1.
                 - apply (HwA a b Hin). }
               apply (field_fixed_len_loaded f1 (Datatypes.length a) qd Hfx Hld).
             - intros a b Hin Hld.
               assert (Hfx : field_fixed_len f2 = Some (Datatypes.length b)).
               { destruct (take_concat_run_head_width r1 f1 a1 f2 b1 body r2 rest
                             (t :: ts') rest' Ehd Erun ltac:(discriminate)) as [_ Hh2].
                 subst tuples. destruct Hin as [Hab | Hin].
                 - injection Hab as -> ->. exact Hh2.
                 - apply (HwB a b Hin). }
               apply (field_fixed_len_loaded f2 (Datatypes.length b) qd Hfx Hld). }
           transitivity (eval_rules
             (map (fun ab => orig_rule2 f1 f2 (fst ab) (snd ab) body r1) tuples ++ rr'') qd).
           { apply (eval_rules_run_collapse
                      (map (fun ab => orig_rule2 f1 f2 (fst ab) (snd ab) body r1) tuples)
                      (rule_loadable (merged_rule2 f1 f2 (setname n) body r1) qd)
                      (outcome (merged_rule2 f1 f2 (setname n) body r1) qd)
                      (merged_rule2 f1 f2 (setname n) body r1) rr'' qd).
             - subst tuples. discriminate.
             - intros r Hr. apply in_map_iff in Hr as [ab [Hab _]]. subst r.
               symmetry. apply merged_rule2_loadable_eq_orig.
             - intros r Hr. apply in_map_iff in Hr as [ab [Hab _]]. subst r.
               symmetry. apply merged_rule2_outcome_eq_orig.
             - reflexivity.
             - reflexivity.
             - rewrite merged_rule2_applies. rewrite Hcert.
               rewrite existsb_map_eq.
               transitivity (existsb (fun ab =>
                   andb (andb (eval_matchcond (MCmp f1 CEq (fst ab)) qd)
                              (eval_matchcond (MCmp f2 CEq (snd ab)) qd))
                        (rule_applies_walk body qd)) tuples).
               + rewrite existsb_andb_const. reflexivity.
               + apply existsb_ext. intros ab _. symmetry. apply orig_rule2_applies. }
           assert (Htail' : eval_rules rr'' qd = eval_rules rest' qd).
           { rewrite Htail. unfold qd.
             (* dn and dd'' both bridge to d on rest' (ok against d) *)
             transitivity (eval_rules rest' (set_env p (env_with_sets base d))).
             - apply (eval_rules_concatN_seam_env d dn rest' p base); [| exact Hokrest'].
               intros nm X Hnmd. subst dn; cbn [sd_sets assoc_str].
               destruct (String.eqb nm (setname n)) eqn:Eq.
               + apply String.eqb_eq in Eq. subst nm. exfalso. apply (Hfresh n (Nat.le_refl n) Hnmd).
               + reflexivity.
             - symmetry.
               apply (eval_rules_concatN_seam_env d dd'' rest' p base Hassoc_dd Hokrest'). }
           rewrite (eval_rules_app_cong
                      (map (fun ab => orig_rule2 f1 f2 (fst ab) (snd ab) body r1) tuples)
                      rr'' rest' qd Htail').
           rewrite <- Hrun_eq.
           unfold qd. apply (eval_rules_concatN_seam_env d dd'' (r1 :: r2 :: rest) p base
                               Hassoc_dd Hok0).
      * remember (optimize_rules_concatN fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst n' d' rs'.
        cbn [eval_rules].
        rewrite (IH (r2 :: rest) n d m'' dd'' rr'' base p (eq_sym Erec) Hrest_ok Hfresh).
        (* r1 no-op lookup rule (head_value2 = None): env-stable via ok-agree *)
        assert (Hag1 : forall nm, In nm (body_set_names (r_body r1)) ->
                  e_set (env_with_sets base dd'') nm = e_set (env_with_sets base d) nm).
        { intros nm Hnm. rewrite !e_set_declared.
          apply (optimize_rules_concatN_assoc_stable fuel n d (r2 :: rest)
                   m'' dd'' rr'' nm _ (eq_sym Erec)).
          intros k Hk Heq. subst nm. apply (Hfresh k Hk). apply (Hr1decl _ Hnm). }
        destruct (rule_lookup_concatN_ok_agree r1 p base dd'' d Hr1ok Hag1) as [Hl [Ha Ho]].
        rewrite Hl, Ha, Ho. reflexivity.
Qed.

(** Chain-level generalized concat correctness. *)
Theorem optimize_chain_concatN_correct_gen : forall n d c n' d' c' base p,
  optimize_chain_concatN n d c = (n', d', c') ->
  rs_concatN_ok d (c_rules c) ->
  (forall k, n <= k -> ~ In (setname k) (map fst (sd_sets d))) ->
  eval_chain c' (set_env p (env_with_sets base d'))
  = eval_chain c  (set_env p (env_with_sets base d)).
Proof.
  intros n d c n' d' c' base p H Hok Hfresh.
  unfold optimize_chain_concatN in H.
  destruct (optimize_rules_concatN (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:Erec.
  inversion H; subst n' d' c'. cbn [c_rules c_policy].
  unfold eval_chain. cbn [c_rules c_policy].
  rewrite (optimize_rules_concatN_correct_gen (List.length (c_rules c)) (c_rules c) n d
             m'' dd'' rr'' base p Erec Hok Hfresh).
  reflexivity.
Qed.
