(** * Optimize_Mapn: the [nft -o] DATA-VALUE-MAP merge (`meta mark set … map`),
    proved STATE-preserving (axiom-free) — TODO 1a.

    [nft -o] folds adjacent rules whose differing part is a STATEMENT VALUE (not the
    verdict) into ONE rule keyed by a map:

        ip saddr A meta mark set M1          ip saddr { A, B }
        ip saddr B meta mark set M2   =>      meta mark set ip saddr map { A:M1, B:M2 }

    Unlike the value→set / concat / vmap merges (which consolidate the VERDICT and
    are checked against the verdict-only [eval_chain]), a data-map merge changes the
    packet's META state (the `mark`), which [eval_chain] cannot observe.  So the
    soundness here is stated over the DSL STATE-threading semantics [eval_rules_mut]
    / [dsl_step] (which thread each rule's [body_writes] meta effect), NOT
    [eval_chain] — this is the per-pass correctness the gap demanded.

    The MERGED rule keeps a head SET guard `ip saddr { A, B }` (the map's key set):
    so the rule only fires when the field is a map key, the map lookup ALWAYS hits,
    and on a non-key value the rule simply does not apply — exactly matching the two
    originals.  This sidesteps any map-MISS subtlety and makes the merge provably
    state-preserving.  The merge synthesises BOTH the anonymous set (`sd_sets`, the
    head guard) AND the data map (`sd_maps`, the statement value) — and is the FIRST
    pass to write `sd_maps`.

    The verdict side is trivial: both the originals and the merged rule are verdict-
    neutral ([Continue]), so they fall through on every packet for ANY environment;
    hence composing this pass preserves [eval_chain] (the verdict) unconditionally,
    while the [dsl_step] equality below is the NON-vacuous content (the map yields the
    right mark). Axiom-free. *)

From Stdlib Require Import List PeanoNat Bool Lia String.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Optimize Optimize_Merge.
Import ListNotations.
Local Open Scope nat_scope.

(** An ORIGINAL rule: `<field> = v  meta <k> set M` (verdict-neutral). *)
Definition orig_map_rule (f : field) (v M : data) (k : meta_key) : rule :=
  {| r_body := [BMatch (MCmp f CEq v); BStmt (SMetaSet k (VImm M))];
     r_verdict := Continue; r_vmap := None; r_nat := None; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.

(** The MERGED rule: `<field> @setname  meta <k> set <field> map @mapname`. *)
Definition mk_map_rule (f : field) (setname mapname : string) (k : meta_key) : rule :=
  {| r_body := [BMatch (MConcatSet [f] false setname);
                BStmt (SMetaSet k (VMap [f] [] mapname))];
     r_verdict := Continue; r_vmap := None; r_nat := None; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.

(** The single-field anonymous SET / data MAP contents the merge synthesises. *)
Definition map2_set (v1 v2 : data) : list (data * data) := [(v1, v1); (v2, v2)].
Definition map2_map (v1 v2 M1 M2 : data) : list (data * data) := [(v1, M1); (v2, M2)].

(** *** The head set-membership test of the merged rule, on a fixed-width field. *)
Lemma mapn_head_mem : forall (f : field) (setname : string) (v1 v2 : data) (p : packet),
  e_set (pkt_env p) setname = map2_set v1 v2 ->
  field_fixed_len f = Some (List.length v1) ->
  field_fixed_len f = Some (List.length v2) ->
  field_loadable f p = true ->
  eval_matchcond (MConcatSet [f] false setname) p
  = (data_eqb v1 (field_value f p) || data_eqb v2 (field_value f p)).
Proof.
  intros f setname v1 v2 p Hset Hfx1 Hfx2 Hld.
  unfold eval_matchcond, eval_matchcond_body, match_loadable.
  cbn [fields_loadable forallb]. rewrite Hld, Bool.andb_true_r. cbn [andb].
  change (map (fun f0 => field_value f0 p) [f]) with [field_value f p].
  rewrite Hset. unfold map2_set.
  rewrite concat_set_mem_single. unfold set_mem. cbn [existsb].
  rewrite !data_in_iv_point. rewrite Bool.orb_false_r. reflexivity.
Qed.

(** *** [set_meta] preserves [pkt_env] and the [field_value] of a PAYLOAD field
    (the only fields with [field_fixed_len = Some], hence the only merge keys): the
    mark write touches [pkt_meta], not the payload bytes a payload load reads. *)
Lemma field_value_set_meta : forall (f : field) (len : nat) (p : packet) (k : meta_key) (v : data),
  field_fixed_len f = Some len ->
  field_value f (set_meta p k v) = field_value f p.
Proof.
  intros f len p k v Hfx. unfold field_value, field_fixed_len in *.
  destruct (field_load f) eqn:Efl; try discriminate.
  unfold do_load, read_payload, set_meta, with_pkt_meta.
  destruct b; reflexivity.
Qed.

Lemma pkt_env_set_meta : forall p k v, pkt_env (set_meta p k v) = pkt_env p.
Proof. intros. unfold set_meta, with_pkt_meta, pkt_env. reflexivity. Qed.

Lemma field_loadable_set_meta : forall (f : field) (len : nat) (p : packet) (k : meta_key) (v : data),
  field_fixed_len f = Some len ->
  field_loadable f (set_meta p k v) = field_loadable f p.
Proof.
  intros f len p k v Hfx. unfold field_loadable, field_fixed_len in *.
  destruct (field_load f) eqn:Efl; try discriminate.
  unfold load_ok, read_payload_ok, set_meta, with_pkt_meta. destruct b; reflexivity.
Qed.

(** *** [body_writes] of one ORIGINAL rule: set the mark to [M] iff the field = [v]. *)
Lemma body_writes_orig : forall (f : field) (v M : data) (k : meta_key) (p : packet),
  field_fixed_len f = Some (List.length v) ->
  field_loadable f p = true ->
  body_writes (r_body (orig_map_rule f v M k)) p
  = (if data_eqb (field_value f p) v then set_meta p k M else p).
Proof.
  intros f v M k p Hfx Hld. cbn [orig_map_rule r_body body_writes].
  rewrite (eval_mcmp_point f v p Hld (field_fixed_len_loaded f (List.length v) p Hfx Hld)).
  destruct (data_eqb (field_value f p) v); [cbn [body_writes vsrc_loadable eval_vsrc] | reflexivity].
  reflexivity.
Qed.

(** *** [body_writes] of the MERGED rule: set the mark to the MAP value iff the field
    is in the head SET (= the map keys). *)
Lemma body_writes_merged : forall (f : field) (setname mapname : string)
                                  (v1 v2 M1 M2 : data) (k : meta_key) (p : packet),
  e_set (pkt_env p) setname = map2_set v1 v2 ->
  e_map (pkt_env p) mapname = map2_map v1 v2 M1 M2 ->
  field_fixed_len f = Some (List.length v1) ->
  field_fixed_len f = Some (List.length v2) ->
  field_loadable f p = true ->
  body_writes (r_body (mk_map_rule f setname mapname k)) p
  = (if data_eqb v1 (field_value f p) || data_eqb v2 (field_value f p)
     then set_meta p k (map_lookup_data (field_value f p) (map2_map v1 v2 M1 M2))
     else p).
Proof.
  intros f setname mapname v1 v2 M1 M2 k p Hset Hmap Hfx1 Hfx2 Hld.
  cbn [mk_map_rule r_body body_writes].
  rewrite (mapn_head_mem f setname v1 v2 p Hset Hfx1 Hfx2 Hld).
  destruct (data_eqb v1 (field_value f p) || data_eqb v2 (field_value f p));
    [| reflexivity].
  cbn [body_writes vsrc_loadable fields_loadable forallb].
  rewrite Hld, Bool.andb_true_r.
  cbn [eval_vsrc apply_transforms map List.concat].
  rewrite app_nil_r, Hmap. reflexivity.
Qed.

(** *** THE CORE (non-vacuous): the merged rule's STATE effect equals the two
    originals' composed effect — the map yields exactly the right mark. *)
Lemma dsl_step_map_merge : forall (f : field) (v1 v2 M1 M2 : data)
                                  (setname mapname : string) (k : meta_key) (p : packet),
  e_set (pkt_env p) setname = map2_set v1 v2 ->
  e_map (pkt_env p) mapname = map2_map v1 v2 M1 M2 ->
  field_fixed_len f = Some (List.length v1) ->
  field_fixed_len f = Some (List.length v2) ->
  data_eqb v1 v2 = false ->
  dsl_step (mk_map_rule f setname mapname k) p
  = dsl_step (orig_map_rule f v2 M2 k) (dsl_step (orig_map_rule f v1 M1 k) p).
Proof.
  intros f v1 v2 M1 M2 setname mapname k p Hset Hmap Hfx1 Hfx2 Hne.
  rewrite (dsl_step_limit_free (mk_map_rule f setname mapname k) p) by reflexivity.
  rewrite (dsl_step_limit_free (orig_map_rule f v1 M1 k) p) by reflexivity.
  rewrite (dsl_step_limit_free (orig_map_rule f v2 M2 k) _) by reflexivity.
  unfold dsl_writes.
  destruct (field_loadable f p) eqn:Hld.
  - (* field loads *)
    rewrite (body_writes_merged f setname mapname v1 v2 M1 M2 k p Hset Hmap Hfx1 Hfx2 Hld).
    rewrite (body_writes_orig f v1 M1 k p Hfx1 Hld).
    rewrite (data_eqb_sym v1 (field_value f p)), (data_eqb_sym v2 (field_value f p)).
    pose proof (field_value_set_meta f (List.length v1) p k M1 Hfx1) as Hfvm1.
    pose proof (field_loadable_set_meta f (List.length v1) p k M1 Hfx1) as Hldm1.
    destruct (data_eqb (field_value f p) v1) eqn:E1.
    + (* fvp = v1: orig1 set mark to M1; orig2 (v2) cannot match (v1<>v2); merged map -> M1 *)
      pose proof (proj1 (data_eqb_true_iff (field_value f p) v1) E1) as Ev1.
      rewrite (body_writes_orig f v2 M2 k (set_meta p k M1) Hfx2 (eq_trans Hldm1 Hld)).
      rewrite Hfvm1, Ev1. cbn [orb].
      unfold map2_map; cbn [map_lookup_data]. rewrite data_eqb_refl, Hne. reflexivity.
    + destruct (data_eqb (field_value f p) v2) eqn:E2.
      * (* fvp = v2: orig1 no match (q=p); orig2 sets M2; merged map -> M2 (skips v1) *)
        rewrite (body_writes_orig f v2 M2 k p Hfx2 Hld).
        rewrite E2. cbn [orb]. unfold map2_map; cbn [map_lookup_data].
        rewrite E1, E2. reflexivity.
      * (* fvp neither: both originals fall through (q=p), merged head fails *)
        rewrite (body_writes_orig f v2 M2 k p Hfx2 Hld).
        rewrite E2. cbn [orb]. reflexivity.
  - (* field does NOT load: every head match fails, so no rule writes; all sides = p *)
    assert (Hmcc : eval_matchcond (MConcatSet [f] false setname) p = false)
      by (unfold eval_matchcond, match_loadable; cbn [fields_loadable forallb];
          rewrite Hld; reflexivity).
    assert (Hmerged_p : body_writes (r_body (mk_map_rule f setname mapname k)) p = p)
      by (cbn [mk_map_rule r_body body_writes]; rewrite Hmcc; reflexivity).
    assert (Horig1 : body_writes (r_body (orig_map_rule f v1 M1 k)) p = p)
      by (cbn [orig_map_rule r_body body_writes];
          unfold eval_matchcond, match_loadable; rewrite Hld; reflexivity).
    assert (Horig2 : body_writes (r_body (orig_map_rule f v2 M2 k)) p = p)
      by (cbn [orig_map_rule r_body body_writes];
          unfold eval_matchcond, match_loadable; rewrite Hld; reflexivity).
    rewrite Hmerged_p, Horig1, Horig2. reflexivity.
Qed.

(** Both rules are verdict-neutral ([Continue] with no side-effect terminal and no
    trailing statements), so their [outcome] is [None] — each just threads its
    [dsl_step] write to the next rule. *)
Lemma outcome_orig_map_none : forall f v M k p,
  outcome (orig_map_rule f v M k) p = None.
Proof. reflexivity. Qed.
Lemma outcome_mk_map_none : forall f setname mapname k p,
  outcome (mk_map_rule f setname mapname k) p = None.
Proof. reflexivity. Qed.

Lemma eval_rules_mut_continue : forall r rest p,
  outcome r p = None ->
  eval_rules_mut (r :: rest) p = eval_rules_mut rest (dsl_step r p).
Proof.
  intros r rest p Ho. cbn [eval_rules_mut]. rewrite Ho.
  destruct (rule_loadable r p && rule_applies r p); reflexivity.
Qed.

(** *** THE per-pass STATE correctness (non-vacuous): replacing the two originals by
    the merged map rule preserves the STATE-threading evaluation [eval_rules_mut] on
    every packet (so the rest of the chain sees the SAME mark). *)
Theorem eval_rules_mut_map_merge : forall (f : field) (v1 v2 M1 M2 : data)
    (setname mapname : string) (k : meta_key) (rest : list rule) (p : packet),
  e_set (pkt_env p) setname = map2_set v1 v2 ->
  e_map (pkt_env p) mapname = map2_map v1 v2 M1 M2 ->
  field_fixed_len f = Some (List.length v1) ->
  field_fixed_len f = Some (List.length v2) ->
  data_eqb v1 v2 = false ->
  eval_rules_mut (mk_map_rule f setname mapname k :: rest) p
  = eval_rules_mut (orig_map_rule f v1 M1 k :: orig_map_rule f v2 M2 k :: rest) p.
Proof.
  intros f v1 v2 M1 M2 setname mapname k rest p Hset Hmap Hfx1 Hfx2 Hne.
  rewrite (eval_rules_mut_continue _ rest p (outcome_mk_map_none f setname mapname k p)).
  rewrite (eval_rules_mut_continue _ _ p (outcome_orig_map_none f v1 M1 k p)).
  rewrite (eval_rules_mut_continue _ rest _ (outcome_orig_map_none f v2 M2 k _)).
  rewrite (dsl_step_map_merge f v1 v2 M1 M2 setname mapname k p Hset Hmap Hfx1 Hfx2 Hne).
  reflexivity.
Qed.

(** *** The VERDICT correctness is trivial (both sides fall through for ANY env), so
    composing this pass preserves [eval_rules] / [eval_chain] unconditionally. *)
Lemma eval_rules_continue : forall r rest p,
  outcome r p = None ->
  eval_rules (r :: rest) p = eval_rules rest p.
Proof.
  intros r rest p Ho. cbn [eval_rules]. rewrite Ho.
  destruct (rule_loadable r p && rule_applies r p); reflexivity.
Qed.

Theorem eval_rules_map_merge : forall (f : field) (v1 v2 M1 M2 : data)
    (setname mapname : string) (k : meta_key) (rest : list rule) (p : packet),
  eval_rules (mk_map_rule f setname mapname k :: rest) p
  = eval_rules (orig_map_rule f v1 M1 k :: orig_map_rule f v2 M2 k :: rest) p.
Proof.
  intros.
  rewrite (eval_rules_continue _ rest p (outcome_mk_map_none f setname mapname k p)).
  rewrite (eval_rules_continue _ _ p (outcome_orig_map_none f v1 M1 k p)).
  rewrite (eval_rules_continue _ rest p (outcome_orig_map_none f v2 M2 k p)).
  reflexivity.
Qed.

(** Axiom-freedom guards. *)
Print Assumptions dsl_step_map_merge.
Print Assumptions eval_rules_mut_map_merge.
Print Assumptions eval_rules_map_merge.
