(** * Optimize_Mapn: a verified DATA-VALUE-MAP consolidation pass (the first to
    write `sd_maps`), proved STATE-preserving (axiom-free) — TODO 1a.

    Adjacent rules whose differing part is a STATEMENT VALUE (the `meta mark` being
    set, not the verdict) are folded into ONE rule keyed by a data map:

        ip saddr A meta mark set M1          ip saddr { A, B }
        ip saddr B meta mark set M2   =>      meta mark set ip saddr map { A:M1, B:M2 }

    Unlike the value→set / concat / vmap merges (which consolidate the VERDICT and
    are checked against the verdict-only [eval_chain]), a data-map merge changes the
    packet's META state (the `mark`), which [eval_chain] cannot observe.  So the
    soundness here is stated over the DSL STATE-threading semantics [eval_rules_mut]
    / [dsl_step] (which thread each rule's [body_writes] meta effect), NOT
    [eval_chain].  This is the non-vacuous content: the map yields exactly the right
    mark.  The verdict side is trivial (all rules are verdict-neutral [Continue], so
    they fall through for ANY environment), hence composing the pass preserves
    [eval_chain] unconditionally.

    *** FIDELITY NOTE — relationship to `nft -o`'s output (read this).

    This pass is NOT byte-identical to `nft -o`, and does not claim to be:

      - `nft -o` (tested: nft v1.1.6) merges value maps only for the NAT verdict-
        statements `dnat to … map {…}` / `snat to … map {…}`; it does NOT merge
        `meta mark set` rules at all.  We use the `meta mark` example because it is
        the simplest STATE write to model (no flow-keyed NAT state).
      - When `nft -o` DOES emit a value map (dnat/snat), it emits a BARE map with NO
        head set guard: `dnat ip to ip saddr map { A:…, B:… }`.

    We instead emit the head-set-GUARDED form `ip saddr { A, B } meta mark set ip
    saddr map { A:M1, B:M2 }`.  This is VALID, loadable nftables and is SEMANTICALLY
    EQUIVALENT to the two originals — but the guard is required for soundness *in our
    model*, not a free stylistic choice:

      - Our statement value-map semantics ([vsrc_loadable (VMap …) = fields_loadable]
        at [Semantics.v:696], mirrored by the VM's [ILookupVal] at [Semantics.v:1241])
        do NOT implement nftables' NFT_BREAK-on-map-miss: a lookup of a key absent
        from the map loads [map_lookup_data]'s default ([] — [Bytes.v:37]) and the
        statement still writes it.  So a BARE merged map would, on a non-key packet,
        overwrite the mark with [] instead of leaving the prior mark untouched —
        diverging from the two originals (which simply don't match).
      - The head SET guard (= the map's key set) makes the merged rule fire ONLY on
        key packets, so the lookup ALWAYS hits and the off-key case is a clean
        non-match — exactly matching the originals.  The merge therefore synthesises
        BOTH the anonymous set (`sd_sets`, the head guard) AND the data map
        (`sd_maps`, the statement value).

    So: what is PROVEN here is a sound, axiom-free, state-preserving data-map
    consolidation that the verified optimizer may legitimately perform.  Matching
    `nft -o`'s exact BARE-map output (no head guard) would first require modelling
    NFT_BREAK-on-map-miss in both [body_writes] and the VM's [ILookupVal] (and re-
    proving [compile_chain_correct] for it) — a core-semantics change left as future
    work.  Axiom-free either way. *)

From Stdlib Require Import List PeanoNat Bool Lia String.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Optimize Optimize_Merge.
Import ListNotations.
Local Open Scope nat_scope.

(** An ORIGINAL rule: `<field> = v  meta <k> set M` (verdict-neutral). *)
Definition orig_map_rule (f : field) (v M : data) (k : meta_key) : rule :=
  {| r_body := [BMatch (MCmp f CEq v); BStmt (SMetaSet k (VImm M))];
     r_outcome := ONone; r_after := [] |}.

(** The MERGED rule: `<field> @setname  meta <k> set <field> map @mapname`. *)
Definition mk_map_rule (f : field) (setname mapname : string) (k : meta_key) : rule :=
  {| r_body := [BMatch (MConcatSet [f] false setname);
                BStmt (SMetaSet k (VMap [f] [] mapname))];
     r_outcome := ONone; r_after := [] |}.

(** The single-field anonymous SET / data MAP contents the merge synthesises. *)
Definition map2_set (v1 v2 : data) : list (data * data) := [(v1, v1); (v2, v2)].
Definition map2_map (v1 v2 M1 M2 : data) : list (data * data) := [(v1, M1); (v2, M2)].

(** *** The head set-membership test of the merged rule, on a fixed-width field. *)
Lemma mapn_head_mem : forall (f : field) (setname : string) (v1 v2 : data) (e : env) (p : packet),
  e_set e setname = map2_set v1 v2 ->
  field_fixed_len f = Some (List.length v1) ->
  field_fixed_len f = Some (List.length v2) ->
  field_loadable f p = true ->
  eval_matchcond (MConcatSet [f] false setname) e p
  = (data_eqb v1 (field_value f e p) || data_eqb v2 (field_value f e p)).
Proof.
  intros f setname v1 v2 e p Hset Hfx1 Hfx2 Hld.
  unfold eval_matchcond, eval_matchcond_body, match_loadable.
  cbn [fields_loadable forallb]. rewrite Hld, Bool.andb_true_r. cbn [andb].
  change (map (fun f0 => field_value f0 e p) [f]) with [field_value f e p].
  rewrite Hset. unfold map2_set.
  rewrite concat_set_mem_single. unfold set_mem. cbn [existsb].
  rewrite !data_in_iv_point. rewrite Bool.orb_false_r. reflexivity.
Qed.

(** Whether a field reads a raw PAYLOAD slice (as opposed to a meta/ct/... selector).
    The [mapN] demo keys on such fields ([ip saddr] & co.); a payload read is
    provably untouched by a `meta … set` write (below), which the value-map STATE
    demonstration relies on.  [field_fixed_len] now also covers fixed-width META
    keys, so the payload restriction is stated explicitly rather than derived from
    [field_fixed_len = Some] (that would be UNSOUND for a `meta mark` key whose value
    the map's own `meta mark set` write would change). *)
Definition is_payload_load (f : field) : bool :=
  match field_load f with LPayload _ _ _ => true | _ => false end.

(** *** [set_meta] preserves the [field_value] of a PAYLOAD field: the
    mark write touches [pkt_meta], not the payload bytes a payload load reads. *)
Lemma field_value_set_meta : forall (f : field) (e : env) (p : packet) (k : meta_key) (v : data),
  is_payload_load f = true ->
  field_value f e (set_meta p k v) = field_value f e p.
Proof.
  intros f e p k v Hpl. unfold field_value, is_payload_load in *.
  destruct (field_load f) eqn:Efl; try discriminate.
  unfold do_load, read_payload, set_meta, with_pkt_meta.
  destruct b; reflexivity.
Qed.


Lemma field_loadable_set_meta : forall (f : field) (p : packet) (k : meta_key) (v : data),
  is_payload_load f = true ->
  field_loadable f (set_meta p k v) = field_loadable f p.
Proof.
  intros f p k v Hpl. unfold field_loadable, is_payload_load in *.
  destruct (field_load f) eqn:Efl; try discriminate.
  unfold load_ok, read_payload_ok, set_meta, with_pkt_meta. destruct b; reflexivity.
Qed.

(** *** [body_writes] of one ORIGINAL rule: set the mark to [M] iff the field = [v]. *)
Lemma body_writes_orig : forall (f : field) (v M : data) (k : meta_key) (e : env) (p : packet),
  field_fixed_len f = Some (List.length v) ->
  field_loadable f p = true ->
  body_writes (r_body (orig_map_rule f v M k)) e p
  = (e, if data_eqb (field_value f e p) v then set_meta p k M else p).
Proof.
  intros f v M k e p Hfx Hld. cbn [orig_map_rule r_body body_writes].
  rewrite (eval_mcmp_point f v e p Hld (field_fixed_len_loaded f (List.length v) e p Hfx Hld)).
  destruct (data_eqb (field_value f e p) v); [cbn [body_writes vsrc_loadable eval_vsrc] | reflexivity].
  reflexivity.
Qed.

(** *** [body_writes] of the MERGED rule: set the mark to the MAP value iff the field
    is in the head SET (= the map keys). *)
Lemma body_writes_merged : forall (f : field) (setname mapname : string)
                                  (v1 v2 M1 M2 : data) (k : meta_key) (e : env) (p : packet),
  e_set e setname = map2_set v1 v2 ->
  e_map e mapname = map2_map v1 v2 M1 M2 ->
  field_fixed_len f = Some (List.length v1) ->
  field_fixed_len f = Some (List.length v2) ->
  field_loadable f p = true ->
  body_writes (r_body (mk_map_rule f setname mapname k)) e p
  = (e, if data_eqb v1 (field_value f e p) || data_eqb v2 (field_value f e p)
        then set_meta p k (map_lookup_data (field_value f e p) (map2_map v1 v2 M1 M2))
        else p).
Proof.
  intros f setname mapname v1 v2 M1 M2 k e p Hset Hmap Hfx1 Hfx2 Hld.
  cbn [mk_map_rule r_body body_writes].
  rewrite (mapn_head_mem f setname v1 v2 e p Hset Hfx1 Hfx2 Hld).
  destruct (data_eqb v1 (field_value f e p) || data_eqb v2 (field_value f e p));
    [| reflexivity].
  cbn [body_writes vsrc_loadable fields_loadable forallb].
  rewrite Hld, Bool.andb_true_r.
  cbn [eval_vsrc apply_transforms map List.concat].
  rewrite app_nil_r, Hmap. reflexivity.
Qed.

(** *** THE CORE (non-vacuous): the merged rule's STATE effect equals the two
    originals' composed effect — the map yields exactly the right mark. *)
Lemma dsl_step_map_merge : forall (f : field) (v1 v2 M1 M2 : data)
                                  (setname mapname : string) (k : meta_key) (e : env) (p : packet),
  is_payload_load f = true ->
  e_set e setname = map2_set v1 v2 ->
  e_map e mapname = map2_map v1 v2 M1 M2 ->
  field_fixed_len f = Some (List.length v1) ->
  field_fixed_len f = Some (List.length v2) ->
  data_eqb v1 v2 = false ->
  dsl_step (mk_map_rule f setname mapname k) e p
  = (let '(e1, p1) := dsl_step (orig_map_rule f v1 M1 k) e p in
     dsl_step (orig_map_rule f v2 M2 k) e1 p1).
Proof.
  intros f v1 v2 M1 M2 setname mapname k e p Hpl Hset Hmap Hfx1 Hfx2 Hne.
  rewrite (dsl_step_limit_free (mk_map_rule f setname mapname k) e p) by reflexivity.
  rewrite (dsl_step_limit_free (orig_map_rule f v1 M1 k) e p) by reflexivity.
  unfold dsl_writes.
  destruct (field_loadable f p) eqn:Hld.
  - (* field loads *)
    rewrite (body_writes_merged f setname mapname v1 v2 M1 M2 k e p Hset Hmap Hfx1 Hfx2 Hld).
    rewrite (body_writes_orig f v1 M1 k e p Hfx1 Hld).
    rewrite (data_eqb_sym v1 (field_value f e p)), (data_eqb_sym v2 (field_value f e p)).
    pose proof (field_value_set_meta f e p k M1 Hpl) as Hfvm1.
    pose proof (field_loadable_set_meta f p k M1 Hpl) as Hldm1.
    destruct (data_eqb (field_value f e p) v1) eqn:E1.
    + (* fvp = v1: orig1 set mark to M1; orig2 (v2) cannot match (v1<>v2); merged map -> M1 *)
      pose proof (proj1 (data_eqb_true_iff (field_value f e p) v1) E1) as Ev1.
      cbv iota beta.
      rewrite (dsl_step_limit_free (orig_map_rule f v2 M2 k) e (set_meta p k M1)) by reflexivity.
      unfold dsl_writes.
      rewrite (body_writes_orig f v2 M2 k e (set_meta p k M1) Hfx2 (eq_trans Hldm1 Hld)).
      rewrite Hfvm1, Ev1. cbn [orb].
      unfold map2_map; cbn [map_lookup_data]. rewrite data_eqb_refl, Hne. reflexivity.
    + destruct (data_eqb (field_value f e p) v2) eqn:E2.
      * (* fvp = v2: orig1 no match (q=p); orig2 sets M2; merged map -> M2 (skips v1) *)
        cbv iota beta.
        rewrite (dsl_step_limit_free (orig_map_rule f v2 M2 k) e p) by reflexivity.
        unfold dsl_writes.
        rewrite (body_writes_orig f v2 M2 k e p Hfx2 Hld).
        rewrite E2. cbn [orb]. unfold map2_map; cbn [map_lookup_data].
        rewrite E1, E2. reflexivity.
      * (* fvp neither: both originals fall through (q=p), merged head fails *)
        cbv iota beta.
        rewrite (dsl_step_limit_free (orig_map_rule f v2 M2 k) e p) by reflexivity.
        unfold dsl_writes.
        rewrite (body_writes_orig f v2 M2 k e p Hfx2 Hld).
        rewrite E2. cbn [orb]. reflexivity.
  - (* field does NOT load: every head match fails, so no rule writes; all sides = p *)
    assert (Hmcc : eval_matchcond (MConcatSet [f] false setname) e p = false)
      by (unfold eval_matchcond, match_loadable; cbn [fields_loadable forallb];
          rewrite Hld; reflexivity).
    assert (Hmerged_p : body_writes (r_body (mk_map_rule f setname mapname k)) e p = (e, p))
      by (cbn [mk_map_rule r_body body_writes]; rewrite Hmcc; reflexivity).
    assert (Horig1 : body_writes (r_body (orig_map_rule f v1 M1 k)) e p = (e, p))
      by (cbn [orig_map_rule r_body body_writes];
          unfold eval_matchcond, match_loadable; rewrite Hld; reflexivity).
    assert (Horig2 : body_writes (r_body (orig_map_rule f v2 M2 k)) e p = (e, p))
      by (cbn [orig_map_rule r_body body_writes];
          unfold eval_matchcond, match_loadable; rewrite Hld; reflexivity).
    rewrite Hmerged_p, Horig1. cbv iota beta.
    rewrite (dsl_step_limit_free (orig_map_rule f v2 M2 k) e p) by reflexivity.
    unfold dsl_writes. rewrite Horig2. reflexivity.
Qed.

(** Both rules are verdict-neutral ([Continue] with no side-effect terminal and no
    trailing statements), so their [outcome] is [None] — each just threads its
    [dsl_step] write to the next rule. *)
Lemma outcome_orig_map_none : forall f v M k e p,
  outcome (orig_map_rule f v M k) e p = None.
Proof. reflexivity. Qed.
Lemma outcome_mk_map_none : forall f setname mapname k e p,
  outcome (mk_map_rule f setname mapname k) e p = None.
Proof. reflexivity. Qed.

Lemma eval_rules_mut_continue : forall r rest e p,
  outcome r e p = None ->
  eval_rules_mut (r :: rest) e p
  = (let '(e', p') := dsl_step r e p in eval_rules_mut rest e' p').
Proof.
  intros r rest e p Ho. cbn [eval_rules_mut dsl_rule_step]. rewrite Ho.
  destruct (rule_loadable r e p && rule_applies r e p);
    destruct (dsl_step r e p) as [e' p']; reflexivity.
Qed.

(** *** THE per-pass STATE correctness (non-vacuous): replacing the two originals by
    the merged map rule preserves the STATE-threading evaluation [eval_rules_mut] on
    every packet (so the rest of the chain sees the SAME mark). *)
Theorem eval_rules_mut_map_merge : forall (f : field) (v1 v2 M1 M2 : data)
    (setname mapname : string) (k : meta_key) (rest : list rule) (e : env) (p : packet),
  is_payload_load f = true ->
  e_set e setname = map2_set v1 v2 ->
  e_map e mapname = map2_map v1 v2 M1 M2 ->
  field_fixed_len f = Some (List.length v1) ->
  field_fixed_len f = Some (List.length v2) ->
  data_eqb v1 v2 = false ->
  eval_rules_mut (mk_map_rule f setname mapname k :: rest) e p
  = eval_rules_mut (orig_map_rule f v1 M1 k :: orig_map_rule f v2 M2 k :: rest) e p.
Proof.
  intros f v1 v2 M1 M2 setname mapname k rest e p Hpl Hset Hmap Hfx1 Hfx2 Hne.
  rewrite (eval_rules_mut_continue _ rest e p (outcome_mk_map_none f setname mapname k e p)).
  rewrite (eval_rules_mut_continue _ _ e p (outcome_orig_map_none f v1 M1 k e p)).
  rewrite (dsl_step_map_merge f v1 v2 M1 M2 setname mapname k e p Hpl Hset Hmap Hfx1 Hfx2 Hne).
  destruct (dsl_step (orig_map_rule f v1 M1 k) e p) as [e1 p1].
  rewrite (eval_rules_mut_continue _ rest e1 p1 (outcome_orig_map_none f v2 M2 k e1 p1)).
  reflexivity.
Qed.

(** *** The VERDICT correctness is trivial (both sides fall through for ANY env), so
    composing this pass preserves [eval_rules] / [eval_chain] unconditionally. *)
Lemma eval_rules_continue : forall r rest e p,
  outcome r e p = None ->
  eval_rules (r :: rest) e p = eval_rules rest e p.
Proof.
  intros r rest e p Ho. cbn [eval_rules]. rewrite Ho.
  destruct (rule_loadable r e p && rule_applies r e p); reflexivity.
Qed.

Theorem eval_rules_map_merge : forall (f : field) (v1 v2 M1 M2 : data)
    (setname mapname : string) (k : meta_key) (rest : list rule) (e : env) (p : packet),
  eval_rules (mk_map_rule f setname mapname k :: rest) e p
  = eval_rules (orig_map_rule f v1 M1 k :: orig_map_rule f v2 M2 k :: rest) e p.
Proof.
  intros.
  rewrite (eval_rules_continue _ rest e p (outcome_mk_map_none f setname mapname k e p)).
  rewrite (eval_rules_continue _ _ e p (outcome_orig_map_none f v1 M1 k e p)).
  rewrite (eval_rules_continue _ rest e p (outcome_orig_map_none f v2 M2 k e p)).
  reflexivity.
Qed.

(* ================================================================== *)
(** ** D1 — why the merged rule carries a head-SET guard.

    [mapN] is a labelled SOUND SUPERSET of `nft -o`: `nft --optimize` does not
    merge `meta mark set` rules at all (differentially confirmed against `nft`
    v1.1.6 and a live-kernel netns; regression gate: [e2e.sh] §B6), so there is
    no bare `nft` output for [mapN] to be byte-faithful to.  The guard (= the
    map's key domain) is a soundness necessity of THIS model: the statement
    value-map ([body_writes] on [SMetaSet _ (VMap …)]) loads [map_lookup_data]'s
    default [] on a miss (gap flagged at [Bytes.v]'s [map_lookup_data]), whereas
    the kernel NFT_BREAKs and leaves the mark untouched — so a guard-less merged
    rule would clobber the mark to [] off-key.  On-key the lookup always hits, so
    the guarded merge is exactly equivalent ([eval_rules_mut_map_merge]); the
    verdict is preserved even without the guard ([eval_rules_map_merge]).  The
    lemmas below pin the off-key divergence of the bare form, axiom-free. *)

(** The guard-less ("bare") merged rule — what `nft` WOULD emit if it merged
    `meta mark set`, and what the kernel runs with NFT_BREAK-on-miss. *)
Definition mk_map_rule_bare (f : field) (mapname : string) (k : meta_key) : rule :=
  {| r_body := [BStmt (SMetaSet k (VMap [f] [] mapname))];
     r_outcome := ONone; r_after := [] |}.

Lemma map_lookup_data_offkey : forall x v1 v2 M1 M2,
  data_eqb x v1 = false -> data_eqb x v2 = false ->
  map_lookup_data x (map2_map v1 v2 M1 M2) = [].
Proof.
  intros x v1 v2 M1 M2 H1 H2. unfold map2_map. cbn [map_lookup_data].
  rewrite H1, H2. reflexivity.
Qed.

(** The single-field value-map ([fields = [f]], no transforms) reads the field and
    looks it up — mirrors the [eval_vsrc] key reduction [body_writes_merged] uses. *)
Lemma eval_vsrc_vmap_single : forall f name e p,
  eval_vsrc (VMap [f] [] name) e p
  = map_lookup_data (field_value f e p) (e_map e name).
Proof.
  intros f name e p. cbn [eval_vsrc apply_transforms map List.concat].
  rewrite app_nil_r. reflexivity.
Qed.

(** OFF-KEY, the BARE rule CLOBBERS the mark to the map default [[]] (our model's
    default-on-miss) — where the kernel would instead BREAK and leave it. *)
Lemma dsl_step_bare_offkey : forall f v1 v2 M1 M2 mapname k e p,
  e_map e mapname = map2_map v1 v2 M1 M2 ->
  field_loadable f p = true ->
  data_eqb (field_value f e p) v1 = false ->
  data_eqb (field_value f e p) v2 = false ->
  dsl_step (mk_map_rule_bare f mapname k) e p = (e, set_meta p k []).
Proof.
  intros f v1 v2 M1 M2 mapname k e p Hmap Hld H1 H2.
  rewrite (dsl_step_limit_free (mk_map_rule_bare f mapname k) e p) by reflexivity.
  unfold dsl_writes. cbn [mk_map_rule_bare r_body body_writes].
  cbn [vsrc_loadable fields_loadable forallb]. rewrite Hld, Bool.andb_true_r.
  rewrite eval_vsrc_vmap_single, Hmap.
  rewrite (map_lookup_data_offkey _ v1 v2 M1 M2 H1 H2). reflexivity.
Qed.

(** OFF-KEY, ONE original is a NO-OP (its head match fails). *)
Lemma dsl_step_orig_offkey : forall f v M k e p,
  field_fixed_len f = Some (List.length v) ->
  field_loadable f p = true ->
  data_eqb (field_value f e p) v = false ->
  dsl_step (orig_map_rule f v M k) e p = (e, p).
Proof.
  intros f v M k e p Hfx Hld Hne.
  rewrite (dsl_step_limit_free (orig_map_rule f v M k) e p) by reflexivity.
  unfold dsl_writes. rewrite (body_writes_orig f v M k e p Hfx Hld), Hne. reflexivity.
Qed.

(** OFF-KEY, the two originals compose to a NO-OP. *)
Lemma dsl_step_orig_pair_offkey : forall f v1 v2 M1 M2 k e p,
  field_fixed_len f = Some (List.length v1) ->
  field_fixed_len f = Some (List.length v2) ->
  field_loadable f p = true ->
  data_eqb (field_value f e p) v1 = false ->
  data_eqb (field_value f e p) v2 = false ->
  (let '(e1, p1) := dsl_step (orig_map_rule f v1 M1 k) e p in
   dsl_step (orig_map_rule f v2 M2 k) e1 p1) = (e, p).
Proof.
  intros f v1 v2 M1 M2 k e p Hfx1 Hfx2 Hld H1 H2.
  rewrite (dsl_step_orig_offkey f v1 M1 k e p Hfx1 Hld H1). cbv iota beta.
  rewrite (dsl_step_orig_offkey f v2 M2 k e p Hfx2 Hld H2). reflexivity.
Qed.

(** *** THE PIN (axiom-free): off-key, the guard-less merged rule and the two
    originals produce DIFFERENT threaded packets — the bare rule writes the map
    default [[]], the originals leave the packet untouched.  They coincide ONLY
    when the mark is already [[]]; for any packet carrying a prior mark (the netns
    sentinel case) they diverge.  Hence the head-set guard is a SOUNDNESS necessity
    of this model's default-on-miss, and [mapN] cannot drop it without the
    NFT_BREAK-on-miss statement-map upgrade. *)
Theorem mapn_bare_diverges_offkey : forall f v1 v2 M1 M2 mapname k e p,
  e_map e mapname = map2_map v1 v2 M1 M2 ->
  field_fixed_len f = Some (List.length v1) ->
  field_fixed_len f = Some (List.length v2) ->
  field_loadable f p = true ->
  data_eqb (field_value f e p) v1 = false ->
  data_eqb (field_value f e p) v2 = false ->
  dsl_step (mk_map_rule_bare f mapname k) e p = (e, set_meta p k [])
  /\ (let '(e1, p1) := dsl_step (orig_map_rule f v1 M1 k) e p in
      dsl_step (orig_map_rule f v2 M2 k) e1 p1) = (e, p).
Proof.
  intros f v1 v2 M1 M2 mapname k e p Hmap Hfx1 Hfx2 Hld H1 H2. split.
  - exact (dsl_step_bare_offkey f v1 v2 M1 M2 mapname k e p Hmap Hld H1 H2).
  - exact (dsl_step_orig_pair_offkey f v1 v2 M1 M2 k e p Hfx1 Hfx2 Hld H1 H2).
Qed.

Print Assumptions mapn_bare_diverges_offkey.

(* ================================================================== *)
(** ** The executable pairwise pass. *)

From Stdlib Require Import Wellfounded Arith.Wf_nat.

(** Fresh map-name minting (a NEW namespace; the existing passes only mint
    [setname]/[vmapname]). *)
Definition mapname (n : nat) : string := String.append "__map" (string_of_nat n).
Lemma mapname_inj : forall a b, mapname a = mapname b -> a = b.
Proof.
  intros a b H. unfold mapname in H.
  apply string_of_nat_inj. cbn in H. repeat (injection H as H). exact H.
Qed.
Global Opaque mapname.

(** Extract the head field/value and the meta-set key/value of a rule shaped like
    `<f> = v  meta <k> set M` (its body), if any. *)
Definition orig_map_data (r : rule) : option (field * data * data * meta_key) :=
  match r_body r with
  | [BMatch (MCmp f CEq v); BStmt (SMetaSet k (VImm M))] => Some (f, v, M, k)
  | _ => None
  end.

(** Recognise a rule as EXACTLY the ORIGINAL shell (body AND end fields), using only
    constructor matches — NO decidable equality.  (The monolithic [rule_eq_dec] would
    re-derive [field]/[matchcond] equality via raw [decide equality], whose [string]
    case emits the per-char [String.get] destructor — unbound in the extracted OCaml
    and a ~42 MB blow-up; see [Optimize_Merge.rule_end_eqb].  Matching the record
    structurally binds [f]/[v]/[M]/[k] without ever comparing a [string].) *)
Definition is_orig_map (r : rule) : option (field * data * data * meta_key) :=
  match orig_map_data r, r_outcome r, r_after r with
  | Some (f, v, M, k), ONone, [] => Some (f, v, M, k)
  | _, _, _ => None
  end.

(** [orig_map_data] is a SINGLE match on [r_body]; its shape inverts cleanly. *)
Lemma orig_map_data_shape : forall r f v M k,
  orig_map_data r = Some (f, v, M, k) ->
  r_body r = [BMatch (MCmp f CEq v); BStmt (SMetaSet k (VImm M))].
Proof.
  intros [body outc aft] f v M k H.
  unfold orig_map_data in H. cbn in H. cbn [r_body].
  repeat (match goal with
          | [ H : (match ?y with _ => _ end) = Some _ |- _ ] => destruct y
          end; cbn in H; try discriminate H).
  injection H as -> -> -> ->. reflexivity.
Qed.

Lemma is_orig_map_shape : forall r f v M k,
  is_orig_map r = Some (f, v, M, k) -> r = orig_map_rule f v M k.
Proof.
  intros r f v M k H. unfold is_orig_map in H.
  destruct (orig_map_data r) as [[[[f0 v0] M0] k0]|] eqn:Hd; [|discriminate H].
  destruct (r_outcome r) eqn:Ho; try discriminate H.
  destruct (r_after r) eqn:Haft; try discriminate H.
  injection H as -> -> -> ->.
  pose proof (orig_map_data_shape r f v M k Hd) as Hbody.
  destruct r; cbn in *. subst. reflexivity.
Qed.

(** Two rules form an eligible map-merge pair: both ORIGINAL shells over the SAME
    fixed-width field and SAME meta key, with DISTINCT key values. *)
Definition map_merge_pair (r1 r2 : rule)
  : option (field * data * data * data * data * meta_key) :=
  match is_orig_map r1, is_orig_map r2 with
  | Some (f1, v1, M1, k1), Some (f2, v2, M2, k2) =>
      if field_eq_dec f1 f2 then if meta_eq_dec k1 k2 then
      match field_fixed_len f1 with
      | Some len =>
          if Nat.eq_dec len (List.length v1) then if Nat.eq_dec len (List.length v2) then
          if data_eqb v1 v2 then None else Some (f1, v1, v2, M1, M2, k1)
          else None else None
      | None => None
      end else None else None
  | _, _ => None
  end.

Lemma map_merge_pair_shape : forall r1 r2 f v1 v2 M1 M2 k,
  map_merge_pair r1 r2 = Some (f, v1, v2, M1, M2, k) ->
  r1 = orig_map_rule f v1 M1 k /\ r2 = orig_map_rule f v2 M2 k /\
  field_fixed_len f = Some (List.length v1) /\ field_fixed_len f = Some (List.length v2) /\
  data_eqb v1 v2 = false.
Proof.
  intros r1 r2 f v1 v2 M1 M2 k H. unfold map_merge_pair in H.
  destruct (is_orig_map r1) as [[[[f1 u1] N1] j1]|] eqn:H1; [|discriminate].
  destruct (is_orig_map r2) as [[[[f2 u2] N2] j2]|] eqn:H2; [|discriminate].
  destruct (field_eq_dec f1 f2) as [<-|]; [|discriminate].
  destruct (meta_eq_dec j1 j2) as [<-|]; [|discriminate].
  destruct (field_fixed_len f1) as [len|] eqn:Hfx; [|discriminate].
  destruct (Nat.eq_dec len (List.length u1)) as [->|]; [|discriminate].
  destruct (Nat.eq_dec (List.length u1) (List.length u2)) as [Hl|]; [|discriminate].
  destruct (data_eqb u1 u2) eqn:Hd; [discriminate|].
  injection H as -> -> -> -> -> ->.
  pose proof (is_orig_map_shape r1 f v1 M1 k H1) as Hr1.
  pose proof (is_orig_map_shape r2 f v2 M2 k H2) as Hr2.
  repeat split.
  - exact Hr1.
  - exact Hr2.
  - exact Hfx.
  - rewrite Hfx. f_equal. exact Hl.
  - exact Hd.
Qed.

Fixpoint optimize_rules_mapn (n : nat) (d : set_decls) (rs : list rule)
  : nat * set_decls * list rule :=
  match rs with
  | r1 :: ((r2 :: rest) as tl) =>
      match map_merge_pair r1 r2 with
      | Some (f, v1, v2, M1, M2, k) =>
          let d' := {| sd_sets := (setname n, map2_set v1 v2) :: sd_sets d;
                       sd_vmaps := sd_vmaps d;
                       sd_maps := (mapname n, map2_map v1 v2 M1 M2) :: sd_maps d |} in
          let merged := mk_map_rule f (setname n) (mapname n) k in
          let '(n'', d'', rest') := optimize_rules_mapn (S n) d' rest in
          (n'', d'', merged :: rest')
      | None =>
          let '(n'', d'', tl') := optimize_rules_mapn n d tl in
          (n'', d'', r1 :: tl')
      end
  | _ => (n, d, rs)
  end.

Lemma optimize_rules_mapn_cons2 : forall n d r1 r2 rest,
  optimize_rules_mapn n d (r1 :: r2 :: rest) =
  match map_merge_pair r1 r2 with
  | Some (f, v1, v2, M1, M2, k) =>
      let d' := {| sd_sets := (setname n, map2_set v1 v2) :: sd_sets d;
                   sd_vmaps := sd_vmaps d;
                   sd_maps := (mapname n, map2_map v1 v2 M1 M2) :: sd_maps d |} in
      let merged := mk_map_rule f (setname n) (mapname n) k in
      let '(n'', d'', rest') := optimize_rules_mapn (S n) d' rest in
      (n'', d'', merged :: rest')
  | None =>
      let '(n'', d'', tl') := optimize_rules_mapn n d (r2 :: rest) in
      (n'', d'', r1 :: tl')
  end.
Proof. reflexivity. Qed.

(** *** VERDICT correctness — ENV-INDEPENDENT (no decls / freshness hypothesis): the
    merged [Continue] rules fall through for any environment, so the rewrite never
    changes a verdict.  This is what composes into [optimize_table_uncond_correct]. *)
Theorem optimize_rules_mapn_eval : forall rs n d n' d' rs' e p,
  optimize_rules_mapn n d rs = (n', d', rs') ->
  eval_rules rs' e p = eval_rules rs e p.
Proof.
  induction rs as [rs IHrs] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' e p H.
  destruct rs as [| r1 [| r2 rest]].
  - cbn in H. inversion H; subst; reflexivity.
  - cbn in H. inversion H; subst; reflexivity.
  - rewrite optimize_rules_mapn_cons2 in H.
    destruct (map_merge_pair r1 r2) as [[[[[[f v1] v2] M1] M2] k]|] eqn:Em.
    + cbv zeta in H.
      destruct (map_merge_pair_shape r1 r2 f v1 v2 M1 M2 k Em) as [Hr1 [Hr2 _]].
      remember (optimize_rules_mapn (S n)
                  {| sd_sets := (setname n, map2_set v1 v2) :: sd_sets d;
                     sd_vmaps := sd_vmaps d;
                     sd_maps := (mapname n, map2_map v1 v2 M1 M2) :: sd_maps d |} rest)
        as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. injection H as Hn' Hd' Hr'. subst n' d' rs'.
      (* merged :: rr''  collapses to orig1 :: orig2 :: rr'' (verdict, any env) *)
      rewrite (eval_rules_map_merge f v1 v2 M1 M2 (setname n) (mapname n) k rr'' e p).
      rewrite Hr1, Hr2.   (* RHS r1 -> orig1, r2 -> orig2 *)
      (* strip the two Continue originals from both sides *)
      rewrite !(eval_rules_continue _ _ e p (outcome_orig_map_none _ _ _ _ _ _)).
      apply (IHrs rest ltac:(unfold ltof; cbn; lia) (S n) _ m'' dd'' rr'' e p (eq_sym Erec)).
    + remember (optimize_rules_mapn n d (r2 :: rest)) as t eqn:Erec.
      destruct t as [[m'' dd''] rr'']. injection H as Hn' Hd' Hr'. subst n' d' rs'.
      cbn [eval_rules].
      rewrite (IHrs (r2 :: rest) ltac:(unfold ltof; cbn; lia) n d m'' dd'' rr'' e p (eq_sym Erec)).
      reflexivity.
Qed.

(** *** Decls seam bookkeeping (mirrors concatK; mapn adds a [setname] to [sd_sets]
    and a [mapname] to [sd_maps], leaving [sd_vmaps] fixed). *)
Lemma optimize_rules_mapn_mono : forall rs n d n' d' rs',
  optimize_rules_mapn n d rs = (n', d', rs') -> n <= n'.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; lia.
  - cbn in H; inversion H; subst; lia.
  - rewrite optimize_rules_mapn_cons2 in H.
    destruct (map_merge_pair r1 r2) as [[[[[[f v1] v2] M1] M2] k]|]; cbv zeta in H.
    + remember (optimize_rules_mapn (S n)
                  {| sd_sets := (setname n, map2_set v1 v2) :: sd_sets d;
                     sd_vmaps := sd_vmaps d;
                     sd_maps := (mapname n, map2_map v1 v2 M1 M2) :: sd_maps d |} rest)
        as t eqn:E.
      destruct t as [[m'' dd''] rr'']. injection H as Hn _ _; subst.
      pose proof (IH rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E)). lia.
    + remember (optimize_rules_mapn n d (r2 :: rest)) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. injection H as Hn _ _; subst.
      exact (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E)).
Qed.

Lemma optimize_rules_mapn_vmaps : forall rs n d n' d' rs',
  optimize_rules_mapn n d rs = (n', d', rs') -> sd_vmaps d' = sd_vmaps d.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; reflexivity.
  - cbn in H; inversion H; subst; reflexivity.
  - rewrite optimize_rules_mapn_cons2 in H.
    destruct (map_merge_pair r1 r2) as [[[[[[f v1] v2] M1] M2] k]|]; cbv zeta in H.
    + remember (optimize_rules_mapn (S n)
                  {| sd_sets := (setname n, map2_set v1 v2) :: sd_sets d;
                     sd_vmaps := sd_vmaps d;
                     sd_maps := (mapname n, map2_map v1 v2 M1 M2) :: sd_maps d |} rest)
        as t eqn:E.
      destruct t as [[m'' dd''] rr'']. injection H as _ Hd _; subst.
      rewrite (IH rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E)). reflexivity.
    + remember (optimize_rules_mapn n d (r2 :: rest)) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. injection H as _ Hd _; subst.
      exact (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E)).
Qed.

Lemma optimize_rules_mapn_assoc_stable : forall rs n d n' d' rs' nm X,
  optimize_rules_mapn n d rs = (n', d', rs') ->
  (forall j, n <= j -> nm <> setname j) ->
  assoc_str nm (sd_sets d') X = assoc_str nm (sd_sets d) X.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' nm X H Hnm. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; reflexivity.
  - cbn in H; inversion H; subst; reflexivity.
  - rewrite optimize_rules_mapn_cons2 in H.
    destruct (map_merge_pair r1 r2) as [[[[[[f v1] v2] M1] M2] k]|]; cbv zeta in H.
    + remember (optimize_rules_mapn (S n)
                  {| sd_sets := (setname n, map2_set v1 v2) :: sd_sets d;
                     sd_vmaps := sd_vmaps d;
                     sd_maps := (mapname n, map2_map v1 v2 M1 M2) :: sd_maps d |} rest)
        as t eqn:E.
      destruct t as [[m'' dd''] rr'']. injection H as _ Hd _; subst d'.
      erewrite (IH rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ nm X (eq_sym E)
                  ltac:(intros j Hj; apply Hnm; lia)).
      cbn [sd_sets assoc_str].
      destruct (String.eqb nm (setname n)) eqn:Eq.
      * apply String.eqb_eq in Eq. exfalso. apply (Hnm n); [lia | exact Eq].
      * reflexivity.
    + remember (optimize_rules_mapn n d (r2 :: rest)) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. injection H as _ Hd _; subst d'.
      exact (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ nm X (eq_sym E) Hnm).
Qed.

(** The synthesised DATA-MAP names are [mapname k] for [k >= n]; any OTHER name's
    [sd_maps] lookup is stable across the pass (mirrors [_assoc_stable] for sets). *)
Lemma optimize_rules_mapn_maps_assoc_stable : forall rs n d n' d' rs' nm X,
  optimize_rules_mapn n d rs = (n', d', rs') ->
  (forall j, n <= j -> nm <> mapname j) ->
  assoc_str nm (sd_maps d') X = assoc_str nm (sd_maps d) X.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' nm X H Hnm. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; reflexivity.
  - cbn in H; inversion H; subst; reflexivity.
  - rewrite optimize_rules_mapn_cons2 in H.
    destruct (map_merge_pair r1 r2) as [[[[[[f v1] v2] M1] M2] k]|]; cbv zeta in H.
    + remember (optimize_rules_mapn (S n)
                  {| sd_sets := (setname n, map2_set v1 v2) :: sd_sets d;
                     sd_vmaps := sd_vmaps d;
                     sd_maps := (mapname n, map2_map v1 v2 M1 M2) :: sd_maps d |} rest)
        as t eqn:E.
      destruct t as [[m'' dd''] rr'']. injection H as _ Hd _; subst d'.
      erewrite (IH rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ nm X (eq_sym E)
                  ltac:(intros j Hj; apply Hnm; lia)).
      cbn [sd_maps assoc_str].
      destruct (String.eqb nm (mapname n)) eqn:Eq.
      * apply String.eqb_eq in Eq. exfalso. apply (Hnm n); [lia | exact Eq].
      * reflexivity.
    + remember (optimize_rules_mapn n d (r2 :: rest)) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. injection H as _ Hd _; subst d'.
      exact (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ nm X (eq_sym E) Hnm).
Qed.

Lemma optimize_rules_mapn_keys_bound : forall rs n d n' d' rs' j,
  optimize_rules_mapn n d rs = (n', d', rs') ->
  In (setname j) (map fst (sd_sets d')) ->
  In (setname j) (map fst (sd_sets d)) \/ j < n'.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' j H Hin. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; left; exact Hin.
  - cbn in H; inversion H; subst; left; exact Hin.
  - rewrite optimize_rules_mapn_cons2 in H.
    destruct (map_merge_pair r1 r2) as [[[[[[f v1] v2] M1] M2] k]|]; cbv zeta in H.
    + remember (optimize_rules_mapn (S n)
                  {| sd_sets := (setname n, map2_set v1 v2) :: sd_sets d;
                     sd_vmaps := sd_vmaps d;
                     sd_maps := (mapname n, map2_map v1 v2 M1 M2) :: sd_maps d |} rest)
        as t eqn:E.
      destruct t as [[m'' dd''] rr'']. injection H as Hn Hd Hr; subst.
      destruct (IH rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ j (eq_sym E) Hin) as [Hd0|Hlt].
      * cbn [sd_sets map] in Hd0. destruct Hd0 as [Heq|Hd0].
        -- apply setname_inj in Heq. subst j. right.
           pose proof (optimize_rules_mapn_mono rest (S n) _ _ _ _ (eq_sym E)). lia.
        -- left; exact Hd0.
      * right; exact Hlt.
    + remember (optimize_rules_mapn n d (r2 :: rest)) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. injection H as Hn Hd Hr; subst.
      exact (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ j (eq_sym E) Hin).
Qed.

Definition optimize_chain_mapn (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n', d', rs') := optimize_rules_mapn n d (c_rules c) in
  (n', d', {| c_policy := c_policy c; c_rules := rs' |}).

Lemma optimize_chain_mapn_mono : forall n d c n' d' c',
  optimize_chain_mapn n d c = (n', d', c') -> n <= n'.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_mapn in H.
  destruct (optimize_rules_mapn n d (c_rules c)) as [[m d0] r0] eqn:E.
  inversion H; subst. exact (optimize_rules_mapn_mono _ _ _ _ _ _ E).
Qed.
Lemma optimize_chain_mapn_vmaps : forall n d c n' d' c',
  optimize_chain_mapn n d c = (n', d', c') -> sd_vmaps d' = sd_vmaps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_mapn in H.
  destruct (optimize_rules_mapn n d (c_rules c)) as [[m d0] r0] eqn:E.
  inversion H; subst. exact (optimize_rules_mapn_vmaps _ _ _ _ _ _ E).
Qed.
Lemma optimize_chain_mapn_keys_bound : forall n d c n' d' c' j,
  optimize_chain_mapn n d c = (n', d', c') ->
  In (setname j) (map fst (sd_sets d')) ->
  In (setname j) (map fst (sd_sets d)) \/ j < n'.
Proof.
  intros n d c n' d' c' j H Hin. unfold optimize_chain_mapn in H.
  destruct (optimize_rules_mapn n d (c_rules c)) as [[m d0] r0] eqn:E.
  inversion H; subst. exact (optimize_rules_mapn_keys_bound _ _ _ _ _ _ j E Hin).
Qed.

(** Axiom-freedom guards. *)
Print Assumptions dsl_step_map_merge.
Print Assumptions eval_rules_mut_map_merge.
Print Assumptions eval_rules_map_merge.
Print Assumptions optimize_rules_mapn_eval.
