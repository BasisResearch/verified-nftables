(** * Optimize_Dnat: the BARE dnat/snat value-map merge (TODO 1a Phase 3).

    [nft -o] folds adjacent rules whose only difference is a NAT TARGET into a
    map keyed by a match, emitting the BARE map with NO head-set guard:

      ip daddr A dnat to T1
      ip daddr B dnat to T2   =>   dnat to ip daddr map { A : T1, B : T2 }

    Unlike the meta-mark [mapN] pass ([Optimize_Mapn.v]), which keeps a head-set
    guard so its statement-map lookup always hits, this pass relies on Phase 1's
    NFT_BREAK-on-map-miss ([ILookupValBr] / [terminal_loadable]'s [map_has_key]):
    a packet whose key is NOT in the map makes the merged rule's [rule_loadable]
    FALSE, so [eval_rules] skips it and falls through — exactly as the two
    original rules fall through when neither head match fires.

    This file proves the per-merge VERDICT correctness over [eval_rules]
    ([eval_rules_dnat_merge]); the meaningfulness rests on the break (a packet
    off the key set must fall through, not accept). *)

From Stdlib Require Import List Bool Arith Lia String.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Optimize Optimize_Merge.

Local Open Scope nat_scope.

(** A dnat NAT spec to an immediate target [T]. *)
Definition dnat_imm_spec (T : data) : nat_spec :=
  {| nat_addr_imm := Some T; nat_field := None; nat_map := None; nat_src := None;
     nat_extra := NXnone; nat_kind := nat_dnat_kind; nat_family := nat_fam_ip4;
     nat_flags := 0 |}.

(** A dnat NAT spec whose target comes from a data MAP keyed by [f]. *)
Definition dnat_map_spec (f : field) (mapname : string) : nat_spec :=
  {| nat_addr_imm := None; nat_field := None; nat_map := Some ([f], [], mapname);
     nat_src := None; nat_extra := NXnone; nat_kind := nat_dnat_kind;
     nat_family := nat_fam_ip4; nat_flags := 0 |}.

(** An ORIGINAL rule: `<field> = v  dnat to T` (terminal accept). *)
Definition orig_dnat_rule (f : field) (v T : data) : rule :=
  {| r_body := [BMatch (MCmp f CEq v)]; r_verdict := Continue; r_vmap := None;
     r_nat := Some (dnat_imm_spec T); r_tproxy := None; r_fwd := None;
     r_queue := None; r_after := [] |}.

(** The MERGED rule: `dnat to <field> map @mapname` — BARE, no head guard. *)
Definition mk_dnat_rule (f : field) (mapname : string) : rule :=
  {| r_body := []; r_verdict := Continue; r_vmap := None;
     r_nat := Some (dnat_map_spec f mapname); r_tproxy := None; r_fwd := None;
     r_queue := None; r_after := [] |}.

(** The 2-entry data map the merge synthesises. *)
Definition dmap2 (v1 v2 T1 T2 : data) : list (data * data) := [(v1, T1); (v2, T2)].

(** *** The key of the merged operand is exactly the field value (single field,
    no transforms). *)
Lemma nat_map_key_single : forall f p,
  nat_map_key [f] [] p = field_value f p.
Proof.
  intros f p. unfold nat_map_key. cbn [apply_transforms map List.concat].
  rewrite app_nil_r. reflexivity.
Qed.

(** *** [outcome] of either rule is [Some Accept] (a NAT terminal), with no
    synproxy/vmap to intervene. *)
Lemma outcome_orig_dnat : forall f v T p, outcome (orig_dnat_rule f v T) p = Some Accept.
Proof.
  intros f v T p. unfold outcome, orig_dnat_rule.
  cbn [body_synproxy_stops r_body body_matches].
  unfold outcome_core. cbn [r_vmap r_nat]. reflexivity.
Qed.

Lemma outcome_mk_dnat : forall f mapname p, outcome (mk_dnat_rule f mapname) p = Some Accept.
Proof. intros. reflexivity. Qed.

(** *** [rule_applies] of the original rule is the head [MCmp] eval; the merged
    rule (empty body) always applies. *)
Lemma applies_orig_dnat : forall f v T p,
  rule_applies (orig_dnat_rule f v T) p = eval_matchcond (MCmp f CEq v) p.
Proof.
  intros f v T p. unfold rule_applies, orig_dnat_rule.
  cbn [r_body rule_applies_walk body_matches]. apply andb_true_r.
Qed.

Lemma applies_mk_dnat : forall f mapname p, rule_applies (mk_dnat_rule f mapname) p = true.
Proof. reflexivity. Qed.

(** *** [rule_loadable] of the original rule = the head field loads (its terminal
    is an immediate, always loadable). *)
Lemma loadable_orig_dnat : forall f v T p,
  rule_loadable (orig_dnat_rule f v T) p = field_loadable f p.
Proof.
  intros f v T p. unfold rule_loadable, orig_dnat_rule, end_loadable, tail_loadable.
  cbn [r_body body_loadable_walk body_item_loadable body_synproxy_stops body_thread
       r_after r_vmap terminal_loadable terminal_outcome r_nat r_tproxy r_fwd r_queue
       nat_src nat_map nat_field dnat_imm_spec forallb].
  unfold match_loadable. rewrite !andb_true_r. reflexivity.
Qed.

(** *** [rule_loadable] of the merged rule = the field loads AND its value is a
    KEY of the map (else the terminal data-map lookup BREAKs — NFT_BREAK). *)
Lemma loadable_mk_dnat : forall f mapname p,
  rule_loadable (mk_dnat_rule f mapname) p
  = field_loadable f p && map_has_key (field_value f p) (e_map (pkt_env p) mapname).
Proof.
  intros f mapname p.
  unfold rule_loadable, mk_dnat_rule, end_loadable, tail_loadable, terminal_loadable,
    terminal_outcome, dnat_map_spec.
  cbn [r_body r_vmap r_nat r_tproxy r_fwd r_queue r_after body_loadable_walk
       body_synproxy_stops body_thread nat_src nat_map fields_loadable forallb].
  rewrite nat_map_key_single. rewrite !andb_true_r, !andb_true_l. reflexivity.
Qed.

(** *** Map membership of the 2-entry map is the disjunction of the two keys. *)
Lemma map_has_key_dmap2 : forall fv v1 v2 T1 T2,
  map_has_key fv (dmap2 v1 v2 T1 T2) = (data_eqb fv v1 || data_eqb fv v2).
Proof.
  intros. unfold dmap2. cbn [map_has_key].
  destruct (data_eqb fv v1); [reflexivity|].
  destruct (data_eqb fv v2); reflexivity.
Qed.

(** *** THE per-merge VERDICT correctness: the bare merged map rule accepts
    EXACTLY the packets the two originals accept, and falls through on the rest —
    the break-on-miss ([loadable_mk_dnat]'s [map_has_key]) is what makes the
    head-guard-free map sound. *)
Theorem eval_rules_dnat_merge : forall (f : field) (v1 v2 T1 T2 : data)
    (mapname : string) (rest : list rule) (p : packet),
  e_map (pkt_env p) mapname = dmap2 v1 v2 T1 T2 ->
  field_fixed_len f = Some (List.length v1) ->
  field_fixed_len f = Some (List.length v2) ->
  eval_rules (mk_dnat_rule f mapname :: rest) p
  = eval_rules (orig_dnat_rule f v1 T1 :: orig_dnat_rule f v2 T2 :: rest) p.
Proof.
  intros f v1 v2 T1 T2 mapname rest p Hmap Hfx1 Hfx2.
  cbn [eval_rules].
  rewrite loadable_mk_dnat, applies_mk_dnat, outcome_mk_dnat.
  rewrite loadable_orig_dnat, applies_orig_dnat, outcome_orig_dnat.
  rewrite loadable_orig_dnat, applies_orig_dnat, outcome_orig_dnat.
  rewrite Hmap, map_has_key_dmap2.
  destruct (field_loadable f p) eqn:Hld.
  - (* field loads: relate the head MCmp matches to the data_eqb disjunction *)
    rewrite (eval_mcmp_point f v1 p Hld (field_fixed_len_loaded f (List.length v1) p Hfx1 Hld)).
    rewrite (eval_mcmp_point f v2 p Hld (field_fixed_len_loaded f (List.length v2) p Hfx2 Hld)).
    rewrite (data_eqb_sym (field_value f p) v1), (data_eqb_sym (field_value f p) v2).
    cbn [andb terminal].
    destruct (data_eqb v1 (field_value f p)); cbn [orb];
      destruct (data_eqb v2 (field_value f p)); reflexivity.
  - (* field does not load: every rule BREAKs (rule_loadable false) -> fall through *)
    cbn [andb]. reflexivity.
Qed.
