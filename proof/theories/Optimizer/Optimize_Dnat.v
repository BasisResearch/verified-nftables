(** * Optimize_Dnat: the BARE dnat/snat value-map merge (TODO 1a Phase 3).

    [nft -o] folds adjacent rules whose only difference is a NAT TARGET into a
    map keyed by a match, emitting the BARE map with NO head-set guard:

      ip daddr A dnat to T1
      ip daddr B dnat to T2   =>   dnat to ip daddr map { A : T1, B : T2 }

    Unlike the meta-mark [mapN] pass ([Optimize_DataMap.v]), which keeps a head-set
    guard so its statement-map lookup always hits, this pass relies on Phase 1's
    NFT_BREAK-on-map-miss ([ILookupValBr] / [terminal_loadable]'s [map_has_key]):
    a packet whose key is NOT in the map makes the merged rule's [rule_loadable]
    FALSE, so the state fold skips it and falls through — exactly as the two
    original rules fall through when neither head match fires.

    The break is what makes the head-guard-free map sound: a packet off the key
    set must fall through, not accept. *)

From Stdlib Require Import List Bool Arith Lia String.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Optimize Optimize_ValueSet Optimize_Vmap Optimize_DataMap.

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

(** An ORIGINAL rule: `<field> = v  dnat to T` (terminal accept).  The [r_verdict]
    is [Accept] to match the frontend's lowering of a bare `dnat` statement
    ([nft_lower]'s [stmt_is_terminal_accept]) so the recogniser FIRES on parsed
    rulesets; the NAT is terminal regardless (a set [r_nat] yields [Some Accept]),
    so the merge is verdict-preserving. *)
Definition orig_dnat_rule (f : field) (v T : data) : rule :=
  {| r_body := [BMatch (MCmp f CEq v)];
     r_outcome := ONat (dnat_imm_spec T); r_after := [] |}.

(** The MERGED rule: `dnat to <field> map @mapname` — BARE, no head guard. *)
Definition mk_dnat_rule (f : field) (mapname : string) : rule :=
  {| r_body := [];
     r_outcome := ONat (dnat_map_spec f mapname); r_after := [] |}.

(** The 2-entry data map the merge synthesises. *)
Definition dmap2 (v1 v2 T1 T2 : data) : list (data * data) := [(v1, T1); (v2, T2)].

(** *** The key of the merged operand is exactly the field value (single field,
    no transforms). *)
Lemma nat_map_key_single : forall f e p,
  nat_map_key [f] [] e p = field_value f e p.
Proof.
  intros f e p. unfold nat_map_key. cbn [apply_transforms map List.concat].
  rewrite app_nil_r. reflexivity.
Qed.

(** *** Map membership of the 2-entry map is the disjunction of the two keys. *)
Lemma map_has_key_dmap2 : forall fv v1 v2 T1 T2,
  map_has_key fv (dmap2 v1 v2 T1 T2) = (data_eqb fv v1 || data_eqb fv v2).
Proof.
  intros. unfold dmap2. cbn [map_has_key].
  destruct (data_eqb fv v1); [reflexivity|].
  destruct (data_eqb fv v2); reflexivity.
Qed.

(** ** The NON-VACUOUS data-plane correctness: the bare merged map rule applies
    the SAME NAT translation as a `dnat to T` rule whose target [T] is the map
    value at the packet's key — i.e. the synthesised map rewrites to exactly the
    right address (not just "some accept"). *)

(** [apply_nat_tuple] / [nat_orig_addr] read the spec ONLY through its address
    family and src/dst-ness, so two specs agreeing there have the same effect. *)
Lemma nat_addrfamily_pkt_ext : forall ns1 ns2 p,
  nat_addrfamily ns1 = nat_addrfamily ns2 ->
  nat_addrfamily_pkt ns1 p = nat_addrfamily_pkt ns2 p.
Proof.
  intros ns1 ns2 p Hf. unfold nat_addrfamily in Hf.
  unfold nat_addrfamily_pkt, nat_af_pkt. rewrite Hf. reflexivity.
Qed.

Lemma apply_nat_tuple_indep : forall ns1 ns2 p m,
  nat_addrfamily ns1 = nat_addrfamily ns2 ->
  nat_is_src ns1 = nat_is_src ns2 ->
  apply_nat_tuple ns1 p m = apply_nat_tuple ns2 p m.
Proof.
  intros ns1 ns2 p m Hf Hs. unfold apply_nat_tuple.
  rewrite (nat_addrfamily_pkt_ext ns1 ns2 p Hf), Hs. reflexivity.
Qed.

Lemma nat_orig_addr_indep : forall ns1 ns2 p,
  nat_addrfamily ns1 = nat_addrfamily ns2 ->
  nat_is_src ns1 = nat_is_src ns2 ->
  nat_orig_addr ns1 p = nat_orig_addr ns2 p.
Proof.
  intros ns1 ns2 p Hf Hs. unfold nat_orig_addr.
  rewrite (nat_addrfamily_pkt_ext ns1 ns2 p Hf), Hs. reflexivity.
Qed.

(** The merged operand resolves to the map value at the key. *)
Lemma nat_operand_addr_dnat_eq : forall h f m T e p,
  map_lookup_data (field_value f e p) (e_map e m) = T ->
  nat_operand_addr h (dnat_map_spec f m) e p = nat_operand_addr h (dnat_imm_spec T) e p.
Proof.
  intros h f m T e p Hlk.
  unfold nat_operand_addr, nat_new_addr, nat_opnd, nat_portonly, nat_has_addr, nat_addr.
  cbn [nat_kind nat_src nat_map nat_field nat_addr_imm dnat_map_spec dnat_imm_spec].
  rewrite nat_map_key_single, Hlk. reflexivity.
Qed.

(** THE data-plane merge: the bare map rule's NAT effect equals that of a
    `dnat to <map value at the key>` rule — at EVERY hook and flow state. *)
Theorem apply_nat_dnat_eq : forall h f m T e p,
  map_lookup_data (field_value f e p) (e_map e m) = T ->
  apply_nat h (mk_dnat_rule f m) e p = apply_nat h (orig_dnat_rule f [] T) e p.
Proof.
  intros h f m T e p Hlk.
  unfold apply_nat, mk_dnat_rule, orig_dnat_rule. cbn [r_nat r_outcome].
  destruct (e_nat e (pkt_flow p)) as [mm |].
  - f_equal.
  - destruct (pkt_ctdir_orig p); [| reflexivity].
    rewrite (nat_orig_addr_indep (dnat_map_spec f m) (dnat_imm_spec T) p eq_refl eq_refl).
    rewrite (nat_operand_addr_dnat_eq h f m T e p Hlk).
    cbn [nat_port_num nat_orig_port nat_extra dnat_map_spec dnat_imm_spec].
    rewrite (apply_nat_tuple_indep (dnat_map_spec f m) (dnat_imm_spec T) p _ eq_refl eq_refl).
    reflexivity.
Qed.

(** Specialised to the two-key map: hitting key [v1] applies [T1]; key [v2]
    (distinct) applies [T2] — the merged rule's translation matches whichever
    original would have fired. *)
Corollary apply_nat_dnat_merge1 : forall h f v1 v2 T1 T2 m e p,
  e_map e m = dmap2 v1 v2 T1 T2 ->
  data_eqb (field_value f e p) v1 = true ->
  apply_nat h (mk_dnat_rule f m) e p = apply_nat h (orig_dnat_rule f v1 T1) e p.
Proof.
  intros h f v1 v2 T1 T2 m e p Hmap Hv1.
  transitivity (apply_nat h (orig_dnat_rule f [] T1) e p).
  - apply apply_nat_dnat_eq.
    rewrite Hmap. unfold dmap2. cbn [map_lookup_data]. rewrite Hv1. reflexivity.
  - unfold apply_nat, orig_dnat_rule. cbn [r_nat r_outcome]. reflexivity.
Qed.

(* ================================================================== *)
(** ** The executable pairwise pass. *)

(** Extract the head field/value and dnat target of a rule shaped EXACTLY like
    `<f> = v  dnat to T` (an [orig_dnat_rule]).  Constructor matches only — no
    monolithic [rule_eq_dec] (cf. [Optimize_DataMap.is_orig_map]). *)
Definition orig_dnat_data (r : rule) : option (field * data * data) :=
  match r_body r, r_outcome r with
  | [BMatch (MCmp f CEq v)], ONat ns =>
      match nat_src ns, nat_map ns, nat_field ns, nat_addr_imm ns, nat_extra ns with
      | None, None, None, Some T, NXnone =>
          if natop_eqb (nat_kind ns) nat_dnat_kind then
          if nataf_eqb (nat_family ns) nat_fam_ip4 then
          match nat_flags ns with O => Some (f, v, T) | _ => None end
          else None else None
      | _, _, _, _, _ => None
      end
  | _, _ => None
  end.

Lemma orig_dnat_data_shape : forall r f v T,
  orig_dnat_data r = Some (f, v, T) ->
  r_body r = [BMatch (MCmp f CEq v)] /\ r_outcome r = ONat (dnat_imm_spec T).
Proof.
  intros [body outc aft] f v T H. unfold orig_dnat_data in H.
  cbn [r_body r_nat r_outcome] in H.
  destruct body as [| it tl]; try discriminate H.
  destruct it as [m|s]; [|discriminate H].
  destruct m as [ b1 b2 | b1 b2 | b1 b2 b3 b4 | b1 b2 b3 b4 b5 | f1 op v1
                | b1 b2 b3 | b1 b2 b3 b4 | b1 b2 b3 b4 | b1 b2 b3 b4 b5
                | b1 | b1 | b1 | b1 b2 b3 ]; try discriminate H.
  destruct op; try discriminate H.
  destruct tl as [| x l]; try discriminate H.
  destruct outc as [vv| |vm|vm2 ns2|ns|tp|fw|qq]; try discriminate H.
  destruct ns as [aimm afld amap asrc aext aknd afam afl].
  cbn [nat_addr_imm nat_field nat_map nat_src nat_extra nat_kind nat_family nat_flags] in H.
  destruct asrc; try discriminate H.
  destruct amap; try discriminate H.
  destruct afld; try discriminate H.
  destruct aimm as [T0|]; [|discriminate H].
  destruct aext; try discriminate H.
  destruct aknd; cbn in H; try discriminate H.
  destruct afam; cbn in H; try discriminate H.
  destruct afl; [|discriminate H].
  injection H as -> -> ->. cbn [r_body r_nat r_outcome]. split; reflexivity.
Qed.

(** Recognise a rule as EXACTLY the original `dnat to <imm>` shell. *)
Definition is_orig_dnat (r : rule) : option (field * data * data) :=
  match orig_dnat_data r, r_after r with
  | Some (f, v, T), [] => Some (f, v, T)
  | _, _ => None
  end.

Lemma is_orig_dnat_shape : forall r f v T,
  is_orig_dnat r = Some (f, v, T) -> r = orig_dnat_rule f v T.
Proof.
  intros r f v T H. unfold is_orig_dnat in H.
  destruct (orig_dnat_data r) as [[[f0 v0] T0]|] eqn:Hd; [|discriminate H].
  destruct (r_after r) eqn:Haft; try discriminate H.
  injection H as -> -> ->.
  pose proof (orig_dnat_data_shape r f v T Hd) as [Hbody Hout].
  destruct r as [body outc aft]; cbn in *.
  subst. reflexivity.
Qed.

(** Two rules form an eligible BARE-map dnat merge: both `dnat to <imm>` shells
    over the SAME fixed-width field, with DISTINCT key values. *)
Definition dnat_merge_pair (r1 r2 : rule)
  : option (field * data * data * data * data) :=
  match is_orig_dnat r1, is_orig_dnat r2 with
  | Some (f1, v1, T1), Some (f2, v2, T2) =>
      if field_eq_dec f1 f2 then
      match field_fixed_len f1 with
      | Some len =>
          if Nat.eq_dec len (List.length v1) then if Nat.eq_dec len (List.length v2) then
          if data_eqb v1 v2 then None else Some (f1, v1, v2, T1, T2)
          else None else None
      | None => None
      end else None
  | _, _ => None
  end.

Lemma dnat_merge_pair_shape : forall r1 r2 f v1 v2 T1 T2,
  dnat_merge_pair r1 r2 = Some (f, v1, v2, T1, T2) ->
  r1 = orig_dnat_rule f v1 T1 /\ r2 = orig_dnat_rule f v2 T2 /\
  field_fixed_len f = Some (List.length v1) /\ field_fixed_len f = Some (List.length v2) /\
  data_eqb v1 v2 = false.
Proof.
  intros r1 r2 f v1 v2 T1 T2 H. unfold dnat_merge_pair in H.
  destruct (is_orig_dnat r1) as [[[f1 u1] N1]|] eqn:H1; [|discriminate].
  destruct (is_orig_dnat r2) as [[[f2 u2] N2]|] eqn:H2; [|discriminate].
  destruct (field_eq_dec f1 f2) as [<-|]; [|discriminate].
  destruct (field_fixed_len f1) as [len|] eqn:Hfx; [|discriminate].
  destruct (Nat.eq_dec len (List.length u1)) as [->|]; [|discriminate].
  destruct (Nat.eq_dec (List.length u1) (List.length u2)) as [Hl|]; [|discriminate].
  destruct (data_eqb u1 u2) eqn:Hd; [discriminate|].
  injection H as -> -> -> -> ->.
  pose proof (is_orig_dnat_shape r1 f v1 T1 H1) as Hr1.
  pose proof (is_orig_dnat_shape r2 f v2 T2 H2) as Hr2.
  repeat split; [exact Hr1 | exact Hr2 | exact Hfx | rewrite Hfx; f_equal; exact Hl | exact Hd].
Qed.

(** The pass: fold each adjacent eligible pair into ONE bare map rule, minting a
    fresh [mapname] (NO [setname] — the bare map needs no head guard). *)
Fixpoint optimize_rules_dnat (n : nat) (d : set_decls) (rs : list rule)
  : nat * set_decls * list rule :=
  match rs with
  | r1 :: ((r2 :: rest) as tl) =>
      match dnat_merge_pair r1 r2 with
      | Some (f, v1, v2, T1, T2) =>
          let d' := {| sd_sets := sd_sets d; sd_vmaps := sd_vmaps d;
                       sd_maps := (mapname n, dmap2 v1 v2 T1 T2) :: sd_maps d |} in
          let merged := mk_dnat_rule f (mapname n) in
          let '(n'', d'', rest') := optimize_rules_dnat (S n) d' rest in
          (n'', d'', merged :: rest')
      | None =>
          let '(n'', d'', tl') := optimize_rules_dnat n d tl in
          (n'', d'', r1 :: tl')
      end
  | _ => (n, d, rs)
  end.

Lemma optimize_rules_dnat_cons2 : forall n d r1 r2 rest,
  optimize_rules_dnat n d (r1 :: r2 :: rest) =
  match dnat_merge_pair r1 r2 with
  | Some (f, v1, v2, T1, T2) =>
      let d' := {| sd_sets := sd_sets d; sd_vmaps := sd_vmaps d;
                   sd_maps := (mapname n, dmap2 v1 v2 T1 T2) :: sd_maps d |} in
      let merged := mk_dnat_rule f (mapname n) in
      let '(n'', d'', rest') := optimize_rules_dnat (S n) d' rest in
      (n'', d'', merged :: rest')
  | None =>
      let '(n'', d'', tl') := optimize_rules_dnat n d (r2 :: rest) in
      (n'', d'', r1 :: tl')
  end.
Proof. reflexivity. Qed.

(** *** Structural invariants: the pass leaves [sd_sets]/[sd_vmaps] untouched and
    its counter is monotone. *)
Lemma optimize_rules_dnat_sets : forall rs n d n' d' rs',
  optimize_rules_dnat n d rs = (n', d', rs') -> sd_sets d' = sd_sets d.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; reflexivity.
  - cbn in H; inversion H; subst; reflexivity.
  - rewrite optimize_rules_dnat_cons2 in H.
    destruct (dnat_merge_pair r1 r2) as [[[[[f v1] v2] T1] T2]|]; cbv zeta in H.
    + remember (optimize_rules_dnat (S n) _ rest) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst.
      exact (IH rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E)).
    + remember (optimize_rules_dnat n d (r2 :: rest)) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst.
      exact (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E)).
Qed.

Lemma optimize_rules_dnat_vmaps : forall rs n d n' d' rs',
  optimize_rules_dnat n d rs = (n', d', rs') -> sd_vmaps d' = sd_vmaps d.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; reflexivity.
  - cbn in H; inversion H; subst; reflexivity.
  - rewrite optimize_rules_dnat_cons2 in H.
    destruct (dnat_merge_pair r1 r2) as [[[[[f v1] v2] T1] T2]|]; cbv zeta in H.
    + remember (optimize_rules_dnat (S n) _ rest) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst.
      exact (IH rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E)).
    + remember (optimize_rules_dnat n d (r2 :: rest)) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst.
      exact (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E)).
Qed.

Lemma optimize_rules_dnat_mono : forall rs n d n' d' rs',
  optimize_rules_dnat n d rs = (n', d', rs') -> n <= n'.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' H. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; lia.
  - cbn in H; inversion H; subst; lia.
  - rewrite optimize_rules_dnat_cons2 in H.
    destruct (dnat_merge_pair r1 r2) as [[[[[f v1] v2] T1] T2]|]; cbv zeta in H.
    + remember (optimize_rules_dnat (S n) _ rest) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst.
      pose proof (IH rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E)). lia.
    + remember (optimize_rules_dnat n d (r2 :: rest)) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst.
      exact (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ (eq_sym E)).
Qed.

(** The synthesised data-map names are [mapname k] for [k >= n]; any OTHER name's
    [sd_maps] lookup is stable across the pass. *)
Lemma optimize_rules_dnat_maps_assoc_stable : forall rs n d n' d' rs' nm X,
  optimize_rules_dnat n d rs = (n', d', rs') ->
  (forall j, n <= j -> nm <> mapname j) ->
  assoc_str nm (sd_maps d') X = assoc_str nm (sd_maps d) X.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' nm X H Hnm. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; reflexivity.
  - cbn in H; inversion H; subst; reflexivity.
  - rewrite optimize_rules_dnat_cons2 in H.
    destruct (dnat_merge_pair r1 r2) as [[[[[f v1] v2] T1] T2]|]; cbv zeta in H.
    + remember (optimize_rules_dnat (S n)
                  {| sd_sets := sd_sets d; sd_vmaps := sd_vmaps d;
                     sd_maps := (mapname n, dmap2 v1 v2 T1 T2) :: sd_maps d |} rest)
        as t eqn:E.
      destruct t as [[m'' dd''] rr'']. injection H as _ Hd _; subst d'.
      erewrite (IH rest ltac:(unfold ltof; cbn; lia) _ _ _ _ _ nm X (eq_sym E)
                  ltac:(intros j Hj; apply Hnm; lia)).
      cbn [sd_maps assoc_str].
      destruct (String.eqb nm (mapname n)) eqn:Eq.
      * apply String.eqb_eq in Eq. exfalso. apply (Hnm n); [lia | exact Eq].
      * reflexivity.
    + remember (optimize_rules_dnat n d (r2 :: rest)) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. injection H as _ Hd _; subst d'.
      exact (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) _ _ _ _ _ nm X (eq_sym E) Hnm).
Qed.

(** ** The chain wrapper. *)
Definition optimize_chain_dnat (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n', d', rs') := optimize_rules_dnat n d (c_rules c) in
  (n', d', {| c_policy := c_policy c; c_rules := rs' |}).

Lemma optimize_chain_dnat_mono : forall n d c n' d' c',
  optimize_chain_dnat n d c = (n', d', c') -> n <= n'.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_dnat in H.
  destruct (optimize_rules_dnat n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_dnat_mono _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_dnat_sets : forall n d c n' d' c',
  optimize_chain_dnat n d c = (n', d', c') -> sd_sets d' = sd_sets d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_dnat in H.
  destruct (optimize_rules_dnat n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_dnat_sets _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_dnat_vmaps : forall n d c n' d' c',
  optimize_chain_dnat n d c = (n', d', c') -> sd_vmaps d' = sd_vmaps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_dnat in H.
  destruct (optimize_rules_dnat n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_dnat_vmaps _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_dnat_maps_assoc_stable : forall n d c n' d' c' nm X,
  optimize_chain_dnat n d c = (n', d', c') ->
  (forall j, n <= j -> nm <> mapname j) ->
  assoc_str nm (sd_maps d') X = assoc_str nm (sd_maps d) X.
Proof.
  intros n d c n' d' c' nm X H Hnm. unfold optimize_chain_dnat in H.
  destruct (optimize_rules_dnat n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst.
  apply (optimize_rules_dnat_maps_assoc_stable _ _ _ _ _ _ nm X E Hnm).
Qed.

(** *** [sd_maps]-DECLARATION freshness threading: every minted [mapname] lies below
    the output counter [n'], so an [n]-fresh mapname namespace stays [n']-fresh in the
    output decls.  (This lets a LATER nat-map-minting pass — the [snat] stage — mint
    disjoint mapnames on top of the [dnat] stage's output.) *)
Lemma optimize_rules_dnat_maps_bound : forall rs n d n' d' rs' k,
  optimize_rules_dnat n d rs = (n', d', rs') ->
  In (mapname k) (map fst (sd_maps d')) ->
  In (mapname k) (map fst (sd_maps d)) \/ k < n'.
Proof.
  induction rs as [rs IH] using (induction_ltof1 _ (@List.length rule)).
  intros n d n' d' rs' k H Hin. destruct rs as [| r1 [| r2 rest]].
  - cbn in H; inversion H; subst; left; exact Hin.
  - cbn in H; inversion H; subst; left; exact Hin.
  - rewrite optimize_rules_dnat_cons2 in H.
    destruct (dnat_merge_pair r1 r2) as [[[[[f v1] v2] T1] T2]|]; cbv zeta in H.
    + remember (optimize_rules_dnat (S n)
                  {| sd_sets := sd_sets d; sd_vmaps := sd_vmaps d;
                     sd_maps := (mapname n, dmap2 v1 v2 T1 T2) :: sd_maps d |} rest)
        as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst n' d' rs'. clear H.
      destruct (IH rest ltac:(unfold ltof; cbn; lia) (S n) _ m'' dd'' rr'' k (eq_sym E) Hin)
        as [Hin' | Hlt].
      * cbn [sd_maps map fst] in Hin'. destruct Hin' as [Heq | Hin_d].
        -- apply mapname_inj in Heq. subst k. right.
           pose proof (optimize_rules_dnat_mono rest (S n) _ _ _ _ (eq_sym E)) as Hmono. lia.
        -- left; exact Hin_d.
      * right; exact Hlt.
    + remember (optimize_rules_dnat n d (r2 :: rest)) as t eqn:E.
      destruct t as [[m'' dd''] rr'']. inversion H; subst n' d' rs'. clear H.
      apply (IH (r2 :: rest) ltac:(unfold ltof; cbn; lia) n d m'' dd'' rr'' k (eq_sym E) Hin).
Qed.

Lemma optimize_chain_dnat_fresh_mapname : forall n d c n' d' c',
  optimize_chain_dnat n d c = (n', d', c') ->
  (forall k, n <= k -> ~ In (mapname k) (map fst (sd_maps d))) ->
  (forall k, n' <= k -> ~ In (mapname k) (map fst (sd_maps d'))).
Proof.
  intros n d c n' d' c' H Hfresh k Hk Hin. unfold optimize_chain_dnat in H.
  destruct (optimize_rules_dnat n d (c_rules c)) as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  pose proof (optimize_rules_dnat_mono (c_rules c) n d _ _ _ E) as Hmono.
  destruct (optimize_rules_dnat_maps_bound (c_rules c) n d _ _ _ k E Hin)
    as [Hin_d | Hlt].
  - apply (Hfresh k); [lia | exact Hin_d].
  - lia.
Qed.
