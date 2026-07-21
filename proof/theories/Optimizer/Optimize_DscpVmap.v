(** * Optimize_DscpVmap: masked-payload value+VERDICT->vmap fold for `ip dscp` / `ip6 dscp`.

    Battery shape "dscp-masked-vmap":

        ip dscp 0x0a accept   ┐
        ip dscp 0x1a drop     ┘   =>   ip dscp vmap { 10 : accept, 26 : drop }

    This is the VMAP sibling of [Optimize_Dscp] (which builds a value->SET for a run
    of SAME-verdict masked rules) and the masked analogue of [Optimize_Vmap]'s
    [optimize_rules_vmap] (which folds an UNGUARDED plain single-selector run of
    DIFFERING-verdict rules into a verdict map).

    The frontend lowers a single positive `ip dscp N` (a sub-byte header bitfield) to
    a MASKED-payload equality test ([nft_lower.ml]'s [bitfield_sel]):

        [ payload load 1b @ network header + 1 ]
        [ bitwise reg 1 = ( reg 1 & 0xfc ) ^ 0x00 ]
        [ cmp eq reg 1 (N << 2) ]                     -- [MMasked f CEq [0xfc] [0] v]

    i.e. `(field & 0xfc) == v` where `v = N << 2`.  `nft --optimize` folds a run of
    such rules that share the field/mask/xor but carry DIFFERING VERDICTS into ONE
    `ip dscp vmap { v1 : w1, v2 : w2, … }` rule, which nft compiles to the SAME masked
    load followed by a verdict-map LOOKUP of the masked register value:

        [ payload load 1b ][ bitwise & 0xfc ][ lookup reg 1 vmap { v1:w1, v2:w2 } ]

    This module recognises the run and emits exactly that: ONE [mk_vmap_rule_t] whose
    verdict-map KEY carries the transform [ [TBitAnd mask xor] ] (so the key read is
    the TRANSFORMED / masked field value, sharing [apply_transforms [TBitAnd mask xor]
    = data_bitops _ mask xor] with the [MMasked] head), over the fresh N-entry point
    vmap [map vmap_pt ((v1,w1)::…)].

    SOUNDNESS.  The masked field value [X = data_bitops (field_value f e p) mask xor] is
    the SAME operand in both the [MMasked] equality and the vmap key; membership of a
    point entry [(v,v,w)] resolves through [assoc_verdict] by [data_in_iv X (v,v) =
    data_eqb X v] ([data_in_iv_point]), which — under the fixed-width side condition
    [field_fixed_len f = Some len = len mask = len xor = len v] ([dscpv_key_width]) —
    coincides with the [MMasked f CEq mask xor v] head's [firstn]-truncated equality.
    So the vmap's first-match scan reproduces the run's first-match order EXACTLY
    ([eval_rules_dscpv_mergeN]).  The point vmap over DISTINCT masked values is a VALID
    single-field vmap (disjoint singletons — no overlapping-interval defect), and nft
    compiles the fold to it.  Every top-level lemma is axiom-free. *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Stdlib Require String.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Optimize Optimize_ValueSet Optimize_Concat Optimize_Vmap Optimize_Dscp.
Import ListNotations.
Local Open Scope nat_scope.

(** ** The merged transform-keyed VMAP rule.

    [mk_vmap_rule_t f ts nm body] is [Optimize_Vmap.mk_vmap_rule] with the vmap KEY
    field carrying the transforms [ts] (here [ [TBitAnd mask xor] ]): the key read is
    [apply_transforms ts (field_value f e p)] instead of the raw [field_value f e p]. *)
Definition mk_vmap_rule_t (f : field) (ts : list transform) (nm : String.string)
    (body : list body_item) : rule :=
  {| r_body := body;
     r_outcome := OVmap {| vm_fields := [f]; vm_keyf := Some (f, ts); vm_name := nm |}; r_after := [] |}.

(** The originals' shape: [mk_head (MMasked f CEq mask xor v) body (mk_vmap_base w)]
    — the same masked head as [Optimize_Dscp.head_dscp] recognises, over a
    pure-terminal verdict base ([mk_vmap_base w]). *)
Definition orig_rule_m (f : field) (mask xor v : data) (body : list body_item)
    (w : verdict) : rule :=
  mk_head (MMasked f CEq mask xor v) body (mk_vmap_base w).

(** *** Bridges: the masked original agrees with the plain [orig_rule] on loadability
    and outcome (both differ only in the head match, whose [match_loadable] is
    [field_loadable f] either way, and whose contribution [outcome_mk_head] strips). *)
Lemma orig_rule_m_loadable_eq : forall f mask xor v body w e p,
  rule_loadable (orig_rule_m f mask xor v body w) e p
  = rule_loadable (orig_rule f v body w) e p.
Proof.
  intros. unfold orig_rule_m, orig_rule.
  rewrite !rule_loadable_mk_head, match_loadable_mmasked. cbn [match_loadable].
  reflexivity.
Qed.

Lemma orig_rule_m_applies : forall f mask xor v body w e p,
  rule_applies (orig_rule_m f mask xor v body w) e p
  = eval_matchcond (MMasked f CEq mask xor v) e p && rule_applies_walk body e p.
Proof. intros. unfold orig_rule_m. apply rule_applies_mk_head. Qed.

Lemma orig_rule_m_outcome_clean : forall f mask xor v body w e p,
  body_synproxy_stops body p = false ->
  body_has_notrack body = false ->
  terminal w = true ->
  outcome (orig_rule_m f mask xor v body w) e p = Some w.
Proof.
  intros f mask xor v body w e p Hsp Hnt Hw.
  unfold orig_rule_m. rewrite outcome_mk_head, Hsp.
  unfold outcome_core, body_thread, mk_vmap_base. cbn [r_vmap r_outcome]. rewrite Hnt.
  apply (terminal_outcome_vmap_base w p Hw).
Qed.

(** ** The masked point-key certificate. *)

Lemma eval_mmasked_point : forall f mask xor v e q,
  field_loadable f q = true ->
  length (data_bitops (field_value f e q) mask xor) = length v ->
  eval_matchcond (MMasked f CEq mask xor v) e q
  = data_eqb (data_bitops (field_value f e q) mask xor) v.
Proof.
  intros f mask xor v e q Hld Hlen.
  unfold eval_matchcond, eval_matchcond_body. rewrite match_loadable_mmasked, Hld.
  cbn [andb]. unfold eval_cmp. rewrite <- Hlen, List.firstn_all. reflexivity.
Qed.

(** The width certificate: when [f] loads, the masked value has the field's fixed
    width, which equals each stored point's width. *)
Lemma dscpv_key_width : forall f (mask xor v : data) e p,
  field_fixed_len f = Some (length v) ->
  length mask = length v -> length xor = length v ->
  field_loadable f p = true ->
  length (data_bitops (field_value f e p) mask xor) = length v.
Proof.
  intros f mask xor v e p Hfx Hm Hx Hld.
  pose proof (field_fixed_len_loaded f (length v) e p Hfx Hld) as Hfv.
  rewrite (data_bitops_length_eq (field_value f e p) mask xor).
  - exact Hfv.
  - rewrite Hfv, Hm; reflexivity.
  - rewrite Hm, Hx; reflexivity.
Qed.

(** The masked first-match scan (over MMasked equalities). *)
Fixpoint first_match_m (f : field) (mask xor : data) (e : env) (q : packet)
    (l : list (data * verdict)) : option verdict :=
  match l with
  | [] => None
  | (v, w) :: tl => if eval_matchcond (MMasked f CEq mask xor v) e q then Some w
                    else first_match_m f mask xor e q tl
  end.

(** [assoc_verdict] over the N-entry point map with the MASKED key = [first_match_m]. *)
Lemma assoc_verdict_points_m : forall es f mask xor e q,
  (forall v w, In (v, w) es -> field_loadable f q = true ->
     length (data_bitops (field_value f e q) mask xor) = length v) ->
  field_loadable f q = true ->
  assoc_verdict (data_bitops (field_value f e q) mask xor) (map vmap_pt es)
  = first_match_m f mask xor e q es.
Proof.
  intros es f mask xor e q Hlen Hld.
  induction es as [| [v w] es IH]; [reflexivity|].
  cbn [map]. unfold vmap_pt at 1. cbn [fst snd assoc_verdict first_match_m].
  rewrite data_in_iv_point_eqb.
  rewrite (eval_mmasked_point f mask xor v e q Hld (Hlen v w (or_introl eq_refl) Hld)).
  destruct (data_eqb (data_bitops (field_value f e q) mask xor) v) eqn:E; [reflexivity|].
  apply IH. intros v' w' Hin Hld'. apply (Hlen v' w'); [right; exact Hin | exact Hld'].
Qed.

(** The merged rule's [outcome_core] over an N-entry point map with the masked key. *)
Lemma outcome_core_dscpvN : forall es f mask xor e q nm body,
  e_vmap e nm = map vmap_pt es ->
  (forall v w, In (v, w) es -> field_loadable f q = true ->
     length (data_bitops (field_value f e q) mask xor) = length v) ->
  field_loadable f q = true ->
  outcome_core (mk_vmap_rule_t f [TBitAnd mask xor] nm body) e q
  = first_match_m f mask xor e q es.
Proof.
  intros es f mask xor e q nm body Hvm Hlen Hld.
  unfold outcome_core, mk_vmap_rule_t. cbn [r_vmap vm_keyf vm_name vm_fields r_outcome].
  cbn [apply_transforms fold_left apply_transform]. rewrite Hvm.
  rewrite (assoc_verdict_points_m es f mask xor e q Hlen Hld).
  destruct (first_match_m f mask xor e q es) eqn:Efm; [reflexivity|].
  unfold terminal_outcome, mk_vmap_rule_t.
  cbn [r_nat r_tproxy r_fwd r_queue r_verdict r_after terminal r_outcome]. reflexivity.
Qed.

(** ** The N-way masked verdict-map collapse, verdict-preserving.

    A run [map (fun (v,w) => orig_rule_m f mask xor v body w) es] of same-field/mask/xor
    DIFFERENT-verdict masked rules, whose merged vmap [nm] carries the N point entries
    [map vmap_pt es], collapses to ONE [mk_vmap_rule_t] over the transform-keyed vmap.
    Mirrors [Optimize_Vmap.eval_rules_vmap_mergeN] with the raw key replaced by the
    masked key [data_bitops (field_value f e p) mask xor]. *)
Lemma eval_rules_dscpv_mergeN : forall f mask xor nm es body rest e p,
  e_vmap e nm = map vmap_pt es ->
  (forall v w, In (v, w) es -> field_fixed_len f = Some (length v)) ->
  (forall v w, In (v, w) es -> length mask = length v) ->
  (forall v w, In (v, w) es -> length xor = length v) ->
  (forall v w, In (v, w) es -> terminal w = true) ->
  body_synproxy_stops body p = false ->
  body_has_notrack body = false ->
  eval_rules (mk_vmap_rule_t f [TBitAnd mask xor] nm body :: rest) e p
  = eval_rules (map (fun vw => orig_rule_m f mask xor (fst vw) body (snd vw)) es ++ rest) e p.
Proof.
  intros f mask xor nm es body rest e p Hvm Hfx Hmw Hxw Hterm Hsp Hnt.
  (* merged rule loadable / applies *)
  assert (HmL : rule_loadable (mk_vmap_rule_t f [TBitAnd mask xor] nm body) e p
                = body_loadable_walk body p && field_loadable f p).
  { unfold rule_loadable, mk_vmap_rule_t. cbn [r_body]. rewrite Hsp.
    unfold body_thread. cbn [r_body]. rewrite Hnt.
    unfold end_loadable. cbn [r_vmap r_outcome]. unfold vmap_loadable.
    cbn [r_vmap vm_keyf vm_name vm_fields r_outcome].
    destruct (field_loadable f p) eqn:Hfld; cbn [andb].
    - destruct (assoc_verdict (apply_transforms [TBitAnd mask xor] (field_value f e p))
                              (e_vmap e nm));
        rewrite ?Bool.andb_true_r; reflexivity.
    - rewrite Bool.andb_false_r. reflexivity. }
  assert (HmA : rule_applies (mk_vmap_rule_t f [TBitAnd mask xor] nm body) e p
                = rule_applies_walk body e p) by reflexivity.
  cbn [eval_rules]. rewrite HmL, HmA.
  destruct (field_loadable f p) eqn:Hfld; cbn [andb].
  - (* f loads: merged outcome = first_match_m; the run scans the same keys *)
    rewrite Bool.andb_true_r.
    assert (Hmout : outcome (mk_vmap_rule_t f [TBitAnd mask xor] nm body) e p
                    = first_match_m f mask xor e p es).
    { unfold outcome, mk_vmap_rule_t. cbn [r_body]. rewrite Hsp.
      unfold body_thread. cbn [r_body]. rewrite Hnt.
      change ({| r_body := body;
     r_outcome := OVmap {| vm_fields := [f]; vm_keyf := Some (f, [TBitAnd mask xor]);
                                   vm_name := nm |}; r_after := [] |}) with (mk_vmap_rule_t f [TBitAnd mask xor] nm body).
      apply (outcome_core_dscpvN es f mask xor e p nm body Hvm
               (fun v w Hin Hld =>
                  dscpv_key_width f mask xor v e p (Hfx v w Hin) (Hmw v w Hin) (Hxw v w Hin) Hld)
               Hfld). }
    rewrite Hmout.
    destruct (body_loadable_walk body p) eqn:HbL; cbn [andb].
    + destruct (rule_applies_walk body e p) eqn:HbA; cbn [andb].
      * (* body loads & applies: induct on es, matching first_match_m to the run *)
        clear HmL HmA Hmout Hvm.
        induction es as [| [v w] es IH]; cbn [map app first_match_m fst snd].
        -- reflexivity.
        -- cbn [eval_rules].
           rewrite orig_rule_m_loadable_eq, orig_rule_m_applies,
                   (orig_rule_m_outcome_clean f mask xor v body w e p Hsp Hnt
                      (Hterm v w (or_introl eq_refl))).
           rewrite orig_rule_loadable. cbn [match_loadable].
           rewrite Hfld, HbL, Hsp. cbn [andb].
           rewrite HbA. cbn [andb].
           destruct (eval_matchcond (MMasked f CEq mask xor v) e p) eqn:Ev.
           ++ rewrite (Hterm v w (or_introl eq_refl)). reflexivity.
           ++ apply IH.
              ** intros v' w' Hin. apply (Hfx v' w'); right; exact Hin.
              ** intros v' w' Hin. apply (Hmw v' w'); right; exact Hin.
              ** intros v' w' Hin. apply (Hxw v' w'); right; exact Hin.
              ** intros v' w' Hin. apply (Hterm v' w'); right; exact Hin.
      * (* body doesn't apply: merged skipped, run all skipped *)
        clear HmL HmA Hmout Hvm.
        induction es as [| [v w] es IH]; cbn [map app fst snd]; [reflexivity|].
        cbn [eval_rules].
        rewrite orig_rule_m_loadable_eq, orig_rule_m_applies.
        rewrite orig_rule_loadable. cbn [match_loadable].
        rewrite Hfld, HbL, Hsp. cbn [andb].
        rewrite HbA. rewrite Bool.andb_false_r. apply IH;
          [ intros v' w' Hin; apply (Hfx v' w'); right; exact Hin
          | intros v' w' Hin; apply (Hmw v' w'); right; exact Hin
          | intros v' w' Hin; apply (Hxw v' w'); right; exact Hin
          | intros v' w' Hin; apply (Hterm v' w'); right; exact Hin ].
    + (* body doesn't load: merged skipped, run all skipped *)
      clear HmL HmA Hmout Hvm.
      induction es as [| [v w] es IH]; cbn [map app fst snd]; [reflexivity|].
      cbn [eval_rules].
      rewrite orig_rule_m_loadable_eq, orig_rule_loadable. cbn [match_loadable].
      rewrite Hfld, HbL, Hsp. cbn [andb]. apply IH;
        [ intros v' w' Hin; apply (Hfx v' w'); right; exact Hin
        | intros v' w' Hin; apply (Hmw v' w'); right; exact Hin
        | intros v' w' Hin; apply (Hxw v' w'); right; exact Hin
        | intros v' w' Hin; apply (Hterm v' w'); right; exact Hin ].
  - (* f does not load: merged skipped; every orig has head field-load false -> skipped *)
    rewrite Bool.andb_false_r. cbn [andb].
    clear HmL HmA Hvm.
    induction es as [| [v w] es IH]; cbn [map app fst snd]; [reflexivity|].
    cbn [eval_rules].
    rewrite orig_rule_m_loadable_eq, orig_rule_loadable. cbn [match_loadable].
    rewrite Hfld. cbn [andb]. apply IH;
      [ intros v' w' Hin; apply (Hfx v' w'); right; exact Hin
      | intros v' w' Hin; apply (Hmw v' w'); right; exact Hin
      | intros v' w' Hin; apply (Hxw v' w'); right; exact Hin
      | intros v' w' Hin; apply (Hterm v' w'); right; exact Hin ].
Qed.

(** ** The compact END-shell test for the masked original. *)
Lemma rule_end_eqb_orig_rule_m : forall r f mask xor v rest,
  head_dscp r = Some (f, mask, xor, v, rest) ->
  (rule_end_eqb r (mk_vmap_base (r_verdict r)) = true
   <-> r = orig_rule_m f mask xor v rest (r_verdict r)).
Proof.
  intros r f mask xor v rest Hhd.
  pose proof (head_dscp_canon r f mask xor v rest Hhd) as Hself.
  unfold orig_rule_m.
  rewrite (rule_end_eqb_mk_head (MMasked f CEq mask xor v) rest r
             (mk_vmap_base (r_verdict r))).
  unfold mk_head in Hself. rewrite <- Hself at 1. reflexivity.
Qed.

(** ** Recognise a masked-vmap-merge run pair (mirrors [Optimize_Vmap.vmap_run_pair]
    with the masked head [head_dscp] and the shared mask/xor). *)
Definition dscpv_run_pair (r1 r2 : rule)
  : option (field * data * data * data * verdict * list body_item) :=
  (* EFFECT-SAFETY GUARD — see [Optimize_ValueSet.value_merge_pair]. *)
  if negb (rule_mutfree r1) then None else
  match head_dscp r1, head_dscp r2 with
  | Some (f1, m1, x1, v1, rest1), Some (f2, m2, x2, v2, rest2) =>
      if field_eq_dec f1 f2 then
      if list_eq_dec Nat.eq_dec m1 m2 then
      if list_eq_dec Nat.eq_dec x1 x2 then
      if list_eq_dec body_item_eq_dec rest1 rest2 then
      match field_fixed_len f1 with
      | Some len =>
        if Nat.eq_dec len (length m1) then
        if Nat.eq_dec len (length x1) then
        if Nat.eq_dec len (length v1) then
        if Nat.eq_dec len (length v2) then
        if terminal (r_verdict r1) then
        if terminal (r_verdict r2) then
        if rule_end_eqb r1 (mk_vmap_base (r_verdict r1)) then
        if rule_end_eqb r2 (mk_vmap_base (r_verdict r2)) then
          Some (f1, m1, x1, v2, r_verdict r2, rest1)
        else None else None
        else None else None else None else None else None else None
      | None => None
      end
      else None else None else None else None
  | _, _ => None
  end.

(** The guard, extracted: a fired pair certifies its canonical rule write-free. *)
Lemma dscpv_run_pair_mutfree : forall r1 r2 x,
  dscpv_run_pair r1 r2 = Some x -> rule_mutfree r1 = true.
Proof.
  intros r1 r2 x H. unfold dscpv_run_pair in H.
  destruct (rule_mutfree r1); [reflexivity | discriminate H].
Qed.

Lemma dscpv_run_pair_shape : forall r1 r2 f mask xor v2 w2 body,
  dscpv_run_pair r1 r2 = Some (f, mask, xor, v2, w2, body) ->
  (exists v1, head_dscp r1 = Some (f, mask, xor, v1, body)
              /\ r1 = orig_rule_m f mask xor v1 body (r_verdict r1)
              /\ field_fixed_len f = Some (length v1)
              /\ length mask = length v1 /\ length xor = length v1
              /\ terminal (r_verdict r1) = true) /\
  r2 = orig_rule_m f mask xor v2 body w2 /\
  field_fixed_len f = Some (length v2) /\
  length mask = length v2 /\ length xor = length v2 /\ terminal w2 = true.
Proof.
  intros r1 r2 f mask xor v2 w2 body H. unfold dscpv_run_pair in H.
  destruct (negb (rule_mutfree r1)); [discriminate |].
  destruct (head_dscp r1) as [[[[[f1 m1] x1] u1] s1] |] eqn:H1; [| discriminate].
  destruct (head_dscp r2) as [[[[[f2 m2] x2] u2] s2] |] eqn:H2; [| discriminate].
  destruct (field_eq_dec f1 f2) as [Ef |]; [| discriminate]. subst f2.
  destruct (list_eq_dec Nat.eq_dec m1 m2) as [Em |]; [| discriminate]. subst m2.
  destruct (list_eq_dec Nat.eq_dec x1 x2) as [Ex |]; [| discriminate]. subst x2.
  destruct (list_eq_dec body_item_eq_dec s1 s2) as [Es |]; [| discriminate]. subst s2.
  destruct (field_fixed_len f1) as [len |] eqn:Hfx; [| discriminate].
  destruct (Nat.eq_dec len (length m1)) as [Elm |]; [| discriminate].
  destruct (Nat.eq_dec len (length x1)) as [Elx |]; [| discriminate].
  destruct (Nat.eq_dec len (length u1)) as [El1 |]; [| discriminate].
  destruct (Nat.eq_dec len (length u2)) as [El2 |]; [| discriminate].
  destruct (terminal (r_verdict r1)) eqn:Ew1; [| discriminate].
  destruct (terminal (r_verdict r2)) eqn:Ew2; [| discriminate].
  destruct (rule_end_eqb r1 (mk_vmap_base (r_verdict r1))) eqn:Eb1; [| discriminate].
  destruct (rule_end_eqb r2 (mk_vmap_base (r_verdict r2))) eqn:Eb2; [| discriminate].
  pose proof (proj1 (rule_end_eqb_orig_rule_m r1 f1 m1 x1 u1 s1 H1) Eb1) as Esh1.
  pose proof (proj1 (rule_end_eqb_orig_rule_m r2 f1 m1 x1 u2 s1 H2) Eb2) as Esh2.
  injection H as Ef' Em' Ex' Ev2 Ew2' Ebody. subst f mask xor w2 body v2.
  assert (Hfx1 : field_fixed_len f1 = Some (length u1)) by (rewrite Hfx; f_equal; exact El1).
  assert (Hfx2 : field_fixed_len f1 = Some (length u2)) by (rewrite Hfx; f_equal; exact El2).
  split.
  - exists u1. repeat split; try assumption; try reflexivity; congruence.
  - repeat split; try assumption; congruence.
Qed.

(** ** Executable N-WAY masked-vmap pass (mirrors [Optimize_Vmap.optimize_rules_vmap]). *)
Fixpoint take_dscpv_run (r1 : rule) (rest : list rule)
  : list (data * verdict) * list rule :=
  match rest with
  | [] => ([], [])
  | r2 :: tl =>
      match dscpv_run_pair r1 r2 with
      | Some (_, _, _, v2, w2, _) =>
          let '(es, rest') := take_dscpv_run r1 tl in ((v2, w2) :: es, rest')
      | None => ([], rest)
      end
  end.

Lemma take_dscpv_run_shape : forall r1 f mask xor v1 body rest es rest',
  head_dscp r1 = Some (f, mask, xor, v1, body) ->
  take_dscpv_run r1 rest = (es, rest') ->
  rest = map (fun vw => orig_rule_m f mask xor (fst vw) body (snd vw)) es ++ rest'
  /\ (forall v w, In (v, w) es -> field_fixed_len f = Some (length v))
  /\ (forall v w, In (v, w) es -> length mask = length v)
  /\ (forall v w, In (v, w) es -> length xor = length v)
  /\ (forall v w, In (v, w) es -> terminal w = true).
Proof.
  intros r1 f mask xor v1 body rest.
  induction rest as [| r2 tl IH]; intros es rest' Hhd H.
  - cbn in H. inversion H; subst.
    split; [reflexivity| repeat split; intros v w []].
  - cbn in H. destruct (dscpv_run_pair r1 r2)
      as [[[[[[f2 m2] x2] v2] w2] bd] |] eqn:Evm.
    + destruct (take_dscpv_run r1 tl) as [es0 rest0] eqn:Erec.
      inversion H; subst es rest'. clear H.
      destruct (dscpv_run_pair_shape r1 r2 f2 m2 x2 v2 w2 bd Evm)
        as [[u1 [Hhd1 _]] [Hr2 [Hfx [Hmw [Hxw Hw2]]]]].
      rewrite Hhd in Hhd1. inversion Hhd1; subst f2 m2 x2 bd.
      destruct (IH es0 rest0 Hhd eq_refl) as [Hsplit [Hall1 [Hall2 [Hall3 Hall4]]]].
      split; [| repeat split].
      * cbn [map app fst snd]. rewrite <- Hr2, <- Hsplit. reflexivity.
      * intros v w [Hvw | Hin]; [ inversion Hvw; subst; exact Hfx | apply (Hall1 v w Hin) ].
      * intros v w [Hvw | Hin]; [ inversion Hvw; subst; exact Hmw | apply (Hall2 v w Hin) ].
      * intros v w [Hvw | Hin]; [ inversion Hvw; subst; exact Hxw | apply (Hall3 v w Hin) ].
      * intros v w [Hvw | Hin]; [ inversion Hvw; subst; exact Hw2 | apply (Hall4 v w Hin) ].
    + inversion H; subst es rest'.
      split; [reflexivity| repeat split; intros v w []].
Qed.

Lemma take_dscpv_run_head : forall r1 f mask xor v1 body r2 rest es rest',
  head_dscp r1 = Some (f, mask, xor, v1, body) ->
  take_dscpv_run r1 (r2 :: rest) = (es, rest') ->
  es <> [] ->
  r1 = orig_rule_m f mask xor v1 body (r_verdict r1) /\
  field_fixed_len f = Some (length v1) /\
  length mask = length v1 /\ length xor = length v1 /\ terminal (r_verdict r1) = true.
Proof.
  intros r1 f mask xor v1 body r2 rest es rest' Hhd Hrun Hne.
  cbn in Hrun. destruct (dscpv_run_pair r1 r2)
    as [[[[[[f2 m2] x2] v2] w2] bd] |] eqn:Evm.
  - destruct (dscpv_run_pair_shape r1 r2 f2 m2 x2 v2 w2 bd Evm)
      as [[u1 [Hhd1 [Hr1 [Hfx1 [Hmw1 [Hxw1 Hw1]]]]]] _].
    rewrite Hhd in Hhd1. inversion Hhd1; subst f2 m2 x2 u1 bd.
    repeat split; assumption.
  - destruct (take_dscpv_run r1 rest) as [es0 rest0] eqn:Erec0.
    inversion Hrun; subst. contradiction.
Qed.

Fixpoint optimize_rules_dscpvmap (fuel n : nat) (d : set_decls) (rs : list rule)
  : nat * set_decls * list rule :=
  match fuel with
  | O => (n, d, rs)
  | S fuel' =>
    match rs with
    | r1 :: ((_ :: _) as rest) =>
        match head_dscp r1 with
        | Some (f, mask, xor, v1, body) =>
            match take_dscpv_run r1 rest with
            | ((_ :: _) as es, rest') =>
                if has_distinct_verdict (r_verdict r1) es && body_vmap_safe body then
                  let name := vmapname n in
                  let entries := (v1, r_verdict r1) :: es in
                  let d' := {| sd_sets := sd_sets d;
                               sd_vmaps := (name, map vmap_pt entries) :: sd_vmaps d;
                               sd_maps := sd_maps d |} in
                  let merged := mk_vmap_rule_t f [TBitAnd mask xor] name body in
                  let '(n'', d'', rest'') := optimize_rules_dscpvmap fuel' (S n) d' rest' in
                  (n'', d'', merged :: rest'')
                else
                  let '(n'', d'', rest') := optimize_rules_dscpvmap fuel' n d rest in
                  (n'', d'', r1 :: rest')
            | ([], _) =>
                let '(n'', d'', rest') := optimize_rules_dscpvmap fuel' n d rest in
                (n'', d'', r1 :: rest')
            end
        | None =>
            let '(n'', d'', rest') := optimize_rules_dscpvmap fuel' n d rest in
            (n'', d'', r1 :: rest')
        end
    | _ => (n, d, rs)
    end
  end.

Definition optimize_chain_dscpvmap (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n', d', rs') := optimize_rules_dscpvmap (length (c_rules c)) n d (c_rules c) in
  (n', d', {| c_policy := c_policy c; c_rules := rs' |}).

Lemma optimize_rules_dscpvmap_consSS : forall fuel n d r1 r2 rest,
  optimize_rules_dscpvmap (S fuel) n d (r1 :: r2 :: rest) =
  match head_dscp r1 with
  | Some (f, mask, xor, v1, body) =>
      match take_dscpv_run r1 (r2 :: rest) with
      | ((_ :: _) as es, rest') =>
          if has_distinct_verdict (r_verdict r1) es && body_vmap_safe body then
            let name := vmapname n in
            let entries := (v1, r_verdict r1) :: es in
            let d' := {| sd_sets := sd_sets d;
                         sd_vmaps := (name, map vmap_pt entries) :: sd_vmaps d;
                         sd_maps := sd_maps d |} in
            let merged := mk_vmap_rule_t f [TBitAnd mask xor] name body in
            let '(n'', d'', rest'') := optimize_rules_dscpvmap fuel (S n) d' rest' in
            (n'', d'', merged :: rest'')
          else
            let '(n'', d'', rest') := optimize_rules_dscpvmap fuel n d (r2 :: rest) in
            (n'', d'', r1 :: rest')
      | ([], _) =>
          let '(n'', d'', rest') := optimize_rules_dscpvmap fuel n d (r2 :: rest) in
          (n'', d'', r1 :: rest')
      end
  | None =>
      let '(n'', d'', rest') := optimize_rules_dscpvmap fuel n d (r2 :: rest) in
      (n'', d'', r1 :: rest')
  end.
Proof. reflexivity. Qed.

(** *** Freshness bookkeeping: the pass only PREPENDS [sd_vmaps] entries keyed by
    [vmapname k] with [n <= k < n'], leaving [sd_sets]/[sd_maps] untouched. *)
Lemma optimize_rules_dscpvmap_assoc_stable : forall fuel n d rs n' d' rs' nm X,
  optimize_rules_dscpvmap fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> nm <> vmapname k) ->
  assoc_str nm (sd_vmaps d') X = assoc_str nm (sd_vmaps d) X.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' nm X H Hnm.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_dscpvmap_consSS in H.
      destruct (head_dscp r1) as [[[[[f mask] xor] v1] body] |] eqn:Ehd.
      * destruct (take_dscpv_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
        -- destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           2:{ remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
               destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
               injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
               eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm]. }
           cbv zeta in H.
           remember (optimize_rules_dscpvmap fuel (S n)
                       {| sd_sets := sd_sets d;
                          sd_vmaps := (vmapname n,
                            map vmap_pt ((v1, r_verdict r1) :: e :: es')) :: sd_vmaps d;
                          sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           erewrite (IH (S n) _ rest'); [ | symmetry; exact Erec | intros k Hk; apply Hnm; lia ].
           cbn [sd_vmaps assoc_str].
           destruct (String.eqb nm (vmapname n)) eqn:Eqn.
           ++ apply String.eqb_eq in Eqn. exfalso. apply (Hnm n); [lia | exact Eqn].
           ++ reflexivity.
      * remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
        eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
Qed.

Lemma optimize_rules_dscpvmap_mono : forall fuel n d rs n' d' rs',
  optimize_rules_dscpvmap fuel n d rs = (n', d', rs') -> n <= n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; lia.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; lia.
    + cbn in H. inversion H; subst; lia.
    + rewrite optimize_rules_dscpvmap_consSS in H.
      destruct (head_dscp r1) as [[[[[f mask] xor] v1] body] |] eqn:Ehd.
      * destruct (take_dscpv_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           2:{ remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
               destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
               eapply (IH n d (r2 :: rest)); symmetry; exact Erec. }
           cbv zeta in H.
           remember (optimize_rules_dscpvmap fuel (S n) _ rest') as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n'.
           assert (S n <= m'')
             by (eapply (IH (S n) _ rest'); symmetry; exact Erec). lia.
      * remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_dscpvmap_sets : forall fuel n d rs n' d' rs',
  optimize_rules_dscpvmap fuel n d rs = (n', d', rs') -> sd_sets d' = sd_sets d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_dscpvmap_consSS in H.
      destruct (head_dscp r1) as [[[[[f mask] xor] v1] body] |] eqn:Ehd.
      * destruct (take_dscpv_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           2:{ remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
               destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
               eapply (IH n d (r2 :: rest)); symmetry; exact Erec. }
           cbv zeta in H.
           remember (optimize_rules_dscpvmap fuel (S n)
                       {| sd_sets := sd_sets d;
                          sd_vmaps := (vmapname n,
                            map vmap_pt ((v1, r_verdict r1) :: e :: es')) :: sd_vmaps d;
                          sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_dscpvmap_maps : forall fuel n d rs n' d' rs',
  optimize_rules_dscpvmap fuel n d rs = (n', d', rs') -> sd_maps d' = sd_maps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_dscpvmap_consSS in H.
      destruct (head_dscp r1) as [[[[[f mask] xor] v1] body] |] eqn:Ehd.
      * destruct (take_dscpv_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           2:{ remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
               destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
               eapply (IH n d (r2 :: rest)); symmetry; exact Erec. }
           cbv zeta in H.
           remember (optimize_rules_dscpvmap fuel (S n)
                       {| sd_sets := sd_sets d;
                          sd_vmaps := (vmapname n,
                            map vmap_pt ((v1, r_verdict r1) :: e :: es')) :: sd_vmaps d;
                          sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_dscpvmap_keys_bound : forall fuel n d rs n' d' rs' k,
  optimize_rules_dscpvmap fuel n d rs = (n', d', rs') ->
  In (vmapname k) (map fst (sd_vmaps d')) ->
  In (vmapname k) (map fst (sd_vmaps d)) \/ k < n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' k H Hin.
  - cbn in H. inversion H; subst. left; exact Hin.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst. left; exact Hin.
    + cbn in H. inversion H; subst. left; exact Hin.
    + rewrite optimize_rules_dscpvmap_consSS in H.
      destruct (head_dscp r1) as [[[[[f mask] xor] v1] body] |] eqn:Ehd.
      * destruct (take_dscpv_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
        -- destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           2:{ remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
               destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
               subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin). }
           cbv zeta in H.
           remember (optimize_rules_dscpvmap fuel (S n)
                       {| sd_sets := sd_sets d;
                          sd_vmaps := (vmapname n,
                            map vmap_pt ((v1, r_verdict r1) :: e :: es')) :: sd_vmaps d;
                          sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'.
           destruct (IH (S n) _ rest' m'' dd'' rr'' k (eq_sym Erec) Hin) as [Hin_dn | Hlt].
           ++ cbn [sd_vmaps map] in Hin_dn. destruct Hin_dn as [Heq | Hin_d].
              ** apply vmapname_inj in Heq. subst k. right.
                 pose proof (optimize_rules_dscpvmap_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec)). lia.
              ** left; exact Hin_d.
           ++ right; exact Hlt.
      * remember (optimize_rules_dscpvmap fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
        subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
Qed.

(** *** Chain-level structural wrappers. *)
Lemma optimize_chain_dscpvmap_mono : forall n d c n' d' c',
  optimize_chain_dscpvmap n d c = (n', d', c') -> n <= n'.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_dscpvmap in H.
  destruct (optimize_rules_dscpvmap (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_dscpvmap_mono _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_dscpvmap_sets : forall n d c n' d' c',
  optimize_chain_dscpvmap n d c = (n', d', c') -> sd_sets d' = sd_sets d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_dscpvmap in H.
  destruct (optimize_rules_dscpvmap (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_dscpvmap_sets _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_dscpvmap_maps : forall n d c n' d' c',
  optimize_chain_dscpvmap n d c = (n', d', c') -> sd_maps d' = sd_maps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_dscpvmap in H.
  destruct (optimize_rules_dscpvmap (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_dscpvmap_maps _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_dscpvmap_keys_bound : forall n d c n' d' c' k,
  optimize_chain_dscpvmap n d c = (n', d', c') ->
  In (vmapname k) (map fst (sd_vmaps d')) ->
  In (vmapname k) (map fst (sd_vmaps d)) \/ k < n'.
Proof.
  intros n d c n' d' c' k H Hin. unfold optimize_chain_dscpvmap in H.
  destruct (optimize_rules_dscpvmap (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  apply (optimize_rules_dscpvmap_keys_bound _ _ _ _ _ _ _ k E Hin).
Qed.

(** ** Non-vacuity witnesses (battery shape "dscp-masked-vmap"): two adjacent
    `ip dscp 10 accept` / `ip dscp 26 drop` masked rules fold to ONE
    `ip dscp vmap { 10 : accept, 26 : drop }` verdict-map rule.  The field is
    [FPayload PNetwork 1 1] (the TOS byte), mask 0xfc, xor 0x00; the compared values
    are the dscp codepoints shifted into the header bits (10<<2 = 0x28 = 40, 26<<2 =
    0x68 = 104), with DIFFERING verdicts. *)
Definition dscpv_base (w : verdict) : rule := mk_vmap_base w.

Definition dscpv_f : field := FPayload PNetwork 1 1.

Definition dscpv_r (v : data) (w : verdict) : rule :=
  mk_head (MMasked dscpv_f CEq [252] [0] v) [] (mk_vmap_base w).

Example dscpv_merge_fires :
  dscpv_run_pair (dscpv_r [40] Accept) (dscpv_r [104] Drop)
  = Some (dscpv_f, [252], [0], [104], Drop, []).
Proof. reflexivity. Qed.

(* the fold collapses the two-rule chain to ONE transform-keyed vmap rule + a fresh
   2-entry verdict map { 40 : accept, 104 : drop } *)
Example dscpv_folds :
  optimize_rules_dscpvmap 2 0 {| sd_sets := []; sd_vmaps := []; sd_maps := [] |}
    [dscpv_r [40] Accept; dscpv_r [104] Drop]
  = (1,
     {| sd_sets := [];
        sd_vmaps := [(vmapname 0, [([40],[40],Accept); ([104],[104],Drop)])];
        sd_maps := [] |},
     [ mk_vmap_rule_t dscpv_f [TBitAnd [252] [0]] (vmapname 0) [] ]).
Proof. reflexivity. Qed.
