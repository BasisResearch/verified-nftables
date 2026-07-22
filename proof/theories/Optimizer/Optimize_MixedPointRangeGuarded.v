(** * Optimize_MixedPointRangeGuarded: GUARDED MIXED point+range set consolidation.

    [Optimize_SetGuarded] folds a GUARDED run of POINT heads [MCmp f CEq v]; [Optimize_IntervalSetGuarded]
    folds a GUARDED run of RANGE heads [MRange f false lo hi].  Neither fires on a run
    that MIXES point and range compares over the same transport selector:

        udp dport 53 accept     ==> [ MCmp meta_l4proto 17 ; MCmp th_dport CEq 0x0035 ]
        udp dport 67-68 accept  ==> [ MCmp meta_l4proto 17 ; MRange th_dport false 67 68 ]
        udp dport 123 accept    ==> [ MCmp meta_l4proto 17 ; MCmp th_dport CEq 0x007b ]

    [setguarded] stops at the first range (its [value_mergeGs_pair] rejects the [MRange]
    head), and [intervalsetguarded] never starts (its [head_rangeGr] fails on the leading [MCmp]).
    So the mixed run is left unfolded — the "transport-port-mixed-point-range-set" gap.
    `nft --optimize` DOES fold it (confirmed against host nft v1.1.6 in a netns):

        udp dport 53 accept ; udp dport 67-68 accept ; udp dport 123 accept
          =>  udp dport { 53, 67-68, 123 } accept

    This module handles that shape.  It recognises a run

        [ GUARD ; HEAD_i ] ++ rest        (i = 1..N)

    where GUARD is a SHARED l4proto/nfproto dependency ([guard_okr], reused from
    [Optimize_IntervalSetGuarded]) and each HEAD_i is EITHER a point compare [MCmp f CEq v]
    (element [MePoint v]) OR a range [MRange f false lo hi] (element [MeRange lo hi]).
    It folds — exactly as `nft --optimize` does — into ONE rule

        [ GUARD ; MConcatSet [f] false __setN ] ++ rest

    over the interval set [map melem_iv elems], where a point contributes the
    degenerate interval [(v,v)] and a range contributes [(lo,hi)] — precisely nft's
    consolidation, which stores each point as a singleton interval and each range as
    a closed interval in the SAME anonymous NFT_SET_INTERVAL set.  The merged shell is
    [Optimize_SetGuarded.merged_ruleGs] VERBATIM.

    Verdict-preservation combines three certificates:
      - [Optimize_IntervalSet.concat_set_ivs_existsb]: a single-field [MConcatSet] over an
        interval set is EXACTLY the [existsb] of the [MRange] matches of its intervals;
      - [eval_melem_mrange] (this file): each element's ORIGINAL head match equals the
        [MRange] match of its interval — trivially for a range; for a point via the
        degenerate-interval identity [data_in_iv_point_eqb] under the field's
        FIXED-WIDTH side-condition ([melem_ok], the same [field_fixed_len] guard the
        point-set pass uses);
      - [Optimize_SetGuarded.existsb_guardhead_factor]: the shared head guard factors out of
        the run's [existsb].

    REPRESENTABILITY GATE.  A single-field nftables interval set lives in the [rbtree]
    backend, a strict PARTITION: it rejects ANY overlap (including a touch [b = c]).  So
    the pass only fires when the elements' intervals are PAIRWISE DISJOINT — reusing
    [Optimize_IntervalSetGuarded.all_disjoint].  A point that falls inside (or touches) another
    element's range is an overlap, so a run like `udp dport 53 ; udp dport 50-60` is
    DECLINED (left unfolded — a correct deferral; folding it would emit the UNLOADABLE
    overlapping set that is exactly `nft --optimize`'s defect).  Axiom-free. *)

From Stdlib Require Import Ascii String.
From Stdlib Require Import List PeanoNat Bool Lia Btauto.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Optimize Optimize_ValueSet Optimize_Concat Optimize_ConcatGuarded Optimize_SetGuarded Optimize_IntervalSet Optimize_IntervalSetGuarded.
Import ListNotations.
Local Open Scope nat_scope.

(** A recognised head element: a discrete POINT value, or a closed RANGE. *)
Inductive melem : Type :=
| MePoint (v : data)
| MeRange (lo hi : data).

(** The ORIGINAL head matchcond an element denotes. *)
Definition melem_mc (f : field) (e : melem) : matchcond :=
  match e with
  | MePoint v => MCmp f CEq v
  | MeRange lo hi => MRange f false lo hi
  end.

(** The interval-set element an element folds to (point -> degenerate [(v,v)]). *)
Definition melem_iv (e : melem) : data * data :=
  match e with
  | MePoint v => (v, v)
  | MeRange lo hi => (lo, hi)
  end.

(** Representability of an element AGAINST field [f]: a RANGE is always fine
    ([data_le] membership coincides with the interval test), a POINT needs the
    FIXED-WIDTH guard — otherwise [MCmp]'s prefix equality differs from the
    degenerate interval's full-width [data_le] membership. *)
Definition melem_ok (f : field) (e : melem) : bool :=
  match e with
  | MePoint v =>
      match field_fixed_len f with
      | Some len => Nat.eqb len (length v)
      | None => false
      end
  | MeRange _ _ => true
  end.

(** The guarded original element shell.  The merged shell is [merged_ruleGs]. *)
Definition orig_ruleGm (f : field) (gm : matchcond) (e : melem)
    (body : list body_item) (r1 : rule) : rule :=
  mk_head gm (BMatch (melem_mc f e) :: body) r1.

(** *** Recogniser: a guarded point-OR-range head. *)
Definition head_mixGm (r : rule)
  : option (matchcond * field * melem * list body_item) :=
  match r_body r with
  | BMatch gm :: BMatch (MCmp f CEq v) :: rest => Some (gm, f, MePoint v, rest)
  | BMatch gm :: BMatch (MRange f false lo hi) :: rest => Some (gm, f, MeRange lo hi, rest)
  | _ => None
  end.

Lemma head_mixGm_rbody : forall r gm f e body,
  head_mixGm r = Some (gm, f, e, body) ->
  r_body r = BMatch gm :: BMatch (melem_mc f e) :: body.
Proof.
  intros r gm f e body H. unfold head_mixGm in H.
  destruct (r_body r) as [| [m | s] tl] eqn:Eb; try discriminate.
  destruct tl as [| [m2 | s2] tl2]; try discriminate.
  destruct m2; try discriminate.
  - (* MRange *) destruct neg; try discriminate. inversion H; subst. reflexivity.
  - (* MCmp *) destruct op; try discriminate. inversion H; subst. reflexivity.
Qed.

Lemma head_mixGm_canon : forall r gm f e body,
  head_mixGm r = Some (gm, f, e, body) ->
  r = orig_ruleGm f gm e body r.
Proof.
  intros r gm f e body H.
  pose proof (head_mixGm_rbody r gm f e body H) as Hb.
  unfold orig_ruleGm, mk_head. rewrite <- Hb. destruct r; reflexivity.
Qed.

(** Two guarded rules form an eligible MIX-merge pair iff their heads are
    GUARD / HEAD over the SAME field [f], the SAME guard, with the SAME tail and the
    SAME end-fields.  Representability ([melem_ok]) and disjointness are checked in the
    run gate, not here — mirroring [Optimize_IntervalSetGuarded.range_mergeGr_pair] +
    [take_rangeg_run]. *)
Definition mix_mergeGm_pair (r1 r2 : rule)
  : option (matchcond * field * melem * melem * list body_item) :=
  (* EFFECT-SAFETY GUARD — see [Optimize_ValueSet.value_merge_pair]. *)
  if negb (rule_mutfree r1) then None else
  match head_mixGm r1, head_mixGm r2 with
  | Some (gm1, f1, e1, rest1), Some (gm2, f2, e2, rest2) =>
      if matchcond_eq_dec gm1 gm2 then
      if guard_okr gm1 then
      if field_eq_dec f1 f2 then
      if list_eq_dec body_item_eq_dec rest1 rest2 then
      if rule_end_eqb r1 r2
      then Some (gm1, f1, e1, e2, rest1)
      else None else None else None else None else None
  | _, _ => None
  end.

(** The guard, extracted: a fired pair certifies its canonical rule write-free. *)
Lemma mix_mergeGm_pair_mutfree : forall r1 r2 x,
  mix_mergeGm_pair r1 r2 = Some x -> rule_mutfree r1 = true.
Proof.
  intros r1 r2 x H. unfold mix_mergeGm_pair in H.
  destruct (rule_mutfree r1); [reflexivity | discriminate H].
Qed.

Lemma mix_mergeGm_pair_shape : forall r1 r2 gm f e1 e2 body,
  mix_mergeGm_pair r1 r2 = Some (gm, f, e1, e2, body) ->
  r1 = orig_ruleGm f gm e1 body r1 /\
  r2 = orig_ruleGm f gm e2 body r1.
Proof.
  intros r1 r2 gm f e1 e2 body H. unfold mix_mergeGm_pair in H.
  destruct (negb (rule_mutfree r1)); [discriminate |].
  destruct (head_mixGm r1) as [[[[gm1 f1] u1] rest1] |] eqn:H1; [| discriminate].
  destruct (head_mixGm r2) as [[[[gm2 f2] u2] rest2] |] eqn:H2; [| discriminate].
  destruct (matchcond_eq_dec gm1 gm2) as [Egm |]; [| discriminate]. subst gm2.
  destruct (guard_okr gm1) eqn:Egok; [| discriminate].
  destruct (field_eq_dec f1 f2) as [Ef |]; [| discriminate]. subst f2.
  destruct (list_eq_dec body_item_eq_dec rest1 rest2) as [Er |]; [| discriminate]. subst rest2.
  destruct (rule_end_eqb r1 r2) eqn:Eeqb; [| discriminate].
  inversion H; subst gm f e1 e2 body. clear H.
  pose proof (head_mixGm_canon r1 gm1 f1 u1 rest1 H1) as Hr1.
  pose proof (head_mixGm_canon r2 gm1 f1 u2 rest1 H2) as Hr2c.
  pose proof (proj1 (rule_end_eqb_mk_head gm1
                       (BMatch (melem_mc f1 u1) :: rest1) r1 r2) Eeqb) as Eshell.
  split; [exact Hr1 |].
  rewrite Hr2c. unfold orig_ruleGm, mk_head in Eshell |- *.
  injection Eshell as Eo Ea.
  rewrite Eo, Ea. reflexivity.
Qed.

Lemma mix_mergeGm_pair_with_head : forall r1 r2 gm f e1 body gm' f' e1' e2 body',
  head_mixGm r1 = Some (gm, f, e1, body) ->
  mix_mergeGm_pair r1 r2 = Some (gm', f', e1', e2, body') ->
  gm' = gm /\ f' = f /\ e1' = e1 /\ body' = body /\
  r2 = orig_ruleGm f gm e2 body r1.
Proof.
  intros r1 r2 gm f e1 body gm' f' e1' e2 body' Hhd Hvm.
  unfold mix_mergeGm_pair in Hvm.
  destruct (negb (rule_mutfree r1)); [discriminate Hvm |].
  rewrite Hhd in Hvm.
  destruct (head_mixGm r2) as [[[[gm2 f2] u2] rest2] |] eqn:H2; [| discriminate].
  destruct (matchcond_eq_dec gm gm2) as [Egm |]; [| discriminate]. subst gm2.
  destruct (guard_okr gm) eqn:Egok; [| discriminate].
  destruct (field_eq_dec f f2) as [Ef |]; [| discriminate]. subst f2.
  destruct (list_eq_dec body_item_eq_dec body rest2) as [Er |]; [| discriminate]. subst rest2.
  destruct (rule_end_eqb r1 r2) eqn:Eeqb; [| discriminate].
  inversion Hvm; subst gm' f' e1' e2 body'. clear Hvm.
  pose proof (head_mixGm_canon r2 gm f u2 body H2) as Hr2c.
  pose proof (proj1 (rule_end_eqb_mk_head gm (BMatch (melem_mc f e1) :: body) r1 r2) Eeqb) as Eshell.
  repeat split.
  rewrite Hr2c. unfold orig_ruleGm, mk_head in Eshell |- *.
  injection Eshell as Eo Ea.
  rewrite Eo, Ea. reflexivity.
Qed.

(** ** The per-element bridge: an element's ORIGINAL head match equals the [MRange]
    match of its interval.  Trivial for a range; for a point it is the degenerate
    interval identity, under the FIXED-WIDTH guard [melem_ok]. *)
Lemma eval_melem_mrange : forall f el en p,
  melem_ok f el = true ->
  eval_matchcond (melem_mc f el) en p
  = eval_matchcond (MRange f false (fst (melem_iv el)) (snd (melem_iv el))) en p.
Proof.
  intros f el en p Hok. destruct el as [v | lo hi]; cbn [melem_mc melem_iv fst snd].
  - unfold melem_ok in Hok.
    destruct (field_fixed_len f) as [len |] eqn:Hfx; [| discriminate].
    apply Nat.eqb_eq in Hok. subst len.
    rewrite eval_mrange_iv.
    destruct (field_loadable f p) eqn:Hld; cbn [andb].
    + rewrite (eval_mcmp_point f v en p Hld (field_fixed_len_loaded f (length v) en p Hfx Hld)).
      rewrite data_in_iv_point_eqb. reflexivity.
    + apply (eval_mcmp_point_unload f v en p Hld).
  - reflexivity.
Qed.

(** ** Loadability / outcome / applies of the guarded element shells. *)

(** ** Executable N-WAY guarded mixed-set pass (fuel-driven). *)

(** Collect the MAXIMAL run of following rules that each mix-merge with [r1]. *)
Fixpoint take_mix_run_raw (r1 : rule) (rest : list rule)
  : list melem * list rule :=
  match rest with
  | [] => ([], [])
  | r2 :: tl =>
      match mix_mergeGm_pair r1 r2 with
      | Some (_, _, _, e2, _) =>
          let '(es, rest') := take_mix_run_raw r1 tl in (e2 :: es, rest')
      | None => ([], rest)
      end
  end.

(** The consolidated run, GATED by representability (every element fixed-width-ok)
    AND disjointness (rbtree partition).  If either fails we DECLINE by returning the
    EMPTY run, keeping the [take_mix_run_shape] split invariant. *)
Definition take_mix_run (r1 : rule) (rest : list rule)
  : list melem * list rule :=
  match head_mixGm r1 with
  | Some (_, f, e1, _) =>
      let '(es, rest') := take_mix_run_raw r1 rest in
      if andb (forallb (melem_ok f) (e1 :: es))
              (all_disjoint (map melem_iv (e1 :: es)))
      then (es, rest') else ([], rest)
  | None => ([], rest)
  end.

Lemma take_mix_run_raw_shape : forall r1 gm f e1 body rest es rest',
  head_mixGm r1 = Some (gm, f, e1, body) ->
  take_mix_run_raw r1 rest = (es, rest') ->
  rest = map (fun e => orig_ruleGm f gm e body r1) es ++ rest'.
Proof.
  intros r1 gm f e1 body rest. induction rest as [| r2 tl IH]; intros es rest' Hhd H.
  - cbn in H. inversion H; subst. reflexivity.
  - cbn in H. destruct (mix_mergeGm_pair r1 r2)
      as [[[[[gm2 fa] ea] e2] bd] |] eqn:Evm.
    + destruct (take_mix_run_raw r1 tl) as [es0 rest0] eqn:Erec.
      inversion H; subst es rest'. clear H.
      destruct (mix_mergeGm_pair_with_head r1 r2 gm f e1 body gm2 fa ea e2 bd Hhd Evm)
        as [_ [_ [_ [_ Hr2]]]].
      cbn [map app]. rewrite <- Hr2, <- (IH es0 rest0 Hhd eq_refl). reflexivity.
    + inversion H; subst es rest'. reflexivity.
Qed.

Lemma take_mix_run_shape : forall r1 gm f e1 body rest es rest',
  head_mixGm r1 = Some (gm, f, e1, body) ->
  take_mix_run r1 rest = (es, rest') ->
  rest = map (fun e => orig_ruleGm f gm e body r1) es ++ rest'.
Proof.
  intros r1 gm f e1 body rest es rest' Hhd H.
  unfold take_mix_run in H. rewrite Hhd in H.
  destruct (take_mix_run_raw r1 rest) as [es0 rest0] eqn:Eraw.
  destruct (andb (forallb (melem_ok f) (e1 :: es0))
                 (all_disjoint (map melem_iv (e1 :: es0)))) eqn:Hgate.
  - inversion H; subst es rest'.
    apply (take_mix_run_raw_shape r1 gm f e1 body rest es0 rest0 Hhd Eraw).
  - inversion H; subst es rest'. reflexivity.
Qed.

(** When the gated run is nonempty, EVERY element (including [r1]'s [e1]) is
    representable — the fact the verdict bridge needs. *)
Lemma take_mix_run_melem_ok : forall r1 gm f e1 body rest es rest',
  head_mixGm r1 = Some (gm, f, e1, body) ->
  take_mix_run r1 rest = (es, rest') ->
  es <> [] ->
  forallb (melem_ok f) (e1 :: es) = true.
Proof.
  intros r1 gm f e1 body rest es rest' Hhd H Hne.
  unfold take_mix_run in H. rewrite Hhd in H.
  destruct (take_mix_run_raw r1 rest) as [es0 rest0] eqn:Eraw.
  destruct (andb (forallb (melem_ok f) (e1 :: es0))
                 (all_disjoint (map melem_iv (e1 :: es0)))) eqn:Hgate.
  - inversion H; subst es rest'.
    apply Bool.andb_true_iff in Hgate as [Hok _]. exact Hok.
  - inversion H; subst es rest'. contradiction.
Qed.

Fixpoint optimize_rules_mixedpointrangeguarded (fuel : nat) (n : nat) (d : set_decls) (rs : list rule)
  : nat * set_decls * list rule :=
  match fuel with
  | O => (n, d, rs)
  | S fuel' =>
    match rs with
    | r1 :: ((_ :: _) as rest) =>
        match head_mixGm r1 with
        | Some (gm, f, e1, body) =>
            match take_mix_run r1 rest with
            | ([], _) =>
                let '(n'', d'', rest') := optimize_rules_mixedpointrangeguarded fuel' n d rest in
                (n'', d'', r1 :: rest')
            | ((_ :: _) as es, rest') =>
                let name := setname n in
                let elems := map melem_iv (e1 :: es) in
                let d' := {| sd_sets := (name, elems) :: sd_sets d;
                             sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
                let merged := merged_ruleGs f gm name body r1 in
                let '(n'', d'', rest'') := optimize_rules_mixedpointrangeguarded fuel' (S n) d' rest' in
                (n'', d'', merged :: rest'')
            end
        | None =>
            let '(n'', d'', rest') := optimize_rules_mixedpointrangeguarded fuel' n d rest in
            (n'', d'', r1 :: rest')
        end
    | _ => (n, d, rs)
    end
  end.

Definition optimize_chain_mixedpointrangeguarded (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n', d', rs') := optimize_rules_mixedpointrangeguarded (length (c_rules c)) n d (c_rules c) in
  (n', d', {| c_policy := c_policy c; c_rules := rs' |}).

Lemma optimize_rules_mixedpointrangeguarded_consSS : forall fuel n d r1 r2 rest,
  optimize_rules_mixedpointrangeguarded (S fuel) n d (r1 :: r2 :: rest) =
  match head_mixGm r1 with
  | Some (gm, f, e1, body) =>
      match take_mix_run r1 (r2 :: rest) with
      | ([], _) =>
          let '(n'', d'', rest') := optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest) in
          (n'', d'', r1 :: rest')
      | ((_ :: _) as es, rest') =>
          let name := setname n in
          let elems := map melem_iv (e1 :: es) in
          let d' := {| sd_sets := (name, elems) :: sd_sets d;
                       sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
          let merged := merged_ruleGs f gm name body r1 in
          let '(n'', d'', rest'') := optimize_rules_mixedpointrangeguarded fuel (S n) d' rest' in
          (n'', d'', merged :: rest'')
      end
  | None =>
      let '(n'', d'', rest') := optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest) in
      (n'', d'', r1 :: rest')
  end.
Proof. reflexivity. Qed.

(** *** Structural invariants (mint [setname]s only; vmaps/maps untouched). *)
Lemma optimize_rules_mixedpointrangeguarded_mono : forall fuel n d rs n' d' rs',
  optimize_rules_mixedpointrangeguarded fuel n d rs = (n', d', rs') -> n <= n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; lia.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; lia.
    + cbn in H. inversion H; subst; lia.
    + rewrite optimize_rules_mixedpointrangeguarded_consSS in H.
      destruct (head_mixGm r1) as [[[[gm f] e1] body] |] eqn:Ehd.
      * destruct (take_mix_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_mixedpointrangeguarded fuel (S n) _ rest') as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n'.
           assert (S n <= m'')
             by (eapply (IH (S n) _ rest'); symmetry; exact Erec). lia.
      * remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_mixedpointrangeguarded_vmaps : forall fuel n d rs n' d' rs',
  optimize_rules_mixedpointrangeguarded fuel n d rs = (n', d', rs') -> sd_vmaps d' = sd_vmaps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_mixedpointrangeguarded_consSS in H.
      destruct (head_mixGm r1) as [[[[gm f] e1] body] |] eqn:Ehd.
      * destruct (take_mix_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_mixedpointrangeguarded fuel (S n)
                       {| sd_sets := (setname n, map melem_iv (e1 :: e :: es')) :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_mixedpointrangeguarded_maps : forall fuel n d rs n' d' rs',
  optimize_rules_mixedpointrangeguarded fuel n d rs = (n', d', rs') -> sd_maps d' = sd_maps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_mixedpointrangeguarded_consSS in H.
      destruct (head_mixGm r1) as [[[[gm f] e1] body] |] eqn:Ehd.
      * destruct (take_mix_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_mixedpointrangeguarded fuel (S n)
                       {| sd_sets := (setname n, map melem_iv (e1 :: e :: es')) :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_mixedpointrangeguarded_keys_bound : forall fuel n d rs n' d' rs' k,
  optimize_rules_mixedpointrangeguarded fuel n d rs = (n', d', rs') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' k H Hin.
  - cbn in H. inversion H; subst. left; exact Hin.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst. left; exact Hin.
    + cbn in H. inversion H; subst. left; exact Hin.
    + rewrite optimize_rules_mixedpointrangeguarded_consSS in H.
      destruct (head_mixGm r1) as [[[[gm f] e1] body] |] eqn:Ehd.
      * destruct (take_mix_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
        -- cbv zeta in H.
           remember (optimize_rules_mixedpointrangeguarded fuel (S n)
                       {| sd_sets := (setname n, map melem_iv (e1 :: e :: es')) :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'.
           destruct (IH (S n) _ rest' m'' dd'' rr'' k (eq_sym Erec) Hin) as [Hin_dn | Hlt].
           ++ cbn [sd_sets map] in Hin_dn. destruct Hin_dn as [Heq | Hin_d].
              ** apply setname_inj in Heq. subst k. right.
                 pose proof (optimize_rules_mixedpointrangeguarded_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec)). lia.
              ** left; exact Hin_d.
           ++ right; exact Hlt.
      * remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
        subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
Qed.

Lemma optimize_rules_mixedpointrangeguarded_assoc_stable : forall fuel n d rs n' d' rs' nm X,
  optimize_rules_mixedpointrangeguarded fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X = assoc_str nm (sd_sets d) X.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' nm X H Hnm.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_mixedpointrangeguarded_consSS in H.
      destruct (head_mixGm r1) as [[[[gm f] e1] body] |] eqn:Ehd.
      * destruct (take_mix_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
        -- cbv zeta in H.
           remember (optimize_rules_mixedpointrangeguarded fuel (S n)
                       {| sd_sets := (setname n, map melem_iv (e1 :: e :: es')) :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           erewrite (IH (S n) _ rest'); [ | symmetry; exact Erec | intros k Hk; apply Hnm; lia ].
           cbn [sd_sets assoc_str].
           destruct (String.eqb nm (setname n)) eqn:Eqn.
           ++ apply String.eqb_eq in Eqn. exfalso. apply (Hnm n); [lia | exact Eqn].
           ++ reflexivity.
      * remember (optimize_rules_mixedpointrangeguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
        eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
Qed.

(** *** Chain-level structural wrappers. *)
Lemma optimize_chain_mixedpointrangeguarded_mono : forall n d c n' d' c',
  optimize_chain_mixedpointrangeguarded n d c = (n', d', c') -> n <= n'.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_mixedpointrangeguarded in H.
  destruct (optimize_rules_mixedpointrangeguarded (length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_mixedpointrangeguarded_mono _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_mixedpointrangeguarded_vmaps : forall n d c n' d' c',
  optimize_chain_mixedpointrangeguarded n d c = (n', d', c') -> sd_vmaps d' = sd_vmaps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_mixedpointrangeguarded in H.
  destruct (optimize_rules_mixedpointrangeguarded (length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_mixedpointrangeguarded_vmaps _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_mixedpointrangeguarded_maps : forall n d c n' d' c',
  optimize_chain_mixedpointrangeguarded n d c = (n', d', c') -> sd_maps d' = sd_maps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_mixedpointrangeguarded in H.
  destruct (optimize_rules_mixedpointrangeguarded (length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_mixedpointrangeguarded_maps _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_mixedpointrangeguarded_keys_bound : forall n d c n' d' c' k,
  optimize_chain_mixedpointrangeguarded n d c = (n', d', c') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  intros n d c n' d' c' k H Hin. unfold optimize_chain_mixedpointrangeguarded in H.
  destruct (optimize_rules_mixedpointrangeguarded (length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  apply (optimize_rules_mixedpointrangeguarded_keys_bound _ _ _ _ _ _ _ k E Hin).
Qed.
