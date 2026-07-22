(** * Optimize_ConcatGuarded: concat-set merge over a transport key GUARDED by an
    implicit meta match (`ip saddr . tcp dport { … }`).

    [Optimize_Concat]'s N-way pass folds a run of rules whose bodies are exactly two
    adjacent [MCmp] head matches ([f1; f2]) into one [MConcatSet [f1;f2]] lookup.
    But a transport selector like `tcp dport` is lowered by the frontend WITH its
    implicit L4-protocol dependency: `ip saddr X tcp dport Y` becomes the THREE-item
    body [MCmp ip_saddr X; MCmp meta_l4proto 6; MCmp tcp_dport Y] — the l4proto guard
    sits BETWEEN the two concat selectors, so [head_value2] never sees two adjacent
    selectors and the pass under-consolidates.

    This module handles that shape.  It recognises a run

        [ MCmp f1 CEq a_i ; GUARD ; MCmp f2 CEq b_i ] ++ rest        (i = 1..N)

    where GUARD is a SHARED matchcond ([MCmp meta_l4proto proto], the l4proto
    dependency), and folds it — exactly as `nft --optimize` does — into ONE rule

        [ GUARD ; MConcatSet [f1;f2] false __setN ] ++ rest

    i.e. the guard is HOISTED to the head (matching nft's netlink output: the
    `[ meta load l4proto ][ cmp eq reg1 proto ]` precedes the `[ lookup ]`), and the
    two selectors become the concat key over the N packed tuples.

    Verdict-preservation reuses the family-agnostic state-fold collapse
    [Optimize_MutEnv.eval_rules_mut_st_run_collapse] and the
    N-way concat membership certificate [concat_two_fields_certificate_N] from
    [Optimize_Concat] VERBATIM — the guard is a pure conjunctive match, transparent to
    loadability/outcome and factored out of the [existsb] by boolean algebra, so it
    needs no new certificate.  Axiom-free. *)

From Stdlib Require Import List PeanoNat Bool Lia Wellfounded Arith.Wf_nat Btauto.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Optimize Optimize_ValueSet Optimize_Concat.
Import ListNotations.
Local Open Scope nat_scope.

(** The guarded original / merged rule shells.  [gm] is the shared guard matchcond
    (kept ABSTRACT — every lemma below is guard-agnostic; the recogniser pins it to
    the l4proto dependency for nft fidelity). *)
Definition orig_rule2g (f1 f2 : field) (gm : matchcond) (a b : data)
    (body : list body_item) (r1 : rule) : rule :=
  mk_head (MCmp f1 CEq a) (BMatch gm :: BMatch (MCmp f2 CEq b) :: body) r1.

Definition merged_rule2g (f1 f2 : field) (gm : matchcond) (name : String.string)
    (body : list body_item) (r1 : rule) : rule :=
  mk_head gm (BMatch (MConcatSet [f1; f2] false name) :: body) r1.

(** [guard_ok gm]: the recogniser only fires when [gm] is the l4proto dependency
    (`meta l4proto <proto>`), so the pass consolidates EXACTLY the transport-keyed
    concats `nft -o` does — not an arbitrary shared middle match. *)
Definition guard_ok (gm : matchcond) : bool :=
  match gm with
  | MCmp FMetaL4proto CEq _ => true
  | _ => false
  end.

(** *** Recogniser: a guarded two-selector head. *)
Definition head_value2g (r : rule)
  : option (field * data * matchcond * field * data * list body_item) :=
  match r_body r with
  | BMatch (MCmp f1 CEq a) :: BMatch gm :: BMatch (MCmp f2 CEq b) :: rest =>
      Some (f1, a, gm, f2, b, rest)
  | _ => None
  end.

Lemma head_value2g_rbody : forall r f1 a gm f2 b body,
  head_value2g r = Some (f1, a, gm, f2, b, body) ->
  r_body r = BMatch (MCmp f1 CEq a) :: BMatch gm :: BMatch (MCmp f2 CEq b) :: body.
Proof.
  intros r f1 a gm f2 b body H. unfold head_value2g in H.
  destruct (r_body r) as [| [m | s] tl] eqn:Eb; try discriminate.
  destruct m as [ | | | | g op u | | | | | | | | ]; try discriminate.
  destruct op; try discriminate.
  destruct tl as [| [m2 | s2] tl2]; try discriminate.
  destruct tl2 as [| [m3 | s3] tl3]; try discriminate.
  destruct m3 as [ | | | | g3 op3 u3 | | | | | | | | ]; try discriminate.
  destruct op3; try discriminate. inversion H; subst. reflexivity.
Qed.

Lemma head_value2g_canon : forall r f1 a gm f2 b body,
  head_value2g r = Some (f1, a, gm, f2, b, body) ->
  r = orig_rule2g f1 f2 gm a b body r.
Proof.
  intros r f1 a gm f2 b body H.
  pose proof (head_value2g_rbody r f1 a gm f2 b body H) as Hb.
  unfold orig_rule2g, mk_head. rewrite <- Hb. destruct r; reflexivity.
Qed.

(** Two guarded rules form an eligible CONCAT-merge pair iff their heads are
    [MCmp f1 CEq a_i] / GUARD / [MCmp f2 CEq b_i] over the SAME two fixed-width fields
    and the SAME guard (l4proto dependency), with the SAME tail, the SAME end-fields,
    and DISTINCT tuples. *)
Definition concat_mergeg_pair (r1 r2 : rule)
  : option (field * field * matchcond * data * data * data * data * list body_item) :=
  (* EFFECT-SAFETY GUARD — see [Optimize_ValueSet.value_merge_pair]. *)
  if negb (rule_mutfree r1) then None else
  match head_value2g r1, head_value2g r2 with
  | Some (f1, a1, gm1, g1, b1, rest1), Some (f2, a2, gm2, g2, b2, rest2) =>
      if field_eq_dec f1 f2 then
      if field_eq_dec g1 g2 then
      if matchcond_eq_dec gm1 gm2 then
      if guard_ok gm1 then
      if list_eq_dec body_item_eq_dec rest1 rest2 then
      match field_fixed_len f1, field_fixed_len g1 with
      | Some lf, Some lg =>
        if Nat.eq_dec lf (length a1) then
        if Nat.eq_dec lf (length a2) then
        if Nat.eq_dec lg (length b1) then
        if Nat.eq_dec lg (length b2) then
        if (if list_eq_dec Nat.eq_dec a1 a2 then
              if list_eq_dec Nat.eq_dec b1 b2 then true else false
            else false)
        then None
        else
        if rule_end_eqb r1 r2
        then Some (f1, g1, gm1, a1, b1, a2, b2, rest1)
        else None
        else None else None else None else None
      | _, _ => None
      end
      else None else None else None else None else None
  | _, _ => None
  end.

(** The guard, extracted: a fired pair certifies its canonical rule write-free. *)
Lemma concat_mergeg_pair_mutfree : forall r1 r2 x,
  concat_mergeg_pair r1 r2 = Some x -> rule_mutfree r1 = true.
Proof.
  intros r1 r2 x H. unfold concat_mergeg_pair in H.
  destruct (rule_mutfree r1); [reflexivity | discriminate H].
Qed.

(** When it fires, both inputs are EXACTLY the guarded [orig_rule2g] shells over the
    same two fixed-width fields and guard. *)
Lemma concat_mergeg_pair_shape : forall r1 r2 f1 f2 gm a1 b1 a2 b2 body,
  concat_mergeg_pair r1 r2 = Some (f1, f2, gm, a1, b1, a2, b2, body) ->
  r1 = orig_rule2g f1 f2 gm a1 b1 body r1 /\
  r2 = orig_rule2g f1 f2 gm a2 b2 body r1 /\
  field_fixed_len f1 = Some (length a1) /\ field_fixed_len f1 = Some (length a2) /\
  field_fixed_len f2 = Some (length b1) /\ field_fixed_len f2 = Some (length b2).
Proof.
  intros r1 r2 f1 f2 gm a1 b1 a2 b2 body H. unfold concat_mergeg_pair in H.
  destruct (negb (rule_mutfree r1)); [discriminate |].
  destruct (head_value2g r1) as [[[[[[fa1 ua1] gm1] ga1] ub1] s1] |] eqn:H1; [| discriminate].
  destruct (head_value2g r2) as [[[[[[fa2 ua2] gm2] ga2] ub2] s2] |] eqn:H2; [| discriminate].
  destruct (field_eq_dec fa1 fa2) as [Ef |]; [| discriminate]. subst fa2.
  destruct (field_eq_dec ga1 ga2) as [Eg |]; [| discriminate]. subst ga2.
  destruct (matchcond_eq_dec gm1 gm2) as [Egm |]; [| discriminate]. subst gm2.
  destruct (guard_ok gm1) eqn:Egok; [| discriminate].
  destruct (list_eq_dec body_item_eq_dec s1 s2) as [Es |]; [| discriminate]. subst s2.
  destruct (field_fixed_len fa1) as [lf |] eqn:Hfxf; [| discriminate].
  destruct (field_fixed_len ga1) as [lg |] eqn:Hfxg; [| discriminate].
  destruct (Nat.eq_dec lf (length ua1)) as [Elf1 |]; [| discriminate].
  destruct (Nat.eq_dec lf (length ua2)) as [Elf2 |]; [| discriminate].
  destruct (Nat.eq_dec lg (length ub1)) as [Elg1 |]; [| discriminate].
  destruct (Nat.eq_dec lg (length ub2)) as [Elg2 |]; [| discriminate].
  destruct (if list_eq_dec Nat.eq_dec ua1 ua2 then
              if list_eq_dec Nat.eq_dec ub1 ub2 then true else false else false);
    [discriminate |].
  destruct (rule_end_eqb r1 r2) eqn:Eeqb; [| discriminate].
  inversion H; subst f1 f2 gm a1 b1 a2 b2 body. clear H.
  pose proof (head_value2g_canon r1 fa1 ua1 gm1 ga1 ub1 s1 H1) as Hr1.
  pose proof (head_value2g_canon r2 fa1 ua2 gm1 ga1 ub2 s1 H2) as Hr2c.
  pose proof (proj1 (rule_end_eqb_mk_head (MCmp fa1 CEq ua1)
                       (BMatch gm1 :: BMatch (MCmp ga1 CEq ub1) :: s1) r1 r2) Eeqb) as Eshell.
  split; [exact Hr1 |].
  split.
  - rewrite Hr2c. unfold orig_rule2g in Eshell |- *.
    unfold mk_head in Eshell |- *.
    injection Eshell as Eo Eaf.
    rewrite Eo, Eaf. reflexivity.
  - rewrite Hfxf, Hfxg. repeat split; f_equal; congruence.
Qed.

Lemma concat_mergeg_pair_with_head : forall r1 r2 f1 a1 gm f2 b1 body
    fa fb gmm aa bb a2 b2 body2,
  head_value2g r1 = Some (f1, a1, gm, f2, b1, body) ->
  concat_mergeg_pair r1 r2 = Some (fa, fb, gmm, aa, bb, a2, b2, body2) ->
  fa = f1 /\ fb = f2 /\ gmm = gm /\ aa = a1 /\ bb = b1 /\ body2 = body /\
  r2 = orig_rule2g f1 f2 gm a2 b2 body r1 /\
  field_fixed_len f1 = Some (length a2) /\ field_fixed_len f2 = Some (length b2).
Proof.
  intros r1 r2 f1 a1 gm f2 b1 body fa fb gmm aa bb a2 b2 body2 Hhd Hvm.
  destruct (concat_mergeg_pair_shape r1 r2 fa fb gmm aa bb a2 b2 body2 Hvm)
    as [Hr1 [Hr2 [_ [Hx2 [_ Hx4]]]]].
  assert (Hhd' : head_value2g r1 = Some (fa, aa, gmm, fb, bb, body2)).
  { rewrite Hr1 at 1. unfold head_value2g, orig_rule2g, mk_head. cbn [r_body]. reflexivity. }
  rewrite Hhd in Hhd'. inversion Hhd'; subst fa aa gmm fb bb body2.
  repeat split; try assumption.
Qed.

(** ** Loadability / outcome / applies of the guarded shells. *)

(** The guard factors out of the [existsb] over the run. *)
Lemma existsb_guard_factor : forall (A : Type) (c1 c2 : A -> bool) (G W : bool) (l : list A),
  existsb (fun x => andb (andb (andb (c1 x) G) (c2 x)) W) l
  = andb (andb G (existsb (fun x => andb (c1 x) (c2 x)) l)) W.
Proof.
  induction l as [| a l IH]; intros; cbn [existsb]; [ btauto |].
  rewrite IH. btauto.
Qed.

(** ** Executable N-WAY guarded concat pass (fuel-driven, mirroring concat). *)

Fixpoint take_concatg_run (r1 : rule) (rest : list rule)
  : list (data * data) * list rule :=
  match rest with
  | [] => ([], [])
  | r2 :: tl =>
      match concat_mergeg_pair r1 r2 with
      | Some (_, _, _, _, _, a2, b2, _) =>
          let '(ts, rest') := take_concatg_run r1 tl in ((a2, b2) :: ts, rest')
      | None => ([], rest)
      end
  end.

Fixpoint optimize_rules_concatguarded (fuel n : nat) (d : set_decls) (rs : list rule)
  : nat * set_decls * list rule :=
  match fuel with
  | O => (n, d, rs)
  | S fuel' =>
    match rs with
    | r1 :: ((_ :: _) as rest) =>
        match head_value2g r1 with
        | Some (f1, a1, gm, f2, b1, body) =>
            match take_concatg_run r1 rest with
            | ([], _) =>
                let '(n'', d'', rest') := optimize_rules_concatguarded fuel' n d rest in
                (n'', d'', r1 :: rest')
            | ((_ :: _) as ts, rest') =>
                let name := setname n in
                let tuples := (a1, b1) :: ts in
                let d' := {| sd_sets := (name, map pack_tuple tuples) :: sd_sets d;
                             sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
                let merged := merged_rule2g f1 f2 gm name body r1 in
                let '(n'', d'', rest'') := optimize_rules_concatguarded fuel' (S n) d' rest' in
                (n'', d'', merged :: rest'')
            end
        | None =>
            let '(n'', d'', rest') := optimize_rules_concatguarded fuel' n d rest in
            (n'', d'', r1 :: rest')
        end
    | _ => (n, d, rs)
    end
  end.

Definition optimize_chain_concatguarded (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n', d', rs') := optimize_rules_concatguarded (length (c_rules c)) n d (c_rules c) in
  (n', d', {| c_policy := c_policy c; c_rules := rs' |}).

Lemma optimize_rules_concatguarded_consSS : forall fuel n d r1 r2 rest,
  optimize_rules_concatguarded (S fuel) n d (r1 :: r2 :: rest) =
  match head_value2g r1 with
  | Some (f1, a1, gm, f2, b1, body) =>
      match take_concatg_run r1 (r2 :: rest) with
      | ([], _) =>
          let '(n'', d'', rest') := optimize_rules_concatguarded fuel n d (r2 :: rest) in
          (n'', d'', r1 :: rest')
      | ((_ :: _) as ts, rest') =>
          let name := setname n in
          let tuples := (a1, b1) :: ts in
          let d' := {| sd_sets := (name, map pack_tuple tuples) :: sd_sets d;
                       sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
          let merged := merged_rule2g f1 f2 gm name body r1 in
          let '(n'', d'', rest'') := optimize_rules_concatguarded fuel (S n) d' rest' in
          (n'', d'', merged :: rest'')
      end
  | None =>
      let '(n'', d'', rest') := optimize_rules_concatguarded fuel n d (r2 :: rest) in
      (n'', d'', r1 :: rest')
  end.
Proof. reflexivity. Qed.

(** The matched run is exactly the guarded shells over its tuples. *)
Lemma take_concatg_run_shape : forall r1 f1 a1 gm f2 b1 body rest ts rest',
  head_value2g r1 = Some (f1, a1, gm, f2, b1, body) ->
  take_concatg_run r1 rest = (ts, rest') ->
  rest = map (fun ab => orig_rule2g f1 f2 gm (fst ab) (snd ab) body r1) ts ++ rest'
  /\ (forall a b, In (a, b) ts -> field_fixed_len f1 = Some (length a))
  /\ (forall a b, In (a, b) ts -> field_fixed_len f2 = Some (length b)).
Proof.
  intros r1 f1 a1 gm f2 b1 body rest. induction rest as [| r2 tl IH]; intros ts rest' Hhd H.
  - cbn in H. inversion H; subst.
    split; [ reflexivity | split; intros a b []].
  - cbn in H. destruct (concat_mergeg_pair r1 r2)
      as [[[[[[[[fa fb] gmm] aa] bb] a2] b2] bd] |] eqn:Evm.
    + destruct (take_concatg_run r1 tl) as [ts0 rest0] eqn:Erec.
      inversion H; subst ts rest'. clear H.
      destruct (concat_mergeg_pair_with_head r1 r2 f1 a1 gm f2 b1 body
                  fa fb gmm aa bb a2 b2 bd Hhd Evm)
        as [_ [_ [_ [_ [_ [_ [Hr2 [Hfx1 Hfx2]]]]]]]].
      destruct (IH ts0 rest0 Hhd eq_refl) as [Hsplit [Hall1 Hall2]].
      repeat split.
      * cbn [map app fst snd]. rewrite <- Hr2, <- Hsplit. reflexivity.
      * intros a b [Hab | Hin]; [ inversion Hab; subst; exact Hfx1 | apply (Hall1 a b Hin) ].
      * intros a b [Hab | Hin]; [ inversion Hab; subst; exact Hfx2 | apply (Hall2 a b Hin) ].
    + inversion H; subst ts rest'.
      split; [ reflexivity | split; intros a b []].
Qed.

Lemma take_concatg_run_head_width : forall r1 f1 a1 gm f2 b1 body r2 rest ts rest',
  head_value2g r1 = Some (f1, a1, gm, f2, b1, body) ->
  take_concatg_run r1 (r2 :: rest) = (ts, rest') ->
  ts <> [] ->
  field_fixed_len f1 = Some (length a1) /\ field_fixed_len f2 = Some (length b1).
Proof.
  intros r1 f1 a1 gm f2 b1 body r2 rest ts rest' Hhd Hrun Hne.
  cbn in Hrun. destruct (concat_mergeg_pair r1 r2)
    as [[[[[[[[fa fb] gmm] aa] bb] a2] b2] bd] |] eqn:Evm.
  - destruct (concat_mergeg_pair_shape r1 r2 fa fb gmm aa bb a2 b2 bd Evm)
      as [Hr1 [_ [Hx1 [_ [Hx3 _]]]]].
    assert (Hhd' : head_value2g r1 = Some (fa, aa, gmm, fb, bb, bd)).
    { rewrite Hr1 at 1. unfold head_value2g, orig_rule2g, mk_head. cbn [r_body]. reflexivity. }
    rewrite Hhd in Hhd'. inversion Hhd'; subst fa aa gmm fb bb bd. split; assumption.
  - destruct (take_concatg_run r1 rest) as [ts0 rest0] eqn:Erec0.
    inversion Hrun; subst. contradiction.
Qed.

(** *** Freshness bookkeeping: the pass only PREPENDS [sd_sets] entries keyed by
    [setname k] with [n <= k < n']. *)
Lemma optimize_rules_concatguarded_assoc_stable : forall fuel n d rs n' d' rs' nm X,
  optimize_rules_concatguarded fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X = assoc_str nm (sd_sets d) X.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' nm X H Hnm.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_concatguarded_consSS in H.
      destruct (head_value2g r1) as [[[[[[f1 a1] gm] f2] b1] body] |] eqn:Ehd.
      * destruct (take_concatg_run r1 (r2 :: rest)) as [ts rest'] eqn:Erun.
        destruct ts as [| t ts'].
        -- remember (optimize_rules_concatguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
        -- cbv zeta in H.
           remember (optimize_rules_concatguarded fuel (S n)
                       {| sd_sets := (setname n, map pack_tuple ((a1,b1) :: t :: ts'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           erewrite (IH (S n) _ rest'); [ | symmetry; exact Erec | intros k Hk; apply Hnm; lia ].
           cbn [sd_sets assoc_str].
           destruct (String.eqb nm (setname n)) eqn:Eqn.
           ++ apply String.eqb_eq in Eqn. exfalso. apply (Hnm n); [lia | exact Eqn].
           ++ reflexivity.
      * remember (optimize_rules_concatguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
        eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
Qed.
