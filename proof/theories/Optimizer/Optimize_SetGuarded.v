(** * Optimize_SetGuarded: single-field value->set merge GUARDED by an implicit meta match
    (`tcp dport { … }` / `udp dport { … }` / `tcp sport …`).

    [Optimize_ValueSet]'s N-way [valueset] pass folds a run of rules whose bodies begin with
    a differing [MCmp f CEq v] HEAD into one [MConcatSet [f] false __setN] lookup.  But
    a bare transport selector like `tcp dport` is lowered by the frontend WITH its
    implicit L4-protocol dependency: `tcp dport Y` becomes the TWO-item body
    [MCmp meta_l4proto proto ; MCmp tcp_dport Y] — the l4proto guard sits BEFORE the
    port cmp, so [head_value] sees the guard (a value SHARED across the run, so
    [value_merge_pair] rejects it as an equal-value pair) and the merge never fires.

    This module handles that shape.  It recognises a run

        [ GUARD ; MCmp f CEq v_i ] ++ rest        (i = 1..N)

    where GUARD is a SHARED matchcond ([MCmp meta_l4proto proto], the l4proto
    dependency), and folds it — exactly as `nft --optimize` does — into ONE rule

        [ GUARD ; MConcatSet [f] false __setN ] ++ rest

    i.e. the guard is KEPT at the head (matching nft's netlink output: the
    `[ meta load l4proto ][ cmp eq proto ]` precedes the `[ lookup ]`), and the single
    selector becomes the set key over the N discrete point values.  The synthesised
    set is [map (fun v => (v,v)) vals] — exactly the encoding [valueset] emits (nft keeps
    the values discrete, never range-coalesced).

    Verdict-preservation reuses the family-agnostic state-fold collapse
    [Optimize_MutEnv.eval_rules_flat_run_collapse] and the
    N-element single-field membership certificate [concat_set_existsb] from
    [Optimize_ValueSet] VERBATIM — the guard is a pure conjunctive match at the head,
    transparent to loadability/outcome and factored out of the [existsb] by boolean
    algebra, so it needs no new certificate.  Axiom-free. *)

From Stdlib Require Import List PeanoNat Bool Lia Btauto.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Optimize Optimize_ValueSet Optimize_Concat Optimize_ConcatGuarded.
Import ListNotations.
Local Open Scope nat_scope.

(** [guard_okl2 gm]: the L2 counterpart of [Optimize_ConcatGuarded.guard_ok].  A bare
    link-layer selector `ether saddr X` / `ether daddr X` is lowered by the frontend
    (in every family whose interfaces are not guaranteed ethernet — ip/ip6/inet/netdev)
    WITH an implicit `meta iiftype == ARPHRD_ETHER (1)` dependency prepended: the body
    becomes [MCmp FMetaIiftype CEq [0;1] ; MCmp FEtherSaddr CEq v] (see
    [nft_lower.ml]'s [DIiftype] dep).  That guard sits BEFORE the address cmp — exactly
    the [Optimize_SetGuarded] guarded single-selector shape — so recognising it lets this
    same N-way value->set pass fold `ether saddr 00:11:.. accept; ether saddr 00:11:..
    accept` into `ether saddr { .., .. } accept`, precisely as `nft --optimize` does.

    The 6-byte MAC field [FEtherSaddr]/[FEtherDaddr] is [LPayload PLink 6/0 6], so
    [field_fixed_len] pins its width at [Some 6] — the exact same fixed-width side
    condition [value_mergeGs_pair] already demands of a transport port, and the reason
    the merge is sound (the [MCmp]'s prefix equality coincides with the set's full-width
    membership).  Distinct MAC literals are disjoint singletons, so the synthesised
    single-field rbtree set is a VALID nftables object (no overlapping-interval defect).

    Every lemma in this module is guard-AGNOSTIC (soundness never inspects [gm]); the
    guard whitelist is purely an nft-fidelity gate, so admitting the iiftype guard adds
    a new fold WITHOUT weakening any proof. *)
Definition guard_okl2 (gm : matchcond) : bool :=
  match gm with
  | MCmp FMetaIiftype CEq _ => true
  | _ => false
  end.

(** The guarded original / merged rule shells.  [gm] is the shared guard matchcond
    (kept ABSTRACT — every lemma below is guard-agnostic; the recogniser pins it to
    the l4proto dependency ([guard_ok]) or the L2 iiftype dependency ([guard_okl2])
    for nft fidelity). *)
Definition orig_ruleGs (f : field) (gm : matchcond) (v : data)
    (body : list body_item) (r1 : rule) : rule :=
  mk_head gm (BMatch (MCmp f CEq v) :: body) r1.

Definition merged_ruleGs (f : field) (gm : matchcond) (name : String.string)
    (body : list body_item) (r1 : rule) : rule :=
  mk_head gm (BMatch (MConcatSet [f] false name) :: body) r1.

(** *** Recogniser: a guarded single-selector head. *)
Definition head_valueGs (r : rule)
  : option (matchcond * field * data * list body_item) :=
  match r_body r with
  | BMatch gm :: BMatch (MCmp f CEq v) :: rest => Some (gm, f, v, rest)
  | _ => None
  end.

Lemma head_valueGs_rbody : forall r gm f v body,
  head_valueGs r = Some (gm, f, v, body) ->
  r_body r = BMatch gm :: BMatch (MCmp f CEq v) :: body.
Proof.
  intros r gm f v body H. unfold head_valueGs in H.
  destruct (r_body r) as [| [m | s] tl] eqn:Eb; try discriminate.
  destruct tl as [| [m2 | s2] tl2]; try discriminate.
  destruct m2 as [ | | | | g op u | | | | | | | | ]; try discriminate.
  destruct op; try discriminate. inversion H; subst. reflexivity.
Qed.

Lemma head_valueGs_canon : forall r gm f v body,
  head_valueGs r = Some (gm, f, v, body) ->
  r = orig_ruleGs f gm v body r.
Proof.
  intros r gm f v body H.
  pose proof (head_valueGs_rbody r gm f v body H) as Hb.
  unfold orig_ruleGs, mk_head. rewrite <- Hb. destruct r; reflexivity.
Qed.

(** Two guarded rules form an eligible value-set-merge pair iff their heads are
    GUARD / [MCmp f CEq v_i] over the SAME fixed-width field [f] and the SAME guard
    (l4proto dependency), with the SAME tail, the SAME end-fields, and DISTINCT
    values. *)
Definition value_mergeGs_pair (r1 r2 : rule)
  : option (matchcond * field * data * data * list body_item) :=
  (* EFFECT-SAFETY GUARD — see [Optimize_ValueSet.value_merge_pair]. *)
  if negb (rule_mutfree r1) then None else
  match head_valueGs r1, head_valueGs r2 with
  | Some (gm1, f1, v1, rest1), Some (gm2, f2, v2, rest2) =>
      if matchcond_eq_dec gm1 gm2 then
      if guard_ok gm1 || guard_okl2 gm1 then
      if field_eq_dec f1 f2 then
      if list_eq_dec body_item_eq_dec rest1 rest2 then
      if list_eq_dec Nat.eq_dec v1 v2 then None
      else
      match field_fixed_len f1 with
      | Some len =>
        if Nat.eq_dec len (length v1) then
        if Nat.eq_dec len (length v2) then
        if rule_end_eqb r1 r2
        then Some (gm1, f1, v1, v2, rest1)
        else None
        else None else None
      | None => None
      end
      else None else None else None else None
  | _, _ => None
  end.

(** The guard, extracted: a fired pair certifies its canonical rule write-free. *)
Lemma value_mergeGs_pair_mutfree : forall r1 r2 x,
  value_mergeGs_pair r1 r2 = Some x -> rule_mutfree r1 = true.
Proof.
  intros r1 r2 x H. unfold value_mergeGs_pair in H.
  destruct (rule_mutfree r1); [reflexivity | discriminate H].
Qed.

(** When it fires, both inputs are EXACTLY the guarded [orig_ruleGs] shells over the
    same field and guard. *)
Lemma value_mergeGs_pair_shape : forall r1 r2 gm f v1 v2 body,
  value_mergeGs_pair r1 r2 = Some (gm, f, v1, v2, body) ->
  r1 = orig_ruleGs f gm v1 body r1 /\
  r2 = orig_ruleGs f gm v2 body r1 /\
  field_fixed_len f = Some (length v1) /\ field_fixed_len f = Some (length v2).
Proof.
  intros r1 r2 gm f v1 v2 body H. unfold value_mergeGs_pair in H.
  destruct (negb (rule_mutfree r1)); [discriminate |].
  destruct (head_valueGs r1) as [[[[gm1 f1] u1] s1] |] eqn:H1; [| discriminate].
  destruct (head_valueGs r2) as [[[[gm2 f2] u2] s2] |] eqn:H2; [| discriminate].
  destruct (matchcond_eq_dec gm1 gm2) as [Egm |]; [| discriminate]. subst gm2.
  destruct (guard_ok gm1 || guard_okl2 gm1) eqn:Egok; [| discriminate].
  destruct (field_eq_dec f1 f2) as [Ef |]; [| discriminate]. subst f2.
  destruct (list_eq_dec body_item_eq_dec s1 s2) as [Es |]; [| discriminate]. subst s2.
  destruct (list_eq_dec Nat.eq_dec u1 u2) as [Eu |]; [discriminate |].
  destruct (field_fixed_len f1) as [len |] eqn:Hfx; [| discriminate].
  destruct (Nat.eq_dec len (length u1)) as [El1 |]; [| discriminate].
  destruct (Nat.eq_dec len (length u2)) as [El2 |]; [| discriminate].
  destruct (rule_end_eqb r1 r2) eqn:Eeqb; [| discriminate].
  inversion H; subst gm f v1 v2 body. clear H.
  pose proof (head_valueGs_canon r1 gm1 f1 u1 s1 H1) as Hr1.
  pose proof (head_valueGs_canon r2 gm1 f1 u2 s1 H2) as Hr2c.
  pose proof (proj1 (rule_end_eqb_mk_head gm1
                       (BMatch (MCmp f1 CEq u1) :: s1) r1 r2) Eeqb) as Eshell.
  split; [exact Hr1 |].
  split.
  - rewrite Hr2c. unfold orig_ruleGs in Eshell |- *.
    unfold mk_head in Eshell |- *.
    injection Eshell as Eo Eaf.
    rewrite Eo, Eaf. reflexivity.
  - rewrite Hfx. split; f_equal; congruence.
Qed.

Lemma value_mergeGs_pair_with_head : forall r1 r2 gm f v1 body
    gm' f' v1' v2 body',
  head_valueGs r1 = Some (gm, f, v1, body) ->
  value_mergeGs_pair r1 r2 = Some (gm', f', v1', v2, body') ->
  gm' = gm /\ f' = f /\ v1' = v1 /\ body' = body /\
  r2 = orig_ruleGs f gm v2 body r1 /\
  field_fixed_len f = Some (length v2).
Proof.
  intros r1 r2 gm f v1 body gm' f' v1' v2 body' Hhd Hvm.
  destruct (value_mergeGs_pair_shape r1 r2 gm' f' v1' v2 body' Hvm)
    as [Hr1 [Hr2 [_ Hx2]]].
  assert (Hhd' : head_valueGs r1 = Some (gm', f', v1', body')).
  { rewrite Hr1 at 1. unfold head_valueGs, orig_ruleGs, mk_head. cbn [r_body]. reflexivity. }
  rewrite Hhd in Hhd'. inversion Hhd'; subst gm' f' v1' body'.
  repeat split; try assumption.
Qed.

(** ** Loadability / outcome / applies of the guarded shells. *)

(** The head guard factors out of the [existsb] over the run. *)
Lemma existsb_guardhead_factor : forall (A : Type) (c : A -> bool) (G W : bool) (l : list A),
  existsb (fun x => andb G (andb (c x) W)) l
  = andb G (andb (existsb (fun x => c x) l) W).
Proof.
  induction l as [| a l IH]; intros; cbn [existsb]; [ btauto |].
  rewrite IH. btauto.
Qed.

(** ** Executable N-WAY guarded single-field value->set pass (fuel-driven). *)

Fixpoint take_setg_run (r1 : rule) (rest : list rule)
  : list data * list rule :=
  match rest with
  | [] => ([], [])
  | r2 :: tl =>
      match value_mergeGs_pair r1 r2 with
      | Some (_, _, _, v2, _) =>
          let '(vs, rest') := take_setg_run r1 tl in (v2 :: vs, rest')
      | None => ([], rest)
      end
  end.

Fixpoint optimize_rules_setguarded (fuel n : nat) (d : set_decls) (rs : list rule)
  : nat * set_decls * list rule :=
  match fuel with
  | O => (n, d, rs)
  | S fuel' =>
    match rs with
    | r1 :: ((_ :: _) as rest) =>
        match head_valueGs r1 with
        | Some (gm, f, v1, body) =>
            match take_setg_run r1 rest with
            | ([], _) =>
                let '(n'', d'', rest') := optimize_rules_setguarded fuel' n d rest in
                (n'', d'', r1 :: rest')
            | ((_ :: _) as vs, rest') =>
                let name := setname n in
                let elems := map (fun v => (v, v)) (v1 :: vs) in
                let d' := {| sd_sets := (name, elems) :: sd_sets d;
                             sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
                let merged := merged_ruleGs f gm name body r1 in
                let '(n'', d'', rest'') := optimize_rules_setguarded fuel' (S n) d' rest' in
                (n'', d'', merged :: rest'')
            end
        | None =>
            let '(n'', d'', rest') := optimize_rules_setguarded fuel' n d rest in
            (n'', d'', r1 :: rest')
        end
    | _ => (n, d, rs)
    end
  end.

Definition optimize_chain_setguarded (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n', d', rs') := optimize_rules_setguarded (length (c_rules c)) n d (c_rules c) in
  (n', d', {| c_policy := c_policy c; c_rules := rs' |}).

Lemma optimize_rules_setguarded_consSS : forall fuel n d r1 r2 rest,
  optimize_rules_setguarded (S fuel) n d (r1 :: r2 :: rest) =
  match head_valueGs r1 with
  | Some (gm, f, v1, body) =>
      match take_setg_run r1 (r2 :: rest) with
      | ([], _) =>
          let '(n'', d'', rest') := optimize_rules_setguarded fuel n d (r2 :: rest) in
          (n'', d'', r1 :: rest')
      | ((_ :: _) as vs, rest') =>
          let name := setname n in
          let elems := map (fun v => (v, v)) (v1 :: vs) in
          let d' := {| sd_sets := (name, elems) :: sd_sets d;
                       sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
          let merged := merged_ruleGs f gm name body r1 in
          let '(n'', d'', rest'') := optimize_rules_setguarded fuel (S n) d' rest' in
          (n'', d'', merged :: rest'')
      end
  | None =>
      let '(n'', d'', rest') := optimize_rules_setguarded fuel n d (r2 :: rest) in
      (n'', d'', r1 :: rest')
  end.
Proof. reflexivity. Qed.

(** The matched run is exactly the guarded shells over its values. *)
Lemma take_setg_run_shape : forall r1 gm f v1 body rest vs rest',
  head_valueGs r1 = Some (gm, f, v1, body) ->
  take_setg_run r1 rest = (vs, rest') ->
  rest = map (fun v => orig_ruleGs f gm v body r1) vs ++ rest'
  /\ (forall v, In v vs -> field_fixed_len f = Some (length v)).
Proof.
  intros r1 gm f v1 body rest. induction rest as [| r2 tl IH]; intros vs rest' Hhd H.
  - cbn in H. inversion H; subst.
    split; [ reflexivity | intros v [] ].
  - cbn in H. destruct (value_mergeGs_pair r1 r2)
      as [[[[[gm2 f2] u1] v2] bd] |] eqn:Evm.
    + destruct (take_setg_run r1 tl) as [vs0 rest0] eqn:Erec.
      inversion H; subst vs rest'. clear H.
      destruct (value_mergeGs_pair_with_head r1 r2 gm f v1 body
                  gm2 f2 u1 v2 bd Hhd Evm)
        as [_ [_ [_ [_ [Hr2 Hfx]]]]].
      destruct (IH vs0 rest0 Hhd eq_refl) as [Hsplit Hall].
      split.
      * cbn [map app]. rewrite <- Hr2, <- Hsplit. reflexivity.
      * intros v [Hv | Hin]; [ subst v; exact Hfx | apply (Hall v Hin) ].
    + inversion H; subst vs rest'.
      split; [ reflexivity | intros v [] ].
Qed.

Lemma take_setg_run_head_width : forall r1 gm f v1 body r2 rest vs rest',
  head_valueGs r1 = Some (gm, f, v1, body) ->
  take_setg_run r1 (r2 :: rest) = (vs, rest') ->
  vs <> [] ->
  field_fixed_len f = Some (length v1).
Proof.
  intros r1 gm f v1 body r2 rest vs rest' Hhd Hrun Hne.
  cbn in Hrun. destruct (value_mergeGs_pair r1 r2)
    as [[[[[gm2 f2] u1] v2] bd] |] eqn:Evm.
  - destruct (value_mergeGs_pair_shape r1 r2 gm2 f2 u1 v2 bd Evm)
      as [Hr1 [_ [Hx1 _]]].
    assert (Hhd' : head_valueGs r1 = Some (gm2, f2, u1, bd)).
    { rewrite Hr1 at 1. unfold head_valueGs, orig_ruleGs, mk_head. cbn [r_body]. reflexivity. }
    rewrite Hhd in Hhd'. inversion Hhd'; subst gm2 f2 u1 bd. exact Hx1.
  - destruct (take_setg_run r1 rest) as [vs0 rest0] eqn:Erec0.
    inversion Hrun; subst. contradiction.
Qed.

(** *** Freshness bookkeeping: the pass only PREPENDS [sd_sets] entries keyed by
    [setname k] with [n <= k < n']. *)
Lemma optimize_rules_setguarded_assoc_stable : forall fuel n d rs n' d' rs' nm X,
  optimize_rules_setguarded fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X = assoc_str nm (sd_sets d) X.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' nm X H Hnm.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_setguarded_consSS in H.
      destruct (head_valueGs r1) as [[[[gm f] v1] body] |] eqn:Ehd.
      * destruct (take_setg_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct vs as [| v vs'].
        -- remember (optimize_rules_setguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
        -- cbv zeta in H.
           remember (optimize_rules_setguarded fuel (S n)
                       {| sd_sets := (setname n, map (fun v0 => (v0, v0)) (v1 :: v :: vs'))
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
      * remember (optimize_rules_setguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
        eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
Qed.
