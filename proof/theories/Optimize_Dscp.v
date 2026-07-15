(** * Optimize_Dscp: masked-payload value->set fold for `ip dscp` / `ip6 dscp`.

    Battery shape "dscp-masked-set":

        ip dscp 10 accept    ┐
        ip dscp 20 accept    ┘   =>   ip dscp { 10, 20 } accept

    The frontend lowers a single positive `ip dscp N` (a sub-byte header bitfield) to
    a MASKED-payload equality test (nft_lower.ml [bitfield_sel]):

        [ payload load 1b @ network header + 1 ]
        [ bitwise reg 1 = ( reg 1 & 0xfc ) ^ 0x00 ]
        [ cmp eq reg 1 (N << 2) ]                     -- [MMasked f false [0xfc] [0] v]

    i.e. `(field & 0xfc) == v` where `v = N << 2` (dscp is the top 6 bits of the TOS
    byte).  `nft --optimize` folds a run of such rules — SAME field, SAME mask, SAME
    xor, SAME verdict, differing exact value — into ONE `ip dscp { v1, v2, … }` rule,
    which nft compiles to the SAME masked load followed by a SET LOOKUP of the masked
    register value:

        [ payload load 1b ][ bitwise & 0xfc ][ lookup reg 1 set { v1, v2 } ]

    This module recognises the run and emits exactly that: ONE rule whose head is
    [MSetT f [TBitAnd mask xor] false __setN] — set membership of the TRANSFORMED
    (masked) field value — over the fresh N-element point set [map (v,v) vals].

    SOUNDNESS.  The masked field value [X = data_bitops (field_value f e p) mask xor] is
    the SAME operand in both the [MMasked] equality and the [MSetT] lookup (they share
    [apply_transforms [TBitAnd mask xor] = data_bitops _ mask xor]); membership of a
    point set [map (v,v) vals] is byte-equality [X = v] ([data_in_iv_point]), so the
    lookup is EXACTLY the [existsb] disjunction of the run's equalities — provided
    [length X = length v], which the fixed-width side condition [field_fixed_len f =
    Some len = len mask = len xor = len v] pins ([data_bitops_length_eq]).  The point
    set over DISTINCT dscp values is a VALID single-field rbtree set (disjoint
    singletons — no overlapping-interval defect), and nft compiles the fold to it, so
    the fold is both verdict-preserving AND a loadable nftables object.  Axiom-free. *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Optimize Optimize_Merge.
Import ListNotations.
Local Open Scope nat_scope.

(** ** Width lemma: [data_bitops] over three equal-length vectors keeps that length. *)
Lemma data_bitops_length_eq : forall a m x,
  length a = length m -> length m = length x ->
  length (data_bitops a m x) = length a.
Proof.
  induction a as [| ah a IH]; intros m x H1 H2; [reflexivity |].
  destruct m as [| mh m]; [discriminate |].
  destruct x as [| xh x]; [cbn in H2; discriminate |].
  cbn [data_bitops length] in *. injection H1 as H1. injection H2 as H2.
  rewrite (IH m x H1 H2). reflexivity.
Qed.

(** ** The N-element membership certificate.

    A point set [map (v,v) vals] matched by [MSetT f [TBitAnd mask xor] false name]
    (membership of the MASKED field value) is exactly the [existsb] disjunction of the
    run's [MMasked f false mask xor v] equalities — when the masked value's width
    equals each element's width (so [MMasked]'s [firstn]-truncated equality coincides
    with the set's full-width membership). *)
Lemma mmasked_set_existsb : forall f mask xor vals name e q,
  e_set e name = map (fun v => (v, v)) vals ->
  (forall v, In v vals -> field_loadable f q = true ->
     length (data_bitops (field_value f e q) mask xor) = length v) ->
  eval_matchcond (MSetT f [TBitAnd mask xor] false name) e q
  = existsb (fun v => eval_matchcond (MMasked f false mask xor v) e q) vals.
Proof.
  intros f mask xor vals name e q Hset Hlen.
  unfold eval_matchcond at 1, eval_matchcond_body at 1.
  cbn [match_loadable].
  destruct (field_loadable f q) eqn:Hld; cbn [andb].
  - (* loadable: set membership = existsb of the point equalities *)
    cbn [xorb]. unfold apply_transforms; cbn [fold_left apply_transform].
    set (X := data_bitops (field_value f e q) mask xor) in *.
    unfold set_mem. rewrite Hset. rewrite existsb_map_eq.
    apply existsb_ext. intros v Hv.
    rewrite data_in_iv_point.
    (* RHS term: eval_matchcond (MMasked ..) e q = firstn-eq on X *)
    unfold eval_matchcond, eval_matchcond_body. cbn [match_loadable]. rewrite Hld.
    cbn [andb eval_cmp]. fold X.
    assert (Hl : length X = length v) by (apply (Hlen v Hv eq_refl)).
    rewrite <- Hl, List.firstn_all. apply data_eqb_sym.
  - (* not loadable: both sides false *)
    symmetry. apply existsb_false_forall. intros v Hv.
    unfold eval_matchcond, eval_matchcond_body. cbn [match_loadable]. rewrite Hld.
    reflexivity.
Qed.

(** ** Recogniser: a masked-equality head [BMatch (MMasked f false mask xor v) :: rest]. *)
Definition head_dscp (r : rule)
  : option (field * data * data * data * list body_item) :=
  match r_body r with
  | BMatch (MMasked f false mask xor v) :: rest => Some (f, mask, xor, v, rest)
  | _ => None
  end.

Lemma head_dscp_rbody : forall r f mask xor v body,
  head_dscp r = Some (f, mask, xor, v, body) ->
  r_body r = BMatch (MMasked f false mask xor v) :: body.
Proof.
  intros r f mask xor v body H. unfold head_dscp in H.
  destruct (r_body r) as [| [m | s] tl] eqn:Eb; try discriminate.
  destruct m as [ | | | g neg mask' xor' v' | | | | | | | | | ]; try discriminate.
  destruct neg; try discriminate.
  inversion H; subst. reflexivity.
Qed.

Lemma head_dscp_canon : forall r f mask xor v body,
  head_dscp r = Some (f, mask, xor, v, body) ->
  r = mk_head (MMasked f false mask xor v) body r.
Proof.
  intros r f mask xor v body H.
  pose proof (head_dscp_rbody r f mask xor v body H) as Hb.
  unfold mk_head. rewrite <- Hb. destruct r; reflexivity.
Qed.

(** Two rules form an eligible masked-value merge pair iff both heads are
    [MMasked f false mask xor v_i] over the SAME fixed-width field [f], the SAME mask
    and xor (each of the field's fixed width), the SAME tail, the SAME end-fields, and
    DISTINCT values (also of that width).  Returns [(f, mask, xor, v1, v2, body)]. *)
Definition dscp_merge_pair (r1 r2 : rule)
  : option (field * data * data * data * data * list body_item) :=
  match head_dscp r1, head_dscp r2 with
  | Some (f1, m1, x1, u1, rest1), Some (f2, m2, x2, u2, rest2) =>
      if field_eq_dec f1 f2 then
      if list_eq_dec Nat.eq_dec m1 m2 then
      if list_eq_dec Nat.eq_dec x1 x2 then
      if list_eq_dec body_item_eq_dec rest1 rest2 then
      if list_eq_dec Nat.eq_dec u1 u2 then None
      else
      match field_fixed_len f1 with
      | Some len =>
        if Nat.eq_dec len (length m1) then
        if Nat.eq_dec len (length x1) then
        if Nat.eq_dec len (length u1) then
        if Nat.eq_dec len (length u2) then
        if rule_end_eqb r1 r2
        then Some (f1, m1, x1, u1, u2, rest1)
        else None
        else None else None else None else None
      | None => None
      end
      else None else None else None else None
  | _, _ => None
  end.

(** When it fires, both inputs are the canonical masked-head shells and every width
    side condition holds. *)
Lemma dscp_merge_pair_shape : forall r1 r2 f mask xor v1 v2 body,
  dscp_merge_pair r1 r2 = Some (f, mask, xor, v1, v2, body) ->
  r1 = mk_head (MMasked f false mask xor v1) body r1 /\
  r2 = mk_head (MMasked f false mask xor v2) body r1 /\
  field_fixed_len f = Some (length v1) /\ field_fixed_len f = Some (length v2) /\
  length mask = length v1 /\ length xor = length v1.
Proof.
  intros r1 r2 f mask xor v1 v2 body H. unfold dscp_merge_pair in H.
  destruct (head_dscp r1) as [[[[[f1 m1] x1] u1] rest1] |] eqn:H1; [| discriminate].
  destruct (head_dscp r2) as [[[[[f2 m2] x2] u2] rest2] |] eqn:H2; [| discriminate].
  destruct (field_eq_dec f1 f2) as [Ef |]; [| discriminate]. subst f2.
  destruct (list_eq_dec Nat.eq_dec m1 m2) as [Em |]; [| discriminate]. subst m2.
  destruct (list_eq_dec Nat.eq_dec x1 x2) as [Ex |]; [| discriminate]. subst x2.
  destruct (list_eq_dec body_item_eq_dec rest1 rest2) as [Er |]; [| discriminate]. subst rest2.
  destruct (list_eq_dec Nat.eq_dec u1 u2) as [Eu |]; [discriminate |].
  destruct (field_fixed_len f1) as [len |] eqn:Hfx; [| discriminate].
  destruct (Nat.eq_dec len (length m1)) as [Elm |]; [| discriminate].
  destruct (Nat.eq_dec len (length x1)) as [Elx |]; [| discriminate].
  destruct (Nat.eq_dec len (length u1)) as [El1 |]; [| discriminate].
  destruct (Nat.eq_dec len (length u2)) as [El2 |]; [| discriminate].
  destruct (rule_end_eqb r1 r2) eqn:Eeqb; [| discriminate].
  inversion H; subst f1 m1 x1 u1 rest1 u2. clear H.
  pose proof (head_dscp_canon r1 f mask xor v1 body H1) as Hr1.
  pose proof (head_dscp_canon r2 f mask xor v2 body H2) as Hr2c.
  pose proof (proj1 (rule_end_eqb_mk_head (MMasked f false mask xor v2) body r1 r2) Eeqb)
    as Eshell.
  split; [exact Hr1 |].
  split; [rewrite Hr2c; symmetry; exact Eshell |].
  split; [rewrite Hfx; f_equal; congruence |].
  split; [rewrite Hfx; f_equal; congruence |].
  split; congruence.
Qed.

Lemma dscp_merge_pair_with_head : forall r1 r2 f mask xor v1 body
    f' m' x' v1' v2 body',
  head_dscp r1 = Some (f, mask, xor, v1, body) ->
  dscp_merge_pair r1 r2 = Some (f', m', x', v1', v2, body') ->
  f' = f /\ m' = mask /\ x' = xor /\ v1' = v1 /\ body' = body /\
  r2 = mk_head (MMasked f false mask xor v2) body r1 /\
  field_fixed_len f = Some (length v2).
Proof.
  intros r1 r2 f mask xor v1 body f' m' x' v1' v2 body' Hhd Hvm.
  destruct (dscp_merge_pair_shape r1 r2 f' m' x' v1' v2 body' Hvm)
    as [Hr1 [Hr2 [_ [Hx2 _]]]].
  assert (Hhd' : head_dscp r1 = Some (f', m', x', v1', body')).
  { rewrite Hr1 at 1. unfold head_dscp, mk_head. cbn [r_body]. reflexivity. }
  rewrite Hhd in Hhd'. inversion Hhd'; subst f' m' x' v1' body'.
  repeat split; try assumption.
Qed.

(** ** [match_loadable] agreement between the masked heads and the merged set head. *)
Lemma match_loadable_mmasked : forall f mask xor v q,
  match_loadable (MMasked f false mask xor v) q = field_loadable f q.
Proof. reflexivity. Qed.

Lemma match_loadable_msett_bitand : forall f mask xor name q,
  match_loadable (MSetT f [TBitAnd mask xor] false name) q = field_loadable f q.
Proof. reflexivity. Qed.

Lemma match_loadable_dscp_run : forall f mask xor vals q m,
  In m (map (fun v => MMasked f false mask xor v) vals) ->
  match_loadable m q = field_loadable f q.
Proof.
  intros f mask xor vals q m Hin. apply in_map_iff in Hin as [v [Hv _]]. subst m.
  apply match_loadable_mmasked.
Qed.

(** ** Executable N-WAY masked-value->set pass (fuel-driven, mirrors [setsN]). *)
Fixpoint take_dscp_run (r1 : rule) (rest : list rule)
  : list data * list rule :=
  match rest with
  | [] => ([], [])
  | r2 :: tl =>
      match dscp_merge_pair r1 r2 with
      | Some (_, _, _, _, v2, _) =>
          let '(vs, rest') := take_dscp_run r1 tl in (v2 :: vs, rest')
      | None => ([], rest)
      end
  end.

Fixpoint optimize_rules_dscp (fuel n : nat) (d : set_decls) (rs : list rule)
  : nat * set_decls * list rule :=
  match fuel with
  | O => (n, d, rs)
  | S fuel' =>
    match rs with
    | r1 :: ((_ :: _) as rest) =>
        match head_dscp r1 with
        | Some (f, mask, xor, v1, body) =>
            match take_dscp_run r1 rest with
            | ([], _) =>
                let '(n'', d'', rest') := optimize_rules_dscp fuel' n d rest in
                (n'', d'', r1 :: rest')
            | ((_ :: _) as vs, rest') =>
                let name := setname n in
                let elems := map (fun v => (v, v)) (v1 :: vs) in
                let d' := {| sd_sets := (name, elems) :: sd_sets d;
                             sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
                let merged := mk_head (MSetT f [TBitAnd mask xor] false name) body r1 in
                let '(n'', d'', rest'') := optimize_rules_dscp fuel' (S n) d' rest' in
                (n'', d'', merged :: rest'')
            end
        | None =>
            let '(n'', d'', rest') := optimize_rules_dscp fuel' n d rest in
            (n'', d'', r1 :: rest')
        end
    | _ => (n, d, rs)
    end
  end.

Definition optimize_chain_dscp (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n', d', rs') := optimize_rules_dscp (length (c_rules c)) n d (c_rules c) in
  (n', d', {| c_policy := c_policy c; c_rules := rs' |}).

Lemma optimize_rules_dscp_consSS : forall fuel n d r1 r2 rest,
  optimize_rules_dscp (S fuel) n d (r1 :: r2 :: rest) =
  match head_dscp r1 with
  | Some (f, mask, xor, v1, body) =>
      match take_dscp_run r1 (r2 :: rest) with
      | ([], _) =>
          let '(n'', d'', rest') := optimize_rules_dscp fuel n d (r2 :: rest) in
          (n'', d'', r1 :: rest')
      | ((_ :: _) as vs, rest') =>
          let name := setname n in
          let elems := map (fun v => (v, v)) (v1 :: vs) in
          let d' := {| sd_sets := (name, elems) :: sd_sets d;
                       sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
          let merged := mk_head (MSetT f [TBitAnd mask xor] false name) body r1 in
          let '(n'', d'', rest'') := optimize_rules_dscp fuel (S n) d' rest' in
          (n'', d'', merged :: rest'')
      end
  | None =>
      let '(n'', d'', rest') := optimize_rules_dscp fuel n d (r2 :: rest) in
      (n'', d'', r1 :: rest')
  end.
Proof. reflexivity. Qed.

(** The matched run is exactly the masked-head shells over its values. *)
Lemma take_dscp_run_shape : forall r1 f mask xor v1 body rest vs rest',
  head_dscp r1 = Some (f, mask, xor, v1, body) ->
  take_dscp_run r1 rest = (vs, rest') ->
  rest = map (fun v => mk_head (MMasked f false mask xor v) body r1) vs ++ rest'
  /\ (forall v, In v vs -> field_fixed_len f = Some (length v)).
Proof.
  intros r1 f mask xor v1 body rest. induction rest as [| r2 tl IH]; intros vs rest' Hhd H.
  - cbn in H. inversion H; subst. split; [ reflexivity | intros v [] ].
  - cbn in H. destruct (dscp_merge_pair r1 r2)
      as [[[[[[f2 m2] x2] u1] v2] bd] |] eqn:Evm.
    + destruct (take_dscp_run r1 tl) as [vs0 rest0] eqn:Erec.
      inversion H; subst vs rest'. clear H.
      destruct (dscp_merge_pair_with_head r1 r2 f mask xor v1 body
                  f2 m2 x2 u1 v2 bd Hhd Evm)
        as [_ [_ [_ [_ [_ [Hr2 Hfx]]]]]].
      destruct (IH vs0 rest0 Hhd eq_refl) as [Hsplit Hall].
      split.
      * cbn [map app]. rewrite <- Hr2, <- Hsplit. reflexivity.
      * intros v [Hv | Hin]; [ subst v; exact Hfx | apply (Hall v Hin) ].
    + inversion H; subst vs rest'.
      split; [ reflexivity | intros v [] ].
Qed.

Lemma take_dscp_run_head_width : forall r1 f mask xor v1 body r2 rest vs rest',
  head_dscp r1 = Some (f, mask, xor, v1, body) ->
  take_dscp_run r1 (r2 :: rest) = (vs, rest') ->
  vs <> [] ->
  field_fixed_len f = Some (length v1).
Proof.
  intros r1 f mask xor v1 body r2 rest vs rest' Hhd Hrun Hne.
  cbn in Hrun. destruct (dscp_merge_pair r1 r2)
    as [[[[[[f2 m2] x2] u1] v2] bd] |] eqn:Evm.
  - destruct (dscp_merge_pair_shape r1 r2 f2 m2 x2 u1 v2 bd Evm)
      as [Hr1 [_ [Hx1 _]]].
    assert (Hhd' : head_dscp r1 = Some (f2, m2, x2, u1, bd)).
    { rewrite Hr1 at 1. unfold head_dscp, mk_head. cbn [r_body]. reflexivity. }
    rewrite Hhd in Hhd'. inversion Hhd'; subst f2 m2 x2 u1 bd. exact Hx1.
  - destruct (take_dscp_run r1 rest) as [vs0 rest0] eqn:Erec0.
    inversion Hrun; subst. contradiction.
Qed.

(** When the run is nonempty, r1's mask/xor also have the field's fixed width. *)
Lemma take_dscp_run_head_widths : forall r1 f mask xor v1 body r2 rest vs rest',
  head_dscp r1 = Some (f, mask, xor, v1, body) ->
  take_dscp_run r1 (r2 :: rest) = (vs, rest') ->
  vs <> [] ->
  length mask = length v1 /\ length xor = length v1.
Proof.
  intros r1 f mask xor v1 body r2 rest vs rest' Hhd Hrun Hne.
  cbn in Hrun. destruct (dscp_merge_pair r1 r2)
    as [[[[[[f2 m2] x2] u1] v2] bd] |] eqn:Evm.
  - destruct (dscp_merge_pair_shape r1 r2 f2 m2 x2 u1 v2 bd Evm)
      as [Hr1 [_ [_ [_ [Hlm Hlx]]]]].
    assert (Hhd' : head_dscp r1 = Some (f2, m2, x2, u1, bd)).
    { rewrite Hr1 at 1. unfold head_dscp, mk_head. cbn [r_body]. reflexivity. }
    rewrite Hhd in Hhd'. inversion Hhd'; subst f2 m2 x2 u1 bd. split; assumption.
  - destruct (take_dscp_run r1 rest) as [vs0 rest0] eqn:Erec0.
    inversion Hrun; subst. contradiction.
Qed.

(** *** Freshness bookkeeping: only PREPENDS [sd_sets] entries keyed [setname k],
    [n <= k < n']. *)
Lemma optimize_rules_dscp_assoc_stable : forall fuel n d rs n' d' rs' nm X,
  optimize_rules_dscp fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X = assoc_str nm (sd_sets d) X.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' nm X H Hnm.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_dscp_consSS in H.
      destruct (head_dscp r1) as [[[[[f mask] xor] v1] body] |] eqn:Ehd.
      * destruct (take_dscp_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct vs as [| v vs'].
        -- remember (optimize_rules_dscp fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
        -- cbv zeta in H.
           remember (optimize_rules_dscp fuel (S n)
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
      * remember (optimize_rules_dscp fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
        eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
Qed.

Lemma optimize_rules_dscp_mono : forall fuel n d rs n' d' rs',
  optimize_rules_dscp fuel n d rs = (n', d', rs') -> n <= n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; lia.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; lia.
    + cbn in H. inversion H; subst; lia.
    + rewrite optimize_rules_dscp_consSS in H.
      destruct (head_dscp r1) as [[[[[f mask] xor] v1] body] |] eqn:Ehd.
      * destruct (take_dscp_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct vs as [| v vs'].
        -- remember (optimize_rules_dscp fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_dscp fuel (S n) _ rest') as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n'.
           assert (S n <= m'')
             by (eapply (IH (S n) _ rest'); symmetry; exact Erec). lia.
      * remember (optimize_rules_dscp fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_dscp_vmaps : forall fuel n d rs n' d' rs',
  optimize_rules_dscp fuel n d rs = (n', d', rs') -> sd_vmaps d' = sd_vmaps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_dscp_consSS in H.
      destruct (head_dscp r1) as [[[[[f mask] xor] v1] body] |] eqn:Ehd.
      * destruct (take_dscp_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct vs as [| v vs'].
        -- remember (optimize_rules_dscp fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_dscp fuel (S n)
                       {| sd_sets := (setname n, map (fun v0 => (v0, v0)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_dscp fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_dscp_maps : forall fuel n d rs n' d' rs',
  optimize_rules_dscp fuel n d rs = (n', d', rs') -> sd_maps d' = sd_maps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_dscp_consSS in H.
      destruct (head_dscp r1) as [[[[[f mask] xor] v1] body] |] eqn:Ehd.
      * destruct (take_dscp_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct vs as [| v vs'].
        -- remember (optimize_rules_dscp fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_dscp fuel (S n)
                       {| sd_sets := (setname n, map (fun v0 => (v0, v0)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_dscp fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_dscp_keys_bound : forall fuel n d rs n' d' rs' k,
  optimize_rules_dscp fuel n d rs = (n', d', rs') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' k H Hin.
  - cbn in H. inversion H; subst. left; exact Hin.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst. left; exact Hin.
    + cbn in H. inversion H; subst. left; exact Hin.
    + rewrite optimize_rules_dscp_consSS in H.
      destruct (head_dscp r1) as [[[[[f mask] xor] v1] body] |] eqn:Ehd.
      * destruct (take_dscp_run r1 (r2 :: rest)) as [vs rest'] eqn:Erun.
        destruct vs as [| v vs'].
        -- remember (optimize_rules_dscp fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
        -- cbv zeta in H.
           remember (optimize_rules_dscp fuel (S n)
                       {| sd_sets := (setname n, map (fun v0 => (v0, v0)) (v1 :: v :: vs'))
                                     :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'.
           destruct (IH (S n) _ rest' m'' dd'' rr'' k (eq_sym Erec) Hin) as [Hin_dn | Hlt].
           ++ cbn [sd_sets map] in Hin_dn. destruct Hin_dn as [Heq | Hin_d].
              ** apply setname_inj in Heq. subst k. right.
                 pose proof (optimize_rules_dscp_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec)). lia.
              ** left; exact Hin_d.
           ++ right; exact Hlt.
      * remember (optimize_rules_dscp fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
        subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
Qed.

(** *** Chain-level structural wrappers. *)
Lemma optimize_chain_dscp_mono : forall n d c n' d' c',
  optimize_chain_dscp n d c = (n', d', c') -> n <= n'.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_dscp in H.
  destruct (optimize_rules_dscp (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_dscp_mono _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_dscp_vmaps : forall n d c n' d' c',
  optimize_chain_dscp n d c = (n', d', c') -> sd_vmaps d' = sd_vmaps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_dscp in H.
  destruct (optimize_rules_dscp (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_dscp_vmaps _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_dscp_maps : forall n d c n' d' c',
  optimize_chain_dscp n d c = (n', d', c') -> sd_maps d' = sd_maps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_dscp in H.
  destruct (optimize_rules_dscp (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_dscp_maps _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_dscp_keys_bound : forall n d c n' d' c' k,
  optimize_chain_dscp n d c = (n', d', c') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  intros n d c n' d' c' k H Hin. unfold optimize_chain_dscp in H.
  destruct (optimize_rules_dscp (List.length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  apply (optimize_rules_dscp_keys_bound _ _ _ _ _ _ _ k E Hin).
Qed.

(** ** Non-vacuity witnesses (battery shape "dscp-masked-set"): two adjacent
    `ip dscp 10/20 accept` masked rules fold to ONE `ip dscp { 10, 20 }` set rule.
    The field is [FPayload PNetwork 1 1] (the TOS byte), mask 0xfc, xor 0x00; the
    compared values are the dscp codepoints shifted into the header bits
    (10<<2 = 0x28 = 40, 20<<2 = 0x50 = 80). *)
Definition acc_witness_d : rule :=
  {| r_body := []; r_verdict := Accept; r_vmap := None; r_nat := None;
     r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.

Definition dscp_f : field := FPayload PNetwork 1 1.

Definition dscp_r (v : data) : rule :=
  mk_head (MMasked dscp_f false [252] [0] v) [] acc_witness_d.

Example dscp_merge_fires :
  dscp_merge_pair (dscp_r [40]) (dscp_r [80])
  = Some (dscp_f, [252], [0], [40], [80], []).
Proof. reflexivity. Qed.

(* the fold collapses the two-rule chain to ONE MSetT rule + a fresh 2-element set *)
Example dscp_folds :
  optimize_rules_dscp 2 0 {| sd_sets := []; sd_vmaps := []; sd_maps := [] |}
    [dscp_r [40]; dscp_r [80]]
  = (1,
     {| sd_sets := [(setname 0, [([40],[40]); ([80],[80])])];
        sd_vmaps := []; sd_maps := [] |},
     [ mk_head (MSetT dscp_f [TBitAnd [252] [0]] false (setname 0)) [] (dscp_r [40]) ]).
Proof. reflexivity. Qed.
