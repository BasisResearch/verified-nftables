(** * Optimize_IntervalSetHostOrder: host-order INTERVAL / range set consolidation (`ct mark`, …).

    Battery shape "host-order interval set".  `nft --optimize` folds a run of
    ADJACENT rules whose differing head is a
    RANGE over the SAME HOST-ENDIAN field (`ct mark`, `meta mark`, iif/oif index, fib
    type — all u32 host-order registers) into ONE interval-set lookup:

        ct mark 10-20 accept   ┐
        ct mark 21-30 accept   ┘   =>   ct mark { 10-20, 21-30 } accept

    Confirmed against host `nft` v1.1.6 in a netns.

    Unlike a plain network-order range `ip saddr a-b` (which [Optimize_IntervalSet] handles as
    a bare [MRange]), a host-endian field is lowered WITH a byteorder transform in front
    of the range test (nft_lower.ml, [host_endian_kind]): nft stores the range immediates
    NETWORK-order and converts the host-endian register to network order with `hton`
    before the numeric compare, so the frontend emits

        ct mark 10-20  ==>  [ MRangeT FCtMark [TByteorder true 4 4] false 0x..0a 0x..14 ]

        (compiled:  [ ct load mark ][ byteorder hton reg1 4 4 ][ range reg1 lo hi ])

    The [MRangeT] head (transformed range) is what [Optimize_IntervalSet]'s bare-[MRange]
    recogniser never fires on — exactly the `ct mark` interval-set gap.  This module
    recognises a run of such [MRangeT] heads over the SAME field/transforms/body/verdict
    and folds the WHOLE run into ONE rule whose head is

        [ MSetT f [TByteorder true 4 4] false __setN ]

        (compiled:  [ ct load mark ][ byteorder hton reg1 4 4 ][ lookup reg1 __setN ])

    over the interval set [(lo_1,hi_1); …; (lo_N,hi_N)] — exactly nft's consolidation,
    with the SAME transforms carried in both the original ranges and the merged set head.

    SOUNDNESS.  The transformed value [v = apply_transforms ts (field_value f e p)] is the
    SAME operand in both an [MRangeT]'s range test ([data_in_iv v (lo,hi)]) and the
    [MSetT]'s membership ([set_mem v = existsb (data_in_iv v)]), so the merged head is
    EXACTLY the [existsb] disjunction of the run's ranges ([msett_ivs_existsb]) — with NO
    fixed-width side-condition ([data_le] does not truncate).  The first-match
    merge is certified over the state fold by
    [Optimize_MutEnv.eval_rules_flat_run_merge_abs].

    REPRESENTABILITY.  A single-field nftables interval set is the kernel [rbtree]
    backend, a strict PARTITION whose insert rejects ANY overlap; so we only emit a fold
    whose intervals are PAIRWISE DISJOINT (the [all_disjoint] gate reused from
    [Optimize_IntervalSetGuarded]) — otherwise the object is unloadable (the `nft --optimize` defect
    we must not replicate).  The recogniser is further gated on [ranget_ok ts] (the
    host-order 4-byte byteorder transform nft actually emits for interval sets) so the
    fold fires EXACTLY on the shape `nft -o` produces.  Axiom-free. *)

From Stdlib Require Import Ascii String.
From Stdlib Require Import List PeanoNat Bool Lia.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Optimize Optimize_ValueSet Optimize_IntervalSet Optimize_IntervalSetGuarded.
Import ListNotations.
Local Open Scope nat_scope.

(** [ranget_ok ts]: the recogniser only fires on the host-order 4-byte byteorder
    transform nft lowers a host-endian interval range to ([TByteorder true 4 4]) — so
    the fold is EXACTLY the loadable `ct mark { … }` / `meta mark { … }` interval set
    `nft -o` emits, never an arbitrary transformed range. *)
Definition ranget_ok (ts : list transform) : bool :=
  match ts with
  | [TByteorder true 4 4] => true
  | _ => false
  end.

(** *** The membership certificate: an [MSetT] over an interval set is EXACTLY the
    [existsb] disjunction of the corresponding [MRangeT] matches (same transforms). *)
Lemma eval_mranget_iv : forall f ts lo hi e q,
  eval_matchcond (MRangeT f ts false lo hi) e q
  = andb (field_loadable f q)
         (data_in_iv (apply_transforms ts (field_value f e q)) (lo, hi)).
Proof.
  intros f ts lo hi e q.
  unfold eval_matchcond, eval_matchcond_body, match_loadable.
  unfold eval_range, data_in_iv. cbn [fst snd]. reflexivity.
Qed.

Lemma match_loadable_mranget : forall f ts lo hi q,
  match_loadable (MRangeT f ts false lo hi) q = field_loadable f q.
Proof. reflexivity. Qed.

Lemma match_loadable_msett : forall f ts name q,
  match_loadable (MSetT f ts false name) q = field_loadable f q.
Proof. reflexivity. Qed.

Lemma msett_ivs_existsb : forall f ts ivs name e q,
  e_set e name = ivs ->
  eval_matchcond (MSetT f ts false name) e q
  = existsb (fun iv => eval_matchcond (MRangeT f ts false (fst iv) (snd iv)) e q) ivs.
Proof.
  intros f ts ivs name e q Hset.
  unfold eval_matchcond at 1, eval_matchcond_body at 1.
  cbn [match_loadable].
  destruct (field_loadable f q) eqn:Hld; cbn [andb].
  - cbn [xorb]. unfold set_mem. rewrite Hset.
    apply existsb_ext. intros [lo hi] Hiv.
    rewrite eval_mranget_iv, Hld. cbn [andb fst snd]. reflexivity.
  - symmetry. apply existsb_false_forall. intros iv Hiv.
    rewrite eval_mranget_iv, Hld. reflexivity.
Qed.

(** Every head in [map (fun iv => MRangeT f ts false (fst iv)(snd iv)) ivs] shares the
    same [match_loadable = field_loadable f]. *)
Lemma match_loadable_ranget_run : forall f ts ivs q m,
  In m (map (fun iv => MRangeT f ts false (fst iv) (snd iv)) ivs) ->
  match_loadable m q = field_loadable f q.
Proof.
  intros f ts ivs q m Hin. apply in_map_iff in Hin as [iv [Hm _]]. subst m.
  apply match_loadable_mranget.
Qed.

(** *** Recogniser: a positive transformed-range head. *)
Definition head_ivsett (r : rule)
  : option (field * list transform * data * data * list body_item) :=
  match r_body r with
  | BMatch (MRangeT f ts false lo hi) :: rest => Some (f, ts, lo, hi, rest)
  | _ => None
  end.

Lemma head_ivsett_rbody : forall r f ts lo hi body,
  head_ivsett r = Some (f, ts, lo, hi, body) ->
  r_body r = BMatch (MRangeT f ts false lo hi) :: body.
Proof.
  intros r f ts lo hi body H. unfold head_ivsett in H.
  destruct (r_body r) as [| [m | s] tl] eqn:Eb; try discriminate.
  destruct m as [ f0 v0 | f0 v0 | f0 n0 lo0 hi0 | f0 n0 mk0 x0 v0 | f0 op0 v0
                | fs0 n0 nm0 | f0 ts0 op0 v0 | f0 ts0 n0 nm0 | f0 ts0 n0 lo0 hi0
                | s0 | s0 | s0 | es0 n0 nm0 ]; try discriminate.
  destruct n0; try discriminate. inversion H; subst. reflexivity.
Qed.

Lemma head_ivsett_canon : forall r f ts lo hi body,
  head_ivsett r = Some (f, ts, lo, hi, body) ->
  r = mk_head (MRangeT f ts false lo hi) body r.
Proof.
  intros r f ts lo hi body H.
  pose proof (head_ivsett_rbody r f ts lo hi body H) as Hb.
  unfold mk_head. rewrite <- Hb. destruct r; reflexivity.
Qed.

(** Two rules form an eligible transformed-range merge pair iff both heads are
    [MRangeT f ts false lo_i hi_i] over the SAME field [f], SAME (host-order) transforms
    [ts], SAME tail, SAME end-fields; [ranget_ok] pins the transform to the loadable
    host-order interval shape. *)
Definition ivsett_merge_pair (r1 r2 : rule)
  : option (field * list transform * (data * data) * (data * data) * list body_item) :=
  (* EFFECT-SAFETY GUARD — see [Optimize_ValueSet.value_merge_pair]. *)
  if negb (rule_mutfree r1) then None else
  match head_ivsett r1, head_ivsett r2 with
  | Some (f1, ts1, lo1, hi1, rest1), Some (f2, ts2, lo2, hi2, rest2) =>
      if field_eq_dec f1 f2 then
      if list_eq_dec transform_eq_dec ts1 ts2 then
      if ranget_ok ts1 then
      if list_eq_dec body_item_eq_dec rest1 rest2 then
      if rule_end_eqb r1 r2
      then Some (f1, ts1, (lo1, hi1), (lo2, hi2), rest1)
      else None
      else None else None else None else None
  | _, _ => None
  end.

(** The guard, extracted: a fired pair certifies its canonical rule write-free. *)
Lemma ivsett_merge_pair_mutfree : forall r1 r2 x,
  ivsett_merge_pair r1 r2 = Some x -> rule_mutfree r1 = true.
Proof.
  intros r1 r2 x H. unfold ivsett_merge_pair in H.
  destruct (rule_mutfree r1); [reflexivity | discriminate H].
Qed.

Lemma ivsett_merge_pair_with_head : forall r1 r2 f ts lo1 hi1 body f' ts' iv1 iv2 body',
  head_ivsett r1 = Some (f, ts, lo1, hi1, body) ->
  ivsett_merge_pair r1 r2 = Some (f', ts', iv1, iv2, body') ->
  f' = f /\ ts' = ts /\ iv1 = (lo1, hi1) /\ body' = body /\
  r2 = mk_head (MRangeT f ts false (fst iv2) (snd iv2)) body r1.
Proof.
  intros r1 r2 f ts lo1 hi1 body f' ts' iv1 iv2 body' Hhd Hvm.
  unfold ivsett_merge_pair in Hvm.
  destruct (negb (rule_mutfree r1)); [discriminate Hvm |].
  rewrite Hhd in Hvm.
  destruct (head_ivsett r2) as [[[[[f2 ts2] lo2] hi2] rest2] |] eqn:H2; [| discriminate].
  destruct (field_eq_dec f f2) as [Ef |]; [| discriminate]. subst f2.
  destruct (list_eq_dec transform_eq_dec ts ts2) as [Ets |]; [| discriminate]. subst ts2.
  destruct (ranget_ok ts) eqn:Egok; [| discriminate].
  destruct (list_eq_dec body_item_eq_dec body rest2) as [Er |]; [| discriminate]. subst rest2.
  destruct (rule_end_eqb r1 r2) eqn:Eeqb; [| discriminate].
  inversion Hvm; subst f' ts' iv1 iv2 body'. clear Hvm. cbn [fst snd].
  pose proof (head_ivsett_canon r2 f ts lo2 hi2 body H2) as Hr2c.
  pose proof (proj1 (rule_end_eqb_mk_head (MRangeT f ts false lo1 hi1) body r1 r2) Eeqb) as Eshell.
  repeat split.
  rewrite Hr2c. unfold mk_head in Eshell |- *.
  injection Eshell as Eo Ea.
  rewrite Eo, Ea. reflexivity.
Qed.

(** *** Collect the MAXIMAL run of following rules that each transformed-range-merge
    with [r1]. *)
Fixpoint take_ivsett_run_raw (r1 : rule) (rest : list rule)
  : list (data * data) * list rule :=
  match rest with
  | [] => ([], [])
  | r2 :: tl =>
      match ivsett_merge_pair r1 r2 with
      | Some (_, _, _, iv2, _) =>
          let '(ivs, rest') := take_ivsett_run_raw r1 tl in (iv2 :: ivs, rest')
      | None => ([], rest)
      end
  end.

(** The run, GATED by the rbtree representability filter: if the intervals (including
    [r1]'s [(lo1,hi1)]) are not pairwise disjoint, DECLINE the fold ([([], rest)]). *)
Definition take_ivsett_run (r1 : rule) (rest : list rule)
  : list (data * data) * list rule :=
  match head_ivsett r1 with
  | Some (_, _, lo1, hi1, _) =>
      let '(ivs, rest') := take_ivsett_run_raw r1 rest in
      if all_disjoint ((lo1, hi1) :: ivs) then (ivs, rest') else ([], rest)
  | None => ([], rest)
  end.

Lemma take_ivsett_run_raw_shape : forall r1 f ts lo1 hi1 body rest ivs rest',
  head_ivsett r1 = Some (f, ts, lo1, hi1, body) ->
  take_ivsett_run_raw r1 rest = (ivs, rest') ->
  rest = map (fun iv => mk_head (MRangeT f ts false (fst iv) (snd iv)) body r1) ivs ++ rest'.
Proof.
  intros r1 f ts lo1 hi1 body rest. induction rest as [| r2 tl IH]; intros ivs rest' Hhd H.
  - cbn in H. inversion H; subst. reflexivity.
  - cbn in H. destruct (ivsett_merge_pair r1 r2)
      as [[[[[f2 ts2] iva] iv2] bd] |] eqn:Evm.
    + destruct (take_ivsett_run_raw r1 tl) as [ivs0 rest0] eqn:Erec.
      inversion H; subst ivs rest'. clear H.
      destruct (ivsett_merge_pair_with_head r1 r2 f ts lo1 hi1 body f2 ts2 iva iv2 bd Hhd Evm)
        as [_ [_ [_ [_ Hr2]]]].
      cbn [map app]. rewrite <- Hr2, <- (IH ivs0 rest0 Hhd eq_refl). reflexivity.
    + inversion H; subst ivs rest'. reflexivity.
Qed.

Lemma take_ivsett_run_shape : forall r1 f ts lo1 hi1 body rest ivs rest',
  head_ivsett r1 = Some (f, ts, lo1, hi1, body) ->
  take_ivsett_run r1 rest = (ivs, rest') ->
  rest = map (fun iv => mk_head (MRangeT f ts false (fst iv) (snd iv)) body r1) ivs ++ rest'.
Proof.
  intros r1 f ts lo1 hi1 body rest ivs rest' Hhd H.
  unfold take_ivsett_run in H. rewrite Hhd in H.
  destruct (take_ivsett_run_raw r1 rest) as [ivs0 rest0] eqn:Eraw.
  destruct (all_disjoint ((lo1, hi1) :: ivs0)) eqn:Hdisj.
  - inversion H; subst ivs rest'.
    apply (take_ivsett_run_raw_shape r1 f ts lo1 hi1 body rest ivs0 rest0 Hhd Eraw).
  - inversion H; subst ivs rest'. reflexivity.
Qed.

(** *** The executable fuel-driven N-way host-order interval-set pass. *)
Fixpoint optimize_rules_intervalsethostorder (fuel : nat) (n : nat) (d : set_decls) (rs : list rule)
  : nat * set_decls * list rule :=
  match fuel with
  | O => (n, d, rs)
  | S fuel' =>
    match rs with
    | r1 :: ((_ :: _) as rest) =>
        match head_ivsett r1 with
        | Some (f, ts, lo1, hi1, body) =>
            match take_ivsett_run r1 rest with
            | ([], _) =>
                let '(n'', d'', rest') := optimize_rules_intervalsethostorder fuel' n d rest in
                (n'', d'', r1 :: rest')
            | ((_ :: _) as ivs, rest') =>
                let name := setname n in
                let elems := (lo1, hi1) :: ivs in
                let d' := {| sd_sets := (name, elems) :: sd_sets d;
                             sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
                let merged := mk_head (MSetT f ts false name) body r1 in
                let '(n'', d'', rest'') := optimize_rules_intervalsethostorder fuel' (S n) d' rest' in
                (n'', d'', merged :: rest'')
            end
        | None =>
            let '(n'', d'', rest') := optimize_rules_intervalsethostorder fuel' n d rest in
            (n'', d'', r1 :: rest')
        end
    | _ => (n, d, rs)
    end
  end.

Definition optimize_chain_intervalsethostorder (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n', d', rs') := optimize_rules_intervalsethostorder (length (c_rules c)) n d (c_rules c) in
  (n', d', {| c_policy := c_policy c; c_rules := rs' |}).

Lemma optimize_rules_intervalsethostorder_consSS : forall fuel n d r1 r2 rest,
  optimize_rules_intervalsethostorder (S fuel) n d (r1 :: r2 :: rest) =
  match head_ivsett r1 with
  | Some (f, ts, lo1, hi1, body) =>
      match take_ivsett_run r1 (r2 :: rest) with
      | ([], _) =>
          let '(n'', d'', rest') := optimize_rules_intervalsethostorder fuel n d (r2 :: rest) in
          (n'', d'', r1 :: rest')
      | ((_ :: _) as ivs, rest') =>
          let name := setname n in
          let elems := (lo1, hi1) :: ivs in
          let d' := {| sd_sets := (name, elems) :: sd_sets d;
                       sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
          let merged := mk_head (MSetT f ts false name) body r1 in
          let '(n'', d'', rest'') := optimize_rules_intervalsethostorder fuel (S n) d' rest' in
          (n'', d'', merged :: rest'')
      end
  | None =>
      let '(n'', d'', rest') := optimize_rules_intervalsethostorder fuel n d (r2 :: rest) in
      (n'', d'', r1 :: rest')
  end.
Proof. reflexivity. Qed.

(** *** Structural invariants (mint [setname]s only; vmaps/maps untouched). *)
Lemma optimize_rules_intervalsethostorder_mono : forall fuel n d rs n' d' rs',
  optimize_rules_intervalsethostorder fuel n d rs = (n', d', rs') -> n <= n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; lia.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; lia.
    + cbn in H. inversion H; subst; lia.
    + rewrite optimize_rules_intervalsethostorder_consSS in H.
      destruct (head_ivsett r1) as [[[[[f ts] lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_ivsett_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_intervalsethostorder fuel (S n) _ rest') as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n'.
           assert (S n <= m'')
             by (eapply (IH (S n) _ rest'); symmetry; exact Erec). lia.
      * remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_intervalsethostorder_vmaps : forall fuel n d rs n' d' rs',
  optimize_rules_intervalsethostorder fuel n d rs = (n', d', rs') -> sd_vmaps d' = sd_vmaps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_intervalsethostorder_consSS in H.
      destruct (head_ivsett r1) as [[[[[f ts] lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_ivsett_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_intervalsethostorder fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_intervalsethostorder_maps : forall fuel n d rs n' d' rs',
  optimize_rules_intervalsethostorder fuel n d rs = (n', d', rs') -> sd_maps d' = sd_maps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_intervalsethostorder_consSS in H.
      destruct (head_ivsett r1) as [[[[[f ts] lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_ivsett_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_intervalsethostorder fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_intervalsethostorder_keys_bound : forall fuel n d rs n' d' rs' k,
  optimize_rules_intervalsethostorder fuel n d rs = (n', d', rs') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' k H Hin.
  - cbn in H. inversion H; subst. left; exact Hin.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst. left; exact Hin.
    + cbn in H. inversion H; subst. left; exact Hin.
    + rewrite optimize_rules_intervalsethostorder_consSS in H.
      destruct (head_ivsett r1) as [[[[[f ts] lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_ivsett_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
        -- cbv zeta in H.
           remember (optimize_rules_intervalsethostorder fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'.
           destruct (IH (S n) _ rest' m'' dd'' rr'' k (eq_sym Erec) Hin) as [Hin_dn | Hlt].
           ++ cbn [sd_sets map] in Hin_dn. destruct Hin_dn as [Heq | Hin_d].
              ** apply setname_inj in Heq. subst k. right.
                 pose proof (optimize_rules_intervalsethostorder_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec)). lia.
              ** left; exact Hin_d.
           ++ right; exact Hlt.
      * remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
        subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
Qed.

Lemma optimize_rules_intervalsethostorder_assoc_stable : forall fuel n d rs n' d' rs' nm X,
  optimize_rules_intervalsethostorder fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X = assoc_str nm (sd_sets d) X.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' nm X H Hnm.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_intervalsethostorder_consSS in H.
      destruct (head_ivsett r1) as [[[[[f ts] lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_ivsett_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
        -- cbv zeta in H.
           remember (optimize_rules_intervalsethostorder fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           erewrite (IH (S n) _ rest'); [ | symmetry; exact Erec | intros k Hk; apply Hnm; lia ].
           cbn [sd_sets assoc_str].
           destruct (String.eqb nm (setname n)) eqn:Eqn.
           ++ apply String.eqb_eq in Eqn. exfalso. apply (Hnm n); [lia | exact Eqn].
           ++ reflexivity.
      * remember (optimize_rules_intervalsethostorder fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
        eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
Qed.

(** *** Chain-level structural wrappers. *)
Lemma optimize_chain_intervalsethostorder_mono : forall n d c n' d' c',
  optimize_chain_intervalsethostorder n d c = (n', d', c') -> n <= n'.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_intervalsethostorder in H.
  destruct (optimize_rules_intervalsethostorder (length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_intervalsethostorder_mono _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_intervalsethostorder_vmaps : forall n d c n' d' c',
  optimize_chain_intervalsethostorder n d c = (n', d', c') -> sd_vmaps d' = sd_vmaps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_intervalsethostorder in H.
  destruct (optimize_rules_intervalsethostorder (length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_intervalsethostorder_vmaps _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_intervalsethostorder_maps : forall n d c n' d' c',
  optimize_chain_intervalsethostorder n d c = (n', d', c') -> sd_maps d' = sd_maps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_intervalsethostorder in H.
  destruct (optimize_rules_intervalsethostorder (length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_intervalsethostorder_maps _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_intervalsethostorder_keys_bound : forall n d c n' d' c' k,
  optimize_chain_intervalsethostorder n d c = (n', d', c') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  intros n d c n' d' c' k H Hin. unfold optimize_chain_intervalsethostorder in H.
  destruct (optimize_rules_intervalsethostorder (length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  apply (optimize_rules_intervalsethostorder_keys_bound _ _ _ _ _ _ _ k E Hin).
Qed.

(** ** Non-vacuity witness (`ct mark` interval set): two adjacent
    `ct mark 10-20 / 21-30 accept` range rules fold to ONE
    `ct mark { 10-20, 21-30 } accept` set rule + a fresh 2-interval set.  The field is
    [FCtMark] with the host-order byteorder transform; bounds are the network-order
    (big-endian) 4-byte immediates the frontend emits. *)
Definition acc_witness_t : rule :=
  {| r_body := [];
     r_outcome := OVerdict Accept; r_after := [] |}.

Definition ctmark_ts : list transform := [TByteorder true 4 4].

Definition ctmark_r (lo hi : data) : rule :=
  mk_head (MRangeT FCtMark ctmark_ts false lo hi) [] acc_witness_t.

Example ivsett_merge_fires :
  ivsett_merge_pair (ctmark_r [0;0;0;10] [0;0;0;20]) (ctmark_r [0;0;0;21] [0;0;0;30])
  = Some (FCtMark, ctmark_ts, ([0;0;0;10],[0;0;0;20]), ([0;0;0;21],[0;0;0;30]), []).
Proof. reflexivity. Qed.

(* the fold collapses the two-rule chain to ONE MSetT rule + a fresh 2-interval set *)
Example ivsett_folds :
  optimize_rules_intervalsethostorder 2 0 {| sd_sets := []; sd_vmaps := []; sd_maps := [] |}
    [ctmark_r [0;0;0;10] [0;0;0;20]; ctmark_r [0;0;0;21] [0;0;0;30]]
  = (1,
     {| sd_sets := [(setname 0, [([0;0;0;10],[0;0;0;20]); ([0;0;0;21],[0;0;0;30])])];
        sd_vmaps := []; sd_maps := [] |},
     [ mk_head (MSetT FCtMark ctmark_ts false (setname 0)) []
               (ctmark_r [0;0;0;10] [0;0;0;20]) ]).
Proof. reflexivity. Qed.
