(** * Optimize_IntervalSet: INTERVAL / range set consolidation (nft -o's range merge).

    [nft --optimize] folds a run of ADJACENT rules whose differing head is a RANGE
    over the SAME field (same body/verdict) into ONE `lookup @s` over an INTERVAL
    set:

        ip saddr 10.0.0.0-10.0.0.255 accept   ┐
        ip saddr 10.0.2.0-10.0.2.255 accept   ┘
          =>  ip saddr { 10.0.0.0-10.0.0.255, 10.0.2.0-10.0.2.255 } accept

    (src/optimize.c [merge_stmts], the interval-set case: the anonymous set carries
    NFT_SET_INTERVAL and stores each range as a `[lo,hi]` element).  Confirmed
    against the host `nft` v1.1.6 in a netns: the two range rules merge into a single
    interval-set lookup (set flags = ANONYMOUS|CONSTANT|INTERVAL).

    The frontend lowers a bare range `ip saddr a-b` to the head match
    [MRange f false lo hi] (nft_lower.ml, [lower_match]).  We recognise a run of such
    heads over the same field/body/verdict and fold the WHOLE run into ONE rule whose
    head is [MConcatSet [f] false __setN] over the interval set
    [(lo_1,hi_1); …; (lo_N,hi_N)] — exactly nft's consolidation.

    Verdict-preservation is CLEANER than the value->point-set pass: an [MRange]'s
    value test is [data_le lo x && data_le x hi = data_in_iv x (lo,hi)] and a
    single-field [MConcatSet]'s membership is [set_mem x = existsb (data_in_iv x)],
    so the merged head is EXACTLY the [existsb] disjunction of the run's ranges —
    with NO fixed-width side-condition ([data_le] does not truncate, unlike [MCmp]'s
    prefix equality).  We reuse [eval_rules_run_merge_abs] (Optimize_ValueSet) VERBATIM.
    Axiom-free. *)

From Stdlib Require Import Ascii String.
From Stdlib Require Import List PeanoNat Bool Lia Wellfounded Arith.Wf_nat.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Optimize Optimize_ValueSet.
Import ListNotations.
Local Open Scope nat_scope.

(** *** Recogniser: a positive-range head [BMatch (MRange f false lo hi) :: rest]. *)
Definition head_range (r : rule) : option (field * data * data * list body_item) :=
  match r_body r with
  | BMatch (MRange f false lo hi) :: rest => Some (f, lo, hi, rest)
  | _ => None
  end.

Lemma head_range_rbody : forall r f lo hi body,
  head_range r = Some (f, lo, hi, body) ->
  r_body r = BMatch (MRange f false lo hi) :: body.
Proof.
  intros r f lo hi body H. unfold head_range in H.
  destruct (r_body r) as [| [m | s] tl] eqn:Eb; try discriminate.
  destruct m; try discriminate.
  destruct neg; try discriminate. inversion H; subst. reflexivity.
Qed.

(** [head_range r = Some (f,lo,hi,body)] means [r] IS the canonical range-head shell. *)
Lemma head_range_canon : forall r f lo hi body,
  head_range r = Some (f, lo, hi, body) ->
  r = mk_head (MRange f false lo hi) body r.
Proof.
  intros r f lo hi body H.
  pose proof (head_range_rbody r f lo hi body H) as Hb.
  unfold mk_head. rewrite <- Hb. destruct r; reflexivity.
Qed.

(** Two rules form an eligible adjacent RANGE-merge pair iff their heads are
    [MRange f false lo_i hi_i] over the SAME field [f], with the SAME tail [rest] and
    the SAME end-fields (verdict/vmap/nat/…).  No fixed-width guard: the range test
    [data_le]-membership already coincides with interval-set membership. *)
Definition range_merge_pair (r1 r2 : rule)
  : option (field * (data * data) * (data * data) * list body_item) :=
  (* EFFECT-SAFETY GUARD — see [Optimize_ValueSet.value_merge_pair]. *)
  if negb (rule_mutfree r1) then None else
  match head_range r1, head_range r2 with
  | Some (f1, lo1, hi1, rest1), Some (f2, lo2, hi2, rest2) =>
      if field_eq_dec f1 f2 then
      if list_eq_dec body_item_eq_dec rest1 rest2 then
      if rule_end_eqb r1 r2
      then Some (f1, (lo1, hi1), (lo2, hi2), rest1)
      else None
      else None
      else None
  | _, _ => None
  end.

(** The guard, extracted: a fired pair certifies its canonical rule write-free. *)
Lemma range_merge_pair_mutfree : forall r1 r2 x,
  range_merge_pair r1 r2 = Some x -> rule_mutfree r1 = true.
Proof.
  intros r1 r2 x H. unfold range_merge_pair in H.
  destruct (rule_mutfree r1); [reflexivity | discriminate H].
Qed.

(** When it fires, both inputs are EXACTLY the canonical range shells over the same
    field, with a common tail and agreeing end-fields. *)
Lemma range_merge_pair_shape : forall r1 r2 f iv1 iv2 body,
  range_merge_pair r1 r2 = Some (f, iv1, iv2, body) ->
  r1 = mk_head (MRange f false (fst iv1) (snd iv1)) body r1 /\
  r2 = mk_head (MRange f false (fst iv2) (snd iv2)) body r1.
Proof.
  intros r1 r2 f iv1 iv2 body H. unfold range_merge_pair in H.
  destruct (negb (rule_mutfree r1)); [discriminate |].
  destruct (head_range r1) as [[[[f1 lo1] hi1] rest1] |] eqn:H1; [| discriminate].
  destruct (head_range r2) as [[[[f2 lo2] hi2] rest2] |] eqn:H2; [| discriminate].
  destruct (field_eq_dec f1 f2) as [Ef |]; [| discriminate]. subst f2.
  destruct (list_eq_dec body_item_eq_dec rest1 rest2) as [Er |]; [| discriminate]. subst rest2.
  destruct (rule_end_eqb r1 r2) eqn:Eeqb; [| discriminate].
  inversion H; subst f iv1 iv2 body. clear H. cbn [fst snd].
  pose proof (head_range_canon r1 f1 lo1 hi1 rest1 H1) as Hr1.
  pose proof (head_range_canon r2 f1 lo2 hi2 rest1 H2) as Hr2c.
  pose proof (proj1 (rule_end_eqb_mk_head (MRange f1 false lo1 hi1) rest1 r1 r2) Eeqb) as Eshell.
  split; [exact Hr1 |].
  rewrite Hr2c. unfold mk_head in Eshell |- *.
  injection Eshell as Eo Ea.
  rewrite Eo, Ea. reflexivity.
Qed.

Lemma range_merge_pair_with_head : forall r1 r2 f lo1 hi1 body f' iv1 iv2 body',
  head_range r1 = Some (f, lo1, hi1, body) ->
  range_merge_pair r1 r2 = Some (f', iv1, iv2, body') ->
  f' = f /\ iv1 = (lo1, hi1) /\ body' = body /\
  r2 = mk_head (MRange f false (fst iv2) (snd iv2)) body r1.
Proof.
  intros r1 r2 f lo1 hi1 body f' iv1 iv2 body' Hhd Hvm.
  unfold range_merge_pair in Hvm.
  destruct (negb (rule_mutfree r1)); [discriminate Hvm |].
  rewrite Hhd in Hvm.
  destruct (head_range r2) as [[[[f2 lo2] hi2] rest2] |] eqn:H2; [| discriminate].
  destruct (field_eq_dec f f2) as [Ef |]; [| discriminate]. subst f2.
  destruct (list_eq_dec body_item_eq_dec body rest2) as [Er |]; [| discriminate]. subst rest2.
  destruct (rule_end_eqb r1 r2) eqn:Eeqb; [| discriminate].
  inversion Hvm; subst f' iv1 iv2 body'. clear Hvm. cbn [fst snd].
  pose proof (head_range_canon r2 f lo2 hi2 body H2) as Hr2c.
  pose proof (proj1 (rule_end_eqb_mk_head (MRange f false lo1 hi1) body r1 r2) Eeqb) as Eshell.
  repeat split.
  rewrite Hr2c. unfold mk_head in Eshell |- *.
  injection Eshell as Eo Ea.
  rewrite Eo, Ea. reflexivity.
Qed.

(** *** Collect the MAXIMAL run of following rules that each range-merge with [r1]. *)
Fixpoint take_range_run (r1 : rule) (rest : list rule)
  : list (data * data) * list rule :=
  match rest with
  | [] => ([], [])
  | r2 :: tl =>
      match range_merge_pair r1 r2 with
      | Some (_, _, iv2, _) =>
          let '(ivs, rest') := take_range_run r1 tl in (iv2 :: ivs, rest')
      | None => ([], rest)
      end
  end.

(** The matched prefix of [rest] is exactly the canonical range shells over its
    intervals, and [rest] splits as that prefix ++ [rest']. *)
Lemma take_range_run_shape : forall r1 f lo1 hi1 body rest ivs rest',
  head_range r1 = Some (f, lo1, hi1, body) ->
  take_range_run r1 rest = (ivs, rest') ->
  rest = map (fun iv => mk_head (MRange f false (fst iv) (snd iv)) body r1) ivs ++ rest'.
Proof.
  intros r1 f lo1 hi1 body rest. induction rest as [| r2 tl IH]; intros ivs rest' Hhd H.
  - cbn in H. inversion H; subst. reflexivity.
  - cbn in H. destruct (range_merge_pair r1 r2)
      as [[[[fa iva] iv2] bd] |] eqn:Evm.
    + destruct (take_range_run r1 tl) as [ivs0 rest0] eqn:Erec.
      inversion H; subst ivs rest'. clear H.
      destruct (range_merge_pair_with_head r1 r2 f lo1 hi1 body fa iva iv2 bd Hhd Evm)
        as [_ [_ [_ Hr2]]].
      cbn [map app]. rewrite <- Hr2, <- (IH ivs0 rest0 Hhd eq_refl). reflexivity.
    + inversion H; subst ivs rest'. reflexivity.
Qed.

(** *** The executable fuel-driven N-way interval-set pass. *)
Fixpoint optimize_rules_intervalset (fuel : nat) (n : nat) (d : set_decls) (rs : list rule)
  : nat * set_decls * list rule :=
  match fuel with
  | O => (n, d, rs)
  | S fuel' =>
    match rs with
    | r1 :: ((_ :: _) as rest) =>
        match head_range r1 with
        | Some (f, lo1, hi1, body) =>
            match take_range_run r1 rest with
            | ([], _) =>
                let '(n'', d'', rest') := optimize_rules_intervalset fuel' n d rest in
                (n'', d'', r1 :: rest')
            | ((_ :: _) as ivs, rest') =>
                let name := setname n in
                let elems := (lo1, hi1) :: ivs in
                let d' := {| sd_sets := (name, elems) :: sd_sets d;
                             sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
                let merged := mk_head (MConcatSet [f] false name) body r1 in
                let '(n'', d'', rest'') := optimize_rules_intervalset fuel' (S n) d' rest' in
                (n'', d'', merged :: rest'')
            end
        | None =>
            let '(n'', d'', rest') := optimize_rules_intervalset fuel' n d rest in
            (n'', d'', r1 :: rest')
        end
    | _ => (n, d, rs)
    end
  end.

Definition optimize_chain_intervalset (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n', d', rs') := optimize_rules_intervalset (length (c_rules c)) n d (c_rules c) in
  (n', d', {| c_policy := c_policy c; c_rules := rs' |}).

Lemma optimize_rules_intervalset_consSS : forall fuel n d r1 r2 rest,
  optimize_rules_intervalset (S fuel) n d (r1 :: r2 :: rest) =
  match head_range r1 with
  | Some (f, lo1, hi1, body) =>
      match take_range_run r1 (r2 :: rest) with
      | ([], _) =>
          let '(n'', d'', rest') := optimize_rules_intervalset fuel n d (r2 :: rest) in
          (n'', d'', r1 :: rest')
      | ((_ :: _) as ivs, rest') =>
          let name := setname n in
          let elems := (lo1, hi1) :: ivs in
          let d' := {| sd_sets := (name, elems) :: sd_sets d;
                       sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
          let merged := mk_head (MConcatSet [f] false name) body r1 in
          let '(n'', d'', rest'') := optimize_rules_intervalset fuel (S n) d' rest' in
          (n'', d'', merged :: rest'')
      end
  | None =>
      let '(n'', d'', rest') := optimize_rules_intervalset fuel n d (r2 :: rest) in
      (n'', d'', r1 :: rest')
  end.
Proof. reflexivity. Qed.

(** *** Structural invariants (mirror concat/concatguarded: mints [setname]s only). *)
Lemma optimize_rules_intervalset_mono : forall fuel n d rs n' d' rs',
  optimize_rules_intervalset fuel n d rs = (n', d', rs') -> n <= n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; lia.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; lia.
    + cbn in H. inversion H; subst; lia.
    + rewrite optimize_rules_intervalset_consSS in H.
      destruct (head_range r1) as [[[[f lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_range_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_intervalset fuel (S n) _ rest') as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n'.
           assert (S n <= m'')
             by (eapply (IH (S n) _ rest'); symmetry; exact Erec). lia.
      * remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_intervalset_vmaps : forall fuel n d rs n' d' rs',
  optimize_rules_intervalset fuel n d rs = (n', d', rs') -> sd_vmaps d' = sd_vmaps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_intervalset_consSS in H.
      destruct (head_range r1) as [[[[f lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_range_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_intervalset fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_intervalset_maps : forall fuel n d rs n' d' rs',
  optimize_rules_intervalset fuel n d rs = (n', d', rs') -> sd_maps d' = sd_maps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_intervalset_consSS in H.
      destruct (head_range r1) as [[[[f lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_range_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_intervalset fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_intervalset_keys_bound : forall fuel n d rs n' d' rs' k,
  optimize_rules_intervalset fuel n d rs = (n', d', rs') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' k H Hin.
  - cbn in H. inversion H; subst. left; exact Hin.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst. left; exact Hin.
    + cbn in H. inversion H; subst. left; exact Hin.
    + rewrite optimize_rules_intervalset_consSS in H.
      destruct (head_range r1) as [[[[f lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_range_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
        -- cbv zeta in H.
           remember (optimize_rules_intervalset fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'.
           destruct (IH (S n) _ rest' m'' dd'' rr'' k (eq_sym Erec) Hin) as [Hin_dn | Hlt].
           ++ cbn [sd_sets map] in Hin_dn. destruct Hin_dn as [Heq | Hin_d].
              ** apply setname_inj in Heq. subst k. right.
                 pose proof (optimize_rules_intervalset_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec)). lia.
              ** left; exact Hin_d.
           ++ right; exact Hlt.
      * remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
        subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
Qed.

(** *** Freshness bookkeeping: the pass only PREPENDS [sd_sets] entries keyed by
    [setname k] with [n <= k < n']. *)
Lemma optimize_rules_intervalset_assoc_stable : forall fuel n d rs n' d' rs' nm X,
  optimize_rules_intervalset fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X = assoc_str nm (sd_sets d) X.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' nm X H Hnm.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_intervalset_consSS in H.
      destruct (head_range r1) as [[[[f lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_range_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
        -- cbv zeta in H.
           remember (optimize_rules_intervalset fuel (S n)
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
      * remember (optimize_rules_intervalset fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
        eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
Qed.

(** *** Chain-level structural wrappers. *)
Lemma optimize_chain_intervalset_mono : forall n d c n' d' c',
  optimize_chain_intervalset n d c = (n', d', c') -> n <= n'.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_intervalset in H.
  destruct (optimize_rules_intervalset (length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_intervalset_mono _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_intervalset_vmaps : forall n d c n' d' c',
  optimize_chain_intervalset n d c = (n', d', c') -> sd_vmaps d' = sd_vmaps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_intervalset in H.
  destruct (optimize_rules_intervalset (length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_intervalset_vmaps _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_intervalset_maps : forall n d c n' d' c',
  optimize_chain_intervalset n d c = (n', d', c') -> sd_maps d' = sd_maps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_intervalset in H.
  destruct (optimize_rules_intervalset (length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_intervalset_maps _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_intervalset_keys_bound : forall n d c n' d' c' k,
  optimize_chain_intervalset n d c = (n', d', c') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  intros n d c n' d' c' k H Hin. unfold optimize_chain_intervalset in H.
  destruct (optimize_rules_intervalset (length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  apply (optimize_rules_intervalset_keys_bound _ _ _ _ _ _ _ k E Hin).
Qed.

(** *** The membership certificate: a single-field [MConcatSet] over an interval set
    is EXACTLY the [existsb] disjunction of the corresponding [MRange] matches. *)
Lemma eval_mrange_iv : forall f lo hi e q,
  eval_matchcond (MRange f false lo hi) e q
  = andb (field_loadable f q) (data_in_iv (field_value f e q) (lo, hi)).
Proof.
  intros f lo hi e q.
  unfold eval_matchcond, eval_matchcond_body, match_loadable.
  unfold eval_range, data_in_iv. cbn [fst snd]. reflexivity.
Qed.

Lemma match_loadable_mrange : forall f lo hi q,
  match_loadable (MRange f false lo hi) q = fields_loadable [f] q.
Proof.
  intros. cbn [match_loadable fields_loadable forallb]. rewrite Bool.andb_true_r.
  reflexivity.
Qed.

Lemma concat_set_ivs_existsb : forall f ivs name e q,
  e_set e name = ivs ->
  eval_matchcond (MConcatSet [f] false name) e q
  = existsb (fun iv => eval_matchcond (MRange f false (fst iv) (snd iv)) e q) ivs.
Proof.
  intros f ivs name e q Hset.
  unfold eval_matchcond at 1, eval_matchcond_body at 1.
  cbn [match_loadable fields_loadable forallb]. rewrite Bool.andb_true_r.
  destruct (field_loadable f q) eqn:Hld; cbn [andb].
  - cbn [map]. rewrite concat_set_mem_single. unfold set_mem. rewrite Hset.
    apply existsb_ext. intros [lo hi] Hiv.
    rewrite eval_mrange_iv, Hld. cbn [andb fst snd]. reflexivity.
  - symmetry. apply existsb_false_forall. intros iv Hiv.
    rewrite eval_mrange_iv, Hld. reflexivity.
Qed.

(** Every head in [map (fun iv => MRange f false (fst iv)(snd iv)) ivs] shares the
    same [match_loadable = fields_loadable [f]]. *)
Lemma match_loadable_range_run : forall f ivs q m,
  In m (map (fun iv => MRange f false (fst iv) (snd iv)) ivs) ->
  match_loadable m q = fields_loadable [f] q.
Proof.
  intros f ivs q m Hin. apply in_map_iff in Hin as [iv [Hm _]]. subst m.
  apply match_loadable_mrange.
Qed.
