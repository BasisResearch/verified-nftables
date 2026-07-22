(** * Optimize_IntervalSetGuarded: GUARDED interval / range set consolidation.

    [Optimize_IntervalSet] folds a run of BARE range heads [MRange f false lo hi] over the
    same field/body/verdict into ONE interval-set lookup.  But a transport selector
    like `tcp dport 20-30` — and a network selector like `ip saddr a-b` in an INET
    table — is lowered by the frontend WITH an implicit meta dependency in FRONT of
    the range:

        tcp dport 20-30  ==>  [ MCmp meta_l4proto 6 ; MRange th_dport false 20 30 ]
        ip saddr a-b     ==>  [ MCmp meta_nfproto 2 ; MRange ip_saddr false a  b  ]  (inet)

    The l4proto/nfproto guard sits BEFORE the range, so [Optimize_IntervalSet.head_range]
    (which expects [MRange] at the very head) never fires and the run is left
    unfolded — exactly the "transport-port-range-set" gap (and the inet network-range
    gap).  `nft --optimize` DOES fold both (confirmed against host nft v1.1.6 in a
    netns):

        tcp dport 20-30 accept ; tcp dport 31-40 accept
          =>  tcp dport { 20-30, 31-40 } accept
        ip saddr A ; ip saddr B (disjoint)  =>  ip saddr { A, B }

    This module handles that shape.  It recognises a run

        [ GUARD ; MRange f false lo_i hi_i ] ++ rest        (i = 1..N)

    where GUARD is a SHARED [MCmp FMetaL4proto/FMetaNfproto CEq _] (the transport /
    family dependency, [guard_okr]), and folds it — exactly as `nft --optimize` does —
    into ONE rule

        [ GUARD ; MConcatSet [f] false __setN ] ++ rest

    over the interval set [(lo_1,hi_1); …; (lo_N,hi_N)].  The guard is KEPT at the head
    (matching nft's netlink output).  The merged shell is [Optimize_SetGuarded.merged_ruleGs]
    (guard + single-field [MConcatSet]) VERBATIM.

    Verdict-preservation combines [Optimize_SetGuarded]'s [existsb_guardhead_factor] (the
    head guard factors out of the run's [existsb]) with [Optimize_IntervalSet]'s interval
    membership certificate [concat_set_ivs_existsb] (a single-field [MConcatSet] over
    an interval set is EXACTLY the [existsb] disjunction of the [MRange] matches).  No
    fixed-width side-condition — [data_le]-range membership coincides with interval-set
    membership.  Axiom-free. *)

From Stdlib Require Import Ascii String.
From Stdlib Require Import List PeanoNat Bool Lia Btauto.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Optimize Optimize_ValueSet Optimize_Concat Optimize_ConcatGuarded Optimize_SetGuarded Optimize_IntervalSet.
Import ListNotations.
Local Open Scope nat_scope.

(** [guard_okr gm]: the recogniser only fires when [gm] is the l4proto OR nfproto
    dependency, so the pass folds EXACTLY the transport-keyed / inet family-keyed
    ranges `nft -o` does — not an arbitrary shared middle match. *)
Definition guard_okr (gm : matchcond) : bool :=
  match gm with
  | MCmp FMetaL4proto CEq _ => true
  | MCmp FMetaNfproto CEq _ => true
  | _ => false
  end.

(** The guarded original range shell.  The merged shell is [merged_ruleGs]. *)
Definition orig_ruleGr (f : field) (gm : matchcond) (lo hi : data)
    (body : list body_item) (r1 : rule) : rule :=
  mk_head gm (BMatch (MRange f false lo hi) :: body) r1.

(** *** Recogniser: a guarded range head. *)
Definition head_rangeGr (r : rule)
  : option (matchcond * field * data * data * list body_item) :=
  match r_body r with
  | BMatch gm :: BMatch (MRange f false lo hi) :: rest => Some (gm, f, lo, hi, rest)
  | _ => None
  end.

Lemma head_rangeGr_rbody : forall r gm f lo hi body,
  head_rangeGr r = Some (gm, f, lo, hi, body) ->
  r_body r = BMatch gm :: BMatch (MRange f false lo hi) :: body.
Proof.
  intros r gm f lo hi body H. unfold head_rangeGr in H.
  destruct (r_body r) as [| [m | s] tl] eqn:Eb; try discriminate.
  destruct tl as [| [m2 | s2] tl2]; try discriminate.
  destruct m2 as [ | | | | | g lo' hi' | | | | | | | ]; try discriminate.
  destruct neg; try discriminate. inversion H; subst. reflexivity.
Qed.

Lemma head_rangeGr_canon : forall r gm f lo hi body,
  head_rangeGr r = Some (gm, f, lo, hi, body) ->
  r = orig_ruleGr f gm lo hi body r.
Proof.
  intros r gm f lo hi body H.
  pose proof (head_rangeGr_rbody r gm f lo hi body H) as Hb.
  unfold orig_ruleGr, mk_head. rewrite <- Hb. destruct r; reflexivity.
Qed.

(** Two guarded rules form an eligible RANGE-merge pair iff their heads are
    GUARD / [MRange f false lo_i hi_i] over the SAME field [f], the SAME guard, with
    the SAME tail and the SAME end-fields.  No fixed-width guard. *)
Definition range_mergeGr_pair (r1 r2 : rule)
  : option (matchcond * field * (data * data) * (data * data) * list body_item) :=
  (* EFFECT-SAFETY GUARD — see [Optimize_ValueSet.value_merge_pair]. *)
  if negb (rule_mutfree r1) then None else
  match head_rangeGr r1, head_rangeGr r2 with
  | Some (gm1, f1, lo1, hi1, rest1), Some (gm2, f2, lo2, hi2, rest2) =>
      if matchcond_eq_dec gm1 gm2 then
      if guard_okr gm1 then
      if field_eq_dec f1 f2 then
      if list_eq_dec body_item_eq_dec rest1 rest2 then
      if rule_end_eqb r1 r2
      then Some (gm1, f1, (lo1, hi1), (lo2, hi2), rest1)
      else None
      else None else None else None else None
  | _, _ => None
  end.

(** The guard, extracted: a fired pair certifies its canonical rule write-free. *)
Lemma range_mergeGr_pair_mutfree : forall r1 r2 x,
  range_mergeGr_pair r1 r2 = Some x -> rule_mutfree r1 = true.
Proof.
  intros r1 r2 x H. unfold range_mergeGr_pair in H.
  destruct (rule_mutfree r1); [reflexivity | discriminate H].
Qed.

Lemma range_mergeGr_pair_shape : forall r1 r2 gm f iv1 iv2 body,
  range_mergeGr_pair r1 r2 = Some (gm, f, iv1, iv2, body) ->
  r1 = orig_ruleGr f gm (fst iv1) (snd iv1) body r1 /\
  r2 = orig_ruleGr f gm (fst iv2) (snd iv2) body r1.
Proof.
  intros r1 r2 gm f iv1 iv2 body H. unfold range_mergeGr_pair in H.
  destruct (negb (rule_mutfree r1)); [discriminate |].
  destruct (head_rangeGr r1) as [[[[[gm1 f1] lo1] hi1] rest1] |] eqn:H1; [| discriminate].
  destruct (head_rangeGr r2) as [[[[[gm2 f2] lo2] hi2] rest2] |] eqn:H2; [| discriminate].
  destruct (matchcond_eq_dec gm1 gm2) as [Egm |]; [| discriminate]. subst gm2.
  destruct (guard_okr gm1) eqn:Egok; [| discriminate].
  destruct (field_eq_dec f1 f2) as [Ef |]; [| discriminate]. subst f2.
  destruct (list_eq_dec body_item_eq_dec rest1 rest2) as [Er |]; [| discriminate]. subst rest2.
  destruct (rule_end_eqb r1 r2) eqn:Eeqb; [| discriminate].
  inversion H; subst gm f iv1 iv2 body. clear H. cbn [fst snd].
  pose proof (head_rangeGr_canon r1 gm1 f1 lo1 hi1 rest1 H1) as Hr1.
  pose proof (head_rangeGr_canon r2 gm1 f1 lo2 hi2 rest1 H2) as Hr2c.
  pose proof (proj1 (rule_end_eqb_mk_head gm1
                       (BMatch (MRange f1 false lo1 hi1) :: rest1) r1 r2) Eeqb) as Eshell.
  split; [exact Hr1 |].
  rewrite Hr2c. unfold orig_ruleGr, mk_head in Eshell |- *.
  injection Eshell as Eo Ea.
  rewrite Eo, Ea. reflexivity.
Qed.

Lemma range_mergeGr_pair_with_head : forall r1 r2 gm f lo1 hi1 body gm' f' iv1 iv2 body',
  head_rangeGr r1 = Some (gm, f, lo1, hi1, body) ->
  range_mergeGr_pair r1 r2 = Some (gm', f', iv1, iv2, body') ->
  gm' = gm /\ f' = f /\ iv1 = (lo1, hi1) /\ body' = body /\
  r2 = orig_ruleGr f gm (fst iv2) (snd iv2) body r1.
Proof.
  intros r1 r2 gm f lo1 hi1 body gm' f' iv1 iv2 body' Hhd Hvm.
  unfold range_mergeGr_pair in Hvm.
  destruct (negb (rule_mutfree r1)); [discriminate Hvm |].
  rewrite Hhd in Hvm.
  destruct (head_rangeGr r2) as [[[[[gm2 f2] lo2] hi2] rest2] |] eqn:H2; [| discriminate].
  destruct (matchcond_eq_dec gm gm2) as [Egm |]; [| discriminate]. subst gm2.
  destruct (guard_okr gm) eqn:Egok; [| discriminate].
  destruct (field_eq_dec f f2) as [Ef |]; [| discriminate]. subst f2.
  destruct (list_eq_dec body_item_eq_dec body rest2) as [Er |]; [| discriminate]. subst rest2.
  destruct (rule_end_eqb r1 r2) eqn:Eeqb; [| discriminate].
  inversion Hvm; subst gm' f' iv1 iv2 body'. clear Hvm. cbn [fst snd].
  pose proof (head_rangeGr_canon r2 gm f lo2 hi2 body H2) as Hr2c.
  pose proof (proj1 (rule_end_eqb_mk_head gm (BMatch (MRange f false lo1 hi1) :: body) r1 r2) Eeqb) as Eshell.
  repeat split.
  rewrite Hr2c. unfold orig_ruleGr, mk_head in Eshell |- *.
  injection Eshell as Eo Ea.
  rewrite Eo, Ea. reflexivity.
Qed.

(** ** Loadability / outcome / applies of the guarded shells. *)

(** ** REPRESENTABILITY GATE.  A single-field nftables interval set is stored in the
    kernel [rbtree] backend, a strict PARTITION: its insert rejects ANY overlap in
    either order (net/netfilter/nft_set_rbtree.c).  So we may only emit a fold whose
    intervals are PAIRWISE DISJOINT (no shared point) — otherwise the synthesised
    object is UNLOADABLE (that is exactly the `nft --optimize` defect we must not
    replicate; see proof/battery_cases/README.md).  Our verdict-preservation proof
    holds for ANY interval list, so this gate only RESTRICTS when the pass fires; it
    is a validity (loadability) filter, never a soundness one.  A run with any overlap
    is DECLINED (left unfolded — a correct deferral). *)
Definition data_lt (a b : data) : bool := andb (data_le a b) (negb (data_eqb a b)).

(** Two closed ranges [a,b],[c,d] are DISJOINT iff one lies strictly below the other
    ([b < c] or [d < a]) — no shared endpoint (a touch [b = c] is an rbtree overlap). *)
Definition iv_disjoint (i j : data * data) : bool :=
  orb (data_lt (snd i) (fst j)) (data_lt (snd j) (fst i)).

Fixpoint all_disjoint (l : list (data * data)) : bool :=
  match l with
  | [] => true
  | i :: tl => andb (forallb (iv_disjoint i) tl) (all_disjoint tl)
  end.

(** ** Executable N-WAY guarded interval-set pass (fuel-driven). *)

(** Collect the MAXIMAL run of following rules that each range-merge with [r1]. *)
Fixpoint take_rangeg_run_raw (r1 : rule) (rest : list rule)
  : list (data * data) * list rule :=
  match rest with
  | [] => ([], [])
  | r2 :: tl =>
      match range_mergeGr_pair r1 r2 with
      | Some (_, _, _, iv2, _) =>
          let '(ivs, rest') := take_rangeg_run_raw r1 tl in (iv2 :: ivs, rest')
      | None => ([], rest)
      end
  end.

(** The consolidated run, GATED by the representability filter: if the run's
    intervals (including [r1]'s [(lo1,hi1)]) are not pairwise disjoint, we DECLINE
    the fold by returning the EMPTY run ([optimize_rules_intervalsetguarded] then keeps [r1] and
    recurses).  Returning [([], rest)] keeps the [take_rangeg_run_shape] invariant. *)
Definition take_rangeg_run (r1 : rule) (rest : list rule)
  : list (data * data) * list rule :=
  match head_rangeGr r1 with
  | Some (_, _, lo1, hi1, _) =>
      let '(ivs, rest') := take_rangeg_run_raw r1 rest in
      if all_disjoint ((lo1, hi1) :: ivs) then (ivs, rest') else ([], rest)
  | None => ([], rest)
  end.

Lemma take_rangeg_run_raw_shape : forall r1 gm f lo1 hi1 body rest ivs rest',
  head_rangeGr r1 = Some (gm, f, lo1, hi1, body) ->
  take_rangeg_run_raw r1 rest = (ivs, rest') ->
  rest = map (fun iv => orig_ruleGr f gm (fst iv) (snd iv) body r1) ivs ++ rest'.
Proof.
  intros r1 gm f lo1 hi1 body rest. induction rest as [| r2 tl IH]; intros ivs rest' Hhd H.
  - cbn in H. inversion H; subst. reflexivity.
  - cbn in H. destruct (range_mergeGr_pair r1 r2)
      as [[[[[gm2 fa] iva] iv2] bd] |] eqn:Evm.
    + destruct (take_rangeg_run_raw r1 tl) as [ivs0 rest0] eqn:Erec.
      inversion H; subst ivs rest'. clear H.
      destruct (range_mergeGr_pair_with_head r1 r2 gm f lo1 hi1 body gm2 fa iva iv2 bd Hhd Evm)
        as [_ [_ [_ [_ Hr2]]]].
      cbn [map app]. rewrite <- Hr2, <- (IH ivs0 rest0 Hhd eq_refl). reflexivity.
    + inversion H; subst ivs rest'. reflexivity.
Qed.

(** The gate preserves the split invariant: the matched prefix is the canonical
    range shells over its intervals, whether or not the fold is declined. *)
Lemma take_rangeg_run_shape : forall r1 gm f lo1 hi1 body rest ivs rest',
  head_rangeGr r1 = Some (gm, f, lo1, hi1, body) ->
  take_rangeg_run r1 rest = (ivs, rest') ->
  rest = map (fun iv => orig_ruleGr f gm (fst iv) (snd iv) body r1) ivs ++ rest'.
Proof.
  intros r1 gm f lo1 hi1 body rest ivs rest' Hhd H.
  unfold take_rangeg_run in H. rewrite Hhd in H.
  destruct (take_rangeg_run_raw r1 rest) as [ivs0 rest0] eqn:Eraw.
  destruct (all_disjoint ((lo1, hi1) :: ivs0)) eqn:Hdisj.
  - inversion H; subst ivs rest'.
    apply (take_rangeg_run_raw_shape r1 gm f lo1 hi1 body rest ivs0 rest0 Hhd Eraw).
  - inversion H; subst ivs rest'. reflexivity.
Qed.

Fixpoint optimize_rules_intervalsetguarded (fuel : nat) (n : nat) (d : set_decls) (rs : list rule)
  : nat * set_decls * list rule :=
  match fuel with
  | O => (n, d, rs)
  | S fuel' =>
    match rs with
    | r1 :: ((_ :: _) as rest) =>
        match head_rangeGr r1 with
        | Some (gm, f, lo1, hi1, body) =>
            match take_rangeg_run r1 rest with
            | ([], _) =>
                let '(n'', d'', rest') := optimize_rules_intervalsetguarded fuel' n d rest in
                (n'', d'', r1 :: rest')
            | ((_ :: _) as ivs, rest') =>
                let name := setname n in
                let elems := (lo1, hi1) :: ivs in
                let d' := {| sd_sets := (name, elems) :: sd_sets d;
                             sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
                let merged := merged_ruleGs f gm name body r1 in
                let '(n'', d'', rest'') := optimize_rules_intervalsetguarded fuel' (S n) d' rest' in
                (n'', d'', merged :: rest'')
            end
        | None =>
            let '(n'', d'', rest') := optimize_rules_intervalsetguarded fuel' n d rest in
            (n'', d'', r1 :: rest')
        end
    | _ => (n, d, rs)
    end
  end.

Definition optimize_chain_intervalsetguarded (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n', d', rs') := optimize_rules_intervalsetguarded (length (c_rules c)) n d (c_rules c) in
  (n', d', {| c_policy := c_policy c; c_rules := rs' |}).

Lemma optimize_rules_intervalsetguarded_consSS : forall fuel n d r1 r2 rest,
  optimize_rules_intervalsetguarded (S fuel) n d (r1 :: r2 :: rest) =
  match head_rangeGr r1 with
  | Some (gm, f, lo1, hi1, body) =>
      match take_rangeg_run r1 (r2 :: rest) with
      | ([], _) =>
          let '(n'', d'', rest') := optimize_rules_intervalsetguarded fuel n d (r2 :: rest) in
          (n'', d'', r1 :: rest')
      | ((_ :: _) as ivs, rest') =>
          let name := setname n in
          let elems := (lo1, hi1) :: ivs in
          let d' := {| sd_sets := (name, elems) :: sd_sets d;
                       sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} in
          let merged := merged_ruleGs f gm name body r1 in
          let '(n'', d'', rest'') := optimize_rules_intervalsetguarded fuel (S n) d' rest' in
          (n'', d'', merged :: rest'')
      end
  | None =>
      let '(n'', d'', rest') := optimize_rules_intervalsetguarded fuel n d (r2 :: rest) in
      (n'', d'', r1 :: rest')
  end.
Proof. reflexivity. Qed.

(** *** Structural invariants (mint [setname]s only; vmaps/maps untouched). *)
Lemma optimize_rules_intervalsetguarded_mono : forall fuel n d rs n' d' rs',
  optimize_rules_intervalsetguarded fuel n d rs = (n', d', rs') -> n <= n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; lia.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; lia.
    + cbn in H. inversion H; subst; lia.
    + rewrite optimize_rules_intervalsetguarded_consSS in H.
      destruct (head_rangeGr r1) as [[[[[gm f] lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_rangeg_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_intervalsetguarded fuel (S n) _ rest') as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst n'.
           assert (S n <= m'')
             by (eapply (IH (S n) _ rest'); symmetry; exact Erec). lia.
      * remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_intervalsetguarded_vmaps : forall fuel n d rs n' d' rs',
  optimize_rules_intervalsetguarded fuel n d rs = (n', d', rs') -> sd_vmaps d' = sd_vmaps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_intervalsetguarded_consSS in H.
      destruct (head_rangeGr r1) as [[[[[gm f] lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_rangeg_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_intervalsetguarded fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_intervalsetguarded_maps : forall fuel n d rs n' d' rs',
  optimize_rules_intervalsetguarded fuel n d rs = (n', d', rs') -> sd_maps d' = sd_maps d.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' H.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_intervalsetguarded_consSS in H.
      destruct (head_rangeGr r1) as [[[[[gm f] lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_rangeg_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
           eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
        -- cbv zeta in H.
           remember (optimize_rules_intervalsetguarded fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'.
           rewrite (IH (S n) _ rest' _ dd'' rr'' (eq_sym Erec)). reflexivity.
      * remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. inversion H; subst.
        eapply (IH n d (r2 :: rest)); symmetry; exact Erec.
Qed.

Lemma optimize_rules_intervalsetguarded_keys_bound : forall fuel n d rs n' d' rs' k,
  optimize_rules_intervalsetguarded fuel n d rs = (n', d', rs') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' k H Hin.
  - cbn in H. inversion H; subst. left; exact Hin.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst. left; exact Hin.
    + cbn in H. inversion H; subst. left; exact Hin.
    + rewrite optimize_rules_intervalsetguarded_consSS in H.
      destruct (head_rangeGr r1) as [[[[[gm f] lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_rangeg_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
        -- cbv zeta in H.
           remember (optimize_rules_intervalsetguarded fuel (S n)
                       {| sd_sets := (setname n, (lo1, hi1) :: iv :: ivs') :: sd_sets d;
                          sd_vmaps := sd_vmaps d; sd_maps := sd_maps d |} rest')
             as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
           subst n' d' rs'.
           destruct (IH (S n) _ rest' m'' dd'' rr'' k (eq_sym Erec) Hin) as [Hin_dn | Hlt].
           ++ cbn [sd_sets map] in Hin_dn. destruct Hin_dn as [Heq | Hin_d].
              ** apply setname_inj in Heq. subst k. right.
                 pose proof (optimize_rules_intervalsetguarded_mono fuel (S n) _ rest' m'' dd'' rr'' (eq_sym Erec)). lia.
              ** left; exact Hin_d.
           ++ right; exact Hlt.
      * remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H. injection H as Hn' Hd' Hr'.
        subst n' d' rs'. eapply (IH n d (r2 :: rest) m'' dd'' rr'' k (eq_sym Erec) Hin).
Qed.

Lemma optimize_rules_intervalsetguarded_assoc_stable : forall fuel n d rs n' d' rs' nm X,
  optimize_rules_intervalsetguarded fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> nm <> setname k) ->
  assoc_str nm (sd_sets d') X = assoc_str nm (sd_sets d) X.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' nm X H Hnm.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_intervalsetguarded_consSS in H.
      destruct (head_rangeGr r1) as [[[[[gm f] lo1] hi1] body] |] eqn:Ehd.
      * destruct (take_rangeg_run r1 (r2 :: rest)) as [ivs rest'] eqn:Erun.
        destruct ivs as [| iv ivs'].
        -- remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
        -- cbv zeta in H.
           remember (optimize_rules_intervalsetguarded fuel (S n)
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
      * remember (optimize_rules_intervalsetguarded fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
        eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
Qed.

(** *** Chain-level structural wrappers. *)
Lemma optimize_chain_intervalsetguarded_mono : forall n d c n' d' c',
  optimize_chain_intervalsetguarded n d c = (n', d', c') -> n <= n'.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_intervalsetguarded in H.
  destruct (optimize_rules_intervalsetguarded (length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_intervalsetguarded_mono _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_intervalsetguarded_vmaps : forall n d c n' d' c',
  optimize_chain_intervalsetguarded n d c = (n', d', c') -> sd_vmaps d' = sd_vmaps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_intervalsetguarded in H.
  destruct (optimize_rules_intervalsetguarded (length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_intervalsetguarded_vmaps _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_intervalsetguarded_maps : forall n d c n' d' c',
  optimize_chain_intervalsetguarded n d c = (n', d', c') -> sd_maps d' = sd_maps d.
Proof.
  intros n d c n' d' c' H. unfold optimize_chain_intervalsetguarded in H.
  destruct (optimize_rules_intervalsetguarded (length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst. apply (optimize_rules_intervalsetguarded_maps _ _ _ _ _ _ _ E).
Qed.

Lemma optimize_chain_intervalsetguarded_keys_bound : forall n d c n' d' c' k,
  optimize_chain_intervalsetguarded n d c = (n', d', c') ->
  In (setname k) (map fst (sd_sets d')) ->
  In (setname k) (map fst (sd_sets d)) \/ k < n'.
Proof.
  intros n d c n' d' c' k H Hin. unfold optimize_chain_intervalsetguarded in H.
  destruct (optimize_rules_intervalsetguarded (length (c_rules c)) n d (c_rules c))
    as [[m'' dd''] rr''] eqn:E.
  inversion H; subst n' d' c'.
  apply (optimize_rules_intervalsetguarded_keys_bound _ _ _ _ _ _ _ k E Hin).
Qed.
