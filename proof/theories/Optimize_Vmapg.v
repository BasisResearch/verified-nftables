(** * Optimize_Vmapg: the VERDICT-MAP merge over a single selector GUARDED by an
    implicit meta match (`tcp dport vmap { 22:drop, 80:accept, 443:drop }`).

    This is the vmap sibling of [Optimize_Setg] (which builds a value->SET for a run
    of same-verdict guarded rules) and the guarded analogue of [Optimize_Vmap]'s
    [optimize_rules_vmapN] (which folds an UNGUARDED single-selector run of
    DIFFERING-verdict rules into a verdict map).

    A bare transport selector like `tcp dport` is lowered by the frontend WITH its
    implicit L4-protocol dependency: `tcp dport Y w` becomes the guarded body

        [ MCmp meta_l4proto proto ; MCmp f CEq Y ]   (verdict w)

    — the l4proto guard sits BEFORE the port cmp.  [head_value] (used by the
    unguarded [optimize_rules_vmapN]) sees the GUARD as its head selector, whose
    value is shared across the run, so the vmap merge never fires.  This module
    recognises the guarded run

        [ GUARD ; MCmp f CEq v_i ] ++ body        (verdict w_i, i = 1..N)

    where GUARD is the shared l4proto dependency ([guard_ok]) and the verdicts DIFFER,
    and folds it — exactly as `nft --optimize` does — into ONE rule

        merged = [ GUARD ] ++ body  with  vmap key f -> { v_i : w_i }

    (a [mk_vmap_rule] whose body is [BMatch GUARD :: body]; the guard is KEPT in the
    body BEFORE the vmap key read, matching nft's netlink `[ meta ][ cmp ]` preceding
    the `[ lookup ]`).

    SOUNDNESS.  The heavy N-way vmap outcome argument is NOT re-proven: the guarded
    merge REDUCES to [Optimize_Vmap.eval_rules_vmap_mergeN] applied with body
    [BMatch GUARD :: body], composed with a per-rule SWAP equivalence
    ([orig_ruleGv_eq_swap]) that commutes the two leading pure matches (GUARD and
    the port cmp) — both are side-effect-free [BMatch]es, transparent to
    loadability / applicability / outcome and to [body_thread].  Every top-level
    lemma is axiom-free. *)

From Stdlib Require Import Ascii String List PeanoNat Bool Lia.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Optimize Optimize_Merge Optimize_Concat Optimize_ConcatM Optimize_Setg Optimize_Vmap.
Import ListNotations.
Local Open Scope nat_scope.

(** [guard_okn gm]: the NETWORK-LAYER counterpart of [Optimize_ConcatM.guard_ok]
    (l4proto) and [Optimize_Setg.guard_okl2] (iiftype).  A bare network-address
    selector `ip saddr X` / `ip daddr X` / `ip6 saddr X` / `ip6 daddr X` is lowered by
    the frontend in the `inet` family WITH an implicit `meta nfproto == <family>`
    dependency prepended (NFPROTO_IPV4 = 2 / NFPROTO_IPV6 = 10): the body becomes
    [MCmp FMetaNfproto CEq [family] ; MCmp f CEq v] — the nfproto guard sits BEFORE the
    address cmp, exactly the [Optimize_Vmapg] guarded single-selector shape.  Admitting
    this guard lets the SAME N-way verdict-map pass fold a run of differing-verdict
    `ip saddr <A> <w>` rules into ONE `ip saddr vmap { A : wA, .. }` lookup, precisely
    as `nft --optimize` does.

    The address fields [FIp4Saddr]/[FIp4Daddr] = [LPayload PNetwork _ 4] and
    [FIp6Saddr]/[FIp6Daddr] = [LPayload PNetwork _ 16] have [field_fixed_len] pinned to
    [Some 4] / [Some 16] — the exact fixed-width certificate [vmap_run_pairG] already
    demands of a transport port, so the merge is sound.  Distinct address literals are
    disjoint exact points => a VALID single-field vmap (no overlapping-interval defect).

    Every lemma in this module is guard-AGNOSTIC (soundness never inspects [gm]); the
    guard whitelist is purely an nft-fidelity gate, so admitting the nfproto guard adds
    a new fold WITHOUT weakening any proof. *)
Definition guard_okn (gm : matchcond) : bool :=
  match gm with
  | MCmp FMetaNfproto CEq _ => true
  | _ => false
  end.

(** ** The guarded original / merged shells. *)

(** The guarded original: a pure-terminal rule [mk_vmap_base w] behind the two head
    matches [GUARD] then [MCmp f CEq v].  This is [Optimize_Setg.orig_ruleGs] with
    the shared tail [r1] pinned to the pure-terminal [mk_vmap_base w]. *)
Definition orig_ruleGv (f : field) (gm : matchcond) (v : data)
    (body : list body_item) (w : verdict) : rule :=
  orig_ruleGs f gm v body (mk_vmap_base w).

(** The guarded merged rule: [Optimize_Vmap.mk_vmap_rule] over the body
    [BMatch gm :: body] — the guard is kept at the FRONT of the body (before the
    vmap key read), the single selector [f] becomes the vmap key. *)
Definition merged_ruleGv (f : field) (gm : matchcond) (nm : String.string)
    (body : list body_item) : rule :=
  mk_vmap_rule f nm (BMatch gm :: body).

(** *** The SWAP equivalence: the guarded original has the SAME per-rule
    [rule_loadable] / [rule_applies] / [outcome] as the UNGUARDED [orig_rule] over
    body [BMatch gm :: body] — i.e. commuting the two leading pure matches (GUARD
    and the port cmp) preserves every observable.  Both are [BMatch]es: transparent
    to [body_synproxy_stops] / [body_thread] and factored through [andb]
    commutativity in [body_loadable_walk] / [rule_applies_walk]. *)
Lemma orig_ruleGv_eq_swap : forall f gm v body w p,
  rule_loadable (orig_ruleGv f gm v body w) p
    = rule_loadable (orig_rule f v (BMatch gm :: body) w) p /\
  rule_applies (orig_ruleGv f gm v body w) p
    = rule_applies (orig_rule f v (BMatch gm :: body) w) p /\
  outcome (orig_ruleGv f gm v body w) p
    = outcome (orig_rule f v (BMatch gm :: body) w) p.
Proof.
  intros f gm v body w p.
  unfold orig_ruleGv, orig_ruleGs, orig_rule.
  split; [| split].
  - (* loadability *)
    rewrite !rule_loadable_mk_head.
    cbn [body_loadable_walk body_item_loadable].
    rewrite !synproxy_stops_bmatch, !body_thread_bmatch.
    (* both sides: 3 loadable booleans and a shared [if] term, reordered *)
    destruct (match_loadable gm p);
    destruct (match_loadable (MCmp f CEq v) p);
    destruct (body_loadable_walk body p); reflexivity.
  - (* applicability *)
    rewrite !rule_applies_mk_head.
    cbn [rule_applies_walk].
    destruct (eval_matchcond gm p);
    destruct (eval_matchcond (MCmp f CEq v) p);
    destruct (rule_applies_walk body p); reflexivity.
  - (* outcome: identical after removing the leading BMatch from stops/thread *)
    rewrite !outcome_mk_head.
    rewrite !synproxy_stops_bmatch, !body_thread_bmatch. reflexivity.
Qed.

(** eval_rules only reads a rule through [rule_loadable]/[rule_applies]/[outcome],
    so pointwise agreement of those over a mapped run (with a shared suffix)
    transfers to [eval_rules]. *)
Lemma eval_rules_map_cong :
  forall (A : Type) (g h : A -> rule) (l : list A) (rest : list rule) (p : packet),
  (forall a, In a l ->
     rule_loadable (g a) p = rule_loadable (h a) p /\
     rule_applies (g a) p = rule_applies (h a) p /\
     outcome (g a) p = outcome (h a) p) ->
  eval_rules (map g l ++ rest) p = eval_rules (map h l ++ rest) p.
Proof.
  intros A g h l rest p Hall.
  induction l as [| a l IH]; cbn [map app]; [reflexivity |].
  destruct (Hall a (or_introl eq_refl)) as [HL [HA HO]].
  cbn [eval_rules]. rewrite HL, HA, HO.
  rewrite (IH (fun a Hin => Hall a (or_intror Hin))). reflexivity.
Qed.

(** *** The guarded N-way verdict-map collapse, verdict-preserving.

    A run [map (fun '(v,w) => orig_ruleGv f gm v body w) es] of guarded same-field,
    DIFFERENT-verdict rules whose merged vmap [nm] carries the N point entries
    [map vmap_pt es] collapses to ONE [merged_ruleGv].  Proved by reducing to the
    unguarded [eval_rules_vmap_mergeN] on body [BMatch gm :: body] and applying the
    per-rule SWAP equivalence to each original. *)
Lemma eval_rules_vmap_mergeNg : forall f gm nm es body rest p,
  e_vmap (pkt_env p) nm = map vmap_pt es ->
  (forall v w, In (v, w) es -> field_fixed_len f = Some (length v)) ->
  (forall v w, In (v, w) es -> terminal w = true) ->
  body_synproxy_stops body p = false ->
  body_has_notrack body = false ->
  eval_rules (merged_ruleGv f gm nm body :: rest) p
  = eval_rules (map (fun vw => orig_ruleGv f gm (fst vw) body (snd vw)) es ++ rest) p.
Proof.
  intros f gm nm es body rest p Hvm Hfx Hterm Hsp Hnt.
  unfold merged_ruleGv.
  rewrite (eval_rules_vmap_mergeN f nm es (BMatch gm :: body) rest p Hvm Hfx Hterm
             ltac:(rewrite synproxy_stops_bmatch; exact Hsp)
             ltac:(rewrite has_notrack_bmatch; exact Hnt)).
  symmetry.
  apply (eval_rules_map_cong _
           (fun vw => orig_ruleGv f gm (fst vw) body (snd vw))
           (fun vw => orig_rule f (fst vw) (BMatch gm :: body) (snd vw))
           es rest p).
  intros [v w] _. apply (orig_ruleGv_eq_swap f gm v body w p).
Qed.

(** ** Recognise a guarded vmap-merge run pair (mirrors [Optimize_Vmap.vmap_run_pair]
    with the shared l4proto GUARD, as in [Optimize_Setg.value_mergeGs_pair]). *)

(** The compact END-shell test for the guarded original. *)
Lemma rule_end_eqb_orig_ruleGv : forall r gm f v rest,
  head_valueGs r = Some (gm, f, v, rest) ->
  (rule_end_eqb r (mk_vmap_base (r_verdict r)) = true
   <-> r = orig_ruleGv f gm v rest (r_verdict r)).
Proof.
  intros r gm f v rest Hhd.
  pose proof (head_valueGs_canon r gm f v rest Hhd) as Hself.
  (* r = mk_head gm (BMatch (MCmp f CEq v) :: rest) r *)
  unfold orig_ruleGv, orig_ruleGs.
  rewrite (rule_end_eqb_mk_head gm (BMatch (MCmp f CEq v) :: rest) r
             (mk_vmap_base (r_verdict r))).
  unfold orig_ruleGs in Hself. rewrite <- Hself at 1. reflexivity.
Qed.

Definition vmap_run_pairG (r1 r2 : rule)
  : option (matchcond * field * data * verdict * list body_item) :=
  match head_valueGs r1, head_valueGs r2 with
  | Some (gm1, f1, v1, rest1), Some (gm2, f2, v2, rest2) =>
      if matchcond_eq_dec gm1 gm2 then
      if guard_ok gm1 || guard_okn gm1 then
      if field_eq_dec f1 f2 then
      if list_eq_dec body_item_eq_dec rest1 rest2 then
      match field_fixed_len f1 with
      | Some len =>
        if Nat.eq_dec len (length v1) then
        if Nat.eq_dec len (length v2) then
        if terminal (r_verdict r1) then
        if terminal (r_verdict r2) then
        if rule_end_eqb r1 (mk_vmap_base (r_verdict r1)) then
        if rule_end_eqb r2 (mk_vmap_base (r_verdict r2)) then
          Some (gm1, f1, v2, r_verdict r2, rest1)
        else None else None
        else None else None else None else None
      | None => None
      end
      else None else None else None else None
  | _, _ => None
  end.

Lemma vmap_run_pairG_shape : forall r1 r2 gm f v2 w2 body,
  vmap_run_pairG r1 r2 = Some (gm, f, v2, w2, body) ->
  (exists v1, head_valueGs r1 = Some (gm, f, v1, body)
              /\ r1 = orig_ruleGv f gm v1 body (r_verdict r1)
              /\ field_fixed_len f = Some (length v1)
              /\ terminal (r_verdict r1) = true) /\
  r2 = orig_ruleGv f gm v2 body w2 /\
  field_fixed_len f = Some (length v2) /\ terminal w2 = true.
Proof.
  intros r1 r2 gm f v2 w2 body H. unfold vmap_run_pairG in H.
  destruct (head_valueGs r1) as [[[[gm1 f1] u1] s1] |] eqn:H1; [| discriminate].
  destruct (head_valueGs r2) as [[[[gm2 f2] u2] s2] |] eqn:H2; [| discriminate].
  destruct (matchcond_eq_dec gm1 gm2) as [Egm |]; [| discriminate]. subst gm2.
  destruct (guard_ok gm1 || guard_okn gm1) eqn:Egok; [| discriminate].
  destruct (field_eq_dec f1 f2) as [Ef |]; [| discriminate]. subst f2.
  destruct (list_eq_dec body_item_eq_dec s1 s2) as [Es |]; [| discriminate]. subst s2.
  destruct (field_fixed_len f1) as [len |] eqn:Hfx; [| discriminate].
  destruct (Nat.eq_dec len (length u1)) as [El1 |]; [| discriminate].
  destruct (Nat.eq_dec len (length u2)) as [El2 |]; [| discriminate].
  destruct (terminal (r_verdict r1)) eqn:Ew1; [| discriminate].
  destruct (terminal (r_verdict r2)) eqn:Ew2; [| discriminate].
  destruct (rule_end_eqb r1 (mk_vmap_base (r_verdict r1))) eqn:Eb1; [| discriminate].
  destruct (rule_end_eqb r2 (mk_vmap_base (r_verdict r2))) eqn:Eb2; [| discriminate].
  pose proof (proj1 (rule_end_eqb_orig_ruleGv r1 gm1 f1 u1 s1 H1) Eb1) as Esh1.
  pose proof (proj1 (rule_end_eqb_orig_ruleGv r2 gm1 f1 u2 s1 H2) Eb2) as Esh2.
  injection H as Egm' Ef' Ev2 Ew2' Ebody. subst gm f w2 body v2.
  assert (Hfx1 : field_fixed_len f1 = Some (length u1)) by (rewrite Hfx; f_equal; exact El1).
  assert (Hfx2 : field_fixed_len f1 = Some (length u2)) by (rewrite Hfx; f_equal; exact El2).
  split.
  - exists u1. repeat split; first [assumption | reflexivity].
  - repeat split; first [assumption | reflexivity].
Qed.

(** ** Executable N-WAY guarded vmap pass (mirrors [optimize_rules_vmapN]). *)

Fixpoint take_vmapG_run (r1 : rule) (rest : list rule)
  : list (data * verdict) * list rule :=
  match rest with
  | [] => ([], [])
  | r2 :: tl =>
      match vmap_run_pairG r1 r2 with
      | Some (_, _, v2, w2, _) =>
          let '(es, rest') := take_vmapG_run r1 tl in ((v2, w2) :: es, rest')
      | None => ([], rest)
      end
  end.

Lemma take_vmapG_run_shape : forall r1 gm f v1 body rest es rest',
  head_valueGs r1 = Some (gm, f, v1, body) ->
  take_vmapG_run r1 rest = (es, rest') ->
  rest = map (fun vw => orig_ruleGv f gm (fst vw) body (snd vw)) es ++ rest'
  /\ (forall v w, In (v, w) es -> field_fixed_len f = Some (length v))
  /\ (forall v w, In (v, w) es -> terminal w = true).
Proof.
  intros r1 gm f v1 body rest. induction rest as [| r2 tl IH]; intros es rest' Hhd H.
  - cbn in H. inversion H; subst. split; [reflexivity| split; intros v w []].
  - cbn in H. destruct (vmap_run_pairG r1 r2)
      as [[[[[gm2 fa] v2] w2] bd] |] eqn:Evm.
    + destruct (take_vmapG_run r1 tl) as [es0 rest0] eqn:Erec.
      inversion H; subst es rest'. clear H.
      destruct (vmap_run_pairG_shape r1 r2 gm2 fa v2 w2 bd Evm)
        as [[u1 [Hhd1 _]] [Hr2 [Hfx Hw2]]].
      rewrite Hhd in Hhd1. inversion Hhd1; subst gm2 fa bd.
      destruct (IH es0 rest0 Hhd eq_refl) as [Hsplit [Hall1 Hall2]].
      split; [| split].
      * cbn [map app fst snd]. rewrite <- Hr2, <- Hsplit. reflexivity.
      * intros v w [Hvw | Hin]; [ inversion Hvw; subst; exact Hfx | apply (Hall1 v w Hin) ].
      * intros v w [Hvw | Hin]; [ inversion Hvw; subst; exact Hw2 | apply (Hall2 v w Hin) ].
    + inversion H; subst es rest'. split; [reflexivity| split; intros v w []].
Qed.

Lemma take_vmapG_run_head : forall r1 gm f v1 body r2 rest es rest',
  head_valueGs r1 = Some (gm, f, v1, body) ->
  take_vmapG_run r1 (r2 :: rest) = (es, rest') ->
  es <> [] ->
  r1 = orig_ruleGv f gm v1 body (r_verdict r1) /\
  field_fixed_len f = Some (length v1) /\ terminal (r_verdict r1) = true.
Proof.
  intros r1 gm f v1 body r2 rest es rest' Hhd Hrun Hne.
  cbn in Hrun. destruct (vmap_run_pairG r1 r2)
    as [[[[[gm2 fa] v2] w2] bd] |] eqn:Evm.
  - destruct (vmap_run_pairG_shape r1 r2 gm2 fa v2 w2 bd Evm)
      as [[u1 [Hhd1 [Hr1 [Hfx1 Hw1]]]] _].
    rewrite Hhd in Hhd1. inversion Hhd1; subst gm2 fa u1 bd.
    split; [exact Hr1 | split; assumption].
  - destruct (take_vmapG_run r1 rest) as [es0 rest0] eqn:Erec0.
    inversion Hrun; subst. contradiction.
Qed.

Fixpoint optimize_rules_vmapNg (fuel n : nat) (d : set_decls) (rs : list rule)
  : nat * set_decls * list rule :=
  match fuel with
  | O => (n, d, rs)
  | S fuel' =>
    match rs with
    | r1 :: ((_ :: _) as rest) =>
        match head_valueGs r1 with
        | Some (gm, f, v1, body) =>
            match take_vmapG_run r1 rest with
            | ((_ :: _) as es, rest') =>
                if has_distinct_verdict (r_verdict r1) es && body_vmap_safe body then
                  let name := vmapname n in
                  let entries := (v1, r_verdict r1) :: es in
                  let d' := {| sd_sets := sd_sets d;
                               sd_vmaps := (name, map vmap_pt entries) :: sd_vmaps d;
                               sd_maps := sd_maps d |} in
                  let merged := merged_ruleGv f gm name body in
                  let '(n'', d'', rest'') := optimize_rules_vmapNg fuel' (S n) d' rest' in
                  (n'', d'', merged :: rest'')
                else
                  let '(n'', d'', rest') := optimize_rules_vmapNg fuel' n d rest in
                  (n'', d'', r1 :: rest')
            | ([], _) =>
                let '(n'', d'', rest') := optimize_rules_vmapNg fuel' n d rest in
                (n'', d'', r1 :: rest')
            end
        | None =>
            let '(n'', d'', rest') := optimize_rules_vmapNg fuel' n d rest in
            (n'', d'', r1 :: rest')
        end
    | _ => (n, d, rs)
    end
  end.

Definition optimize_chain_vmapNg (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  let '(n', d', rs') := optimize_rules_vmapNg (length (c_rules c)) n d (c_rules c) in
  (n', d', {| c_policy := c_policy c; c_rules := rs' |}).

Lemma optimize_rules_vmapNg_consSS : forall fuel n d r1 r2 rest,
  optimize_rules_vmapNg (S fuel) n d (r1 :: r2 :: rest) =
  match head_valueGs r1 with
  | Some (gm, f, v1, body) =>
      match take_vmapG_run r1 (r2 :: rest) with
      | ((_ :: _) as es, rest') =>
          if has_distinct_verdict (r_verdict r1) es && body_vmap_safe body then
            let name := vmapname n in
            let entries := (v1, r_verdict r1) :: es in
            let d' := {| sd_sets := sd_sets d;
                         sd_vmaps := (name, map vmap_pt entries) :: sd_vmaps d;
                         sd_maps := sd_maps d |} in
            let merged := merged_ruleGv f gm name body in
            let '(n'', d'', rest'') := optimize_rules_vmapNg fuel (S n) d' rest' in
            (n'', d'', merged :: rest'')
          else
            let '(n'', d'', rest') := optimize_rules_vmapNg fuel n d (r2 :: rest) in
            (n'', d'', r1 :: rest')
      | ([], _) =>
          let '(n'', d'', rest') := optimize_rules_vmapNg fuel n d (r2 :: rest) in
          (n'', d'', r1 :: rest')
      end
  | None =>
      let '(n'', d'', rest') := optimize_rules_vmapNg fuel n d (r2 :: rest) in
      (n'', d'', r1 :: rest')
  end.
Proof. reflexivity. Qed.

(** *** Freshness bookkeeping: the pass only PREPENDS [sd_vmaps] entries keyed by
    [vmapname k] with [n <= k < n']. *)
Lemma optimize_rules_vmapNg_assoc_stable : forall fuel n d rs n' d' rs' nm X,
  optimize_rules_vmapNg fuel n d rs = (n', d', rs') ->
  (forall k, n <= k -> nm <> vmapname k) ->
  assoc_str nm (sd_vmaps d') X = assoc_str nm (sd_vmaps d) X.
Proof.
  induction fuel as [| fuel IH]; intros n d rs n' d' rs' nm X H Hnm.
  - cbn in H. inversion H; subst; reflexivity.
  - destruct rs as [| r1 [| r2 rest] ].
    + cbn in H. inversion H; subst; reflexivity.
    + cbn in H. inversion H; subst; reflexivity.
    + rewrite optimize_rules_vmapNg_consSS in H.
      destruct (head_valueGs r1) as [[[[gm f] v1] body] |] eqn:Ehd.
      * destruct (take_vmapG_run r1 (r2 :: rest)) as [es rest'] eqn:Erun.
        destruct es as [| e es'].
        -- remember (optimize_rules_vmapNg fuel n d (r2 :: rest)) as tt eqn:Erec.
           destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
           injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
           eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
        -- destruct (has_distinct_verdict (r_verdict r1) (e :: es') && body_vmap_safe body) eqn:Hdv.
           2:{ remember (optimize_rules_vmapNg fuel n d (r2 :: rest)) as tt eqn:Erec.
               destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
               injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
               eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm]. }
           cbv zeta in H.
           remember (optimize_rules_vmapNg fuel (S n)
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
      * remember (optimize_rules_vmapNg fuel n d (r2 :: rest)) as tt eqn:Erec.
        destruct tt as [[m'' dd''] rr'']. cbv zeta in H.
        injection H as Hn' Hd' Hr'. subst d'. clear Hn' Hr'.
        eapply (IH n d (r2 :: rest)); [symmetry; exact Erec | exact Hnm].
Qed.
