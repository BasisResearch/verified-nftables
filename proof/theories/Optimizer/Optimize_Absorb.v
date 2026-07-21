(** * Optimize_Absorb: same-verdict PREFIX ABSORPTION (nft -o's covering-prefix fold).

    Battery shape 05:

        ip saddr 10.0.0.0/24 drop      (the SPECIFIC /24)
        ip saddr 10.0.0.0/16 drop      (the COVERING /16)

    The /24 is CONTAINED in the /16 and both carry the SAME verdict, so the covering
    /16 SUBSUMES the specific /24.  `nft -o` folds these into
    `ip saddr { 10.0.0.0/24, 10.0.0.0/16 }` which the KERNEL then NORMALISES to
    `{ 10.0.0.0/16 }` — i.e. it keeps only the covering prefix (confirmed against
    nft v1.1.6 in a netns: the committed ruleset is `ip saddr { 10.0.0.0/16 } drop`).
    We soundly DROP the subsumed /24 rule and keep the covering /16 — verdict-
    identical to the kernel's committed form, and trivially loadable (a subset of the
    original rules).

    The frontend lowers a BYTE-ALIGNED CIDR prefix `ip saddr A/8k` (post
    [normalize_chain]) to `MCmp (FPayload PNetwork off k) CEq (firstn k A)` — a
    k-byte payload compare over the network header (nft_lower.payload_prefix_field).
    So the /24 is a 3-byte compare and the /16 a 2-byte compare over the SAME base
    and offset.  A packet matching the LONGER (3-byte) compare necessarily matches
    the SHORTER (2-byte) one — prefix subsumption on [slice] (= [firstn]/[skipn]),
    with NO fixed-width side-condition.  When the specific rule PRECEDES the covering
    rule (as here), the covering rule at the specific rule's old position reproduces
    every verdict, so DROPPING the specific rule is verdict-preserving.

    The pass mints NO fresh names and touches NO set declaration ([n]/[d] pass
    through unchanged): it only DELETES a subsumed rule.  Axiom-free. *)

From Stdlib Require Import Ascii String.
From Stdlib Require Import List PeanoNat Bool Lia.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Optimize Optimize_ValueSet.
Import ListNotations.
Local Open Scope nat_scope.

Definition pbase_eq_dec (a b : pbase) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** *** Recogniser: a single byte-aligned payload-prefix head
    [BMatch (MCmp (FPayload b off w) CEq v) :: rest]. *)
Definition head_pfx (r : rule)
  : option (pbase * nat * nat * data * list body_item) :=
  match r_body r with
  | BMatch (MCmp (FPayload b off w) CEq v) :: rest => Some (b, off, w, v, rest)
  | _ => None
  end.

Lemma head_pfx_rbody : forall r b off w v body,
  head_pfx r = Some (b, off, w, v, body) ->
  r_body r = BMatch (MCmp (FPayload b off w) CEq v) :: body.
Proof.
  intros r b off w v body H. unfold head_pfx in H.
  destruct (r_body r) as [| [m | s] tl] eqn:Eb; try discriminate.
  destruct m as [ | | | | f op u | | | | | | | | ]; try discriminate.
  destruct f; try discriminate. destruct op; try discriminate.
  inversion H; subst. reflexivity.
Qed.

Lemma head_pfx_canon : forall r b off w v body,
  head_pfx r = Some (b, off, w, v, body) ->
  r = mk_head (MCmp (FPayload b off w) CEq v) body r.
Proof.
  intros r b off w v body H.
  pose proof (head_pfx_rbody r b off w v body H) as Hb.
  unfold mk_head. rewrite <- Hb. destruct r; reflexivity.
Qed.

(** Two rules form an eligible ABSORPTION pair iff [r1]'s head is a byte-prefix
    STRICTLY REFINING (or equal to) [r2]'s head over the SAME base/offset: a
    [w1]-byte compare against [v1] and a [w2]-byte compare against [v2] with
    [w2 <= w1], the values well-formed ([len v1 = w1], [len v2 = w2]) and [v2] the
    [w2]-byte prefix of [v1] ([firstn w2 v1 = v2]).  Same tail, same end-fields.
    Then a packet matching [r1] matches [r2], so [r1] is redundant given [r2]. *)
Definition absorb_pair (r1 r2 : rule)
  : option (pbase * nat * nat * nat * data * data * list body_item) :=
  (* EFFECT-SAFETY GUARD — see [Optimize_ValueSet.value_merge_pair].  Deleting
     the absorbed rule [r1] is only EFFECT-preserving when [r1] writes nothing
     (its body could otherwise run — and write — on a packet the surviving
     [r2] then re-matches). *)
  if negb (rule_mutfree r1) then None else
  match head_pfx r1, head_pfx r2 with
  | Some (b1, off1, w1, v1, rest1), Some (b2, off2, w2, v2, rest2) =>
      if pbase_eq_dec b1 b2 then
      if Nat.eq_dec off1 off2 then
      if Nat.leb w2 w1 then
      if Nat.eq_dec (length v1) w1 then
      if Nat.eq_dec (length v2) w2 then
      if list_eq_dec Nat.eq_dec (firstn w2 v1) v2 then
      if list_eq_dec body_item_eq_dec rest1 rest2 then
      if rule_end_eqb r1 r2
      then Some (b1, off1, w1, w2, v1, v2, rest1)
      else None
      else None else None else None else None else None else None else None
  | _, _ => None
  end.

(** The guard, extracted: a fired pair certifies the absorbed rule write-free. *)
Lemma absorb_pair_mutfree : forall r1 r2 x,
  absorb_pair r1 r2 = Some x -> rule_mutfree r1 = true.
Proof.
  intros r1 r2 x H. unfold absorb_pair in H.
  destruct (rule_mutfree r1); [reflexivity | discriminate H].
Qed.

Lemma absorb_pair_facts : forall r1 r2 b off w1 w2 v1 v2 body,
  absorb_pair r1 r2 = Some (b, off, w1, w2, v1, v2, body) ->
  r1 = mk_head (MCmp (FPayload b off w1) CEq v1) body r1 /\
  r2 = mk_head (MCmp (FPayload b off w2) CEq v2) body r1 /\
  w2 <= w1 /\ length v1 = w1 /\ length v2 = w2 /\ firstn w2 v1 = v2.
Proof.
  intros r1 r2 b off w1 w2 v1 v2 body H. unfold absorb_pair in H.
  destruct (negb (rule_mutfree r1)); [discriminate |].
  destruct (head_pfx r1) as [[[[[b1 off1] u1] s1] rest1] |] eqn:H1; [| discriminate].
  destruct (head_pfx r2) as [[[[[b2 off2] u2] s2] rest2] |] eqn:H2; [| discriminate].
  destruct (pbase_eq_dec b1 b2) as [Eb |]; [| discriminate]. subst b2.
  destruct (Nat.eq_dec off1 off2) as [Eoff |]; [| discriminate]. subst off2.
  destruct (Nat.leb u2 u1) eqn:Ele; [| discriminate].
  destruct (Nat.eq_dec (length s1) u1) as [Els1 |]; [| discriminate].
  destruct (Nat.eq_dec (length s2) u2) as [Els2 |]; [| discriminate].
  destruct (list_eq_dec Nat.eq_dec (firstn u2 s1) s2) as [Efn |]; [| discriminate].
  destruct (list_eq_dec body_item_eq_dec rest1 rest2) as [Erest |]; [| discriminate].
  subst rest2.
  destruct (rule_end_eqb r1 r2) eqn:Eeqb; [| discriminate].
  inversion H; subst b1 off1 w1 w2 v1 v2 body. clear H.
  pose proof (head_pfx_canon r1 b off u1 s1 rest1 H1) as Hr1.
  pose proof (head_pfx_canon r2 b off u2 s2 rest1 H2) as Hr2c.
  pose proof (proj1 (rule_end_eqb_mk_head (MCmp (FPayload b off u2) CEq s2) rest1 r1 r2) Eeqb)
    as Eshell.
  split; [exact Hr1 |].
  split; [rewrite Hr2c; symmetry; exact Eshell |].
  split; [apply Nat.leb_le; exact Ele |].
  split; [exact Els1 |].
  split; [exact Els2 | exact Efn].
Qed.

(** *** The abstract single-rule ABSORPTION step: dropping [r1] before [r2] is
    verdict-preserving whenever [r1] and [r2] have the SAME realised outcome and
    every firing of [r1] is also a firing of [r2] (so nothing that [r1] would have
    decided is lost — [r2], reached at [r1]'s old slot, decides it identically). *)
Lemma eval_rules_absorb_pair : forall r1 r2 rest e p,
  outcome r1 e p = outcome r2 e p ->
  (rule_loadable r1 e p && rule_applies r1 e p = true ->
   rule_loadable r2 e p && rule_applies r2 e p = true) ->
  eval_rules (r2 :: rest) e p = eval_rules (r1 :: r2 :: rest) e p.
Proof.
  intros r1 r2 rest e p Ho Hfire.
  transitivity
    (if rule_loadable r1 e p && rule_applies r1 e p
     then match outcome r1 e p with
          | Some v => if terminal v then Some v else eval_rules (r2 :: rest) e p
          | None => eval_rules (r2 :: rest) e p end
     else eval_rules (r2 :: rest) e p).
  2:{ reflexivity. }
  destruct (rule_loadable r1 e p && rule_applies r1 e p) eqn:E1.
  - specialize (Hfire eq_refl).
    destruct (outcome r1 e p) as [v |] eqn:Eo.
    + destruct (terminal v) eqn:Et; [| reflexivity].
      assert (Ho2 : outcome r2 e p = Some v) by (symmetry; exact Ho).
      change (eval_rules (r2 :: rest) e p) with
        (if rule_loadable r2 e p && rule_applies r2 e p
         then match outcome r2 e p with
              | Some w => if terminal w then Some w else eval_rules rest e p
              | None => eval_rules rest e p end
         else eval_rules rest e p).
      rewrite Hfire, Ho2, Et. reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

(** *** Head-level obligation discharge for two [mk_head] shells over a COMMON base
    rule: when [m1] loadable/matching implies [m2] loadable/matching, dropping the
    [m1] shell before the [m2] shell preserves every verdict. *)
Lemma eval_rules_absorb_mk : forall m1 m2 body rbase rest e p,
  (match_loadable m1 p = true -> match_loadable m2 p = true) ->
  (eval_matchcond m1 e p = true -> eval_matchcond m2 e p = true) ->
  eval_rules (mk_head m2 body rbase :: rest) e p
    = eval_rules (mk_head m1 body rbase :: mk_head m2 body rbase :: rest) e p.
Proof.
  intros m1 m2 body rbase rest e p Pload Peval.
  apply eval_rules_absorb_pair.
  - rewrite !outcome_mk_head. reflexivity.
  - intro Hf.
    rewrite rule_loadable_mk_head, rule_applies_mk_head in Hf.
    rewrite !rule_loadable_mk_head, !rule_applies_mk_head.
    apply andb_true_iff in Hf as [HL HA].
    apply andb_true_iff in HL as [Hml1 Hrest].
    apply andb_true_iff in HA as [Hev1 Hwalk].
    rewrite (Pload Hml1), Hrest, (Peval Hev1), Hwalk. reflexivity.
Qed.

(** *** The two concrete certificates: prefix subsumption on [read_payload]. *)
Lemma read_payload_ok_mono : forall b off w2 w1 p,
  w2 <= w1 -> read_payload_ok b off w1 p = true -> read_payload_ok b off w2 p = true.
Proof.
  intros b off w2 w1 p Hle H. unfold read_payload_ok in *.
  apply andb_true_iff in H as [Hlayer Hfit].
  apply andb_true_iff. split; [exact Hlayer |].
  apply Bool.negb_true_iff in Hfit. apply Bool.negb_true_iff.
  apply Nat.ltb_ge in Hfit. apply Nat.ltb_ge. lia.
Qed.

Lemma slice_prefix : forall bs off w2 w1,
  w2 <= w1 -> slice bs off w2 = firstn w2 (slice bs off w1).
Proof.
  intros bs off w2 w1 Hle. unfold slice.
  rewrite firstn_firstn, Nat.min_l by lia. reflexivity.
Qed.

Lemma firstn_len_slice : forall bs off w,
  firstn w (slice bs off w) = slice bs off w.
Proof.
  intros bs off w. apply firstn_all2.
  unfold slice. rewrite length_firstn. lia.
Qed.

Lemma read_payload_slice : forall b off len p,
  read_payload b off len p = slice (base_bytes b p) off len.
Proof. intros b off len p. destruct b; reflexivity. Qed.

(** *** The absorption-pair correctness: an eligible pair may drop its FIRST rule. *)
Lemma eval_rules_absorb_correct : forall r1 r2 tup rest e p,
  absorb_pair r1 r2 = Some tup ->
  eval_rules (r2 :: rest) e p = eval_rules (r1 :: r2 :: rest) e p.
Proof.
  intros r1 r2 [[[[[[b off] w1] w2] v1] v2] body] rest e p H.
  destruct (absorb_pair_facts r1 r2 b off w1 w2 v1 v2 body H)
    as [Hr1 [Hr2 [Hle [Hlv1 [Hlv2 Hfn]]]]].
  (* rewrite both rules to their common-base [mk_head] shells *)
  set (m1 := MCmp (FPayload b off w1) CEq v1) in *.
  set (m2 := MCmp (FPayload b off w2) CEq v2) in *.
  rewrite Hr1. rewrite Hr2.
  apply eval_rules_absorb_mk.
  - (* match_loadable m1 -> match_loadable m2 *)
    unfold m1, m2. cbn [match_loadable field_loadable field_load load_ok].
    apply read_payload_ok_mono. exact Hle.
  - (* eval_matchcond m1 -> eval_matchcond m2 *)
    unfold eval_matchcond, m1, m2, eval_matchcond_body.
    cbn [match_loadable field_loadable field_load load_ok].
    intro Hm1. apply andb_true_iff in Hm1 as [Hl1 Hb1].
    apply andb_true_iff. split.
    + apply (read_payload_ok_mono b off w2 w1 p Hle Hl1).
    + (* value test on the shorter compare *)
      cbn [eval_cmp field_value field_load do_load] in Hb1 |- *.
      rewrite read_payload_slice in Hb1. rewrite read_payload_slice.
      apply data_eqb_true_iff in Hb1. apply data_eqb_true_iff.
      rewrite Hlv1 in Hb1. rewrite firstn_len_slice in Hb1.
      rewrite Hlv2. rewrite firstn_len_slice.
      rewrite (slice_prefix (base_bytes b p) off w2 w1 Hle), Hb1. exact Hfn.
Qed.

(** *** The executable fuel-driven pass: sweep adjacent pairs, DROP the subsumed
    first rule and retry, else keep and advance. *)
Fixpoint optimize_rules_absorb (fuel : nat) (rs : list rule) : list rule :=
  match fuel with
  | O => rs
  | S fuel' =>
    match rs with
    | r1 :: ((r2 :: _) as rest) =>
        match absorb_pair r1 r2 with
        | Some _ => optimize_rules_absorb fuel' rest
        | None => r1 :: optimize_rules_absorb fuel' rest
        end
    | _ => rs
    end
  end.

(** The pass output rules are a SUBSET of the input rules (it only deletes). *)
Lemma optimize_rules_absorb_incl : forall fuel rs,
  incl (optimize_rules_absorb fuel rs) rs.
Proof.
  induction fuel as [| fuel IH]; intros rs.
  - apply incl_refl.
  - destruct rs as [| r1 [| r2 rest]].
    + apply incl_refl.
    + apply incl_refl.
    + cbn [optimize_rules_absorb]. destruct (absorb_pair r1 r2) eqn:Eap.
      * (* dropped r1 *) intros x Hx.
        specialize (IH (r2 :: rest) x Hx). right; exact IH.
      * (* kept r1 *) intros x Hx. destruct Hx as [-> | Hx]; [left; reflexivity |].
        specialize (IH (r2 :: rest) x Hx). right; exact IH.
Qed.

(** Cons congruence for [eval_rules] under a tail that is verdict-equal. *)
Lemma eval_rules_cons_cong : forall r tl tl' e p,
  eval_rules tl e p = eval_rules tl' e p ->
  eval_rules (r :: tl) e p = eval_rules (r :: tl') e p.
Proof.
  intros r tl tl' e p Htl. cbn [eval_rules].
  destruct (rule_loadable r e p && rule_applies r e p).
  - destruct (outcome r e p) as [v |]; [destruct (terminal v) |];
      rewrite ?Htl; reflexivity.
  - exact Htl.
Qed.

(** *** Verdict-preservation of the whole pass. *)
Lemma optimize_rules_absorb_eval : forall fuel rs e p,
  eval_rules (optimize_rules_absorb fuel rs) e p = eval_rules rs e p.
Proof.
  induction fuel as [| fuel IH]; intros rs e p.
  - reflexivity.
  - destruct rs as [| r1 [| r2 rest]].
    + reflexivity.
    + reflexivity.
    + cbn [optimize_rules_absorb]. destruct (absorb_pair r1 r2) eqn:Eap.
      * rewrite IH. apply (eval_rules_absorb_correct r1 r2 _ rest e p Eap).
      * apply eval_rules_cons_cong. apply IH.
Qed.

(** *** Chain wrapper (counter and declarations pass through UNCHANGED). *)
Definition absorb_chain (c : chain) : chain :=
  {| c_policy := c_policy c;
     c_rules := optimize_rules_absorb (length (c_rules c)) (c_rules c) |}.

Definition optimize_chain_absorb (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  (n, d, absorb_chain c).

Lemma optimize_chain_absorb_eq : forall n d c,
  optimize_chain_absorb n d c = (n, d, absorb_chain c).
Proof. reflexivity. Qed.

Lemma absorb_chain_eval : forall c e p,
  eval_chain (absorb_chain c) e p = eval_chain c e p.
Proof.
  intros c e p. unfold eval_chain, absorb_chain. cbn [c_rules c_policy].
  rewrite optimize_rules_absorb_eval. reflexivity.
Qed.

Lemma absorb_chain_rules_incl : forall c,
  incl (c_rules (absorb_chain c)) (c_rules c).
Proof.
  intro c. unfold absorb_chain. cbn [c_rules]. apply optimize_rules_absorb_incl.
Qed.

(** Freshness / any per-rule predicate transfers from the input chain (superset). *)
Lemma absorb_chain_Forall : forall (P : rule -> Prop) c,
  Forall P (c_rules c) -> Forall P (c_rules (absorb_chain c)).
Proof.
  intros P c HF. apply Forall_forall. intros r Hr.
  rewrite Forall_forall in HF. apply HF.
  apply (absorb_chain_rules_incl c). exact Hr.
Qed.

(** ** Non-vacuity witness: battery shape 05 (`ip saddr 10.0.0.0/24 drop` ;
    `ip saddr 10.0.0.0/16 drop`, both post-[normalize_chain]).  The frontend lowers
    the /24 to a 3-byte and the /16 to a 2-byte payload compare over network+12.
    The pass FIRES: [absorb_pair] recognises the subsumption and the fold drops the
    specific /24, leaving ONLY the covering /16 rule — exactly the kernel's committed
    normalisation of `nft -o`'s `{ 10.0.0.0/24, 10.0.0.0/16 }` to `{ 10.0.0.0/16 }`. *)
Definition drp_witness : rule :=
  {| r_body := [];
     r_outcome := OVerdict Drop; r_after := [] |}.

Definition absorb_05_r24 : rule :=
  mk_head (MCmp (FPayload PNetwork 12 3) CEq [10; 0; 0]) [] drp_witness.
Definition absorb_05_r16 : rule :=
  mk_head (MCmp (FPayload PNetwork 12 2) CEq [10; 0]) [] drp_witness.

(* the recogniser fires on the adjacent /24 (specific) then /16 (covering) pair *)
Example absorb_05_fires :
  absorb_pair absorb_05_r24 absorb_05_r16
  = Some (PNetwork, 12, 3, 2, [10; 0; 0], [10; 0], []).
Proof. reflexivity. Qed.

(* the fold collapses the two-rule chain to the single covering /16 rule *)
Example absorb_05_folds :
  optimize_rules_absorb 2 [absorb_05_r24; absorb_05_r16] = [absorb_05_r16].
Proof. reflexivity. Qed.

(* and it does NOT fire in the reverse direction (covering-first is not subsumed) *)
Example absorb_05_no_reverse :
  optimize_rules_absorb 2 [absorb_05_r16; absorb_05_r24]
  = [absorb_05_r16; absorb_05_r24].
Proof. reflexivity. Qed.
