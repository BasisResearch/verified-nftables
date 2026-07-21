(** * Optimize_PayMerge: the adjacent-payload-load merge (corpus class I).

    nftables fuses two consecutive payload EQUALITY matches whose loads are
    byte-contiguous in the SAME header into one wider load+compare — e.g.
    `tcp sport 1 tcp dport 2` becomes a single 4-byte `payload load 4b @
    transport header + 0 ; cmp eq 0x00010002` instead of two 2-byte loads.  The
    merge decision is nft's own [payload_can_merge] (src/payload.c): adjacent,
    same base, combined width in [1,NFT_REG_SIZE=16] bytes, and either the
    combined width fits the u32 fast path (<= 4 bytes), or the base is the link
    layer, or one side is already wider than a u32 — the fast-path caveats that
    keep e.g. `tcp sport tcp dport tcp sequence` from over-merging past 4 bytes
    on the transport base (src/payload.c:1466-1478) while still merging
    `ether saddr` + `ether type` to 8 bytes on the link base.

    The pass is SELF-GUARDING: it rewrites ONLY where the syntactic precondition
    (two adjacent full-width payload equalities) holds, so its correctness is
    UNCONDITIONAL — [eval_chain (paymerge_chain c) e p = eval_chain c e p] for
    every chain, env and packet, no hypotheses.  The load-bearing fact is that a
    payload read splits at any interior offset ([read_payload_split]) and its
    loadability splits the same way ([read_payload_ok_split]) — both hold for
    ALL packets (a short/absent header fails the wide read exactly when it fails
    one of the parts), so no byte- or length-well-formedness hypothesis is
    needed.  Axiom-free. *)

From Stdlib Require Import List Bool Arith Lia.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics.
Import ListNotations.

(** Decidable equality on payload bases. *)
Definition pbase_eqb (a b : pbase) : bool :=
  match a, b with
  | PLink, PLink | PNetwork, PNetwork | PTransport, PTransport
  | PInner, PInner | PTunnel, PTunnel => true
  | _, _ => false
  end.

Lemma pbase_eqb_eq : forall a b, pbase_eqb a b = true -> a = b.
Proof. intros [] []; simpl; congruence. Qed.

(** *** A payload read splits at any interior offset [l1]. *)
Lemma firstn_plus : forall (A : Type) n m (l : list A),
  firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
  induction n as [|k IH]; intros m l; [reflexivity|].
  destruct l as [|x xs]; simpl; [now rewrite firstn_nil|].
  rewrite IH. reflexivity.
Qed.

Lemma slice_split : forall bs o l1 l2,
  slice bs o (l1 + l2) = slice bs o l1 ++ slice bs (o + l1) l2.
Proof.
  intros bs o l1 l2. unfold slice.
  rewrite firstn_plus.
  f_equal. rewrite skipn_skipn.
  replace (l1 + o) with (o + l1) by lia. reflexivity.
Qed.

Lemma read_payload_split : forall b o l1 l2 p,
  read_payload b o (l1 + l2) p
  = read_payload b o l1 p ++ read_payload b (o + l1) l2 p.
Proof.
  intros b o l1 l2 p. destruct b; apply slice_split.
Qed.

(** Its loadability splits the same way: the wide read loads iff BOTH parts do
    (the layer guard is shared; the length guard [off+len <= |hdr|] for the whole
    holds iff it holds for the far part, which subsumes the near part). *)
Lemma read_payload_ok_split : forall b o l1 l2 p,
  read_payload_ok b o (l1 + l2) p
  = read_payload_ok b o l1 p && read_payload_ok b (o + l1) l2 p.
Proof.
  intros b o l1 l2 p. unfold read_payload_ok.
  replace (o + (l1 + l2)) with ((o + l1) + l2) by lia.
  set (layer := match b with
                | PTransport | PInner => pkt_have_l4 p && (pkt_fragoff p =? 0)
                | PLink => pkt_have_l2 p | _ => true end).
  set (len := length (base_bytes b p)).
  (* goal: layer && negb (len <? (o+l1)+l2)
         = (layer && negb (len <? o+l1)) && (layer && negb (len <? (o+l1)+l2)) *)
  destruct (Nat.ltb len (o + l1)) eqn:E1;
    destruct (Nat.ltb len ((o + l1) + l2)) eqn:E2;
    destruct layer; cbn; try reflexivity;
    (* only the impossible len<o+l1 yet len>=(o+l1)+l2 branch survives *)
    apply Nat.ltb_lt in E1; apply Nat.ltb_ge in E2; lia.
Qed.

Lemma read_payload_len_le : forall b o l p,
  read_payload_ok b o l p = true -> length (read_payload b o l p) = l.
Proof.
  intros b o l p H. unfold read_payload_ok in H.
  apply andb_true_iff in H as [_ H]. apply negb_true_iff, Nat.ltb_ge in H.
  destruct b; unfold read_payload, slice, base_bytes in *;
    rewrite length_firstn, length_skipn; lia.
Qed.

(** Same-length head splits list equality into head- and tail-equality. *)
Lemma app_head_eq : forall (A : Type) (a c b d : list A),
  length a = length c -> a ++ b = c ++ d -> a = c /\ b = d.
Proof.
  induction a as [|x a IH]; destruct c as [|y c]; simpl; intros b d Hl H;
    try discriminate.
  - split; [reflexivity | exact H].
  - injection Hl as Hl. injection H as -> H.
    destruct (IH c b d Hl H) as [<- <-]. split; reflexivity.
Qed.

(** data_eqb of two concatenations with a matching split point. *)
Lemma data_eqb_app : forall a b c d, length a = length c ->
  data_eqb (a ++ b) (c ++ d) = data_eqb a c && data_eqb b d.
Proof.
  intros a b c d Hlen.
  destruct (data_eqb a c) eqn:Eac; simpl.
  - apply data_eqb_true_iff in Eac; subst c.
    destruct (data_eqb b d) eqn:Ebd.
    + apply data_eqb_true_iff in Ebd; subst d. apply data_eqb_refl.
    + destruct (data_eqb (a ++ b) (a ++ d)) eqn:E; [|reflexivity].
      apply data_eqb_true_iff in E. apply app_inv_head in E. subst d.
      rewrite data_eqb_refl in Ebd; discriminate.
  - destruct (data_eqb (a ++ b) (c ++ d)) eqn:E; [|reflexivity].
    apply data_eqb_true_iff in E.
    apply (app_head_eq _ a c b d Hlen) in E as [Eac' _].
    subst c. rewrite data_eqb_refl in Eac; discriminate.
Qed.

(** *** The merge is exact on a single [eval_matchcond], for two adjacent
    full-width payload equalities on the same base. *)
Lemma merge_eval_ok : forall b o1 l1 v1 l2 v2 e p,
  length v1 = l1 -> length v2 = l2 ->
  eval_matchcond (MEq (FPayload b o1 (l1 + l2)) (v1 ++ v2)) e p
  = eval_matchcond (MEq (FPayload b o1 l1) v1) e p
    && eval_matchcond (MEq (FPayload b (o1 + l1) l2) v2) e p.
Proof.
  intros b o1 l1 v1 l2 v2 e p Hv1 Hv2.
  unfold eval_matchcond, match_loadable, eval_matchcond_body, field_loadable,
         field_value, field_load, load_ok.
  cbn [field_load].
  rewrite (read_payload_ok_split b o1 l1 l2 p).
  set (ld1 := read_payload_ok b o1 l1 p).
  set (ld2 := read_payload_ok b (o1 + l1) l2 p).
  destruct ld1 eqn:E1; destruct ld2 eqn:E2; simpl.
  - (* both loadable: reads have exact lengths; the cmp splits *)
    assert (Hr1 : length (read_payload b o1 l1 p) = l1)
      by (apply read_payload_len_le; exact E1).
    rewrite (read_payload_split b o1 l1 l2 p).
    cbn [eval_cmp].
    rewrite length_app, Hv1, Hv2.
    (* firstn (l1+l2) (r1 ++ r2) = r1 ++ firstn l2 r2 *)
    rewrite firstn_app, Hr1.
    replace (l1 + l2 - l1) with l2 by lia.
    rewrite firstn_all2 with (n := l1 + l2) (l := read_payload b o1 l1 p)
      by (rewrite Hr1; lia).
    rewrite (data_eqb_app (read_payload b o1 l1 p)
               (firstn l2 (read_payload b (o1 + l1) l2 p)) v1 v2)
      by (rewrite Hr1; lia).
    rewrite firstn_all2 with (n := l1) (l := read_payload b o1 l1 p)
      by (rewrite Hr1; lia).
    reflexivity.
  - now rewrite !andb_false_r.
  - reflexivity.
  - reflexivity.
Qed.

(** [MEq f v] and [MCmp f CEq v] depend on [f] only through [field_load]; a
    payload field is interchangeable with the raw [FPayload] of its load. *)
Lemma eval_MEq_field_load : forall f b o l v e p,
  field_load f = LPayload b o l ->
  eval_matchcond (MEq f v) e p = eval_matchcond (MEq (FPayload b o l) v) e p.
Proof.
  intros f b o l v e p Hf.
  unfold eval_matchcond, match_loadable, eval_matchcond_body, field_loadable,
         field_value.
  rewrite Hf. reflexivity.
Qed.

Lemma eval_MCmpEq_is_MEq : forall f v e p,
  eval_matchcond (MCmp f CEq v) e p = eval_matchcond (MEq f v) e p.
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(** ** The pass. *)

(** A matchcond that is a full-width payload equality: its [(base, offset,
    length, value)] view, with the value filling the whole load. *)
Definition payload_seg (m : matchcond) : option (pbase * nat * nat * data) :=
  let seg f v :=
    match field_load f with
    | LPayload b o l => if Nat.eqb (length v) l then Some (b, o, l, v) else None
    | _ => None
    end in
  match m with
  | MEq f v => seg f v
  | MCmp f CEq v => seg f v
  | _ => None
  end.

(** A recognised segment is a full-width payload equality: its eval and its
    loadability are those of the raw [FPayload] load, and the value fills it. *)
Lemma payload_seg_spec : forall m b o l v,
  payload_seg m = Some (b, o, l, v) ->
  (forall e p, eval_matchcond m e p = eval_matchcond (MEq (FPayload b o l) v) e p)
  /\ (forall p, match_loadable m p = read_payload_ok b o l p)
  /\ length v = l.
Proof.
  intros m b o l v H. unfold payload_seg in H.
  destruct m as [f v0|f v0|f n lo hi|f op msk xr w|f op v0| | | | | | | | ];
    try discriminate.
  - (* MEq f v0 *)
    destruct (field_load f) as [| | | | | | | | | | | | |b' o' l'] eqn:Efl;
      try discriminate.
    destruct (Nat.eqb (length v0) l') eqn:El; [|discriminate].
    injection H as <- <- <- <-. apply Nat.eqb_eq in El.
    split; [| split; [| exact El]].
    + intros e p. apply (eval_MEq_field_load f b' o' l' v0 e p Efl).
    + intros p. unfold match_loadable, field_loadable. rewrite Efl. reflexivity.
  - (* MCmp f op v0 : only op = CEq recognises *)
    destruct op; try discriminate.
    destruct (field_load f) as [| | | | | | | | | | | | |b' o' l'] eqn:Efl;
      try discriminate.
    destruct (Nat.eqb (length v0) l') eqn:El; [|discriminate].
    injection H as <- <- <- <-. apply Nat.eqb_eq in El.
    split; [| split; [| exact El]].
    + intros e p. rewrite eval_MCmpEq_is_MEq.
      apply (eval_MEq_field_load f b' o' l' v0 e p Efl).
    + intros p. unfold match_loadable, field_loadable. rewrite Efl. reflexivity.
Qed.

(** nft's [payload_can_merge] as a boolean over the two segments' geometry. *)
Definition seg_can_merge (b1 : pbase) (o1 l1 : nat)
                         (b2 : pbase) (o2 l2 : nat) : bool :=
  pbase_eqb b1 b2
  && Nat.eqb o2 (o1 + l1)                 (* adjacent *)
  && Nat.leb (l1 + l2) 16                 (* <= NFT_REG_SIZE bytes *)
  && (Nat.leb (l1 + l2) 4                 (* u32 fast path, or ... *)
      || pbase_eqb b1 PLink               (* ... link base, or ... *)
      || Nat.ltb 4 l1 || Nat.ltb 4 l2).   (* ... a side already > u32 *)

(** Fuse two matchconds if both are adjacent mergeable payload equalities. *)
Definition try_merge (m1 m2 : matchcond) : option matchcond :=
  match payload_seg m1, payload_seg m2 with
  | Some (b1, o1, l1, v1), Some (b2, o2, l2, v2) =>
      if seg_can_merge b1 o1 l1 b2 o2 l2
      then Some (MEq (FPayload b1 o1 (l1 + l2)) (v1 ++ v2))
      else None
  | _, _ => None
  end.

(** [seg_can_merge] gives the two geometry facts the merge needs: same base and
    adjacency (the fast-path caveats are only about WHERE nft merges). *)
Lemma seg_can_merge_geom : forall b1 o1 l1 b2 o2 l2,
  seg_can_merge b1 o1 l1 b2 o2 l2 = true -> b2 = b1 /\ o2 = o1 + l1.
Proof.
  intros b1 o1 l1 b2 o2 l2 C. unfold seg_can_merge in C.
  apply andb_true_iff in C as [C _]; apply andb_true_iff in C as [C _];
    apply andb_true_iff in C as [Cb Co].
  apply pbase_eqb_eq in Cb; apply Nat.eqb_eq in Co. split; congruence.
Qed.

(** The correctness of one fusion, on a single [eval_matchcond]. *)
Lemma try_merge_eval : forall m1 m2 m e p,
  try_merge m1 m2 = Some m ->
  eval_matchcond m e p = eval_matchcond m1 e p && eval_matchcond m2 e p.
Proof.
  intros m1 m2 m e p H. unfold try_merge in H.
  destruct (payload_seg m1) as [[[[b1 o1] l1] v1]|] eqn:S1; [|discriminate].
  destruct (payload_seg m2) as [[[[b2 o2] l2] v2]|] eqn:S2; [|discriminate].
  destruct (seg_can_merge b1 o1 l1 b2 o2 l2) eqn:C; [|discriminate].
  injection H as <-.
  apply seg_can_merge_geom in C as [-> ->].
  apply payload_seg_spec in S1 as (E1 & _ & L1).
  apply payload_seg_spec in S2 as (E2 & _ & L2).
  rewrite E1, E2.
  apply (merge_eval_ok b1 o1 l1 v1 l2 v2 e p L1 L2).
Qed.

(** The same fusion preserves [match_loadable] (the loadability walk needs this
    independently of applicability). *)
Lemma try_merge_loadable : forall m1 m2 m p,
  try_merge m1 m2 = Some m ->
  match_loadable m p = match_loadable m1 p && match_loadable m2 p.
Proof.
  intros m1 m2 m p H. unfold try_merge in H.
  destruct (payload_seg m1) as [[[[b1 o1] l1] v1]|] eqn:S1; [|discriminate].
  destruct (payload_seg m2) as [[[[b2 o2] l2] v2]|] eqn:S2; [|discriminate].
  destruct (seg_can_merge b1 o1 l1 b2 o2 l2) eqn:C; [|discriminate].
  injection H as <-.
  apply seg_can_merge_geom in C as [-> ->].
  apply payload_seg_spec in S1 as (_ & M1 & _).
  apply payload_seg_spec in S2 as (_ & M2 & _).
  rewrite M1, M2.
  unfold match_loadable, field_loadable, load_ok. cbn [field_load].
  apply (read_payload_ok_split b1 o1 l1 l2 p).
Qed.

(** Fuse adjacent mergeable payload equalities across a body, fuel-bounded so a
    merged pair can chain into a further neighbour (the link-layer 6+2 -> 8 ->
    ... cascades).  Fuel [= length body] always suffices; the correctness holds
    for ANY fuel (out of fuel = identity). *)
Fixpoint merge_body_fuel (fuel : nat) (b : list body_item) : list body_item :=
  match fuel with
  | 0 => b
  | S fk =>
      match b with
      | BMatch m1 :: BMatch m2 :: rest =>
          match try_merge m1 m2 with
          | Some m => merge_body_fuel fk (BMatch m :: rest)
          | None => BMatch m1 :: merge_body_fuel fk (BMatch m2 :: rest)
          end
      | it :: rest => it :: merge_body_fuel fk rest
      | [] => []
      end
  end.

Definition merge_body (b : list body_item) : list body_item :=
  merge_body_fuel (length b) b.

Definition paymerge_rule (r : rule) : rule :=
  {| r_body := merge_body (r_body r);
     r_outcome := r_outcome r; r_after := r_after r |}.

Definition paymerge_chain (c : chain) : chain :=
  {| c_policy := c_policy c; c_rules := map paymerge_rule (c_rules c) |}.

(* ================================================================== *)
(** ** Body-scan predicates are invariant (the pass touches only [BMatch]
    items and only merges them into another [BMatch] — never a [BStmt]). *)

Lemma existsb_cons : forall (A : Type) (P : A -> bool) x xs,
  existsb P (x :: xs) = P x || existsb P xs.
Proof. reflexivity. Qed.

(** Any [existsb] over a predicate that is FALSE on every [BMatch] is invariant:
    the pass only rewrites [BMatch] items into a [BMatch] item and leaves every
    [BStmt] verbatim, so no such predicate's witness moves. *)
Lemma merge_body_fuel_existsb : forall (P : body_item -> bool),
  (forall m, P (BMatch m) = false) ->
  forall fuel b, existsb P (merge_body_fuel fuel b) = existsb P b.
Proof.
  intros P HP. induction fuel as [|fk IH]; intro b; [reflexivity|].
  destruct b as [|it1 [|it2 rest]]; [reflexivity | |].
  - destruct it1 as [m|s]; cbn [merge_body_fuel];
      rewrite existsb_cons, IH; reflexivity.
  - destruct it1 as [m1|s1].
    + destruct it2 as [m2|s2]; cbn [merge_body_fuel].
      * destruct (try_merge m1 m2) as [m|] eqn:T.
        -- rewrite IH, !existsb_cons, !HP. reflexivity.
        -- rewrite existsb_cons, IH, !existsb_cons, !HP. reflexivity.
      * rewrite existsb_cons, IH, !existsb_cons, HP. reflexivity.
    + cbn [merge_body_fuel]. rewrite existsb_cons, IH, !existsb_cons. reflexivity.
Qed.

Lemma merge_body_has_notrack : forall b,
  body_has_notrack (merge_body b) = body_has_notrack b.
Proof.
  intro b. unfold body_has_notrack, merge_body.
  apply merge_body_fuel_existsb. reflexivity.
Qed.

Lemma merge_body_synproxy_stops : forall b p,
  body_synproxy_stops (merge_body b) p = body_synproxy_stops b p.
Proof.
  intros b p. unfold body_synproxy_stops, merge_body.
  apply (merge_body_fuel_existsb
           (fun it => match it with BStmt (SSynproxy _ _) => synproxy_stops p
                                  | _ => false end)).
  reflexivity.
Qed.

Lemma merge_body_thread : forall b p,
  body_thread (merge_body b) p = body_thread b p.
Proof.
  intros b p. unfold body_thread. rewrite merge_body_has_notrack. reflexivity.
Qed.

(* ================================================================== *)
(** ** Applicability / loadability walks are invariant. *)

Lemma merge_body_fuel_applies : forall fuel b e p,
  rule_applies_walk (merge_body_fuel fuel b) e p = rule_applies_walk b e p.
Proof.
  induction fuel as [|fk IH]; intros b e p; [reflexivity|].
  destruct b as [|it1 [|it2 rest]]; try reflexivity.
  - cbn [merge_body_fuel]. destruct it1 as [m|s]; cbn [rule_applies_walk].
    + now rewrite IH.
    + destruct s; cbn [rule_applies_walk]; rewrite IH; reflexivity.
  - cbn [merge_body_fuel]. destruct it1 as [m1|s1].
    + destruct it2 as [m2|s2].
      * destruct (try_merge m1 m2) as [m|] eqn:T.
        -- rewrite IH. cbn [rule_applies_walk].
           rewrite (try_merge_eval m1 m2 m e p T). now rewrite andb_assoc.
        -- cbn [rule_applies_walk]. rewrite IH. reflexivity.
      * cbn [rule_applies_walk]. rewrite IH. reflexivity.
    + destruct s1; cbn [rule_applies_walk]; rewrite IH; reflexivity.
Qed.

Lemma merge_body_fuel_loadable : forall fuel b p,
  body_loadable_walk (merge_body_fuel fuel b) p = body_loadable_walk b p.
Proof.
  induction fuel as [|fk IH]; intros b p; [reflexivity|].
  destruct b as [|it1 [|it2 rest]]; try reflexivity.
  - cbn [merge_body_fuel]. destruct it1 as [m|s];
      cbn [body_loadable_walk body_item_loadable].
    + now rewrite IH.
    + destruct s; cbn [body_loadable_walk body_item_loadable]; rewrite IH;
        reflexivity.
  - cbn [merge_body_fuel]. destruct it1 as [m1|s1].
    + destruct it2 as [m2|s2].
      * destruct (try_merge m1 m2) as [m|] eqn:T.
        -- rewrite IH. cbn [body_loadable_walk body_item_loadable].
           rewrite (try_merge_loadable m1 m2 m p T). now rewrite andb_assoc.
        -- cbn [body_loadable_walk body_item_loadable]. rewrite IH. reflexivity.
      * cbn [body_loadable_walk body_item_loadable]. rewrite IH. reflexivity.
    + destruct s1; cbn [body_loadable_walk body_item_loadable]; rewrite IH;
        reflexivity.
Qed.

(* ================================================================== *)
(** ** Lift to [eval_rules] / [eval_chain]. *)

Lemma merge_body_loadable : forall b p,
  body_loadable_walk (merge_body b) p = body_loadable_walk b p.
Proof. intros b p. apply merge_body_fuel_loadable. Qed.

Lemma merge_body_applies : forall b e p,
  rule_applies_walk (merge_body b) e p = rule_applies_walk b e p.
Proof. intros b e p. apply merge_body_fuel_applies. Qed.

Lemma paymerge_rule_body : forall r,
  r_body (paymerge_rule r) = merge_body (r_body r).
Proof. reflexivity. Qed.

Lemma paymerge_rule_loadable : forall r e p,
  rule_loadable (paymerge_rule r) e p = rule_loadable r e p.
Proof.
  intros r e p. unfold rule_loadable. rewrite paymerge_rule_body.
  rewrite merge_body_loadable, merge_body_synproxy_stops, merge_body_thread.
  reflexivity.
Qed.

Lemma paymerge_rule_applies : forall r e p,
  rule_applies (paymerge_rule r) e p = rule_applies r e p.
Proof.
  intros r e p. unfold rule_applies. rewrite paymerge_rule_body.
  apply merge_body_applies.
Qed.

Lemma paymerge_outcome : forall r e p,
  outcome (paymerge_rule r) e p = outcome r e p.
Proof.
  intros r e p. unfold outcome. rewrite paymerge_rule_body.
  rewrite merge_body_synproxy_stops, merge_body_thread.
  destruct (body_synproxy_stops (r_body r) p); reflexivity.
Qed.

Lemma paymerge_eval_rules : forall rs e p,
  eval_rules (map paymerge_rule rs) e p = eval_rules rs e p.
Proof.
  induction rs as [| r rs IH]; intros e p; [reflexivity|].
  cbn [map]. rewrite ?eval_rules_cons, ?eval_rules_nil.
  rewrite paymerge_rule_loadable, paymerge_rule_applies, paymerge_outcome.
  destruct (rule_loadable r e p && rule_applies r e p); [| apply IH].
  destruct (outcome r e p) as [v|]; [destruct v|]; rewrite ?IH; reflexivity.
Qed.

Theorem paymerge_chain_eval : forall c e p,
  eval_chain (paymerge_chain c) e p = eval_chain c e p.
Proof.
  intros c e p. unfold eval_chain, paymerge_chain. cbn [c_rules c_policy].
  rewrite paymerge_eval_rules. reflexivity.
Qed.

(* ================================================================== *)
(** ** Non-vacuity: the pass GENUINELY rewrites.

    `tcp sport 1 tcp dport 2` — two adjacent 2-byte transport payload
    equalities (FThSport @ transport+0, FThDport @ transport+2) — fuse into one
    4-byte load compared against the concatenated value [0x00 01 00 02].  This is
    the corpus class-I merge (inet/payloadmerge.t.payload:1). *)
Example paymerge_witness :
  merge_body [BMatch (MEq FThSport [0;1]); BMatch (MEq FThDport [0;2])]
  = [BMatch (MEq (FPayload PTransport 0 4) [0;1;0;2])].
Proof. vm_compute. reflexivity. Qed.

(** The output is NOT the input — a real rewrite, not the identity. *)
Example paymerge_nonvacuous :
  merge_body [BMatch (MEq FThSport [0;1]); BMatch (MEq FThDport [0;2])]
  <> [BMatch (MEq FThSport [0;1]); BMatch (MEq FThDport [0;2])].
Proof. vm_compute. discriminate. Qed.

(** The link-layer 6+2 cascade: `ether saddr` (6b @ link+6) fuses with the
    synthesised `ether type` guard (2b @ link+12) into one 8-byte load. *)
Example paymerge_link_witness :
  merge_body [BMatch (MEq FEtherSaddr [0;1;2;3;4;5]);
              BMatch (MEq FEtherType [129;0])]
  = [BMatch (MEq (FPayload PLink 6 8) [0;1;2;3;4;5;129;0])].
Proof. vm_compute. reflexivity. Qed.

(** A non-adjacent pair does NOT merge (the guard is offset-exact). *)
Example paymerge_no_gap :
  merge_body [BMatch (MEq FThSport [0;1]); BMatch (MEq FTcpSeq [0;0;0;0])]
  = [BMatch (MEq FThSport [0;1]); BMatch (MEq FTcpSeq [0;0;0;0])].
Proof. vm_compute. reflexivity. Qed.

(** Axiom-freedom audit (build-time guard). *)
Print Assumptions paymerge_chain_eval.
