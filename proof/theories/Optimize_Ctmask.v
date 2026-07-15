(** * Optimize_Ctmask: bitmask-UNION fold for `ct state` (and any bitmask-membership
    selector lowered to [MMasked f true mask 0 0]).

    Battery shape "ctstate-mask-union":

        ct state new accept            ┐
        ct state established accept    ┘  =>  ct state new,established accept

    The frontend lowers a single positive `ct state X` to the BITMASK test
    [MMasked FCtState true bits 0 0] (nft_lower.ml; ct_state has .basetype =
    bitmask_type and the relational evaluator keeps the OP_IMPLICIT bitmask form
    for TYPE_CT_STATE — see [Ct_State.v]).  Its meaning is `(state & bits) != 0`.
    Two adjacent such rules over the SAME field, with the SAME verdict, are
    verdict-equivalent to ONE rule whose mask is the bytewise OR of the two masks:

        (state & m1) != 0   OR   (state & m2) != 0    <=>    (state & (m1|m2)) != 0

    because `x & (a|b) = (x&a) | (x&b)` and `u|v = 0 <-> u=0 /\ v=0` bytewise.  The
    fold emits [MMasked f true (data_or m1 m2) 0 0] — which is EXACTLY the bytecode
    nft compiles the comma-list `ct state new,established` to
    (`[ct load state][bitwise reg1 = (reg1 & 0xa) ^ 0][cmp neq reg1 0]`, mask
    0x8|0x2=0xa; confirmed against nft v1.1.6 in a netns).  So the fold is a VALID,
    loadable nftables object and is verdict-equivalent to the two originals.

    FIDELITY NOTE.  `nft --optimize` folds these two rules to the SET form
    `ct state { new, established }`, which nft compiles to an EXACT set lookup
    `state ∈ {0x8, 0x2}` — a NARROWER object than the bitmask union: it differs
    from the two originals on a multi-bit state such as `established|untracked`
    (= 0x2|0x40 = 0x42), which the originals MATCH (0x42 & 0x2 != 0) but the exact
    set does NOT (0x42 ∉ {0x8,0x2}).  Our model admits multi-bit ct states (see
    [Ct_State.v] estab_matches_established_plus_other), so nft's exact-set fold is
    NOT verdict-preserving HERE; we deliberately emit the SOUND bitmask-union form
    (nft's own comma-list compilation), which IS verdict-preserving in our
    semantics and kernel-equivalent to the originals (the real kernel's `ct state`
    register is always single-bit, so union and exact-set coincide there).  This is
    a labelled sound divergence from nft -o's byte-output, exactly like the [mapn]
    stage — NOT an unsound/invalid fold.  Axiom-free. *)

From Stdlib Require Import Ascii String.
From Stdlib Require Import List PeanoNat Bool Lia Btauto.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Optimize Optimize_Merge Optimize_Table_Inv.
Import ListNotations.
Local Open Scope nat_scope.

(** ** Bitwise helper lemmas. *)

Lemma eqb_lor_0 : forall u v,
  Nat.eqb (Nat.lor u v) 0 = Nat.eqb u 0 && Nat.eqb v 0.
Proof.
  intros u v. destruct (Nat.eqb u 0) eqn:Eu; destruct (Nat.eqb v 0) eqn:Ev; cbn [andb].
  - apply Nat.eqb_eq in Eu, Ev; subst; reflexivity.
  - apply Nat.eqb_eq in Eu; subst. rewrite Nat.lor_0_l. exact Ev.
  - apply Nat.eqb_eq in Ev; subst. rewrite Nat.lor_0_r. exact Eu.
  - apply Nat.eqb_neq in Eu.
    destruct (Nat.eqb (Nat.lor u v) 0) eqn:E; [| reflexivity].
    apply Nat.eqb_eq, Nat.lor_eq_0_iff in E as [Hu _]. contradiction.
Qed.

Lemma eqb_land_lor_0 : forall x a b,
  Nat.eqb (Nat.land x (Nat.lor a b)) 0
  = Nat.eqb (Nat.land x a) 0 && Nat.eqb (Nat.land x b) 0.
Proof.
  intros x a b.
  rewrite Nat.land_comm, Nat.land_lor_distr_l,
    (Nat.land_comm a x), (Nat.land_comm b x).
  apply eqb_lor_0.
Qed.

Lemma data_eqb_nil_l : forall l,
  data_eqb [] l = match l with [] => true | _ => false end.
Proof.
  intros [| x l]; unfold data_eqb; cbn; reflexivity.
Qed.

Lemma data_eqb_cons : forall a l b l',
  data_eqb (a :: l) (b :: l') = Nat.eqb a b && data_eqb l l'.
Proof.
  intros a l b l'. unfold data_eqb.
  destruct (Nat.eqb a b) eqn:Eab; cbn [andb].
  - apply Nat.eqb_eq in Eab; subst.
    destruct (list_eq_dec Nat.eq_dec l l') as [E | Ne];
    destruct (list_eq_dec Nat.eq_dec (b :: l) (b :: l')) as [E2 | Ne2];
      try reflexivity.
    + exfalso. apply Ne2. rewrite E. reflexivity.
    + exfalso. apply Ne. injection E2 as H. exact H.
  - apply Nat.eqb_neq in Eab.
    destruct (list_eq_dec Nat.eq_dec (a :: l) (b :: l')) as [E | Ne]; [| reflexivity].
    exfalso. apply Eab. injection E as H _. exact H.
Qed.

(** The bytewise-OR mask disjunction, phrased as [data_eqb ... = andb ...] on the
    all-zero comparand [z] (both the xor and the compared value in a ct-state
    [MMasked]).  [z]'s length pins the mask lengths so [data_or] aligns. *)
Lemma ctmask_disj_body : forall z s m1 m2,
  length m1 = length z -> length m2 = length z ->
  Forall (fun b => b = 0) z ->
  data_eqb (data_bitops s (data_or m1 m2) z) z
  = data_eqb (data_bitops s m1 z) z && data_eqb (data_bitops s m2 z) z.
Proof.
  induction z as [| e z' IH]; intros s m1 m2 Hl1 Hl2 Hz.
  - destruct m1; [| discriminate]. destruct m2; [| discriminate].
    cbn [data_or]. destruct s; cbn [data_bitops]; reflexivity.
  - destruct m1 as [| a m1']; [discriminate |].
    destruct m2 as [| b m2']; [discriminate |].
    cbn [length] in Hl1, Hl2. injection Hl1 as Hl1. injection Hl2 as Hl2.
    inversion Hz as [| e0 z0 He Hz']; subst. clear Hz.
    destruct s as [| xh st].
    + cbn [data_or data_bitops]. rewrite !data_eqb_nil_l. reflexivity.
    + cbn [data_or data_bitops].
      unfold byte_xor, byte_and, byte_or.
      rewrite !Nat.lxor_0_r.
      rewrite !data_eqb_cons.
      rewrite (IH st m1' m2' Hl1 Hl2 Hz').
      rewrite eqb_land_lor_0.
      btauto.
Qed.

Lemma data_bitops_len_le : forall s m z,
  length (data_bitops s m z) <= length z.
Proof.
  induction s as [| x s' IH]; intros m z.
  - simpl. lia.
  - destruct m as [| y m']; [ simpl; lia |].
    destruct z as [| e z']; [ simpl; lia |].
    cbn [data_bitops length]. specialize (IH m' z'). lia.
Qed.

(** The eval-level disjunction certificate: on ANY packet, the union-mask
    [MMasked] equals the [orb] of the two single-mask [MMasked]s, when the xor and
    compared value are the SAME all-zero vector [z] of the masks' width. *)
Lemma mmasked_ctmask_disjunction : forall f m1 m2 z e p,
  length m1 = length z -> length m2 = length z ->
  Forall (fun b => b = 0) z ->
  eval_matchcond (MMasked f true (data_or m1 m2) z z) e p
  = orb (eval_matchcond (MMasked f true m1 z z) e p)
        (eval_matchcond (MMasked f true m2 z z) e p).
Proof.
  intros f m1 m2 z e p Hl1 Hl2 Hz.
  unfold eval_matchcond. cbn [match_loadable].
  destruct (field_loadable f p) eqn:Hld; cbn [andb]; [| reflexivity].
  unfold eval_matchcond_body. cbn [eval_cmp].
  (* body(mask) = negb (data_eqb (firstn (length z) (data_bitops s mask z)) z) *)
  set (s := field_value f e p) in *.
  rewrite !firstn_all2 by apply data_bitops_len_le.
  rewrite (ctmask_disj_body z s m1 m2 Hl1 Hl2 Hz).
  rewrite Bool.negb_andb. reflexivity.
Qed.

(** ** Recogniser. *)

Definition all_zero (l : data) : bool := forallb (fun b => Nat.eqb b 0) l.

Lemma all_zero_Forall : forall l, all_zero l = true -> Forall (fun b => b = 0) l.
Proof.
  induction l as [| x l IH]; intro H; [constructor |].
  cbn [all_zero forallb] in H. apply Bool.andb_true_iff in H as [Hx Hrest].
  apply Nat.eqb_eq in Hx. constructor; [exact Hx | apply IH; exact Hrest].
Qed.

(** A bitmask-membership head [BMatch (MMasked f true mask xor v) :: rest]. *)
Definition head_ctmask (r : rule)
  : option (field * data * data * data * list body_item) :=
  match r_body r with
  | BMatch (MMasked f true mask xor v) :: rest => Some (f, mask, xor, v, rest)
  | _ => None
  end.

Lemma head_ctmask_rbody : forall r f mask xor v body,
  head_ctmask r = Some (f, mask, xor, v, body) ->
  r_body r = BMatch (MMasked f true mask xor v) :: body.
Proof.
  intros r f mask xor v body H. unfold head_ctmask in H.
  destruct (r_body r) as [| [m | s] tl] eqn:Eb; try discriminate.
  destruct m as [ | | | g neg mask' xor' v' | | | | | | | | | ]; try discriminate.
  destruct neg; try discriminate.
  inversion H; subst. reflexivity.
Qed.

Lemma head_ctmask_canon : forall r f mask xor v body,
  head_ctmask r = Some (f, mask, xor, v, body) ->
  r = mk_head (MMasked f true mask xor v) body r.
Proof.
  intros r f mask xor v body H.
  pose proof (head_ctmask_rbody r f mask xor v body H) as Hb.
  unfold mk_head. rewrite <- Hb. destruct r; reflexivity.
Qed.

(** Two rules form an eligible bitmask-union pair iff both heads are
    [MMasked f true mask_i z z] over the SAME field [f], sharing the SAME all-zero
    xor/compared vector [z] (which equals the masks' width), same tail, same
    end-fields.  Returns [(f, m1, m2, z, body)]. *)
Definition ctmask_pair (r1 r2 : rule)
  : option (field * data * data * data * list body_item) :=
  match head_ctmask r1, head_ctmask r2 with
  | Some (f1, m1, x1, v1, rest1), Some (f2, m2, x2, v2, rest2) =>
      if field_eq_dec f1 f2 then
      if list_eq_dec Nat.eq_dec x1 x2 then
      if list_eq_dec Nat.eq_dec v1 v2 then
      if list_eq_dec Nat.eq_dec x1 v1 then
      if all_zero x1 then
      if Nat.eq_dec (length m1) (length x1) then
      if Nat.eq_dec (length m2) (length x1) then
      if list_eq_dec body_item_eq_dec rest1 rest2 then
      if rule_end_eqb r1 r2
      then Some (f1, m1, m2, x1, rest1)
      else None
      else None else None else None else None else None else None else None else None
  | _, _ => None
  end.

Lemma ctmask_pair_facts : forall r1 r2 f m1 m2 z body,
  ctmask_pair r1 r2 = Some (f, m1, m2, z, body) ->
  r1 = mk_head (MMasked f true m1 z z) body r1 /\
  r2 = mk_head (MMasked f true m2 z z) body r1 /\
  length m1 = length z /\ length m2 = length z /\
  Forall (fun b => b = 0) z.
Proof.
  intros r1 r2 f m1 m2 z body H. unfold ctmask_pair in H.
  destruct (head_ctmask r1) as [[[[[f1 mm1] x1] v1] rest1] |] eqn:H1; [| discriminate].
  destruct (head_ctmask r2) as [[[[[f2 mm2] x2] v2] rest2] |] eqn:H2; [| discriminate].
  destruct (field_eq_dec f1 f2) as [Ef |]; [| discriminate]. subst f2.
  destruct (list_eq_dec Nat.eq_dec x1 x2) as [Ex |]; [| discriminate]. subst x2.
  destruct (list_eq_dec Nat.eq_dec v1 v2) as [Ev |]; [| discriminate]. subst v2.
  destruct (list_eq_dec Nat.eq_dec x1 v1) as [Exv |]; [| discriminate]. subst v1.
  destruct (all_zero x1) eqn:Ez; [| discriminate].
  destruct (Nat.eq_dec (length mm1) (length x1)) as [El1 |]; [| discriminate].
  destruct (Nat.eq_dec (length mm2) (length x1)) as [El2 |]; [| discriminate].
  destruct (list_eq_dec body_item_eq_dec rest1 rest2) as [Er |]; [| discriminate]. subst rest2.
  destruct (rule_end_eqb r1 r2) eqn:Eeqb; [| discriminate].
  inversion H; subst f1 mm1 mm2 x1 rest1. clear H.
  pose proof (head_ctmask_canon r1 f m1 z z body H1) as Hr1.
  pose proof (head_ctmask_canon r2 f m2 z z body H2) as Hr2c.
  pose proof (proj1 (rule_end_eqb_mk_head (MMasked f true m2 z z) body r1 r2) Eeqb)
    as Eshell.
  split; [exact Hr1 |].
  split; [rewrite Hr2c; symmetry; exact Eshell |].
  split; [exact El1 |].
  split; [exact El2 | apply all_zero_Forall; exact Ez].
Qed.

(** The merged rule the pass emits. *)
Definition ctmask_merged (f : field) (m1 m2 z : data) (body : list body_item)
  (r1 : rule) : rule :=
  mk_head (MMasked f true (data_or m1 m2) z z) body r1.

(** *** Two-rule correctness: an eligible pair collapses to its merged rule,
    preserving every verdict.  Reuses [eval_rules_value_merge] with the bitmask
    disjunction certificate. *)
Lemma eval_rules_ctmask_correct : forall r1 r2 f m1 m2 z body rest e p,
  ctmask_pair r1 r2 = Some (f, m1, m2, z, body) ->
  eval_rules (ctmask_merged f m1 m2 z body r1 :: rest) e p
  = eval_rules (r1 :: r2 :: rest) e p.
Proof.
  intros r1 r2 f m1 m2 z body rest e p H.
  destruct (ctmask_pair_facts r1 r2 f m1 m2 z body H)
    as [Hr1 [Hr2 [Hl1 [Hl2 Hz]]]].
  unfold ctmask_merged.
  transitivity (eval_rules (mk_head (MMasked f true m1 z z) body r1
                            :: mk_head (MMasked f true m2 z z) body r1 :: rest) e p).
  - apply (eval_rules_value_merge (MMasked f true m1 z z) (MMasked f true m2 z z)
             (MMasked f true (data_or m1 m2) z z) body r1 rest e p).
    + intro q. reflexivity.
    + intro q. reflexivity.
    + intro q. apply (mmasked_ctmask_disjunction f m1 m2 z e q Hl1 Hl2 Hz).
  - rewrite <- Hr1, <- Hr2. reflexivity.
Qed.

(** ** Executable fuel-driven pass: merge an adjacent eligible pair into its union
    rule and RETRY (so an N-way run folds by repeated pairwise union), else keep
    and advance. *)
Fixpoint optimize_rules_ctmask (fuel : nat) (rs : list rule) : list rule :=
  match fuel with
  | O => rs
  | S fuel' =>
    match rs with
    | r1 :: ((r2 :: rest) as tl) =>
        match ctmask_pair r1 r2 with
        | Some (f, m1, m2, z, body) =>
            optimize_rules_ctmask fuel' (ctmask_merged f m1 m2 z body r1 :: rest)
        | None => r1 :: optimize_rules_ctmask fuel' tl
        end
    | _ => rs
    end
  end.

Lemma optimize_rules_ctmask_eval : forall fuel rs e p,
  eval_rules (optimize_rules_ctmask fuel rs) e p = eval_rules rs e p.
Proof.
  induction fuel as [| fuel IH]; intros rs e p; [reflexivity |].
  destruct rs as [| r1 [| r2 rest]]; try reflexivity.
  cbn [optimize_rules_ctmask].
  destruct (ctmask_pair r1 r2) as [[[[[f m1] m2] z] body] |] eqn:Ep.
  - rewrite IH. apply (eval_rules_ctmask_correct r1 r2 f m1 m2 z body rest e p Ep).
  - apply eval_rules_cons_cong. apply IH.
Qed.

(** *** Freshness / name-set preservation: a merged rule reads EXACTLY the names
    its base rule [r1] reads (the union [MMasked] head references no set name, and
    the end-fields are copied from [r1]).  Hence the three fresh-name predicates
    used by [optimize_table]'s composition transfer through the pass. *)
Lemma ctmask_merged_body_set_names : forall r1 r2 f m1 m2 z body,
  ctmask_pair r1 r2 = Some (f, m1, m2, z, body) ->
  body_set_names (r_body (ctmask_merged f m1 m2 z body r1))
  = body_set_names (r_body r1).
Proof.
  intros r1 r2 f m1 m2 z body H.
  destruct (ctmask_pair_facts r1 r2 f m1 m2 z body H) as [Hr1 _].
  assert (Hb : r_body r1 = BMatch (MMasked f true m1 z z) :: body).
  { rewrite Hr1. reflexivity. }
  unfold ctmask_merged, body_set_names. cbn [r_body body_matches flat_map mc_set_name].
  rewrite Hb. cbn [body_matches flat_map mc_set_name]. reflexivity.
Qed.

Lemma ctmask_merged_vmap_name : forall r1 f m1 m2 z body,
  rule_vmap_name (ctmask_merged f m1 m2 z body r1) = rule_vmap_name r1.
Proof. intros. unfold ctmask_merged, mk_head, rule_vmap_name. cbn [r_vmap]. reflexivity. Qed.

Lemma ctmask_merged_nat_map_name : forall r1 f m1 m2 z body,
  rule_nat_map_name (ctmask_merged f m1 m2 z body r1) = rule_nat_map_name r1.
Proof. intros. unfold ctmask_merged, mk_head, rule_nat_map_name. cbn [r_nat]. reflexivity. Qed.

(** A generic Forall transfer: any per-rule predicate that survives the merge step
    survives the whole pass. *)
Lemma optimize_rules_ctmask_Forall : forall (P : rule -> Prop) fuel rs,
  (forall r1 r2 f m1 m2 z body,
     ctmask_pair r1 r2 = Some (f, m1, m2, z, body) ->
     P r1 -> P (ctmask_merged f m1 m2 z body r1)) ->
  Forall P rs -> Forall P (optimize_rules_ctmask fuel rs).
Proof.
  intros P fuel. induction fuel as [| fuel IH]; intros rs Hmerge HF; [exact HF |].
  destruct rs as [| r1 [| r2 rest]]; try exact HF.
  cbn [optimize_rules_ctmask].
  inversion HF as [| ? ? HP1 HFtl]; subst.
  destruct (ctmask_pair r1 r2) as [[[[[f m1] m2] z] body] |] eqn:Ep.
  - apply IH; [exact Hmerge |].
    inversion HFtl as [| ? ? HP2 HFrest]; subst.
    constructor; [ apply (Hmerge r1 r2 f m1 m2 z body Ep HP1) | exact HFrest ].
  - constructor; [ exact HP1 | apply IH; [ exact Hmerge | exact HFtl ] ].
Qed.

(** ** Chain wrapper — counter and declarations pass through UNCHANGED. *)
Definition ctmask_chain (c : chain) : chain :=
  {| c_policy := c_policy c;
     c_rules := optimize_rules_ctmask (length (c_rules c)) (c_rules c) |}.

Definition optimize_chain_ctmask (n : nat) (d : set_decls) (c : chain)
  : nat * set_decls * chain :=
  (n, d, ctmask_chain c).

Lemma optimize_chain_ctmask_eq : forall n d c,
  optimize_chain_ctmask n d c = (n, d, ctmask_chain c).
Proof. reflexivity. Qed.

Lemma ctmask_chain_eval : forall c e p,
  eval_chain (ctmask_chain c) e p = eval_chain c e p.
Proof.
  intros c e p. unfold eval_chain, ctmask_chain. cbn [c_rules c_policy].
  rewrite optimize_rules_ctmask_eval. reflexivity.
Qed.

(** ** Non-vacuity witnesses (battery shape "ctstate-mask-union"): two adjacent
    `ct state new/established accept` bitmask rules fold to ONE union rule. *)
Definition acc_witness : rule :=
  {| r_body := []; r_verdict := Accept; r_vmap := None; r_nat := None;
     r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.

Definition ctm_new : rule :=
  mk_head (MMasked FCtState true [0;0;0;8] [0;0;0;0] [0;0;0;0]) [] acc_witness.
Definition ctm_estab : rule :=
  mk_head (MMasked FCtState true [0;0;0;2] [0;0;0;0] [0;0;0;0]) [] acc_witness.

Example ctmask_fires :
  ctmask_pair ctm_new ctm_estab
  = Some (FCtState, [0;0;0;8], [0;0;0;2], [0;0;0;0], []).
Proof. reflexivity. Qed.

(* the fold collapses the two-rule chain to ONE union-mask rule (mask 0x8|0x2=0xa) *)
Example ctmask_folds :
  optimize_rules_ctmask 2 [ctm_new; ctm_estab]
  = [ mk_head (MMasked FCtState true [0;0;0;10] [0;0;0;0] [0;0;0;0]) [] acc_witness ].
Proof. reflexivity. Qed.
