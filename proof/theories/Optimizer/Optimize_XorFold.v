(** * Optimize_XorFold: the bitwise-xor constant fold (corpus class L).

    A pure `xor` match — `meta mark xor C <op> V`, `ct mark xor C <op> V` — nft
    lowers to `bitwise reg = (reg & 0xff..ff) ^ C ; cmp <op> reg V`.  nftables'
    own evaluator folds the xor CONSTANT into the comparison (src/evaluate.c
    `binop_transfer` / `binop_can_transfer`, OP_XOR case:
    `expr_is_constant(left->right)`): the register-side `^ C` moves to the value
    side as `V ^ C`, since bytewise xor is its own inverse
    (`a ^ C = V  <->  a = V ^ C`).

    This pass performs exactly that transfer on the [matchcond]: it recognises
    the pure-xor shape (an all-ones AND mask — the register is unmasked) under an
    equality/inequality comparison, and rewrites

        MMasked f op (all-ones) C V   ->   MMasked f op (all-ones) 0 (V ^ C).

    The transfer holds for ANY register value (bytewise xor is involutive with
    no width or byte-range side condition), so the pass is SELF-GUARDING and its
    correctness is UNCONDITIONAL: [eval_chain (xorfold_chain c) e p = eval_chain
    c e p] for every chain, env and packet — no hypotheses.  Restricted to the
    all-ones mask so it fires on `xor` alone and never on an `and`/`or` mask
    (which nft does not fold).  Axiom-free.

    Scope note — the residual identity mask: nft additionally DROPS the now-trivial
    `(reg & 0xff..ff) ^ 0` binop, emitting a bare `cmp`.  Every meta/ct/rt/socket
    read is now WIDTH-normalised by construction ([Syntax.meta_width] & co. — the
    kernel register width table — via [Bytes.fit] in [do_load]), so the LENGTH of
    such a register is pinned; but a model byte is a [nat] with no 0..255 bound
    ([Bytes.byte]), so `reg & 0xff..ff` is still NOT provably the identity (a
    byte >= 256 would be truncated by the mask), and dropping it would be UNSOUND
    over the byte model — a byte-RANGE fact, not a width fact.  So the fold stops
    at the transfer nft's [binop_transfer] performs; the mask elimination awaits a
    by-construction byte-range normalisation, the same discipline [fit] applies
    to widths.  (The host-endian `mark` blocks are also endian-unportable in the
    text corpus — see DEVELOPMENT.md "The 83 source-divergences".) *)

From Stdlib Require Import List Bool Arith Lia.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics.
Import ListNotations.

(** Bytewise xor of two byte strings. *)
Fixpoint data_xor (a b : data) : data :=
  match a, b with
  | x :: xs, y :: ys => byte_xor x y :: data_xor xs ys
  | _, _ => []
  end.

Lemma data_xor_length : forall a b, length (data_xor a b) = Nat.min (length a) (length b).
Proof.
  induction a as [|x xs IH]; intros [|y ys]; simpl; try reflexivity.
  rewrite IH. reflexivity.
Qed.

(** Bytewise xor is involutive on each byte and on strings. *)
Lemma byte_xor_invol : forall x z, byte_xor (byte_xor x z) z = x.
Proof.
  intros x z. unfold byte_xor.
  rewrite Nat.lxor_assoc, Nat.lxor_nilpotent, Nat.lxor_0_r. reflexivity.
Qed.

Lemma data_bitops_length_le : forall a m x, length (data_bitops a m x) <= length m.
Proof.
  induction a as [|a0 a IH]; intros [|m0 m] [|x0 x]; simpl; try lia.
  specialize (IH m x). lia.
Qed.

(** [data_bitops a m x] is [(a & m)] then a bytewise xor with [x]: it equals
    [data_xor (a & m) x], where [a & m = data_bitops a m 0]. *)
Lemma data_bitops_as_xor : forall a m x w,
  length x = w -> length m = w ->
  data_bitops a m x = data_xor (data_bitops a m (repeat 0 w)) x.
Proof.
  induction a as [|a0 a IH]; intros [|m0 m] [|x0 x] w Hx Hm; simpl in *;
    try reflexivity; try (destruct w; discriminate).
  destruct w as [|w]; [discriminate|].
  injection Hx as Hx. injection Hm as Hm.
  cbn [repeat data_bitops data_xor].
  rewrite (IH m x w Hx Hm).
  unfold byte_xor, byte_and.
  rewrite Nat.lxor_0_r. reflexivity.
Qed.

(** Decidable-equality cons law for [data_eqb]. *)
Lemma data_eqb_cons : forall x l y l',
  data_eqb (x :: l) (y :: l') = (Nat.eqb x y && data_eqb l l')%bool.
Proof.
  intros x l y l'. destruct (Nat.eqb x y) eqn:Exy; simpl.
  - apply Nat.eqb_eq in Exy; subst y.
    destruct (data_eqb l l') eqn:El.
    + apply data_eqb_true_iff in El; subst l'. apply data_eqb_refl.
    + destruct (data_eqb (x :: l) (x :: l')) eqn:E; [|reflexivity].
      apply data_eqb_true_iff in E. injection E as E. subst l'.
      rewrite data_eqb_refl in El; discriminate.
  - destruct (data_eqb (x :: l) (y :: l')) eqn:E; [|reflexivity].
    apply data_eqb_true_iff in E. injection E as -> _.
    rewrite Nat.eqb_refl in Exy; discriminate.
Qed.

(** The transfer at the [data_eqb] level: moving the xor operand across the
    comparison preserves equality, for any [B0] no longer than [v]. *)
Lemma data_eqb_xor_transfer : forall B0 v x,
  length v = length x -> length B0 <= length v ->
  data_eqb B0 (data_xor v x) = data_eqb (data_xor B0 x) v.
Proof.
  induction B0 as [|b0 B0 IH]; intros v x Hvx Hlen.
  - (* B0 = [] : data_xor [] x = [] *) simpl.
    destruct v as [|y v]; destruct x as [|z x]; simpl in *; try lia;
      try reflexivity.
  - destruct v as [|y v]; [simpl in Hlen; lia|].
    destruct x as [|z x]; [simpl in Hvx; discriminate|].
    simpl in Hvx; injection Hvx as Hvx. simpl in Hlen.
    cbn [data_xor].
    rewrite !data_eqb_cons.
    rewrite (IH v x Hvx) by lia.
    f_equal.
    (* (b0 =? byte_xor y z) = (byte_xor b0 z =? y) *)
    destruct (Nat.eqb b0 (byte_xor y z)) eqn:E1.
    + apply Nat.eqb_eq in E1; subst b0.
      rewrite byte_xor_invol, Nat.eqb_refl. reflexivity.
    + destruct (Nat.eqb (byte_xor b0 z) y) eqn:E2; [|reflexivity].
      apply Nat.eqb_eq in E2; subst y.
      rewrite byte_xor_invol, Nat.eqb_refl in E1; discriminate.
Qed.

(** The transfer on one match body, for an equality/inequality comparison. *)
Lemma xor_transfer_body : forall f op mask xor v e p,
  (op = CEq \/ op = CNe) ->
  length mask = length v -> length xor = length v ->
  eval_matchcond_body (MMasked f op mask (repeat 0 (length v)) (data_xor v xor)) e p
  = eval_matchcond_body (MMasked f op mask xor v) e p.
Proof.
  intros f op mask xor v e p Hop Hm Hx.
  cbn [eval_matchcond_body].
  set (fv := field_value f e p).
  set (B0 := data_bitops fv mask (repeat 0 (length v))).
  (* the two register values: [B0] (masked, no xor) and [Bx = data_xor B0 xor] *)
  assert (HBx : data_bitops fv mask xor = data_xor B0 xor).
  { unfold B0. apply (data_bitops_as_xor fv mask xor (length v)); assumption. }
  assert (HB0len : length B0 <= length v).
  { unfold B0. rewrite <- Hm. apply data_bitops_length_le. }
  assert (Hdvx : length (data_xor v xor) = length v).
  { rewrite data_xor_length. rewrite Hx. apply Nat.min_id. }
  (* reduce both [eval_cmp]s: firstn drops (both register values are <= |v|) *)
  assert (Hcore :
    data_eqb (firstn (length (data_xor v xor)) B0) (data_xor v xor)
    = data_eqb (firstn (length v) (data_bitops fv mask xor)) v).
  { rewrite Hdvx.
    rewrite firstn_all2 with (l := B0) by lia.
    rewrite HBx.
    rewrite firstn_all2 with (l := data_xor B0 xor)
      by (rewrite data_xor_length; lia).
    apply data_eqb_xor_transfer; [ symmetry; exact Hx | exact HB0len ]. }
  destruct Hop as [-> | ->]; cbn [eval_cmp]; fold fv.
  - fold B0. rewrite Hcore. reflexivity.
  - fold B0. rewrite Hcore. reflexivity.
Qed.

(* ================================================================== *)
(** ** The pass. *)

(** Recognise the pure-xor shape and perform nft's constant transfer.  The
    all-ones mask ([repeat 255 (length v)]) is the `xor`-only lowering; an
    `and`/`or` mask is left untouched (nft does not fold those). *)
Definition xorfold_mc (m : matchcond) : matchcond :=
  match m with
  | MMasked f op mask xor v =>
      if (data_eqb mask (repeat 255 (length v))
          && Nat.eqb (length xor) (length v)
          && match op with CEq | CNe => true | _ => false end)%bool
      then MMasked f op mask (repeat 0 (length v)) (data_xor v xor)
      else m
  | _ => m
  end.

Lemma xorfold_mc_body : forall m e p,
  eval_matchcond_body (xorfold_mc m) e p = eval_matchcond_body m e p.
Proof.
  intros m e p.
  destruct m as [f v|f v|f n lo hi|f op msk xr w|f op v|fs n nm|f ts op v
                |f ts n nm|f ts n lo hi|sp|sp|sp|el n nm]; try reflexivity.
  cbn [xorfold_mc].
  destruct (data_eqb msk (repeat 255 (length w)) && Nat.eqb (length xr) (length w)
            && match op with CEq | CNe => true | _ => false end)%bool eqn:G;
    [|reflexivity].
  apply andb_true_iff in G as [G Gop].
  apply andb_true_iff in G as [Gmask Gxor].
  apply data_eqb_true_iff in Gmask.
  apply Nat.eqb_eq in Gxor.
  assert (Hml : length msk = length w)
    by (rewrite Gmask; apply repeat_length).
  apply xor_transfer_body.
  - destruct op; cbn in Gop; try discriminate; [left | right]; reflexivity.
  - exact Hml.
  - exact Gxor.
Qed.

Lemma xorfold_mc_loadable : forall m p,
  match_loadable (xorfold_mc m) p = match_loadable m p.
Proof.
  intros m p.
  destruct m as [f v|f v|f n lo hi|f op msk xr w|f op v|fs n nm|f ts op v
                |f ts n nm|f ts n lo hi|sp|sp|sp|el n nm]; try reflexivity.
  cbn [xorfold_mc].
  destruct (data_eqb msk (repeat 255 (length w)) && Nat.eqb (length xr) (length w)
            && match op with CEq | CNe => true | _ => false end)%bool;
    reflexivity.
Qed.

Lemma xorfold_mc_matchcond : forall m e p,
  eval_matchcond (xorfold_mc m) e p = eval_matchcond m e p.
Proof.
  intros m e p. unfold eval_matchcond.
  rewrite xorfold_mc_loadable, xorfold_mc_body. reflexivity.
Qed.

Definition xorfold_bi (it : body_item) : body_item :=
  match it with
  | BMatch m => BMatch (xorfold_mc m)
  | BStmt s => BStmt s
  end.

Definition xorfold_rule (r : rule) : rule :=
  {| r_body := map xorfold_bi (r_body r);
     r_outcome := r_outcome r; r_after := r_after r |}.

Definition xorfold_chain (c : chain) : chain :=
  {| c_policy := c_policy c; c_rules := map xorfold_rule (c_rules c) |}.

(* ================================================================== *)
(** ** Body-scan predicates are invariant (only [BMatch] items change, and only
    into another [BMatch] item; every [BStmt] is copied verbatim). *)

Lemma xorfold_body_has_notrack : forall body,
  body_has_notrack (map xorfold_bi body) = body_has_notrack body.
Proof.
  induction body as [| it b IH]; [reflexivity|].
  unfold body_has_notrack in *. cbn [map existsb]. rewrite IH.
  destruct it as [m | s]; [reflexivity | destruct s; reflexivity].
Qed.

Lemma xorfold_body_synproxy_stops : forall body p,
  body_synproxy_stops (map xorfold_bi body) p = body_synproxy_stops body p.
Proof.
  induction body as [| it b IH]; intro p; [reflexivity|].
  unfold body_synproxy_stops in *. cbn [map existsb]. rewrite IH.
  destruct it as [m | s]; [reflexivity | destruct s; reflexivity].
Qed.

Lemma xorfold_body_thread : forall body p,
  body_thread (map xorfold_bi body) p = body_thread body p.
Proof.
  intros body p. unfold body_thread. rewrite xorfold_body_has_notrack. reflexivity.
Qed.

Lemma xorfold_rule_applies_walk : forall body e p,
  rule_applies_walk (map xorfold_bi body) e p = rule_applies_walk body e p.
Proof.
  induction body as [| it b IH]; intros e p; [reflexivity|].
  destruct it as [m | s]; cbn [map xorfold_bi rule_applies_walk].
  - rewrite xorfold_mc_matchcond, IH. reflexivity.
  - destruct s; cbn [rule_applies_walk]; rewrite IH; reflexivity.
Qed.

Lemma xorfold_body_loadable_walk : forall body p,
  body_loadable_walk (map xorfold_bi body) p = body_loadable_walk body p.
Proof.
  induction body as [| it b IH]; intro p; [reflexivity|].
  destruct it as [m | s]; cbn [map xorfold_bi body_loadable_walk body_item_loadable].
  - rewrite xorfold_mc_loadable, IH. reflexivity.
  - destruct s; cbn [body_loadable_walk body_item_loadable stmt_loadable];
      rewrite IH; reflexivity.
Qed.

Lemma xorfold_r_body : forall r,
  r_body (xorfold_rule r) = map xorfold_bi (r_body r).
Proof. reflexivity. Qed.

Lemma xorfold_rule_loadable : forall r e p,
  rule_loadable (xorfold_rule r) e p = rule_loadable r e p.
Proof.
  intros r e p. unfold rule_loadable. rewrite xorfold_r_body.
  rewrite xorfold_body_loadable_walk, xorfold_body_synproxy_stops,
          xorfold_body_thread.
  destruct (body_synproxy_stops (r_body r) p); reflexivity.
Qed.

Lemma xorfold_rule_applies : forall r e p,
  rule_applies (xorfold_rule r) e p = rule_applies r e p.
Proof.
  intros r e p. unfold rule_applies. rewrite xorfold_r_body.
  apply xorfold_rule_applies_walk.
Qed.

Lemma xorfold_outcome : forall r e p,
  outcome (xorfold_rule r) e p = outcome r e p.
Proof.
  intros r e p. unfold outcome. rewrite xorfold_r_body.
  rewrite xorfold_body_synproxy_stops, xorfold_body_thread.
  destruct (body_synproxy_stops (r_body r) p); reflexivity.
Qed.

Lemma xorfold_eval_rules : forall rs e p,
  eval_rules (map xorfold_rule rs) e p = eval_rules rs e p.
Proof.
  induction rs as [| r rs IH]; intros e p; [reflexivity|].
  cbn [map eval_rules].
  rewrite xorfold_rule_loadable, xorfold_rule_applies, xorfold_outcome.
  destruct (rule_loadable r e p && rule_applies r e p); [| apply IH].
  destruct (outcome r e p) as [v|]; [destruct v|]; rewrite ?IH; reflexivity.
Qed.

Theorem xorfold_chain_eval : forall c e p,
  eval_chain (xorfold_chain c) e p = eval_chain c e p.
Proof.
  intros c e p. unfold eval_chain, xorfold_chain. cbn [c_rules c_policy].
  rewrite xorfold_eval_rules. reflexivity.
Qed.

(* ================================================================== *)
(** ** Non-vacuity: the pass GENUINELY rewrites.

    `meta mark xor 0x23 == 0x11` lowers to [MMasked FMetaMark CEq 0xff..ff
    0x00000023 0x00000011] (all-ones mask = pure xor).  The fold transfers the
    xor operand onto the value side: the register xor becomes 0 and the compare
    value becomes 0x11 ^ 0x23 = 0x32 (corpus class-L, any/ct.t.payload:151 /
    any/meta.t.payload:174; bytes shown little-endian, the mark register order). *)
Example xorfold_witness :
  xorfold_mc (MMasked FMetaMark CEq (repeat 255 4) [35;0;0;0] [17;0;0;0])
  = MMasked FMetaMark CEq (repeat 255 4) [0;0;0;0] [50;0;0;0].
Proof. vm_compute. reflexivity. Qed.

(** The output is NOT the input — a real constant fold. *)
Example xorfold_nonvacuous :
  xorfold_mc (MMasked FMetaMark CEq (repeat 255 4) [35;0;0;0] [17;0;0;0])
  <> MMasked FMetaMark CEq (repeat 255 4) [35;0;0;0] [17;0;0;0].
Proof. vm_compute. discriminate. Qed.

(** An `and` mask (NOT all-ones) is left untouched — nft does not fold those. *)
Example xorfold_leaves_and :
  xorfold_mc (MMasked FMetaMark CEq [3;0;0;0] [0;0;0;0] [1;0;0;0])
  = MMasked FMetaMark CEq [3;0;0;0] [0;0;0;0] [1;0;0;0].
Proof. vm_compute. reflexivity. Qed.

(** Axiom-freedom audit (build-time guard). *)
Print Assumptions xorfold_chain_eval.
