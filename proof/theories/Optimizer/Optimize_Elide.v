(** * Optimize_Elide: nft's trivial-binop elision (the class-L residue).

    When nftables' evaluator finishes transferring a pure-xor constant onto the
    compare value (src/evaluate.c [binop_transfer], the [Optimize_XorFold]
    stage), it does not leave the spent binop behind: [binop_transfer_handle_lhs]
    (src/evaluate.c, OP_XOR case) REPLACES the whole binop expression by its
    left operand — `(reg & 0xff..ff) ^ 0x00` disappears and the linearizer
    emits a bare load + cmp, no bitwise instruction (golden corpus:
    any/meta.t.payload's `meta mark xor` blocks carry no bitwise).

    This pass performs exactly that deletion on the [matchcond]: it recognises
    the trivial shape

        MMasked f op (all-ones at w) (all-zeros at w) v,   |v| = w,

    where [w] is the KERNEL REGISTER WIDTH of [f]'s load
    ([Syntax.load_octet_width] — the fixed-width oracle reads, normalised at
    the [do_load] boundary by [Bytes.fit]/[Bytes.octets]), and rewrites it to
    the bare compare

        MCmp f op v.

    Soundness is BY CONSTRUCTION, with NO hypotheses: a normalised read is
    width-pinned AND octet-clamped definitionally, and the all-ones/zero
    bitwise at that width is the identity on such a value
    ([Syntax.do_load_bitops_id]) — so the masked compare and the bare compare
    see the SAME register value.  [elide_chain_eval] is UNCONDITIONAL
    ([forall c e p]), axiom-free.

    Guard notes:
    - The guard is syntactic width equality [|v| = w] plus the all-ones mask
      and zero xor — the exact residue [Optimize_XorFold] leaves (nft's
      transferred cmp value has the operand's width).  Any other mask/xor/width
      is left untouched.
    - [load_octet_width _ = None] (payload/exthdr/fib/opaque loads) is left
      untouched: those reads carry their width in the load descriptor or are
      deliberately opaque, and no octet normalisation is claimed for them.
    - The IR carries no provenance, so a hand-written all-ones AND over a
      normalised field (`meta mark and 0xffffffff == v`) elides too.  That is
      semantics-preserving by the same identity; nft itself would keep such a
      no-op binop (only XOR/LSHIFT/RSHIFT transfer), but nft's own `-o`
      passes make no promise to preserve no-ops either. *)

From Stdlib Require Import List Bool Arith Lia.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics.
Import ListNotations.

(* ================================================================== *)
(** ** The pass. *)

(** Recognise the trivial binop — all-ones mask, zero xor, compare value at
    the field's kernel register width — and drop it, leaving the bare cmp. *)
Definition elide_mc (m : matchcond) : matchcond :=
  match m with
  | MMasked f op mask xor v =>
      match load_octet_width (field_load f) with
      | Some w =>
          if (Nat.eqb (length v) w
              && data_eqb mask (repeat 255 w)
              && data_eqb xor (repeat 0 w))%bool
          then MCmp f op v
          else m
      | None => m
      end
  | _ => m
  end.

Lemma elide_mc_body : forall m e p,
  eval_matchcond_body (elide_mc m) e p = eval_matchcond_body m e p.
Proof.
  intros m e p.
  destruct m as [f v|f v|f n lo hi|f op msk xr w|f op v|fs n nm|f ts op v
                |f ts n nm|f ts n lo hi|sp|sp|sp|el n nm]; try reflexivity.
  cbn [elide_mc].
  destruct (load_octet_width (field_load f)) as [wd|] eqn:Hw; [|reflexivity].
  destruct (Nat.eqb (length w) wd && data_eqb msk (repeat 255 wd)
            && data_eqb xr (repeat 0 wd))%bool eqn:G; [|reflexivity].
  apply andb_true_iff in G as [G Gxor].
  apply andb_true_iff in G as [_ Gmask].
  apply data_eqb_true_iff in Gmask.
  apply data_eqb_true_iff in Gxor.
  subst msk xr.
  cbn [eval_matchcond_body].
  unfold field_value.
  rewrite (do_load_bitops_id _ _ _ _ Hw).
  reflexivity.
Qed.

Lemma elide_mc_loadable : forall m p,
  match_loadable (elide_mc m) p = match_loadable m p.
Proof.
  intros m p.
  destruct m as [f v|f v|f n lo hi|f op msk xr w|f op v|fs n nm|f ts op v
                |f ts n nm|f ts n lo hi|sp|sp|sp|el n nm]; try reflexivity.
  cbn [elide_mc].
  destruct (load_octet_width (field_load f)); [|reflexivity].
  destruct (Nat.eqb (length w) n && data_eqb msk (repeat 255 n)
            && data_eqb xr (repeat 0 n))%bool; reflexivity.
Qed.

Lemma elide_mc_matchcond : forall m e p,
  eval_matchcond (elide_mc m) e p = eval_matchcond m e p.
Proof.
  intros m e p. unfold eval_matchcond.
  rewrite elide_mc_loadable, elide_mc_body. reflexivity.
Qed.

Definition elide_bi (it : body_item) : body_item :=
  match it with
  | BMatch m => BMatch (elide_mc m)
  | BStmt s => BStmt s
  end.

Definition elide_rule (r : rule) : rule :=
  {| r_body := map elide_bi (r_body r);
     r_outcome := r_outcome r; r_after := r_after r |}.

Definition elide_chain (c : chain) : chain :=
  {| c_policy := c_policy c; c_rules := map elide_rule (c_rules c) |}.

(* ================================================================== *)
(** ** Body-scan predicates are invariant (only [BMatch] items change, and only
    into another [BMatch] item; every [BStmt] is copied verbatim). *)

Lemma elide_body_has_notrack : forall body,
  body_has_notrack (map elide_bi body) = body_has_notrack body.
Proof.
  induction body as [| it b IH]; [reflexivity|].
  unfold body_has_notrack in *. cbn [map existsb]. rewrite IH.
  destruct it as [m | s]; [reflexivity | destruct s; reflexivity].
Qed.

Lemma elide_body_synproxy_stops : forall body p,
  body_synproxy_stops (map elide_bi body) p = body_synproxy_stops body p.
Proof.
  induction body as [| it b IH]; intro p; [reflexivity|].
  unfold body_synproxy_stops in *. cbn [map existsb]. rewrite IH.
  destruct it as [m | s]; [reflexivity | destruct s; reflexivity].
Qed.

Lemma elide_body_thread : forall body p,
  body_thread (map elide_bi body) p = body_thread body p.
Proof.
  intros body p. unfold body_thread. rewrite elide_body_has_notrack. reflexivity.
Qed.

Lemma elide_rule_applies_walk : forall body e p,
  rule_applies_walk (map elide_bi body) e p = rule_applies_walk body e p.
Proof.
  induction body as [| it b IH]; intros e p; [reflexivity|].
  destruct it as [m | s]; cbn [map elide_bi rule_applies_walk].
  - rewrite elide_mc_matchcond, IH. reflexivity.
  - destruct s; cbn [rule_applies_walk]; rewrite IH; reflexivity.
Qed.

Lemma elide_body_loadable_walk : forall body p,
  body_loadable_walk (map elide_bi body) p = body_loadable_walk body p.
Proof.
  induction body as [| it b IH]; intro p; [reflexivity|].
  destruct it as [m | s]; cbn [map elide_bi body_loadable_walk body_item_loadable].
  - rewrite elide_mc_loadable, IH. reflexivity.
  - destruct s; cbn [body_loadable_walk body_item_loadable stmt_loadable];
      rewrite IH; reflexivity.
Qed.

Lemma elide_r_body : forall r,
  r_body (elide_rule r) = map elide_bi (r_body r).
Proof. reflexivity. Qed.

Lemma elide_rule_loadable : forall r e p,
  rule_loadable (elide_rule r) e p = rule_loadable r e p.
Proof.
  intros r e p. unfold rule_loadable. rewrite elide_r_body.
  rewrite elide_body_loadable_walk, elide_body_synproxy_stops,
          elide_body_thread.
  destruct (body_synproxy_stops (r_body r) p); reflexivity.
Qed.

Lemma elide_rule_applies : forall r e p,
  rule_applies (elide_rule r) e p = rule_applies r e p.
Proof.
  intros r e p. unfold rule_applies. rewrite elide_r_body.
  apply elide_rule_applies_walk.
Qed.

Lemma elide_outcome : forall r e p,
  outcome (elide_rule r) e p = outcome r e p.
Proof.
  intros r e p. unfold outcome. rewrite elide_r_body.
  rewrite elide_body_synproxy_stops, elide_body_thread.
  destruct (body_synproxy_stops (r_body r) p); reflexivity.
Qed.

Lemma elide_eval_rules : forall rs e p,
  eval_rules (map elide_rule rs) e p = eval_rules rs e p.
Proof.
  induction rs as [| r rs IH]; intros e p; [reflexivity|].
  cbn [map eval_rules].
  rewrite elide_rule_loadable, elide_rule_applies, elide_outcome.
  destruct (rule_loadable r e p && rule_applies r e p); [| apply IH].
  destruct (outcome r e p) as [v|]; [destruct v|]; rewrite ?IH; reflexivity.
Qed.

Theorem elide_chain_eval : forall c e p,
  eval_chain (elide_chain c) e p = eval_chain c e p.
Proof.
  intros c e p. unfold eval_chain, elide_chain. cbn [c_rules c_policy].
  rewrite elide_eval_rules. reflexivity.
Qed.

(* ================================================================== *)
(** ** Non-vacuity: the pass GENUINELY deletes the trivial binop.

    The xor-fold residue of `meta mark xor 0x23 == 0x11`
    ([Optimize_XorFold.xorfold_witness]: all-ones mask, zero xor, value
    0x11 ^ 0x23 = 0x32) becomes the BARE compare — the bitwise stage is gone
    (nft's emitted form: cmp only, any/meta.t.payload's xor blocks). *)
Example elide_witness :
  elide_mc (MMasked FMetaMark CEq (repeat 255 4) [0;0;0;0] [50;0;0;0])
  = MCmp FMetaMark CEq [50;0;0;0].
Proof. vm_compute. reflexivity. Qed.

(** The output is NOT the input — a real deletion. *)
Example elide_nonvacuous :
  elide_mc (MMasked FMetaMark CEq (repeat 255 4) [0;0;0;0] [50;0;0;0])
  <> MMasked FMetaMark CEq (repeat 255 4) [0;0;0;0] [50;0;0;0].
Proof. vm_compute. discriminate. Qed.

(** A REAL mask (not all-ones) is left untouched — that bitwise is load-bearing. *)
Example elide_leaves_real_mask :
  elide_mc (MMasked FMetaMark CEq [3;0;0;0] [0;0;0;0] [1;0;0;0])
  = MMasked FMetaMark CEq [3;0;0;0] [0;0;0;0] [1;0;0;0].
Proof. vm_compute. reflexivity. Qed.

(** A LIVE xor (nonzero) is left untouched — [Optimize_XorFold] transfers it
    first; only the spent residue is deleted. *)
Example elide_leaves_live_xor :
  elide_mc (MMasked FMetaMark CEq (repeat 255 4) [35;0;0;0] [17;0;0;0])
  = MMasked FMetaMark CEq (repeat 255 4) [35;0;0;0] [17;0;0;0].
Proof. vm_compute. reflexivity. Qed.

(** A payload field is left untouched even in the trivial shape — its read is
    not register-normalised ([load_octet_width = None]). *)
Example elide_leaves_payload :
  elide_mc (MMasked FThDport CEq (repeat 255 2) [0;0] [0;80])
  = MMasked FThDport CEq (repeat 255 2) [0;0] [0;80].
Proof. vm_compute. reflexivity. Qed.

(** Axiom-freedom audit (build-time guard; enforcement is `make axioms`). *)
Print Assumptions elide_chain_eval.
