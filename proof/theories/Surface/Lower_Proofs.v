(** * Surface.Lower_Proofs: NON-definitional erasure — the typed numeric
    semantics (Semantics.TypedEval) agrees with the byte-level evaluation of
    the elaborated form (Typed.elab_tx), one theorem per new scalar shape and
    one composed theorem over all of them ([txmatch_erasure]).

    These are the M-D bricks, and they are NOT reflexivity: the two sides
    compute along genuinely different routes.  The typed side decodes the
    loaded register bytes to a NUMBER and compares in [N]; the byte side
    compares byte strings the elaboration ENCODED.  Bridging them costs the
    real obligations the milestone names:

      - byte-LEXICOGRAPHIC order equals NUMERIC order — for same-width,
        byte-wf, BIG-ENDIAN strings only ([data_le_num]); this is exactly the
        precondition the historical core-byteorder bug violated;
      - the host-endian `hton` range path: a full-width [TByteorder] swap is
        list reversal ([data_byteorder_full_rev]), after which the register
        holds the big-endian image of the host-endian field and the stored
        bounds must be the big-endian RE-encoding ([Typed.encode_be]), not
        the register encoding ([range_erasure_host]);
      - bytewise [(a & m) ^ x] distributes over the big-endian numeric
        reading as [N.lxor (N.land · ·) ·] ([data_to_N_bitops]) — proved by a
        byte-split lemma for each bit operation ([N_bitop_split]);
      - nft's three bitwise realisations are the boolean identities
        and/or/xor: (x & ~m) ^ m = x | m and (x & ~0) ^ m = x ^ m, within the
        register's bit width ([land_not_xor_is_or] etc.);
      - the bitfield mask/shift arithmetic: (x & ((2^bits-1) << s)) = v << s
        iff ((x >> s) & (2^bits-1)) = v ([land_shiftl_mask] + shift-cancel).

    Every theorem here is axiom-free and enforced by `make axioms`
    ([range_erasure_be], [range_erasure_host], [bitmask_erasure],
    [bitfield_erasure], [bitwise_erasure], [flag_erasure],
    [txmatch_erasure]).  Non-vacuity: concrete packets exercise each theorem's
    hypotheses at the bottom of the file (the typed side computes [Some true]
    AND the byte side computes [true] by [vm_compute]). *)

From Stdlib Require Import List PeanoNat Bool NArith Lia String.
From Nft Require Import Bytes Packet Verdict Bytecode Syntax Semantics Nftval
  Elab Ast Datatype Symbols Selector Typecheck Typed Lower TypedEval.
Import ListNotations.

(* ================================================================== *)
(** ** Byte-level bridges between [Nat] bit operations (the [data] domain)
    and [N] bit operations (the numeric domain), by finite check over the
    byte range — the [Nat]<->[N] bitwise conversion lemmas the stdlib lacks. *)

Definition byte2_ok (f : nat -> nat -> bool) : bool :=
  forallb (fun a => forallb (f a) (seq 0 256)) (seq 0 256).

Lemma byte2_ok_spec : forall f, byte2_ok f = true ->
  forall a b, a < 256 -> b < 256 -> f a b = true.
Proof.
  intros f H a b Ha Hb. unfold byte2_ok in H.
  rewrite forallb_forall in H.
  assert (Hin : In a (seq 0 256)) by (apply in_seq; lia).
  specialize (H a Hin). rewrite forallb_forall in H.
  apply H, in_seq; lia.
Qed.

Lemma byte_land_N : forall a b, a < 256 -> b < 256 ->
  N.of_nat (Nat.land a b) = N.land (N.of_nat a) (N.of_nat b).
Proof.
  intros a b Ha Hb. apply N.eqb_eq.
  apply (byte2_ok_spec
    (fun a b => (N.of_nat (Nat.land a b) =? N.land (N.of_nat a) (N.of_nat b))%N));
    [vm_compute; reflexivity | exact Ha | exact Hb].
Qed.

Lemma byte_lxor_N : forall a b, a < 256 -> b < 256 ->
  N.of_nat (Nat.lxor a b) = N.lxor (N.of_nat a) (N.of_nat b).
Proof.
  intros a b Ha Hb. apply N.eqb_eq.
  apply (byte2_ok_spec
    (fun a b => (N.of_nat (Nat.lxor a b) =? N.lxor (N.of_nat a) (N.of_nat b))%N));
    [vm_compute; reflexivity | exact Ha | exact Hb].
Qed.

Lemma byte_land_lt : forall a b, a < 256 -> b < 256 -> Nat.land a b < 256.
Proof.
  intros a b Ha Hb. apply Nat.ltb_lt.
  apply (byte2_ok_spec (fun a b => (Nat.land a b <? 256)%nat));
    [vm_compute; reflexivity | exact Ha | exact Hb].
Qed.

Lemma byte_lxor_lt : forall a b, a < 256 -> b < 256 -> Nat.lxor a b < 256.
Proof.
  intros a b Ha Hb. apply Nat.ltb_lt.
  apply (byte2_ok_spec (fun a b => (Nat.lxor a b <? 256)%nat));
    [vm_compute; reflexivity | exact Ha | exact Hb].
Qed.

Lemma byte_land_255 : forall a, a < 256 -> Nat.land a 255 = a.
Proof.
  intros a Ha. apply Nat.eqb_eq.
  exact (byte2_ok_spec (fun x _ => (Nat.land x 255 =? x)%nat)
           ltac:(vm_compute; reflexivity) a a Ha Ha).
Qed.

(* ================================================================== *)
(** ** [data_to_N] arithmetic. *)

Lemma bytes_wfb_cons : forall b d, bytes_wfb (b :: d) = true ->
  b < 256 /\ bytes_wfb d = true.
Proof.
  intros b d H. unfold bytes_wfb in H. cbn [forallb] in H.
  apply andb_prop in H as [Hb Hd]. apply Nat.ltb_lt in Hb. auto.
Qed.

Lemma data_to_N_acc : forall d acc,
  fold_left (fun a b => (a * 256 + N.of_nat b)%N) d acc
  = (acc * 256 ^ N.of_nat (List.length d) + data_to_N d)%N.
Proof.
  induction d as [|x d IH]; intro acc.
  - cbn. lia.
  - cbn [fold_left List.length]. rewrite IH.
    unfold data_to_N. cbn [fold_left].
    rewrite (IH (0 * 256 + N.of_nat x)%N).
    rewrite Nat2N.inj_succ, N.pow_succ_r'. fold (data_to_N d). nia.
Qed.

Lemma data_to_N_cons : forall x d,
  data_to_N (x :: d)
  = (N.of_nat x * 256 ^ N.of_nat (List.length d) + data_to_N d)%N.
Proof.
  intros x d. unfold data_to_N at 1. cbn [fold_left].
  rewrite data_to_N_acc.
  replace (0 * 256 + N.of_nat x)%N with (N.of_nat x) by lia. reflexivity.
Qed.

Lemma bytes_wfb_Forall : forall d,
  bytes_wfb d = true <-> Forall (fun b => b < 256) d.
Proof.
  intro d. unfold bytes_wfb. rewrite forallb_forall, Forall_forall.
  split; intros H x Hx; specialize (H x Hx); apply Nat.ltb_lt; exact H.
Qed.

Lemma pow256_pos : forall w, (0 < 256 ^ N.of_nat w)%N.
Proof.
  intro w. apply N.neq_0_lt_0. apply N.pow_nonzero. lia.
Qed.

Lemma data_to_N_bound : forall d, bytes_wfb d = true ->
  (data_to_N d < 256 ^ N.of_nat (List.length d))%N.
Proof.
  induction d as [|x d IH]; intro H.
  - cbn. lia.
  - apply bytes_wfb_cons in H as [Hx Hd].
    rewrite data_to_N_cons. cbn [List.length].
    rewrite Nat2N.inj_succ, N.pow_succ_r'.
    specialize (IH Hd).
    pose proof (pow256_pos (List.length d)).
    assert (N.of_nat x <= 255)%N by lia. nia.
Qed.

Lemma N_to_data_wfb : forall w n, bytes_wfb (N_to_data w n) = true.
Proof.
  induction w; intro n; cbn [N_to_data].
  - reflexivity.
  - unfold bytes_wfb in *. rewrite forallb_app, IHw. cbn [forallb].
    rewrite !andb_true_r, andb_true_l. apply Nat.ltb_lt.
    assert (n mod 256 < 256)%N by (apply N.mod_lt; lia). lia.
Qed.

Lemma repeat_wfb : forall b w, b < 256 -> bytes_wfb (repeat b w) = true.
Proof.
  intros b w Hb. apply bytes_wfb_Forall.
  apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
Qed.

Lemma data_to_N_repeat0 : forall w, data_to_N (repeat 0 w) = 0%N.
Proof.
  induction w; [reflexivity|].
  cbn [repeat]. rewrite data_to_N_cons, IHw. lia.
Qed.

Lemma data_to_N_repeat255 : forall w,
  data_to_N (repeat 255 w) = (256 ^ N.of_nat w - 1)%N.
Proof.
  induction w; [reflexivity|].
  cbn [repeat]. rewrite data_to_N_cons, IHw, repeat_length.
  rewrite (Nat2N.inj_succ w), N.pow_succ_r'.
  pose proof (pow256_pos w). lia.
Qed.

Lemma data_eqb_num : forall a b,
  List.length a = List.length b -> bytes_wfb a = true -> bytes_wfb b = true ->
  data_eqb a b = (data_to_N a =? data_to_N b)%N.
Proof.
  intros a b Hl Ha Hb.
  destruct (data_eqb a b) eqn:E.
  - apply data_eqb_true_iff in E. subst. symmetry. apply N.eqb_refl.
  - symmetry. apply Bool.not_true_is_false. rewrite N.eqb_eq. intro Hn.
    assert (a = b).
    { apply bytes_wfb_Forall in Ha. apply bytes_wfb_Forall in Hb.
      rewrite <- (N_to_data_data_to_N a Ha), <- (N_to_data_data_to_N b Hb).
      f_equal; [exact Hl | exact Hn]. }
    subst. rewrite data_eqb_refl in E. discriminate.
Qed.

Lemma data_le_num : forall a b,
  List.length a = List.length b -> bytes_wfb a = true -> bytes_wfb b = true ->
  data_le a b = (data_to_N a <=? data_to_N b)%N.
Proof.
  induction a as [|x xs IH]; intros [|y ys] Hl Ha Hb; try discriminate.
  - reflexivity.
  - cbn in Hl. injection Hl as Hl.
    apply bytes_wfb_cons in Ha as [Hx Ha]. apply bytes_wfb_cons in Hb as [Hy Hb].
    cbn [data_le]. rewrite !data_to_N_cons, Hl.
    set (P := (256 ^ N.of_nat (List.length ys))%N).
    assert (HP : (0 < P)%N) by apply pow256_pos.
    assert (HA : (data_to_N xs < P)%N).
    { unfold P. rewrite <- Hl. apply data_to_N_bound. exact Ha. }
    assert (HB : (data_to_N ys < P)%N) by (apply data_to_N_bound; exact Hb).
    destruct (Nat.eqb x y) eqn:Exy.
    + apply Nat.eqb_eq in Exy. subst y.
      rewrite (IH ys Hl Ha Hb).
      destruct (data_to_N xs <=? data_to_N ys)%N eqn:E; symmetry.
      * apply N.leb_le. apply N.leb_le in E. lia.
      * apply N.leb_gt. apply N.leb_gt in E. lia.
    + apply Nat.eqb_neq in Exy.
      destruct (Nat.leb x y) eqn:L; symmetry.
      * apply Nat.leb_le in L. apply N.leb_le.
        assert (N.of_nat x < N.of_nat y)%N by lia. nia.
      * apply Nat.leb_gt in L. apply N.leb_gt.
        assert (N.of_nat y < N.of_nat x)%N by lia. nia.
Qed.

(* ================================================================== *)
(** ** Bit-operation split lemmas over [N] (byte-string concatenation is
    shift-and-add on disjoint bit ranges). *)

Lemma N_testbit_bounded : forall n k i,
  (n < 2 ^ k)%N -> (k <= i)%N -> N.testbit n i = false.
Proof.
  intros n k i Hn Hk.
  destruct (N.eq_dec n 0) as [->|Hnz]; [apply N.bits_0|].
  apply N.bits_above_log2.
  apply N.log2_lt_pow2 in Hn; lia.
Qed.

Lemma N_bounded_testbit : forall n k,
  (forall i, (k <= i)%N -> N.testbit n i = false) -> (n < 2 ^ k)%N.
Proof.
  intros n k H.
  destruct (N.eq_dec n 0) as [->|Hnz].
  { apply N.neq_0_lt_0. apply N.pow_nonzero. lia. }
  destruct (N.lt_ge_cases n (2 ^ k)) as [|Hge]; [assumption|exfalso].
  pose proof (N.bit_log2 n Hnz) as Hb.
  rewrite H in Hb; [discriminate|].
  apply N.log2_le_pow2; [lia|exact Hge].
Qed.

Lemma shiftl_add_disjoint : forall h l k, (l < 2 ^ k)%N ->
  (N.shiftl h k + l)%N = N.lor (N.shiftl h k) l.
Proof.
  intros h l k Hl.
  assert (Hland : N.land (N.shiftl h k) l = 0%N).
  { apply N.bits_inj_iff. intro i. rewrite N.land_spec, N.bits_0.
    destruct (N.lt_ge_cases i k) as [Hik|Hik].
    - rewrite N.shiftl_spec_low by lia. reflexivity.
    - rewrite (N_testbit_bounded l k i Hl Hik), andb_false_r. reflexivity. }
  rewrite (N.add_nocarry_lxor _ _ Hland). apply N.lxor_lor. exact Hland.
Qed.

Lemma N_bitop_split :
  forall (opN : N -> N -> N) (f : bool -> bool -> bool),
    (forall a b i, N.testbit (opN a b) i = f (N.testbit a i) (N.testbit b i)) ->
    f false false = false ->
    forall hb hm lb lm k,
      (lb < 2 ^ k)%N -> (lm < 2 ^ k)%N ->
      opN (N.shiftl hb k + lb)%N (N.shiftl hm k + lm)%N
      = (N.shiftl (opN hb hm) k + opN lb lm)%N.
Proof.
  intros opN f Hspec Hff hb hm lb lm k Hlb Hlm.
  assert (Hop : (opN lb lm < 2 ^ k)%N).
  { apply N_bounded_testbit. intros i Hi. rewrite Hspec.
    rewrite (N_testbit_bounded lb k i Hlb Hi),
            (N_testbit_bounded lm k i Hlm Hi). exact Hff. }
  rewrite (shiftl_add_disjoint hb lb k Hlb),
          (shiftl_add_disjoint hm lm k Hlm),
          (shiftl_add_disjoint (opN hb hm) (opN lb lm) k Hop).
  apply N.bits_inj_iff. intro i.
  rewrite Hspec, !N.lor_spec.
  destruct (N.lt_ge_cases i k) as [Hik|Hik].
  - rewrite !N.shiftl_spec_low by lia. cbn [orb]. rewrite Hspec. reflexivity.
  - rewrite (N_testbit_bounded lb k i Hlb Hik),
            (N_testbit_bounded lm k i Hlm Hik),
            (N_testbit_bounded (opN lb lm) k i Hop Hik).
    rewrite !orb_false_r.
    rewrite !N.shiftl_spec_high' by lia.
    apply eq_sym, Hspec.
Qed.

Lemma N_land_bound_l : forall a b k, (a < 2 ^ k)%N -> (N.land a b < 2 ^ k)%N.
Proof.
  intros a b k Ha. apply N_bounded_testbit. intros i Hi.
  rewrite N.land_spec, (N_testbit_bounded a k i Ha Hi). reflexivity.
Qed.

Lemma pow256_pow2 : forall w,
  (256 ^ N.of_nat w)%N = (2 ^ (8 * N.of_nat w))%N.
Proof.
  intro w. change 256%N with (2 ^ 8)%N. rewrite <- N.pow_mul_r. reflexivity.
Qed.

(* ================================================================== *)
(** ** Bytewise [(a & m) ^ x] is [N.lxor (N.land · ·) ·] on the big-endian
    numeric reading — the arithmetic core of every masked-compare erasure. *)

Lemma data_bitops_length_eq : forall a m x,
  List.length m = List.length a -> List.length x = List.length a ->
  List.length (data_bitops a m x) = List.length a.
Proof.
  induction a as [|a0 a' IH]; intros [|m0 m'] [|x0 x'] Hm Hx;
    try discriminate; [reflexivity|].
  cbn in *. f_equal. apply IH; lia.
Qed.

Lemma data_bitops_wfb : forall a m x,
  List.length m = List.length a -> List.length x = List.length a ->
  bytes_wfb a = true -> bytes_wfb m = true -> bytes_wfb x = true ->
  bytes_wfb (data_bitops a m x) = true.
Proof.
  induction a as [|a0 a' IH]; intros [|m0 m'] [|x0 x'] Hm Hx Ha Hwm Hwx;
    try discriminate; [reflexivity|].
  cbn in Hm, Hx. injection Hm as Hm. injection Hx as Hx.
  apply bytes_wfb_cons in Ha as [Ha0 Ha'].
  apply bytes_wfb_cons in Hwm as [Hm0 Hm'].
  apply bytes_wfb_cons in Hwx as [Hx0 Hx'].
  cbn [data_bitops]. unfold bytes_wfb. cbn [forallb].
  apply andb_true_intro. split.
  - apply Nat.ltb_lt. unfold byte_xor, byte_and.
    apply byte_lxor_lt; [apply byte_land_lt|]; assumption.
  - apply IH; assumption.
Qed.

Lemma data_to_N_bitops : forall a m x,
  List.length m = List.length a -> List.length x = List.length a ->
  bytes_wfb a = true -> bytes_wfb m = true -> bytes_wfb x = true ->
  data_to_N (data_bitops a m x)
  = N.lxor (N.land (data_to_N a) (data_to_N m)) (data_to_N x).
Proof.
  induction a as [|a0 a' IH]; intros [|m0 m'] [|x0 x'] Hm Hx Ha Hwm Hwx;
    try discriminate; [reflexivity|].
  cbn in Hm, Hx. injection Hm as Hm. injection Hx as Hx.
  apply bytes_wfb_cons in Ha as [Ha0 Ha'].
  apply bytes_wfb_cons in Hwm as [Hm0 Hm'].
  apply bytes_wfb_cons in Hwx as [Hx0 Hx'].
  cbn [data_bitops].
  rewrite !data_to_N_cons.
  rewrite data_bitops_length_eq by assumption.
  rewrite Hm, Hx.
  rewrite (IH m' x' Hm Hx Ha' Hm' Hx').
  set (K := (8 * N.of_nat (List.length a'))%N).
  rewrite pow256_pow2. fold K.
  rewrite <- !N.shiftl_mul_pow2.
  assert (HA' : (data_to_N a' < 2 ^ K)%N).
  { unfold K. rewrite <- pow256_pow2. apply data_to_N_bound. exact Ha'. }
  assert (HM' : (data_to_N m' < 2 ^ K)%N).
  { unfold K. rewrite <- pow256_pow2, <- Hm. apply data_to_N_bound. exact Hm'. }
  assert (HX' : (data_to_N x' < 2 ^ K)%N).
  { unfold K. rewrite <- pow256_pow2, <- Hx. apply data_to_N_bound. exact Hx'. }
  rewrite (N_bitop_split N.land andb N.land_spec (eq_refl false)
             _ _ _ _ K HA' HM').
  rewrite (N_bitop_split N.lxor xorb N.lxor_spec (eq_refl false)
             _ _ _ _ K (N_land_bound_l _ _ _ HA') HX').
  unfold byte_xor, byte_and.
  rewrite byte_lxor_N by (try apply byte_land_lt; assumption).
  rewrite byte_land_N by assumption.
  reflexivity.
Qed.

(* ================================================================== *)
(** ** Reversal plumbing (the host-endian register views). *)

Lemma bytes_wfb_rev : forall d, bytes_wfb (rev d) = bytes_wfb d.
Proof.
  intro d.
  destruct (bytes_wfb d) eqn:E.
  - apply bytes_wfb_Forall, Forall_rev, bytes_wfb_Forall, E.
  - destruct (bytes_wfb (rev d)) eqn:E2; [|reflexivity].
    apply bytes_wfb_Forall in E2. apply Forall_rev in E2.
    rewrite rev_involutive in E2.
    apply bytes_wfb_Forall in E2. congruence.
Qed.

Lemma data_bitops_app : forall a m x p q r,
  List.length m = List.length a -> List.length x = List.length a ->
  data_bitops (a ++ p)%list (m ++ q)%list (x ++ r)%list
  = (data_bitops a m x ++ data_bitops p q r)%list.
Proof.
  induction a as [|a0 a' IH]; intros [|m0 m'] [|x0 x'] p q r Hm Hx;
    try discriminate; [reflexivity|].
  cbn in Hm, Hx. injection Hm as Hm. injection Hx as Hx.
  cbn [app data_bitops]. f_equal. apply IH; assumption.
Qed.

Lemma data_bitops_rev : forall a m x,
  List.length m = List.length a -> List.length x = List.length a ->
  data_bitops (rev a) (rev m) (rev x) = rev (data_bitops a m x).
Proof.
  induction a as [|a0 a' IH]; intros [|m0 m'] [|x0 x'] Hm Hx;
    try discriminate; [reflexivity|].
  cbn in Hm, Hx. injection Hm as Hm. injection Hx as Hx.
  cbn [rev data_bitops].
  rewrite data_bitops_app by (rewrite !length_rev; congruence).
  rewrite IH by assumption. cbn [data_bitops app]. reflexivity.
Qed.

Lemma data_eqb_rev : forall a b, data_eqb (rev a) (rev b) = data_eqb a b.
Proof.
  intros a b.
  destruct (data_eqb a b) eqn:E.
  - apply data_eqb_true_iff in E. subst. apply data_eqb_refl.
  - destruct (data_eqb (rev a) (rev b)) eqn:E2; [|reflexivity].
    apply data_eqb_true_iff in E2.
    assert (a = b) by (rewrite <- (rev_involutive a), <- (rev_involutive b);
                       f_equal; exact E2).
    subst. rewrite data_eqb_refl in E. discriminate.
Qed.

Lemma data_not_rev : forall d, data_not (rev d) = rev (data_not d).
Proof. intro d. unfold data_not. apply map_rev. Qed.

Lemma data_not_length : forall d, List.length (data_not d) = List.length d.
Proof. intro d. unfold data_not. apply length_map. Qed.

Lemma data_not_wfb : forall d, bytes_wfb d = true -> bytes_wfb (data_not d) = true.
Proof.
  intro d. unfold bytes_wfb, data_not.
  rewrite !forallb_forall. intros H x Hx.
  apply in_map_iff in Hx as (y & <- & Hy). specialize (H y Hy).
  apply Nat.ltb_lt in H. apply Nat.ltb_lt. apply byte_lxor_lt; [exact H|lia].
Qed.

Lemma data_not_cons : forall b d,
  data_not (b :: d) = Nat.lxor b 255 :: data_not d.
Proof. reflexivity. Qed.

(** The numeric value of the bytewise complement: XOR with the all-ones word. *)
Lemma data_to_N_data_not : forall d, bytes_wfb d = true ->
  data_to_N (data_not d)
  = N.lxor (data_to_N d) (256 ^ N.of_nat (List.length d) - 1)%N.
Proof.
  induction d as [|b d IH]; intro H; [reflexivity|].
  apply bytes_wfb_cons in H as [Hb Hd].
  rewrite data_not_cons, !data_to_N_cons.
  rewrite data_not_length, (IH Hd).
  cbn [List.length].
  set (K := (8 * N.of_nat (List.length d))%N).
  rewrite (Nat2N.inj_succ (List.length d)), N.pow_succ_r', !pow256_pow2. fold K.
  rewrite <- !N.shiftl_mul_pow2.
  assert (HD : (data_to_N d < 2 ^ K)%N).
  { unfold K. rewrite <- pow256_pow2. apply data_to_N_bound. exact Hd. }
  assert (Hones : (2 ^ K - 1 < 2 ^ K)%N).
  { assert (0 < 2 ^ K)%N by (apply N.neq_0_lt_0, N.pow_nonzero; lia). lia. }
  replace (N.shiftl 256 K - 1)%N with (N.shiftl 255 K + (2 ^ K - 1))%N.
  2:{ rewrite !N.shiftl_mul_pow2.
      assert (0 < 2 ^ K)%N by (apply N.neq_0_lt_0, N.pow_nonzero; lia). lia. }
  rewrite (N_bitop_split N.lxor xorb N.lxor_spec (eq_refl false)
             _ _ _ _ K HD Hones).
  rewrite byte_lxor_N by lia.
  reflexivity.
Qed.

(* ================================================================== *)
(** ** Full-width byteorder swap is list reversal. *)

Lemma byteorder_chunks_nil : forall fuel size,
  byteorder_chunks fuel size [] = [].
Proof. destruct fuel; reflexivity. Qed.

Lemma data_byteorder_full_rev : forall h w d,
  List.length d = w -> data_byteorder h w w d = rev d.
Proof.
  intros h w d Hl. unfold data_byteorder.
  destruct d as [|b d'].
  - apply byteorder_chunks_nil.
  - cbn [byteorder_chunks List.length].
    rewrite <- Hl, firstn_all, skipn_all, byteorder_chunks_nil, app_nil_r.
    reflexivity.
Qed.

(* ================================================================== *)
(** ** Typed-value encoding facts (the [encode]-side bridge). *)

Lemma val_width_encode : forall v,
  List.length (Nftval.encode v) = val_width v.
Proof.
  destruct v; cbn [Nftval.encode val_width];
    try apply N_to_data_length; try reflexivity;
    rewrite length_rev; apply N_to_data_length.
Qed.

Lemma encode_wfb : forall v, val_wfb v = true ->
  bytes_wfb (Nftval.encode v) = true.
Proof.
  destruct v; cbn [Nftval.encode val_wfb]; intro H;
    try apply N_to_data_wfb; try assumption;
    rewrite bytes_wfb_rev; apply N_to_data_wfb.
Qed.

Lemma encode_num_be : forall v, val_wfb v = true -> host_val v = false ->
  data_to_N (Nftval.encode v) = val_N v.
Proof.
  destruct v; cbn [Nftval.encode val_wfb val_N host_val]; intros H Hh;
    try discriminate; try reflexivity;
    apply data_to_N_N_to_data; apply N.ltb_lt in H; exact H.
Qed.

Lemma encode_be_num : forall v, val_wfb v = true ->
  data_to_N (encode_be v) = val_N v.
Proof.
  destruct v; intro H;
    try (apply encode_num_be; [exact H | reflexivity]);
    cbn [encode_be val_N]; apply data_to_N_N_to_data;
    cbn [val_wfb] in H; apply N.ltb_lt in H; exact H.
Qed.

Lemma encode_be_len : forall v, List.length (encode_be v) = val_width v.
Proof.
  destruct v; cbn [encode_be val_width];
    try apply N_to_data_length; apply val_width_encode.
Qed.

Lemma encode_be_wfb : forall v, val_wfb v = true ->
  bytes_wfb (encode_be v) = true.
Proof.
  destruct v; intro H; try (apply encode_wfb; exact H);
    cbn [encode_be]; apply N_to_data_wfb.
Qed.

Lemma encode_host_rev : forall v, host_val v = true ->
  Nftval.encode v = rev (encode_be v).
Proof.
  destruct v; intro H; try discriminate; reflexivity.
Qed.

(* ================================================================== *)
(** ** Read inversions and small evaluation bridges. *)

Lemma read_be_N_inv : forall w d x, read_be_N w d = Some x ->
  List.length d = w /\ bytes_wfb d = true /\ x = data_to_N d.
Proof.
  intros w d x H. unfold read_be_N in H.
  destruct (Nat.eqb (List.length d) w) eqn:E1; [|discriminate].
  destruct (bytes_wfb d) eqn:E2; [|discriminate].
  cbn in H. injection H as <-. apply Nat.eqb_eq in E1. auto.
Qed.

Lemma eval_cmp_eq_num : forall fv vb,
  List.length vb = List.length fv ->
  bytes_wfb fv = true -> bytes_wfb vb = true ->
  eval_cmp CEq fv vb = (data_to_N fv =? data_to_N vb)%N.
Proof.
  intros fv vb Hl Hf Hv. cbn [eval_cmp].
  rewrite Hl, firstn_all. apply data_eqb_num; auto.
Qed.

Lemma eval_cmp_negcases : forall (neg : bool) (fv vb : data),
  eval_cmp (if neg then CNe else CEq) fv vb
  = xorb neg (eval_cmp CEq fv vb).
Proof. intros [] fv vb; reflexivity. Qed.

Lemma eval_range_negcases : forall (neg : bool) (fv lo hi : data),
  eval_range (if neg then CNe else CEq) fv lo hi
  = xorb neg (andb (data_le lo fv) (data_le fv hi)).
Proof. intros [] fv lo hi; reflexivity. Qed.

Lemma eval_range_num : forall (neg : bool) (fv lob hib : data),
  List.length lob = List.length fv -> List.length hib = List.length fv ->
  bytes_wfb fv = true -> bytes_wfb lob = true -> bytes_wfb hib = true ->
  eval_range (if neg then CNe else CEq) fv lob hib
  = xorb neg (andb (data_to_N lob <=? data_to_N fv)%N
                   (data_to_N fv <=? data_to_N hib)%N).
Proof.
  intros neg fv lob hib Hlo Hhi Hf Hl Hh.
  rewrite eval_range_negcases.
  rewrite (data_le_num lob fv Hlo Hl Hf).
  rewrite (data_le_num fv hib (eq_sym Hhi) Hf Hh).
  reflexivity.
Qed.

(** The pointwise bit identities inside the register width. *)
Lemma land_not_xor_is_or : forall x m K,
  (x < 2 ^ K)%N -> (m < 2 ^ K)%N ->
  N.lxor (N.land x (N.lxor m (2 ^ K - 1))) m = N.lor x m.
Proof.
  intros x m K Hx Hm.
  assert (Hones : (2 ^ K - 1)%N = N.ones K) by (rewrite N.ones_equiv; lia).
  rewrite Hones.
  apply N.bits_inj_iff. intro i.
  rewrite N.lxor_spec, N.land_spec, N.lxor_spec, N.lor_spec.
  destruct (N.lt_ge_cases i K) as [Hik|Hik].
  - rewrite N.ones_spec_low by lia.
    destruct (N.testbit x i), (N.testbit m i); reflexivity.
  - rewrite (N_testbit_bounded x K i Hx Hik),
            (N_testbit_bounded m K i Hm Hik),
            N.ones_spec_high by lia.
    reflexivity.
Qed.

Lemma land_ones_id : forall x K, (x < 2 ^ K)%N -> N.land x (2 ^ K - 1)%N = x.
Proof.
  intros x K Hx.
  assert (Hones : (2 ^ K - 1)%N = N.ones K) by (rewrite N.ones_equiv; lia).
  rewrite Hones, N.land_ones. apply N.mod_small. exact Hx.
Qed.

Lemma land_shiftl_mask : forall x m s,
  N.land x (N.shiftl m s) = N.shiftl (N.land (N.shiftr x s) m) s.
Proof.
  intros x m s. apply N.bits_inj_iff. intro i.
  rewrite N.land_spec.
  destruct (N.lt_ge_cases i s) as [His|His].
  - rewrite !N.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !N.shiftl_spec_high' by lia.
    rewrite N.land_spec, N.shiftr_spec'.
    replace (i - s + s)%N with i by lia. reflexivity.
Qed.

Lemma shiftl_eqb_cancel : forall a b s,
  (N.shiftl a s =? N.shiftl b s)%N = (a =? b)%N.
Proof.
  intros a b s. rewrite !N.shiftl_mul_pow2.
  destruct (N.eqb a b) eqn:E.
  - apply N.eqb_eq in E. subst. apply N.eqb_refl.
  - apply N.eqb_neq in E. apply N.eqb_neq. intro Hc. apply E.
    apply N.mul_cancel_r in Hc; [exact Hc|].
    apply N.pow_nonzero. lia.
Qed.

(* ================================================================== *)
(** ** THE ERASURE THEOREMS. *)

(** Plain big-endian ranges: byte-lexicographic register order IS numeric
    order — for same-width, byte-wf, big-endian values (the side conditions
    the typed evaluation checks at run time). *)
Theorem range_erasure_be : forall f dt neg lo hi e p b,
  range_hton dt = false ->
  eval_txm (TXRange f dt neg lo hi) e p = Some b ->
  eval_matchcond (elab_tx (TXRange f dt neg lo hi)) e p = b.
Proof.
  intros f dt neg lo hi e p b Hh Hev.
  cbn [eval_txm] in Hev. cbn [elab_tx]. rewrite Hh in *.
  destruct (field_loadable f p) eqn:HL; cbn [negb] in Hev.
  2:{ injection Hev as <-.
      unfold eval_matchcond. cbn [match_loadable]. rewrite HL. reflexivity. }
  destruct (bound_ok dt lo && bound_ok dt hi) eqn:HB; cbn [negb] in Hev;
    [|discriminate].
  destruct (byteorder_eqb (dt_byteorder dt) BoBig) eqn:HBO; [|discriminate].
  destruct (host_val lo || host_val hi) eqn:HH; [discriminate|].
  unfold read_dt_N in Hev.
  assert (Hbo2 : byteorder_eqb (dt_byteorder dt) BoHost = false)
    by (destruct (dt_byteorder dt); cbn in *; congruence).
  rewrite Hbo2 in Hev.
  destruct (read_be_N (dt_bytes dt) (field_value f e p)) as [x|] eqn:HR;
    [|discriminate].
  injection Hev as <-.
  apply read_be_N_inv in HR as (Hlen & Hwf & ->).
  apply andb_prop in HB as [HBlo HBhi].
  unfold bound_ok in HBlo, HBhi.
  apply andb_prop in HBlo as [Hwlo Hflo].
  apply andb_prop in HBhi as [Hwhi Hfhi].
  apply Nat.eqb_eq in Hwlo, Hwhi.
  apply orb_false_elim in HH as [Hhlo Hhhi].
  unfold eval_matchcond. cbn [match_loadable]. rewrite HL.
  cbn [eval_matchcond_body andb].
  rewrite eval_range_num;
    try (rewrite val_width_encode; congruence);
    try exact Hwf; try (apply encode_wfb; assumption).
  rewrite !encode_num_be by assumption. reflexivity.
Qed.

(** Host-endian (mark / ifindex / fib-type) ranges: the mandatory
    `byteorder hton` path.  The full-width byteorder transform is list
    reversal; the stored bounds are the big-endian RE-encoding; the numeric
    value is the host-endian reading of the loaded register.  This is the
    byte-order obligation the historical core-byteorder bug got wrong —
    proved here, not tested. *)
Theorem range_erasure_host : forall f dt neg lo hi e p b,
  range_hton dt = true ->
  eval_txm (TXRange f dt neg lo hi) e p = Some b ->
  eval_matchcond (elab_tx (TXRange f dt neg lo hi)) e p = b.
Proof.
  intros f dt neg lo hi e p b Hh Hev.
  cbn [eval_txm] in Hev. cbn [elab_tx]. rewrite Hh in *.
  destruct (field_loadable f p) eqn:HL; cbn [negb] in Hev.
  2:{ injection Hev as <-.
      unfold eval_matchcond. cbn [match_loadable]. rewrite HL. reflexivity. }
  destruct (bound_ok dt lo && bound_ok dt hi) eqn:HB; cbn [negb] in Hev;
    [|discriminate].
  assert (HboH : dt_byteorder dt = BoHost)
    by (destruct dt; cbn in Hh; try discriminate; reflexivity).
  unfold read_dt_N in Hev. rewrite HboH in Hev. cbn [byteorder_eqb] in Hev.
  destruct (read_be_N (dt_bytes dt) (rev (field_value f e p))) as [x|] eqn:HR;
    [|discriminate].
  injection Hev as <-.
  apply read_be_N_inv in HR as (Hlen & Hwf & ->).
  rewrite length_rev in Hlen. rewrite bytes_wfb_rev in Hwf.
  apply andb_prop in HB as [HBlo HBhi].
  unfold bound_ok in HBlo, HBhi.
  apply andb_prop in HBlo as [Hwlo Hflo].
  apply andb_prop in HBhi as [Hwhi Hfhi].
  apply Nat.eqb_eq in Hwlo, Hwhi.
  unfold eval_matchcond. cbn [match_loadable]. rewrite HL.
  cbn [eval_matchcond_body andb].
  cbn [apply_transforms fold_left apply_transform].
  rewrite (data_byteorder_full_rev true (dt_bytes dt) _ Hlen).
  rewrite eval_range_num;
    try (rewrite encode_be_len, length_rev; congruence);
    try (rewrite bytes_wfb_rev; exact Hwf);
    try (apply encode_be_wfb; assumption).
  rewrite !encode_be_num by assumption. reflexivity.
Qed.

(** Bitmask forms (ct state / ct status / tcp flags): the OR-fold's byte
    encoding tests the same bits the numeric [N.land] tests. *)
Theorem bitmask_erasure : forall f dt op bits e p b,
  eval_txm (TXBitmask f dt op bits) e p = Some b ->
  eval_matchcond (elab_tx (TXBitmask f dt op bits)) e p = b.
Proof.
  intros f dt op bits e p b Hev.
  cbn [eval_txm] in Hev.
  destruct (field_loadable f p) eqn:HL; cbn [negb] in Hev.
  2:{ injection Hev as <-.
      unfold eval_matchcond. destruct op; cbn [elab_tx match_loadable];
        rewrite HL; reflexivity. }
  destruct (byteorder_eqb (dt_byteorder dt) BoBig) eqn:HBO; [|discriminate].
  set (m := bm_fold bits) in *.
  set (w := dt_bytes dt) in *.
  destruct (m <? 256 ^ N.of_nat w)%N eqn:HM; cbn [negb] in Hev; [|discriminate].
  apply N.ltb_lt in HM.
  unfold read_dt_N in Hev.
  assert (Hbo2 : byteorder_eqb (dt_byteorder dt) BoHost = false)
    by (destruct (dt_byteorder dt); cbn in *; congruence).
  rewrite Hbo2 in Hev. fold w in Hev.
  destruct (read_be_N w (field_value f e p)) as [x|] eqn:HR; [|discriminate].
  injection Hev as <-.
  apply read_be_N_inv in HR as (Hlen & Hwf & ->).
  assert (Hmb_len : List.length (N_to_data w m) = List.length (field_value f e p))
    by (rewrite N_to_data_length; congruence).
  assert (Hmb_num : data_to_N (N_to_data w m) = m)
    by (apply data_to_N_N_to_data; exact HM).
  assert (Hz_len : List.length (repeat 0 w) = List.length (field_value f e p))
    by (rewrite repeat_length; congruence).
  unfold eval_matchcond.
  destruct op; cbn [elab_tx match_loadable]; rewrite HL;
    cbn [eval_matchcond_body andb]; fold m w.
  - (* implicit: MMasked CNe mb 0 0 — (field & m) <> 0 *)
    change (eval_cmp CNe ?a ?b) with (negb (eval_cmp CEq a b)).
    rewrite eval_cmp_eq_num;
      [ | rewrite data_bitops_length_eq by assumption;
          rewrite repeat_length; congruence
        | apply data_bitops_wfb;
          [exact Hmb_len | exact Hz_len | exact Hwf
           | apply N_to_data_wfb | apply repeat_wfb; lia]
        | apply repeat_wfb; lia ].
    rewrite data_to_N_bitops;
      [ | exact Hmb_len | exact Hz_len | exact Hwf
        | apply N_to_data_wfb | apply repeat_wfb; lia ].
    rewrite Hmb_num, data_to_N_repeat0, N.lxor_0_r. reflexivity.
  - (* ==: MEq f mb *)
    rewrite eval_cmp_eq_num;
      [ | exact Hmb_len | exact Hwf | apply N_to_data_wfb ].
    rewrite Hmb_num. reflexivity.
  - (* !=: MNeq f mb *)
    change (eval_cmp CNe ?a ?b) with (negb (eval_cmp CEq a b)).
    rewrite eval_cmp_eq_num;
      [ | exact Hmb_len | exact Hwf | apply N_to_data_wfb ].
    rewrite Hmb_num. reflexivity.
  - (* bang: MMasked CEq mb 0 0 — (field & m) == 0 *)
    rewrite eval_cmp_eq_num;
      [ | rewrite data_bitops_length_eq by assumption;
          rewrite repeat_length; congruence
        | apply data_bitops_wfb;
          [exact Hmb_len | exact Hz_len | exact Hwf
           | apply N_to_data_wfb | apply repeat_wfb; lia]
        | apply repeat_wfb; lia ].
    rewrite data_to_N_bitops;
      [ | exact Hmb_len | exact Hz_len | exact Hwf
        | apply N_to_data_wfb | apply repeat_wfb; lia ].
    rewrite Hmb_num, data_to_N_repeat0, N.lxor_0_r. reflexivity.
Qed.

(** Sub-byte bitfields: the Coq-computed mask/shift bytes test exactly the
    field's bits — (x & ((2^bits-1)<<s)) = v<<s iff ((x>>s) & (2^bits-1)) = v. *)
Theorem bitfield_erasure : forall spec neg v e p b,
  eval_txm (TXBitfield spec neg v) e p = Some b ->
  eval_matchcond (elab_tx (TXBitfield spec neg v)) e p = b.
Proof.
  intros spec neg v e p b Hev.
  cbn [eval_txm] in Hev. cbn [elab_tx].
  destruct (field_loadable (bf_field spec) p) eqn:HL; cbn [negb] in Hev.
  2:{ injection Hev as <-.
      unfold eval_matchcond. cbn [match_loadable]. rewrite HL. reflexivity. }
  destruct ((bf_bits spec + bf_shift spec <=? 8 * bf_bytes spec)%nat) eqn:Hfit;
    [|discriminate].
  destruct (v <? 2 ^ N.of_nat (bf_bits spec))%N eqn:Hv; cbn [negb] in Hev;
    [|discriminate].
  apply Nat.leb_le in Hfit. apply N.ltb_lt in Hv.
  destruct (read_be_N (bf_bytes spec) (field_value (bf_field spec) e p))
    as [x|] eqn:HR; [|discriminate].
  injection Hev as <-.
  apply read_be_N_inv in HR as (Hlen & Hwf & ->).
  set (bits := bf_bits spec) in *. set (s := bf_shift spec) in *.
  set (len := bf_bytes spec) in *.
  set (fv := field_value (bf_field spec) e p) in *.
  (* the mask and compare value fit the loaded width *)
  assert (Hpow : (2 ^ (N.of_nat bits + N.of_nat s) <= 2 ^ (8 * N.of_nat len))%N).
  { apply N.pow_le_mono_r; lia. }
  assert (HM : (N.shiftl (N.ones (N.of_nat bits)) (N.of_nat s)
                < 256 ^ N.of_nat len)%N).
  { rewrite pow256_pow2, N.shiftl_mul_pow2, N.ones_equiv.
    eapply N.lt_le_trans; [|exact Hpow].
    rewrite N.pow_add_r.
    assert (0 < 2 ^ N.of_nat bits)%N by (apply N.neq_0_lt_0, N.pow_nonzero; lia).
    assert (0 < 2 ^ N.of_nat s)%N by (apply N.neq_0_lt_0, N.pow_nonzero; lia).
    nia. }
  assert (HV : (N.shiftl v (N.of_nat s) < 256 ^ N.of_nat len)%N).
  { rewrite pow256_pow2, N.shiftl_mul_pow2.
    eapply N.lt_le_trans; [|exact Hpow].
    rewrite N.pow_add_r.
    assert (0 < 2 ^ N.of_nat s)%N by (apply N.neq_0_lt_0, N.pow_nonzero; lia).
    nia. }
  unfold eval_matchcond. cbn [match_loadable]. rewrite HL.
  cbn [eval_matchcond_body andb].
  unfold bf_mask, bf_cmpval. fold bits s len fv.
  rewrite eval_cmp_negcases.
  assert (Hmlen : List.length
            (N_to_data len (N.shiftl (N.ones (N.of_nat bits)) (N.of_nat s)))
          = List.length fv) by (rewrite N_to_data_length; congruence).
  assert (Hzlen : List.length (repeat 0 len) = List.length fv)
    by (rewrite repeat_length; congruence).
  rewrite eval_cmp_eq_num;
    [ | rewrite data_bitops_length_eq by assumption;
        rewrite N_to_data_length; congruence
      | apply data_bitops_wfb;
        [exact Hmlen | exact Hzlen | exact Hwf
         | apply N_to_data_wfb | apply repeat_wfb; lia]
      | apply N_to_data_wfb ].
  rewrite data_to_N_bitops;
    [ | exact Hmlen | exact Hzlen | exact Hwf
      | apply N_to_data_wfb | apply repeat_wfb; lia ].
  rewrite data_to_N_repeat0, N.lxor_0_r.
  rewrite !data_to_N_N_to_data by assumption.
  rewrite land_shiftl_mask, shiftl_eqb_cancel.
  reflexivity.
Qed.

(** Presence flags: the 1-byte compare is the numeric compare. *)
Theorem flag_erasure : forall f neg v e p b,
  eval_txm (TXFlag f neg v) e p = Some b ->
  eval_matchcond (elab_tx (TXFlag f neg v)) e p = b.
Proof.
  intros f neg v e p b Hev.
  cbn [eval_txm] in Hev. cbn [elab_tx].
  destruct (field_loadable f p) eqn:HL; cbn [negb] in Hev.
  2:{ injection Hev as <-.
      unfold eval_matchcond. destruct neg; cbn [match_loadable];
        rewrite HL; reflexivity. }
  destruct (v <? 256)%N eqn:Hv; cbn [negb] in Hev; [|discriminate].
  apply N.ltb_lt in Hv.
  destruct (read_be_N 1 (field_value f e p)) as [x|] eqn:HR; [|discriminate].
  injection Hev as <-.
  apply read_be_N_inv in HR as (Hlen & Hwf & ->).
  assert (Hv1 : (v < 256 ^ N.of_nat 1)%N) by (cbn; lia).
  unfold eval_matchcond.
  destruct neg; cbn [match_loadable]; rewrite HL;
    cbn [eval_matchcond_body andb].
  - change (eval_cmp CNe ?a ?b) with (negb (eval_cmp CEq a b)).
    rewrite eval_cmp_eq_num;
      [| rewrite N_to_data_length; congruence | exact Hwf | apply N_to_data_wfb].
    rewrite data_to_N_N_to_data by exact Hv1. reflexivity.
  - rewrite eval_cmp_eq_num;
      [| rewrite N_to_data_length; congruence | exact Hwf | apply N_to_data_wfb].
    rewrite data_to_N_N_to_data by exact Hv1. reflexivity.
Qed.

(** Explicit bitwise matches: nft's three (mask, xor) realisations compute
    [N.land] / [N.lor] / [N.lxor] of the register's numeric value — in the
    register's own byte order (the host-endian case reduces to the big-endian
    one by reversal on BOTH sides of the compare). *)

(** The big-endian core, shared by both byteorder cases: the compare of the
    realised (mask, xor) form against the encoded value equals the numeric
    predicate. *)
Lemma bitwise_core : forall bop (fv mbe vbe : data) w,
  List.length fv = w -> List.length mbe = w -> List.length vbe = w ->
  bytes_wfb fv = true -> bytes_wfb mbe = true -> bytes_wfb vbe = true ->
  eval_cmp CEq
    (match bop with
     | BOand => data_bitops fv mbe (repeat 0 w)
     | BOor  => data_bitops fv (data_not mbe) mbe
     | BOxor => data_bitops fv (repeat 255 w) mbe
     end) vbe
  = ((match bop with
      | BOand => N.land (data_to_N fv) (data_to_N mbe)
      | BOor  => N.lor  (data_to_N fv) (data_to_N mbe)
      | BOxor => N.lxor (data_to_N fv) (data_to_N mbe)
      end) =? data_to_N vbe)%N.
Proof.
  intros bop fv mbe vbe w Hf Hm Hv Hwf Hwm Hwv.
  assert (Hxbound : (data_to_N fv < 2 ^ (8 * N.of_nat w))%N).
  { rewrite <- pow256_pow2, <- Hf. apply data_to_N_bound. exact Hwf. }
  assert (Hmbound : (data_to_N mbe < 2 ^ (8 * N.of_nat w))%N).
  { rewrite <- pow256_pow2, <- Hm. apply data_to_N_bound. exact Hwm. }
  destruct bop.
  - (* and: (fv & m) ^ 0 *)
    rewrite eval_cmp_eq_num;
      [| rewrite Hv, data_bitops_length_eq;
         rewrite ?repeat_length; congruence
       | apply data_bitops_wfb; rewrite ?repeat_length; try congruence;
         auto using repeat_wfb with arith
       | exact Hwv].
    rewrite data_to_N_bitops; rewrite ?repeat_length; try congruence;
      auto using repeat_wfb with arith.
    rewrite data_to_N_repeat0, N.lxor_0_r. reflexivity.
  - (* or: (fv & ~m) ^ m *)
    rewrite eval_cmp_eq_num;
      [| rewrite Hv, data_bitops_length_eq;
         rewrite ?data_not_length; congruence
       | apply data_bitops_wfb; rewrite ?data_not_length; try congruence;
         auto using data_not_wfb
       | exact Hwv].
    rewrite data_to_N_bitops; rewrite ?data_not_length; try congruence;
      auto using data_not_wfb.
    rewrite data_to_N_data_not by exact Hwm. rewrite Hm.
    rewrite pow256_pow2.
    rewrite land_not_xor_is_or by assumption. reflexivity.
  - (* xor: (fv & ~0) ^ m *)
    rewrite eval_cmp_eq_num;
      [| rewrite Hv, data_bitops_length_eq;
         rewrite ?repeat_length; congruence
       | apply data_bitops_wfb; rewrite ?repeat_length; try congruence;
         auto using repeat_wfb with arith
       | exact Hwv].
    rewrite data_to_N_bitops; rewrite ?repeat_length; try congruence;
      auto using repeat_wfb with arith.
    rewrite data_to_N_repeat255, pow256_pow2.
    rewrite land_ones_id by exact Hxbound. reflexivity.
Qed.

Lemma eval_cmp_eq_rev : forall a b, List.length a = List.length b ->
  eval_cmp CEq a b = eval_cmp CEq (rev a) (rev b).
Proof.
  intros a b Hl. cbn [eval_cmp].
  rewrite <- Hl, firstn_all.
  rewrite length_rev, <- Hl, <- (length_rev a), firstn_all.
  apply eq_sym, data_eqb_rev.
Qed.

Lemma encode_be_nonhost : forall v, host_val v = false ->
  encode_be v = Nftval.encode v.
Proof. destruct v; intro H; try discriminate; reflexivity. Qed.

Theorem bitwise_erasure : forall f dt bop neg mask v e p b,
  eval_txm (TXBitwise f dt bop neg mask v) e p = Some b ->
  eval_matchcond (elab_tx (TXBitwise f dt bop neg mask v)) e p = b.
Proof.
  intros f dt bop neg mask v e p b Hev.
  cbn [eval_txm] in Hev.
  destruct (field_loadable f p) eqn:HL; cbn [negb] in Hev.
  2:{ injection Hev as <-.
      unfold eval_matchcond. destruct bop; cbn [elab_tx match_loadable];
        rewrite HL; reflexivity. }
  destruct (operand_ok dt mask && operand_ok dt v) eqn:HOK; cbn [negb] in Hev;
    [|discriminate].
  apply andb_prop in HOK as [HOm HOv].
  unfold operand_ok in HOm, HOv.
  apply andb_prop in HOm as [HOm Hbm]. apply andb_prop in HOm as [Hwm Hfm].
  apply andb_prop in HOv as [HOv Hbv]. apply andb_prop in HOv as [Hwv Hfv].
  apply Nat.eqb_eq in Hwm, Hwv.
  apply Bool.eqb_prop in Hbm, Hbv.
  unfold read_dt_N in Hev.
  set (w := dt_bytes dt) in *.
  set (fv := field_value f e p) in *.
  (* common facts about the encoded operands *)
  assert (Hmlen : List.length (encode_be mask) = w)
    by (rewrite encode_be_len; congruence).
  assert (Hvlen : List.length (encode_be v) = w)
    by (rewrite encode_be_len; congruence).
  assert (Hmwf : bytes_wfb (encode_be mask) = true)
    by (apply encode_be_wfb; assumption).
  assert (Hvwf : bytes_wfb (encode_be v) = true)
    by (apply encode_be_wfb; assumption).
  assert (Hmnum : data_to_N (encode_be mask) = val_N mask)
    by (apply encode_be_num; assumption).
  assert (Hvnum : data_to_N (encode_be v) = val_N v)
    by (apply encode_be_num; assumption).
  destruct (byteorder_eqb (dt_byteorder dt) BoHost) eqn:HBO.
  - (* HOST-endian register: both compare sides reverse to the BE core *)
    destruct (read_be_N w (rev fv)) as [x|] eqn:HR; [|discriminate].
    injection Hev as <-.
    apply read_be_N_inv in HR as (Hlen & Hwf & ->).
    rewrite length_rev in Hlen. rewrite bytes_wfb_rev in Hwf.
    assert (Hmenc : Nftval.encode mask = rev (encode_be mask))
      by (apply encode_host_rev; exact Hbm).
    assert (Hvenc : Nftval.encode v = rev (encode_be v))
      by (apply encode_host_rev; exact Hbv).
    assert (Hmenclen : List.length (Nftval.encode mask) = w)
      by (rewrite val_width_encode; congruence).
    destruct bop; cbn [elab_tx match_loadable]; unfold eval_matchcond;
      cbn [match_loadable]; rewrite HL; cbn [eval_matchcond_body andb];
      fold w fv; rewrite eval_cmp_negcases.
    + (* and *)
      rewrite eval_cmp_eq_rev
        by (rewrite val_width_encode, data_bitops_length_eq;
            rewrite ?repeat_length; congruence).
      rewrite <- data_bitops_rev by (rewrite ?repeat_length; congruence).
      rewrite Hmenc, Hvenc, !rev_involutive, rev_repeat.
      rewrite (bitwise_core BOand (rev fv) (encode_be mask) (encode_be v) w);
        rewrite ?length_rev, ?bytes_wfb_rev; auto.
      rewrite Hmnum, Hvnum. reflexivity.
    + (* or *)
      rewrite eval_cmp_eq_rev
        by (rewrite val_width_encode, data_bitops_length_eq;
            rewrite ?data_not_length, ?val_width_encode; congruence).
      rewrite <- data_bitops_rev
        by (rewrite ?data_not_length; congruence).
      rewrite Hmenc, Hvenc, data_not_rev, !rev_involutive.
      rewrite (bitwise_core BOor (rev fv) (encode_be mask) (encode_be v) w);
        rewrite ?length_rev, ?bytes_wfb_rev; auto.
      rewrite Hmnum, Hvnum. reflexivity.
    + (* xor *)
      rewrite eval_cmp_eq_rev
        by (rewrite val_width_encode, data_bitops_length_eq;
            rewrite ?repeat_length, ?val_width_encode; congruence).
      rewrite <- data_bitops_rev
        by (rewrite ?repeat_length, ?val_width_encode; congruence).
      rewrite Hmenc, Hvenc, !rev_involutive, rev_repeat.
      rewrite (bitwise_core BOxor (rev fv) (encode_be mask) (encode_be v) w);
        rewrite ?length_rev, ?bytes_wfb_rev; auto.
      rewrite Hmnum, Hvnum. reflexivity.
  - (* BIG-endian register: the core applies directly *)
    destruct (read_be_N w fv) as [x|] eqn:HR; [|discriminate].
    injection Hev as <-.
    apply read_be_N_inv in HR as (Hlen & Hwf & ->).
    assert (Hmenc : Nftval.encode mask = encode_be mask)
      by (apply eq_sym, encode_be_nonhost; exact Hbm).
    assert (Hvenc : Nftval.encode v = encode_be v)
      by (apply eq_sym, encode_be_nonhost; exact Hbv).
    destruct bop; cbn [elab_tx match_loadable]; unfold eval_matchcond;
      cbn [match_loadable]; rewrite HL; cbn [eval_matchcond_body andb];
      fold w fv; rewrite eval_cmp_negcases; rewrite Hmenc, Hvenc.
    + rewrite (bitwise_core BOand fv (encode_be mask) (encode_be v) w); auto.
      rewrite Hmnum, Hvnum. reflexivity.
    + rewrite (bitwise_core BOor fv (encode_be mask) (encode_be v) w); auto.
      rewrite Hmnum, Hvnum. reflexivity.
    + rewrite (bitwise_core BOxor fv (encode_be mask) (encode_be v) w); auto.
      rewrite Hmnum, Hvnum. reflexivity.
Qed.

(** The four M0 shapes: their agreement is Elab's documented consistency
    check ([elab_matchcond_correct]), restated in the [Some]-form. *)
Corollary txelab_erasure : forall m e p b,
  eval_txm (TXElab m) e p = Some b ->
  eval_matchcond (elab_tx (TXElab m)) e p = b.
Proof.
  intros m e p b H. injection H as <-. cbn [elab_tx].
  apply elab_matchcond_correct.
Qed.

(** THE COMPOSED THEOREM (the M-D brick): whenever the typed numeric
    semantics yields a verdict, the elaborated byte IR computes the SAME
    verdict — for every typed scalar match shape. *)
Theorem txmatch_erasure : forall t e p b,
  eval_txm t e p = Some b ->
  eval_matchcond (elab_tx t) e p = b.
Proof.
  intros t e p b H.
  destruct t as [m|f dt neg lo hi|f dt op bits|spec neg v|f dt bop neg mask v
                 |f neg v].
  - apply txelab_erasure; exact H.
  - destruct (range_hton dt) eqn:Hh.
    + apply range_erasure_host; assumption.
    + apply range_erasure_be; assumption.
  - apply bitmask_erasure; exact H.
  - apply bitfield_erasure; exact H.
  - apply bitwise_erasure; exact H.
  - apply flag_erasure; exact H.
Qed.

(* ================================================================== *)
(** ** Non-vacuity: each theorem's hypotheses are satisfied by concrete
    terms/packets, and BOTH sides compute the same concrete verdicts
    (vm_compute, using TypedEval's witnesses). *)

Example erasure_bitmask_exercised :
  eval_txm (TXBitmask FCtState DTct_state SOpImplicit [2%N]) tev_env tev_pkt
    = Some true
  /\ eval_matchcond (elab_tx (TXBitmask FCtState DTct_state SOpImplicit [2%N]))
       tev_env tev_pkt = true.
Proof. vm_compute. split; reflexivity. Qed.

Example erasure_range_be_exercised :
  eval_txm (TXRange FThDport DTinet_service false (VPort 400) (VPort 500))
    tev_env tev_pkt = Some true
  /\ eval_matchcond
       (elab_tx (TXRange FThDport DTinet_service false (VPort 400) (VPort 500)))
       tev_env tev_pkt = true.
Proof. vm_compute. split; reflexivity. Qed.

Example erasure_range_host_exercised :
  eval_txm (TXRange FCtMark DTmark false (VHostInt 4 0x32) (VHostInt 4 0x45))
    tev_env tev_pkt = Some true
  /\ eval_matchcond
       (elab_tx (TXRange FCtMark DTmark false (VHostInt 4 0x32) (VHostInt 4 0x45)))
       tev_env tev_pkt = true.
Proof. vm_compute. split; reflexivity. Qed.

Example erasure_bitwise_exercised :
  (* ct mark or 0x03 == 0x43 on the host-endian register holding 0x40 *)
  eval_txm (TXBitwise FCtMark DTmark BOor false (VHostInt 4 3) (VHostInt 4 0x43))
    tev_env tev_pkt = Some true
  /\ eval_matchcond
       (elab_tx (TXBitwise FCtMark DTmark BOor false (VHostInt 4 3)
                   (VHostInt 4 0x43))) tev_env tev_pkt = true.
Proof. vm_compute. split; reflexivity. Qed.

Example erasure_bitfield_exercised :
  (* tcp doff of the witness packet: transport byte 12 is 0x00 -> doff 0 *)
  eval_txm (TXBitfield (bf (FPayload PTransport 12 1) 1 4 4 (dep_l4 "tcp") false)
              false 0) tev_env tev_pkt = Some true
  /\ eval_matchcond
       (elab_tx (TXBitfield (bf (FPayload PTransport 12 1) 1 4 4
                               (dep_l4 "tcp") false) false 0))
       tev_env tev_pkt = true.
Proof. vm_compute. split; reflexivity. Qed.

Example erasure_flag_exercised :
  (* the fib present flag loads [] in the witness env -> undecodable, STUCK;
     a loadable 1-byte field exercises the flag compare instead *)
  eval_txm (TXFlag FTcpFlags false 0x12) tev_env tev_pkt = Some true
  /\ eval_matchcond (elab_tx (TXFlag FTcpFlags false 0x12)) tev_env tev_pkt
     = true.
Proof. vm_compute. split; reflexivity. Qed.

(** Axiom-freedom guards (informational; the enforcement point is
    `make axioms`). *)
Print Assumptions range_erasure_be.
Print Assumptions range_erasure_host.
Print Assumptions bitmask_erasure.
Print Assumptions bitfield_erasure.
Print Assumptions bitwise_erasure.
Print Assumptions flag_erasure.
Print Assumptions txmatch_erasure.
