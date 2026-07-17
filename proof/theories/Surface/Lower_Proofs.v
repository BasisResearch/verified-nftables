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
        iff ((x >> s) & (2^bits-1)) = v ([land_shiftl_mask] + shift-cancel);
      - the typed eq/neq register decode at the VALUE's byteorder
        ([eq_erasure]/[neq_erasure]) and the leading-bytes numeric view of a
        genuinely short compare ([wildcard_erasure]);
      - the CIDR prefix mask arithmetic, over BOTH prefix_expand branches —
        nft's byte-aligned truncated-load shortening and the full-width
        masked compare ([prefix_erasure]: a masked top-bits compare is
        numerically a right-shift compare of both sides).

    These four scalar-shape theorems SUPERSEDE the retired
    [Elab.elab_matchcond_correct] (a definitional consistency check, proved
    by [reflexivity] because the legacy typed semantics was itself defined
    through the byte encoding); the shapes now carry the same NON-definitional
    erasure obligations as every other typed construct.

    Every theorem here is axiom-free and enforced by `make axioms`
    ([eq_erasure], [neq_erasure], [prefix_erasure], [wildcard_erasure],
    [range_erasure_be], [range_erasure_host], [bitmask_erasure],
    [bitfield_erasure], [bitwise_erasure], [flag_erasure],
    [txmatch_erasure]).  Non-vacuity: concrete packets exercise each theorem's
    hypotheses at the bottom of the file (the typed side computes [Some true]
    AND the byte side computes [true] by [vm_compute]). *)

From Stdlib Require Import List PeanoNat Bool NArith Lia String.
From Nft Require Import Bytes Packet Verdict Bytecode Syntax Semantics Nftval
  Ast Datatype Symbols Selector Typecheck Typed Lower TypedEval.
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

(** [bytes_wfb] distributes over append and restricts to a prefix. *)
Lemma bytes_wfb_app : forall a b : data,
  bytes_wfb (a ++ b)%list = andb (bytes_wfb a) (bytes_wfb b).
Proof. intros a b. unfold bytes_wfb. apply forallb_app. Qed.

Lemma bytes_wfb_firstn : forall k d,
  bytes_wfb d = true -> bytes_wfb (firstn k d) = true.
Proof.
  induction k as [|k IH]; intros [|x d] H; try reflexivity.
  apply bytes_wfb_cons in H as [Hx Hd].
  cbn [firstn]. unfold bytes_wfb. cbn [forallb].
  apply andb_true_intro. split; [apply Nat.ltb_lt; exact Hx | apply IH; exact Hd].
Qed.

(** [data_to_N] splits over append: the leading bytes are the high-order
    bits, so dropping the tail is a right shift. *)
Lemma data_to_N_app : forall a b : data,
  data_to_N (a ++ b)%list
  = (data_to_N a * 256 ^ N.of_nat (List.length b) + data_to_N b)%N.
Proof.
  intros a b.
  replace (data_to_N (a ++ b)%list)
    with (fold_left (fun x y => (x * 256 + N.of_nat y)%N) b (data_to_N a))
    by (unfold data_to_N; rewrite fold_left_app; reflexivity).
  apply data_to_N_acc.
Qed.

Lemma data_to_N_app_shiftr : forall a b : data,
  bytes_wfb b = true ->
  N.shiftr (data_to_N (a ++ b)%list) (8 * N.of_nat (List.length b)) = data_to_N a.
Proof.
  intros a b Hwb.
  rewrite data_to_N_app, N.shiftr_div_pow2, <- pow256_pow2.
  rewrite N.div_add_l by (apply N.pow_nonzero; lia).
  rewrite N.div_small by (apply data_to_N_bound; exact Hwb).
  apply N.add_0_r.
Qed.

(** The leading-bytes register read ([TypedEval.read_lead_N]) returns exactly
    the numeric value of the register's first [k] bytes. *)
Lemma read_lead_N_inv : forall k d x, read_lead_N k d = Some x ->
  (k <= List.length d)%nat /\ bytes_wfb d = true
  /\ x = data_to_N (firstn k d).
Proof.
  intros k d x H. unfold read_lead_N in H.
  destruct ((k <=? List.length d)%nat && bytes_wfb d) eqn:E; [|discriminate].
  apply andb_prop in E as [Hk Hwf]. apply Nat.leb_le in Hk.
  injection H as <-.
  split; [exact Hk|]. split; [exact Hwf|].
  assert (Hwb : bytes_wfb (skipn k d) = true).
  { rewrite <- (firstn_skipn k d), bytes_wfb_app in Hwf.
    apply andb_prop in Hwf as [_ Hwb]. exact Hwb. }
  replace (List.length d - k)%nat with (List.length (skipn k d))
    by (rewrite length_skipn; reflexivity).
  rewrite <- (firstn_skipn k d) at 1.
  apply data_to_N_app_shiftr. exact Hwb.
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
(** ** Prefix-mask arithmetic (shared by [prefix_erasure] and the M3 CIDR
    interval agreement below). *)

Lemma prefix_mask_length : forall w plen, List.length (prefix_mask w plen) = w.
Proof. intros w plen. unfold prefix_mask. rewrite length_map, length_seq. reflexivity. Qed.

Lemma prefix_mask_cons : forall w plen,
  prefix_mask (S w) plen = mask_byte plen :: prefix_mask w (plen - 8).
Proof.
  intros w plen. unfold prefix_mask. cbn [seq map]. f_equal.
  - f_equal. lia.
  - rewrite <- seq_shift, map_map. apply map_ext_in. intros i _. f_equal. lia.
Qed.

Lemma prefix_mask_wfb : forall w plen, bytes_wfb (prefix_mask w plen) = true.
Proof.
  intros w plen. apply bytes_wfb_Forall, Forall_forall.
  intros x Hx. unfold prefix_mask in Hx. apply in_map_iff in Hx as (i & <- & _).
  unfold mask_byte. assert (Nat.pow 2 (8 - Nat.min (plen - 8*i) 8) <= 256)%nat.
  { transitivity (Nat.pow 2 8); [apply Nat.pow_le_mono_r; lia | cbn; lia]. }
  assert (1 <= Nat.pow 2 (8 - Nat.min (plen - 8*i) 8))%nat
    by (change 1%nat with (Nat.pow 2 0); apply Nat.pow_le_mono_r; lia). lia.
Qed.

Lemma data_and_length : forall a m, List.length m = List.length a ->
  List.length (data_and a m) = List.length a.
Proof.
  intros a m H. unfold data_and. apply data_bitops_length_eq;
    [exact H | rewrite repeat_length; reflexivity].
Qed.

Lemma data_and_wfb : forall a m, List.length m = List.length a ->
  bytes_wfb a = true -> bytes_wfb m = true -> bytes_wfb (data_and a m) = true.
Proof.
  intros a m Hl Ha Hm. unfold data_and. apply data_bitops_wfb;
    [exact Hl | rewrite repeat_length; reflexivity | exact Ha | exact Hm
     | apply repeat_wfb; lia].
Qed.

Lemma data_to_N_data_and : forall a m, List.length m = List.length a ->
  bytes_wfb a = true -> bytes_wfb m = true ->
  data_to_N (data_and a m) = N.land (data_to_N a) (data_to_N m).
Proof.
  intros a m Hl Ha Hm. unfold data_and.
  rewrite data_to_N_bitops;
    [ | exact Hl | rewrite repeat_length; reflexivity | exact Ha | exact Hm
      | apply repeat_wfb; lia].
  rewrite data_to_N_repeat0, N.lxor_0_r. reflexivity.
Qed.

Lemma data_to_N_data_or : forall a b, List.length b = List.length a ->
  bytes_wfb a = true -> bytes_wfb b = true ->
  data_to_N (data_or a b) = N.lor (data_to_N a) (data_to_N b).
Proof.
  intros a b Hl Ha Hb. unfold data_or.
  rewrite data_to_N_bitops;
    [ | rewrite data_not_length; exact Hl | exact Hl | exact Ha
      | apply data_not_wfb; exact Hb | exact Hb ].
  rewrite data_to_N_data_not by exact Hb.
  set (K := (8 * N.of_nat (List.length a))%N).
  assert (Hbb : (256 ^ N.of_nat (List.length b))%N = (2 ^ K)%N)
    by (unfold K; rewrite Hl, pow256_pow2; reflexivity).
  rewrite Hbb.
  assert (HaB : (data_to_N a < 2 ^ K)%N)
    by (unfold K; rewrite <- pow256_pow2; apply data_to_N_bound; exact Ha).
  assert (HbB : (data_to_N b < 2 ^ K)%N)
    by (unfold K; rewrite <- pow256_pow2, <- Hl; apply data_to_N_bound; exact Hb).
  apply land_not_xor_is_or; assumption.
Qed.

(** The numeric value of a prefix mask: the top [plen] bits set of a [w]-byte
    big-endian word — i.e. [2^(8w) - 2^(8w-plen)]. *)
Lemma prefix_mask_val : forall w plen, (plen <= 8 * w)%nat ->
  data_to_N (prefix_mask w plen)
  = (2 ^ (8 * N.of_nat w) - 2 ^ (8 * N.of_nat w - N.of_nat plen))%N.
Proof.
  induction w as [|w IH]; intros plen Hle.
  - assert (plen = 0)%nat by lia. subst. reflexivity.
  - rewrite prefix_mask_cons, data_to_N_cons, prefix_mask_length.
    rewrite (IH (plen - 8) ltac:(lia)).
    rewrite Nat2N.inj_succ.
    replace (8 * N.succ (N.of_nat w))%N with (8 * N.of_nat w + 8)%N by lia.
    rewrite pow256_pow2.
    set (E := (8 * N.of_nat w)%N).
    assert (Hpow8 : (2 ^ (E + 8) = 2 ^ E * 256)%N)
      by (rewrite N.pow_add_r; reflexivity).
    destruct (Nat.ltb plen 8) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      assert (Hmb : N.of_nat (mask_byte plen)
                    = (256 - 2 ^ (8 - N.of_nat plen))%N).
      { unfold mask_byte.
        rewrite Nat.min_l by lia.
        rewrite Nat2N.inj_sub, Nat2N.inj_pow, Nat2N.inj_sub. reflexivity. }
      rewrite Hmb.
      replace (plen - 8)%nat with 0%nat by lia. cbn [N.of_nat].
      rewrite N.sub_0_r, N.sub_diag.
      replace (E + 8 - N.of_nat plen)%N with (E + (8 - N.of_nat plen))%N by lia.
      rewrite Hpow8, N.pow_add_r.
      assert (H8 : (2 ^ (8 - N.of_nat plen) <= 256)%N).
      { replace 256%N with (2 ^ 8)%N by reflexivity. apply N.pow_le_mono_r; lia. }
      nia.
    + apply Nat.ltb_ge in Hlt.
      assert (Hmb : N.of_nat (mask_byte plen) = 255%N).
      { unfold mask_byte. rewrite Nat.min_r by lia.
        replace (8 - 8)%nat with 0%nat by lia. reflexivity. }
      rewrite Hmb.
      replace (E - N.of_nat (plen - 8))%N with (E + 8 - N.of_nat plen)%N
        by (rewrite Nat2N.inj_sub; unfold E; lia).
      rewrite Hpow8.
      assert (Hle2 : (2 ^ (E + 8 - N.of_nat plen) <= 2 ^ E)%N).
      { apply N.pow_le_mono_r; lia. }
      set (X := (2 ^ (E + 8 - N.of_nat plen))%N) in *.
      set (Y := (2 ^ E)%N) in *. lia.
Qed.

(** A prefix mask ANDs a [w]-byte value down to its top [plen] bits (the low
    [8w-plen] bits cleared): [land x mask = (x >> k) << k], [k = 8w-plen]. *)
Lemma land_prefix_mask : forall w plen x, (plen <= 8 * w)%nat ->
  (x < 2 ^ (8 * N.of_nat w))%N ->
  N.land x (data_to_N (prefix_mask w plen))
  = N.shiftl (N.shiftr x (N.of_nat (8 * w - plen))) (N.of_nat (8 * w - plen)).
Proof.
  intros w plen x Hle Hx.
  rewrite prefix_mask_val by exact Hle.
  set (K := N.of_nat (8 * w - plen)).
  assert (HK : K = (8 * N.of_nat w - N.of_nat plen)%N)
    by (unfold K; rewrite Nat2N.inj_sub; lia).
  assert (HP : (N.of_nat plen + K = 8 * N.of_nat w)%N) by (rewrite HK; lia).
  assert (Hmask : (2 ^ (8 * N.of_nat w) - 2 ^ (8 * N.of_nat w - N.of_nat plen))%N
                  = N.shiftl (N.ones (N.of_nat plen)) K).
  { rewrite N.shiftl_mul_pow2, N.ones_equiv, <- N.sub_1_r.
    rewrite N.mul_sub_distr_r, N.mul_1_l, <- N.pow_add_r, HP, <- HK. reflexivity. }
  rewrite Hmask, land_shiftl_mask.
  rewrite N.land_ones.
  rewrite N.shiftr_div_pow2.
  assert (Hlt : (x / 2 ^ K < 2 ^ N.of_nat plen)%N).
  { apply N.div_lt_upper_bound; [apply N.pow_nonzero; lia|].
    rewrite <- N.pow_add_r.
    replace (K + N.of_nat plen)%N with (8 * N.of_nat w)%N by lia. exact Hx. }
  rewrite N.mod_small by exact Hlt. reflexivity.
Qed.

(** The bytewise complement of a prefix mask is the low [8w-plen] bits set:
    [~mask = 2^(8w-plen) - 1] (the broadcast host part). *)
Lemma data_not_prefix_mask : forall w plen, (plen <= 8 * w)%nat ->
  data_to_N (Typed.data_not (prefix_mask w plen))
  = (2 ^ N.of_nat (8 * w - plen) - 1)%N.
Proof.
  intros w plen Hle.
  rewrite data_to_N_data_not by apply prefix_mask_wfb.
  rewrite prefix_mask_length, pow256_pow2.
  rewrite prefix_mask_val by exact Hle.
  set (K := N.of_nat (8 * w - plen)).
  assert (HKn : K = (8 * N.of_nat w - N.of_nat plen)%N)
    by (unfold K; rewrite Nat2N.inj_sub; lia).
  set (M := (2 ^ (8 * N.of_nat w) - 2 ^ (8 * N.of_nat w - N.of_nat plen))%N).
  assert (Hdisj : N.land M (2 ^ K - 1) = 0%N).
  { unfold M. rewrite <- HKn.
    apply N.bits_inj_iff. intro i. rewrite N.land_spec, N.bits_0.
    destruct (N.lt_ge_cases i K) as [Hi|Hi].
    - replace (2 ^ (8 * N.of_nat w) - 2 ^ K)%N
        with (N.shiftl (2 ^ (8 * N.of_nat w - K) - 1) K).
      2:{ rewrite N.shiftl_mul_pow2, N.mul_sub_distr_r, N.mul_1_l, <- N.pow_add_r.
          replace (8 * N.of_nat w - K + K)%N with (8 * N.of_nat w)%N
            by (rewrite HKn; lia). reflexivity. }
      rewrite N.shiftl_spec_low by lia. reflexivity.
    - rewrite N.sub_1_r, <- N.ones_equiv, N.ones_spec_high by lia. apply andb_false_r. }
  assert (Hsum : (2 ^ (8 * N.of_nat w) - 1)%N = N.lxor M (2 ^ K - 1)).
  { rewrite <- (N.add_nocarry_lxor _ _ Hdisj). unfold M. rewrite <- HKn.
    assert (0 < 2 ^ K)%N by (apply N.neq_0_lt_0, N.pow_nonzero; lia).
    assert (2 ^ K <= 2 ^ (8 * N.of_nat w))%N
      by (apply N.pow_le_mono_r; [lia | rewrite HKn; lia]). lia. }
  fold M. rewrite Hsum, <- N.lxor_assoc, N.lxor_nilpotent, N.lxor_0_l. reflexivity.
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

(** Typed equality / inequality: the register decodes — at the VALUE's
    byteorder — to the value's number exactly when the byte compare against
    its register encoding succeeds (the host-endian case reduces to the
    big-endian one by reversal on both sides).  These SUPERSEDE the retired
    [Elab.elab_matchcond_correct] consistency check with genuine
    decode-vs-encode obligations. *)

(** The shared compare core of the eq / neq shapes. *)
Lemma read_val_cmp_num : forall f v e p x,
  val_wfb v = true ->
  read_val_N v (field_value f e p) = Some x ->
  eval_cmp CEq (field_value f e p) (Nftval.encode v) = (x =? val_N v)%N.
Proof.
  intros f v e p x Hwfv HR. unfold read_val_N in HR.
  set (fv := field_value f e p) in *.
  destruct (host_val v) eqn:Hh.
  - (* host-endian: both compare sides reverse *)
    apply read_be_N_inv in HR as (Hlen & Hwf & ->).
    rewrite length_rev in Hlen.
    cbn [eval_cmp].
    rewrite val_width_encode, <- Hlen, firstn_all.
    rewrite (encode_host_rev v Hh).
    rewrite <- (rev_involutive fv) at 1.
    rewrite data_eqb_rev.
    rewrite data_eqb_num;
      [ | rewrite encode_be_len, length_rev; congruence
        | exact Hwf
        | apply encode_be_wfb; exact Hwfv ].
    rewrite encode_be_num by exact Hwfv. reflexivity.
  - (* big-endian: the direct numeric compare *)
    apply read_be_N_inv in HR as (Hlen & Hwf & ->).
    cbn [eval_cmp].
    rewrite val_width_encode, <- Hlen, firstn_all.
    rewrite data_eqb_num;
      [ | rewrite val_width_encode; congruence
        | exact Hwf
        | apply encode_wfb; exact Hwfv ].
    rewrite encode_num_be by assumption. reflexivity.
Qed.

Theorem eq_erasure : forall f v e p b,
  eval_txm (TXEq f v) e p = Some b ->
  eval_matchcond (elab_tx (TXEq f v)) e p = b.
Proof.
  intros f v e p b Hev.
  cbn [eval_txm] in Hev. cbn [elab_tx].
  destruct (field_loadable f p) eqn:HL; cbn [negb] in Hev.
  2:{ injection Hev as <-.
      unfold eval_matchcond. cbn [match_loadable]. rewrite HL. reflexivity. }
  destruct (val_wfb v) eqn:Hwfv; cbn [negb] in Hev; [|discriminate].
  destruct (read_val_N v (field_value f e p)) as [x|] eqn:HR; [|discriminate].
  injection Hev as <-.
  unfold eval_matchcond. cbn [match_loadable]. rewrite HL.
  cbn [eval_matchcond_body andb].
  apply read_val_cmp_num; assumption.
Qed.

Theorem neq_erasure : forall f v e p b,
  eval_txm (TXNeq f v) e p = Some b ->
  eval_matchcond (elab_tx (TXNeq f v)) e p = b.
Proof.
  intros f v e p b Hev.
  cbn [eval_txm] in Hev. cbn [elab_tx].
  destruct (field_loadable f p) eqn:HL; cbn [negb] in Hev.
  2:{ injection Hev as <-.
      unfold eval_matchcond. cbn [match_loadable]. rewrite HL. reflexivity. }
  destruct (val_wfb v) eqn:Hwfv; cbn [negb] in Hev; [|discriminate].
  destruct (read_val_N v (field_value f e p)) as [x|] eqn:HR; [|discriminate].
  injection Hev as <-.
  unfold eval_matchcond. cbn [match_loadable]. rewrite HL.
  cbn [eval_matchcond_body andb].
  change (eval_cmp CNe ?a ?b) with (negb (eval_cmp CEq a b)).
  rewrite (read_val_cmp_num f v e p x Hwfv HR). reflexivity.
Qed.

(** Wildcards: the field's LEADING bytes are the prefix — the leading bytes
    of a big-endian word are its high-order bits ([read_lead_N]'s right
    shift), so the short byte compare is the numeric compare of the shifted
    register against the prefix value. *)
Theorem wildcard_erasure : forall f pre e p b,
  eval_txm (TXWildcard f pre) e p = Some b ->
  eval_matchcond (elab_tx (TXWildcard f pre)) e p = b.
Proof.
  intros f pre e p b Hev.
  cbn [eval_txm] in Hev. cbn [elab_tx].
  destruct (field_loadable f p) eqn:HL; cbn [negb] in Hev.
  2:{ injection Hev as <-.
      unfold eval_matchcond. cbn [match_loadable]. rewrite HL. reflexivity. }
  destruct (bytes_wfb pre) eqn:Hwp; cbn [negb] in Hev; [|discriminate].
  destruct (read_lead_N (List.length pre) (field_value f e p)) as [x|] eqn:HR;
    [|discriminate].
  injection Hev as <-.
  apply read_lead_N_inv in HR as (Hk & Hwf & ->).
  set (fv := field_value f e p) in *.
  unfold eval_matchcond. cbn [match_loadable]. rewrite HL.
  cbn [eval_matchcond_body andb].
  cbn [eval_cmp].
  rewrite data_eqb_num;
    [ reflexivity
    | rewrite firstn_length_le by exact Hk; reflexivity
    | apply bytes_wfb_firstn; exact Hwf
    | exact Hwp ].
Qed.

(** CIDR prefixes: the verified expansion — BOTH branches: nft's
    byte-aligned truncated-load shortening AND the full-width masked
    compare — tests exactly "the top [plen] bits agree"; a masked top-bits
    compare is numerically a right-shift compare of both sides
    ([land_prefix_mask] + [shiftl_eqb_cancel]). *)

(** The full-width masked branch. *)
Lemma prefix_full_erasure : forall f (neg : bool) v plen e p b,
  val_wfb v = true -> host_val v = false ->
  (plen <= 8 * val_width v)%nat ->
  prefix_full_N f neg v plen e p = Some b ->
  eval_matchcond
    (MMasked f (if neg then CNe else CEq)
       (prefix_mask (val_width v) plen)
       (repeat 0 (val_width v))
       (data_and (Nftval.encode v) (prefix_mask (val_width v) plen))) e p = b.
Proof.
  intros f neg v plen e p b Hwfv Hnh Hple Hev.
  unfold prefix_full_N in Hev.
  destruct (field_loadable f p) eqn:HL; cbn [negb] in Hev.
  2:{ injection Hev as <-.
      unfold eval_matchcond. destruct neg; cbn [match_loadable];
        rewrite HL; reflexivity. }
  destruct (read_be_N (val_width v) (field_value f e p)) as [x|] eqn:HR;
    [|discriminate].
  injection Hev as <-.
  apply read_be_N_inv in HR as (Hlen & Hwf & ->).
  set (fv := field_value f e p) in *.
  set (ev := Nftval.encode v) in *.
  assert (Hew : List.length ev = val_width v) by apply val_width_encode.
  set (w := val_width v) in *.
  set (mask := prefix_mask w plen) in *.
  set (net := data_and ev mask) in *.
  assert (Hml : List.length mask = w) by apply prefix_mask_length.
  assert (Hmw : bytes_wfb mask = true) by apply prefix_mask_wfb.
  assert (Hwev : bytes_wfb ev = true) by (apply encode_wfb; exact Hwfv).
  assert (Hnl : List.length net = w)
    by (unfold net; rewrite data_and_length by congruence; congruence).
  assert (Hnw : bytes_wfb net = true)
    by (unfold net; apply data_and_wfb; [congruence | exact Hwev | exact Hmw]).
  assert (Hxb : (data_to_N fv < 2 ^ (8 * N.of_nat w))%N)
    by (rewrite <- pow256_pow2, <- Hlen; apply data_to_N_bound; exact Hwf).
  assert (Heb : (data_to_N ev < 2 ^ (8 * N.of_nat w))%N)
    by (rewrite <- pow256_pow2, <- Hew; apply data_to_N_bound; exact Hwev).
  unfold eval_matchcond. destruct neg; cbn [match_loadable]; rewrite HL;
    cbn [eval_matchcond_body andb]; fold fv.
  - change (eval_cmp CNe ?a ?b) with (negb (eval_cmp CEq a b)).
    rewrite eval_cmp_eq_num;
      [ | rewrite data_bitops_length_eq
            by (rewrite ?repeat_length; congruence); congruence
        | apply data_bitops_wfb;
          [ congruence | rewrite repeat_length; congruence | exact Hwf
            | exact Hmw | apply repeat_wfb; lia ]
        | exact Hnw ].
    rewrite data_to_N_bitops;
      [ | congruence | rewrite repeat_length; congruence | exact Hwf
        | exact Hmw | apply repeat_wfb; lia ].
    rewrite data_to_N_repeat0, N.lxor_0_r.
    unfold net. rewrite data_to_N_data_and
      by (congruence || assumption).
    unfold mask. rewrite !land_prefix_mask by assumption.
    rewrite shiftl_eqb_cancel.
    unfold ev. rewrite encode_num_be by assumption.
    reflexivity.
  - rewrite eval_cmp_eq_num;
      [ | rewrite data_bitops_length_eq
            by (rewrite ?repeat_length; congruence); congruence
        | apply data_bitops_wfb;
          [ congruence | rewrite repeat_length; congruence | exact Hwf
            | exact Hmw | apply repeat_wfb; lia ]
        | exact Hnw ].
    rewrite data_to_N_bitops;
      [ | congruence | rewrite repeat_length; congruence | exact Hwf
        | exact Hmw | apply repeat_wfb; lia ].
    rewrite data_to_N_repeat0, N.lxor_0_r.
    unfold net. rewrite data_to_N_data_and
      by (congruence || assumption).
    unfold mask. rewrite !land_prefix_mask by assumption.
    rewrite shiftl_eqb_cancel.
    unfold ev. rewrite encode_num_be by assumption.
    reflexivity.
Qed.

(** The byte-aligned truncated-load branch: the elaborated form loads and
    compares just the prefix bytes of [f']; the compared immediate — the
    leading [k] bytes of the masked network address — is numerically the
    value's top [plen] bits. *)
Lemma prefix_short_erasure : forall f' (neg : bool) v plen k e p b,
  val_wfb v = true -> host_val v = false ->
  plen = (8 * k)%nat -> (k <= val_width v)%nat ->
  (if negb (field_loadable f' p) then Some false else
   match read_lead_N k (field_value f' e p) with
   | Some x => Some (xorb neg (x =? N.shiftr (val_N v)
                                     (N.of_nat (8 * val_width v - plen)))%N)
   | None => None
   end) = Some b ->
  eval_matchcond
    (if neg
     then MNeq f' (firstn k (data_and (Nftval.encode v)
                     (prefix_mask (val_width v) plen)))
     else MEq f' (firstn k (data_and (Nftval.encode v)
                     (prefix_mask (val_width v) plen)))) e p = b.
Proof.
  intros f' neg v plen k e p b Hwfv Hnh Hpk Hkw Hev.
  destruct (field_loadable f' p) eqn:HL; cbn [negb] in Hev.
  2:{ injection Hev as <-.
      unfold eval_matchcond. destruct neg; cbn [match_loadable];
        rewrite HL; reflexivity. }
  destruct (read_lead_N k (field_value f' e p)) as [x|] eqn:HR; [|discriminate].
  injection Hev as <-.
  apply read_lead_N_inv in HR as (Hk & Hwf & ->).
  set (fv := field_value f' e p) in *.
  set (ev := Nftval.encode v) in *.
  assert (Hew : List.length ev = val_width v) by apply val_width_encode.
  set (w := val_width v) in *.
  set (mask := prefix_mask w plen) in *.
  set (net := data_and ev mask) in *.
  assert (Hml : List.length mask = w) by apply prefix_mask_length.
  assert (Hmw : bytes_wfb mask = true) by apply prefix_mask_wfb.
  assert (Hwev : bytes_wfb ev = true) by (apply encode_wfb; exact Hwfv).
  assert (Hnl : List.length net = w)
    by (unfold net; rewrite data_and_length by congruence; congruence).
  assert (Hnw : bytes_wfb net = true)
    by (unfold net; apply data_and_wfb; [congruence | exact Hwev | exact Hmw]).
  assert (Heb : (data_to_N ev < 2 ^ (8 * N.of_nat w))%N)
    by (rewrite <- pow256_pow2, <- Hew; apply data_to_N_bound; exact Hwev).
  assert (Hple : (plen <= 8 * w)%nat) by lia.
  (* the shared CEq core *)
  assert (Hcore : eval_cmp CEq fv (firstn k net)
                  = (data_to_N (firstn k fv)
                     =? N.shiftr (val_N v) (N.of_nat (8 * w - plen)))%N).
  { cbn [eval_cmp].
    rewrite firstn_length_le by lia.
    rewrite data_eqb_num;
      [ | rewrite !firstn_length_le by lia; reflexivity
        | apply bytes_wfb_firstn; exact Hwf
        | apply bytes_wfb_firstn; exact Hnw ].
    assert (Hwbs : bytes_wfb (skipn k net) = true).
    { pose proof Hnw as Hnw'.
      rewrite <- (firstn_skipn k net), bytes_wfb_app in Hnw'.
      apply andb_prop in Hnw' as [_ Hs]. exact Hs. }
    assert (Hnetk : data_to_N (firstn k net)
                    = N.shiftr (data_to_N net) (8 * N.of_nat (w - k))).
    { replace (w - k)%nat with (List.length (skipn k net))
        by (rewrite length_skipn; lia).
      rewrite <- (firstn_skipn k net) at 2.
      symmetry. apply data_to_N_app_shiftr. exact Hwbs. }
    rewrite Hnetk.
    unfold net. rewrite data_to_N_data_and by (congruence || assumption).
    unfold mask. rewrite land_prefix_mask by assumption.
    assert (HKM : (8 * N.of_nat (w - k))%N = N.of_nat (8 * w - plen)) by lia.
    rewrite HKM.
    rewrite N.shiftr_shiftl_l by lia.
    rewrite N.sub_diag, N.shiftl_0_r.
    unfold ev. rewrite encode_num_be by assumption.
    reflexivity. }
  destruct neg; unfold eval_matchcond; cbn [match_loadable]; rewrite HL;
    cbn [eval_matchcond_body andb]; fold fv.
  - change (eval_cmp CNe ?a ?b) with (negb (eval_cmp CEq a b)).
    rewrite Hcore. reflexivity.
  - rewrite Hcore. reflexivity.
Qed.

Theorem prefix_erasure : forall f op v plen e p b,
  eval_txm (TXPrefix f op v plen) e p = Some b ->
  eval_matchcond (elab_tx (TXPrefix f op v plen)) e p = b.
Proof.
  intros f op v plen e p b Hev.
  cbn [eval_txm] in Hev. cbn [elab_tx].
  destruct (val_wfb v && negb (host_val v) && (plen <=? 8 * val_width v)%nat)
    eqn:HC; cbn [negb] in Hev; [|discriminate].
  apply andb_prop in HC as [HC1 Hple]. apply andb_prop in HC1 as [Hwfv Hnh].
  apply negb_true_iff in Hnh. apply Nat.leb_le in Hple.
  destruct op; try discriminate;
  cbv beta iota zeta in Hev;
  cbv beta iota zeta delta [prefix_expand];
  rewrite !(val_width_encode v).
  - (* CEq *)
    destruct ((0 <? plen)%nat && (plen <? 8 * val_width v)%nat
              && (Nat.modulo plen 8 =? 0)%nat) eqn:HA.
    + apply andb_prop in HA as [HA1 Hmod].
      apply andb_prop in HA1 as [Hpos Hlt].
      apply Nat.ltb_lt in Hpos, Hlt. apply Nat.eqb_eq in Hmod.
      assert (Hpk : plen = (8 * Nat.div plen 8)%nat).
      { rewrite (Nat.div_mod plen 8) at 1 by lia. lia. }
      destruct (payload_prefix_field f (Nat.div plen 8)) as [f'|] eqn:HF.
      * apply (prefix_short_erasure f' false v plen (Nat.div plen 8));
          try assumption; lia.
      * apply (prefix_full_erasure f false v plen); assumption.
    + apply (prefix_full_erasure f false v plen); assumption.
  - (* CNe *)
    destruct ((0 <? plen)%nat && (plen <? 8 * val_width v)%nat
              && (Nat.modulo plen 8 =? 0)%nat) eqn:HA.
    + apply andb_prop in HA as [HA1 Hmod].
      apply andb_prop in HA1 as [Hpos Hlt].
      apply Nat.ltb_lt in Hpos, Hlt. apply Nat.eqb_eq in Hmod.
      assert (Hpk : plen = (8 * Nat.div plen 8)%nat).
      { rewrite (Nat.div_mod plen 8) at 1 by lia. lia. }
      destruct (payload_prefix_field f (Nat.div plen 8)) as [f'|] eqn:HF.
      * apply (prefix_short_erasure f' true v plen (Nat.div plen 8));
          try assumption; lia.
      * apply (prefix_full_erasure f true v plen); assumption.
    + apply (prefix_full_erasure f true v plen); assumption.
Qed.

(** THE COMPOSED THEOREM (the M-D brick): whenever the typed numeric
    semantics yields a verdict, the elaborated byte IR computes the SAME
    verdict — for every typed scalar match shape. *)
Theorem txmatch_erasure : forall t e p b,
  eval_txm t e p = Some b ->
  eval_matchcond (elab_tx t) e p = b.
Proof.
  intros t e p b H.
  destruct t as [f v|f v|f op v plen|f pre|f dt neg lo hi|f dt op bits
                 |spec neg v|f dt bop neg mask v|f neg v].
  - apply eq_erasure; exact H.
  - apply neq_erasure; exact H.
  - apply prefix_erasure; exact H.
  - apply wildcard_erasure; exact H.
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

Example erasure_eq_exercised :
  eval_txm (TXEq FThDport (VPort 443)) tev_env tev_pkt4 = Some true
  /\ eval_matchcond (elab_tx (TXEq FThDport (VPort 443))) tev_env tev_pkt4
     = true.
Proof. vm_compute. split; reflexivity. Qed.

Example erasure_neq_exercised :
  eval_txm (TXNeq FThDport (VPort 22)) tev_env tev_pkt4 = Some true
  /\ eval_matchcond (elab_tx (TXNeq FThDport (VPort 22))) tev_env tev_pkt4
     = true.
Proof. vm_compute. split; reflexivity. Qed.

(** BOTH prefix_expand branches: /24 is the byte-aligned truncated load, /20
    the full-width masked compare — 192.168.100.7 is in both. *)
Example erasure_prefix_exercised :
  (eval_txm (TXPrefix FIp4Saddr CEq (VIpv4 [192;168;100;0]) 24)
     tev_env tev_pkt4 = Some true
   /\ eval_matchcond (elab_tx (TXPrefix FIp4Saddr CEq (VIpv4 [192;168;100;0]) 24))
        tev_env tev_pkt4 = true)
  /\ (eval_txm (TXPrefix FIp4Saddr CEq (VIpv4 [192;168;96;0]) 20)
        tev_env tev_pkt4 = Some true
      /\ eval_matchcond (elab_tx (TXPrefix FIp4Saddr CEq (VIpv4 [192;168;96;0]) 20))
           tev_env tev_pkt4 = true).
Proof. vm_compute. repeat split; reflexivity. Qed.

Example erasure_wildcard_exercised :
  eval_txm (TXWildcard FMetaIifname (sbytes "dummy")) tev_env tev_pkt4
    = Some true
  /\ eval_matchcond (elab_tx (TXWildcard FMetaIifname (sbytes "dummy")))
       tev_env tev_pkt4 = true.
Proof. vm_compute. split; reflexivity. Qed.

(* ================================================================== *)
(** ** M3: composite-immediate erasure — set / concat / CIDR.

    The set/map/vmap byte composition ([Lower.value_interval]/[cidr_interval]/
    [pad_slot]/[concat_padded]) agrees with the byte-level membership the VM
    runs, discharging genuine obligations:

      - [set_interval_erasure]: byte-level interval [set_mem] over ENCODED
        bounds equals the INDEPENDENT numeric membership over DECODED values —
        the byte-lexicographic-vs-numeric obligation ([data_le_num], M2);
      - [concat_key_erasure]: the slot-padded concatenation is FAITHFUL — the
        VM's split-and-truncate recovers each field's own bound, so
        concatenated-key membership is exactly the per-field cross product
        (the historical padding bug, proved by [split_by_recover] injectivity);
      - [cidr_interval_agrees_prefix_expand]: the CIDR net/broadcast interval
        and [prefix_expand]'s masked compare decide membership
        IDENTICALLY (one Coq expansion, the two-implementations tension gone). *)

(** *** Set-interval erasure (numeric = byte membership). *)

Theorem set_interval_erasure : forall (w : nat) (fv : data) (ivs : list (data * data)),
  List.length fv = w -> bytes_wfb fv = true ->
  Forall (fun iv => List.length (fst iv) = w /\ List.length (snd iv) = w
                    /\ bytes_wfb (fst iv) = true /\ bytes_wfb (snd iv) = true) ivs ->
  set_mem fv ivs = set_mem_N (data_to_N fv) ivs.
Proof.
  intros w fv ivs Hfv Hwf Hall.
  unfold set_mem, set_mem_N.
  induction ivs as [|[lo hi] ivs IH]; [reflexivity|].
  rewrite Forall_cons_iff in Hall. destruct Hall as [Hhd Htl].
  cbn [fst snd] in Hhd. destruct Hhd as (Hlo & Hhi & Hwlo & Hwhi).
  cbn [existsb]. rewrite IH by exact Htl. f_equal.
  unfold data_in_iv, iv_mem_N. cbn [fst snd].
  rewrite (data_le_num lo fv) by (try congruence; assumption).
  rewrite (data_le_num fv hi) by (try congruence; assumption).
  reflexivity.
Qed.

(** *** Concat-key erasure (slot padding is faithful). *)

Lemma reg_slot_ge : forall n, (n <= reg_slot n)%nat.
Proof.
  intro n. unfold reg_slot.
  pose proof (Nat.div_mod (n + 3) 4 ltac:(lia)) as Hd.
  pose proof (Nat.mod_upper_bound (n + 3) 4 ltac:(lia)) as Hm. lia.
Qed.

Lemma pad_slot_length : forall d, List.length (pad_slot d) = reg_slot (List.length d).
Proof.
  intro d. unfold pad_slot. rewrite length_app, repeat_length.
  pose proof (reg_slot_ge (List.length d)). lia.
Qed.

Lemma pad_slot_firstn : forall d n, n = List.length d -> firstn n (pad_slot d) = d.
Proof.
  intros d n ->. unfold pad_slot.
  rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. apply app_nil_r.
Qed.

(** One split-by step at a cons-cons width list (avoids over-unfolding the
    tail [split_by] into a [match] on the opaque remaining widths). *)
Lemma split_by_cons2 : forall (w0 w1 : nat) (ws : list nat) (d : data),
  split_by (w0 :: w1 :: ws) d = firstn w0 d :: split_by (w1 :: ws) (skipn w0 d).
Proof. reflexivity. Qed.

(** Splitting a concatenation by its chunks' own lengths recovers the chunks:
    the concatenated key is injective in its per-field pieces. *)
Lemma split_by_recover : forall (chunks : list data),
  chunks <> [] ->
  split_by (map (@List.length byte) chunks) (List.concat chunks) = chunks.
Proof.
  induction chunks as [|c cs IH]; [congruence|]. intros _.
  destruct cs as [|c2 cs'].
  - cbn [map List.concat split_by]. rewrite app_nil_r. reflexivity.
  - change (map (@List.length byte) (c :: c2 :: cs'))
      with (List.length c :: List.length c2 :: map (@List.length byte) cs').
    change (List.concat (c :: c2 :: cs'))
      with (c ++ List.concat (c2 :: cs'))%list.
    rewrite split_by_cons2.
    rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite skipn_app, skipn_all, Nat.sub_diag, skipn_O, app_nil_l.
    change (List.length c2 :: map (@List.length byte) cs')
      with (map (@List.length byte) (c2 :: cs')).
    rewrite IH by discriminate. reflexivity.
Qed.

(** The per-field test after split-and-truncate discards the padding exactly. *)
Lemma concat_split_forallb : forall vals los his,
  Forall2 (fun v lo => List.length lo = List.length v) vals los ->
  Forall2 (fun v hi => List.length hi = List.length v) vals his ->
  forallb (fun t => let '(val, (lo, hi)) := t in
             field_in_iv val (firstn (List.length val) lo, firstn (List.length val) hi))
          (combine vals (combine (map pad_slot los) (map pad_slot his)))
  = forallb (fun t => let '(val, (lo, hi)) := t in field_in_iv val (lo, hi))
          (combine vals (combine los his)).
Proof.
  intros vals los his Hlos. revert his.
  induction Hlos as [|v lo vals los Hvlo Hlos IH]; intros his Hhis.
  - reflexivity.
  - inversion Hhis as [|v' hi vals' his' Hvhi Hhis']; subst.
    cbn [map combine forallb].
    rewrite (pad_slot_firstn lo (List.length v)) by (symmetry; exact Hvlo).
    rewrite (pad_slot_firstn hi (List.length v)) by (symmetry; exact Hvhi).
    rewrite IH by exact Hhis'. reflexivity.
Qed.

(** The per-field register-slot widths equal the padded chunks' lengths. *)
Lemma slot_widths_eq : forall vals los,
  Forall2 (fun v lo => List.length lo = List.length v) vals los ->
  map (fun v : data => reg_slot (List.length v)) vals
  = map (@List.length byte) (map pad_slot los).
Proof.
  intros vals los H. rewrite map_map.
  induction H as [|v lo vals los Hvlo H IH]; [reflexivity|].
  cbn [map]. rewrite pad_slot_length, Hvlo. f_equal. exact IH.
Qed.

(** Splitting the slot-padded concatenation by the PER-FIELD slot widths
    recovers each field's padded chunk. *)
Lemma split_by_slots : forall vals los,
  Forall2 (fun v lo => List.length lo = List.length v) vals los -> los <> [] ->
  split_by (map (fun v : data => reg_slot (List.length v)) vals)
           (List.concat (map pad_slot los))
  = map pad_slot los.
Proof.
  intros vals los H Hne.
  rewrite (slot_widths_eq _ _ H). apply split_by_recover.
  destruct los; [congruence | cbn [map]; discriminate].
Qed.

(** The cons-cons unfolding of [concat_in_iv] (its non-single-field branch),
    stated as a rewrite so [cbn] does not also fire [map]/[split_by]. *)
Lemma concat_in_iv_cons2 : forall a b rest lo hi,
  concat_in_iv (a :: b :: rest) (lo, hi)
  = forallb (fun t => let '(val, (l, h)) := t in
       field_in_iv val (firstn (List.length val) l, firstn (List.length val) h))
     (combine (a :: b :: rest)
        (combine (split_by (map (fun v : data => reg_slot (List.length v))
                                (a :: b :: rest)) lo)
                 (split_by (map (fun v : data => reg_slot (List.length v))
                                (a :: b :: rest)) hi))).
Proof. reflexivity. Qed.

Theorem concat_key_erasure : forall (vals los his : list data),
  (2 <= List.length vals)%nat ->
  Forall2 (fun v lo => List.length lo = List.length v) vals los ->
  Forall2 (fun v hi => List.length hi = List.length v) vals his ->
  concat_in_iv vals (List.concat (map pad_slot los), List.concat (map pad_slot his))
  = forallb (fun t => let '(val, (lo, hi)) := t in field_in_iv val (lo, hi))
            (combine vals (combine los his)).
Proof.
  intros vals los his Hlen Hlos Hhis.
  destruct vals as [|a [|b rest]]; cbn [List.length] in Hlen; try lia.
  assert (Hlos_ne : los <> [])
    by (destruct los; [inversion Hlos | discriminate]).
  assert (Hhis_ne : his <> [])
    by (destruct his; [inversion Hhis | discriminate]).
  rewrite concat_in_iv_cons2.
  rewrite (split_by_slots _ _ Hlos Hlos_ne), (split_by_slots _ _ Hhis Hhis_ne).
  apply concat_split_forallb; assumption.
Qed.

(** *** CIDR interval vs masked-prefix compare agreement. *)


Theorem cidr_interval_agrees_prefix_expand : forall (v : nftval) (plen : nat) (fv : data),
  (plen <= 8 * List.length (Nftval.encode v))%nat ->
  List.length fv = List.length (Nftval.encode v) ->
  bytes_wfb (Nftval.encode v) = true ->
  bytes_wfb fv = true ->
  data_in_iv fv (cidr_interval v plen)
  = data_eqb (data_and fv (prefix_mask (List.length (Nftval.encode v)) plen))
             (fst (cidr_interval v plen)).
Proof.
  intros v plen fv Hle Hlen Hev Hfv.
  set (ev := Nftval.encode v) in *.
  set (w := List.length ev) in *.
  set (mask := prefix_mask w plen) in *.
  set (net := data_and ev mask) in *.
  set (K := N.of_nat (8 * w - plen)) in *.
  (* length / wf bookkeeping *)
  assert (Hml : List.length mask = w) by (unfold mask; apply prefix_mask_length).
  assert (Hmw : bytes_wfb mask = true) by (unfold mask; apply prefix_mask_wfb).
  assert (Hnl : List.length net = w)
    by (unfold net; rewrite data_and_length; [reflexivity | rewrite Hml; reflexivity]).
  assert (Hnw : bytes_wfb net = true)
    by (unfold net; apply data_and_wfb; [rewrite Hml; reflexivity | exact Hev | exact Hmw]).
  assert (Hnotl : List.length (Typed.data_not mask) = w)
    by (rewrite data_not_length; exact Hml).
  assert (Hnotw : bytes_wfb (Typed.data_not mask) = true)
    by (apply data_not_wfb; exact Hmw).
  assert (Hbl : List.length (data_or net (Typed.data_not mask)) = w).
  { unfold data_or. rewrite data_bitops_length_eq.
    - exact Hnl.
    - rewrite !data_not_length. congruence.
    - rewrite data_not_length. congruence. }
  assert (Hbw : bytes_wfb (data_or net (Typed.data_not mask)) = true).
  { unfold data_or. apply data_bitops_wfb.
    - rewrite !data_not_length. congruence.
    - rewrite data_not_length. congruence.
    - exact Hnw.
    - apply data_not_wfb; exact Hnotw.
    - exact Hnotw. }
  (* numeric values *)
  set (Wn := N.of_nat w).
  assert (Hxbound : (data_to_N fv < 2 ^ (8 * Wn))%N)
    by (unfold Wn; rewrite <- pow256_pow2, <- Hlen; apply data_to_N_bound; exact Hfv).
  assert (Hebound : (data_to_N ev < 2 ^ (8 * Wn))%N)
    by (unfold Wn; rewrite <- pow256_pow2; apply data_to_N_bound; exact Hev).
  assert (Hnetv : data_to_N net = N.shiftl (N.shiftr (data_to_N ev) K) K).
  { unfold net. rewrite data_to_N_data_and by
      (try (rewrite Hml; reflexivity); assumption).
    unfold K. apply land_prefix_mask; assumption. }
  (* LHS: data_in_iv fv (net, bcast) via numeric order *)
  unfold data_in_iv, cidr_interval. fold ev w mask net.
  cbn [fst snd].
  rewrite (data_le_num net fv) by (try congruence; assumption).
  rewrite (data_le_num fv (data_or net (Typed.data_not mask)))
    by (try congruence; assumption).
  (* RHS: data_and fv mask =? net, numerically *)
  rewrite (data_eqb_num (data_and fv mask) net)
    by (try (rewrite data_and_length; [congruence | rewrite Hml; congruence]);
        try (apply data_and_wfb; [rewrite Hml; congruence | exact Hfv | exact Hmw]);
        exact Hnw).
  rewrite (data_to_N_data_and fv mask) by
    (try (rewrite Hml; congruence); assumption).
  (* bcast numeric value *)
  assert (Hbv : data_to_N (data_or net (Typed.data_not mask))
                = (N.shiftl (N.shiftr (data_to_N ev) K) K + (2 ^ K - 1))%N).
  { rewrite data_to_N_data_or by (try (rewrite Hnotl; congruence); assumption).
    rewrite Hnetv.
    assert (Hnotv : data_to_N (Typed.data_not mask) = (2 ^ K - 1)%N).
    { replace K with (N.of_nat (8 * w - plen)) by reflexivity.
      unfold mask. apply data_not_prefix_mask; exact Hle. }
    rewrite Hnotv.
    rewrite (shiftl_add_disjoint (N.shiftr (data_to_N ev) K) (2 ^ K - 1) K).
    2:{ assert (0 < 2 ^ K)%N by (apply N.neq_0_lt_0, N.pow_nonzero; lia). lia. }
    reflexivity. }
  rewrite Hbv, Hnetv.
  (* now purely numeric: A := ev>>K, B := fv>>K, everything as A*2^K, B*2^K *)
  replace (data_to_N mask) with (data_to_N (prefix_mask w plen)) by reflexivity.
  rewrite land_prefix_mask by assumption. fold K.
  set (A := N.shiftr (data_to_N ev) K).
  set (B := N.shiftr (data_to_N fv) K).
  rewrite !N.shiftl_mul_pow2.
  set (P := (2 ^ K)%N).
  assert (HPpos : (0 < P)%N) by (unfold P; apply N.neq_0_lt_0, N.pow_nonzero; lia).
  (* fv = B*P + r, r < P *)
  assert (Hfvdec : (data_to_N fv = B * P + data_to_N fv mod P)%N).
  { unfold B, P. rewrite N.shiftr_div_pow2. rewrite N.mul_comm.
    apply N.div_mod. lia. }
  assert (Hr : (data_to_N fv mod P < P)%N) by (apply N.mod_lt; lia).
  set (r := (data_to_N fv mod P)%N) in Hfvdec, Hr.
  assert (Hmul : forall a b, (a <= b)%N -> (a * P <= b * P)%N)
    by (intros a b Hab; apply N.mul_le_mono_r; exact Hab).
  (* the interval iff = A =? B, both bounds *)
  assert (Hlo : (A * P <=? data_to_N fv)%N = (A <=? B)%N).
  { destruct (A <=? B)%N eqn:E.
    - apply N.leb_le in E. apply N.leb_le. specialize (Hmul _ _ E).
      rewrite Hfvdec. lia.
    - apply N.leb_gt in E. apply N.leb_gt.
      specialize (Hmul (B + 1)%N A ltac:(lia)).
      rewrite N.mul_add_distr_r, N.mul_1_l in Hmul. rewrite Hfvdec. lia. }
  assert (Hhi : (data_to_N fv <=? A * P + (P - 1))%N = (B <=? A)%N).
  { destruct (B <=? A)%N eqn:E.
    - apply N.leb_le in E. apply N.leb_le. specialize (Hmul _ _ E).
      rewrite Hfvdec. lia.
    - apply N.leb_gt in E. apply N.leb_gt.
      specialize (Hmul (A + 1)%N B ltac:(lia)).
      rewrite N.mul_add_distr_r, N.mul_1_l in Hmul. rewrite Hfvdec. lia. }
  rewrite Hlo, Hhi.
  destruct (N.eqb (B * P) (A * P)) eqn:Emul.
  - apply N.eqb_eq in Emul.
    rewrite N.mul_cancel_r in Emul by lia.
    rewrite Emul, N.leb_refl. reflexivity.
  - apply N.eqb_neq in Emul.
    destruct (A <=? B)%N eqn:E1, (B <=? A)%N eqn:E2; cbn; try reflexivity.
    apply N.leb_le in E1, E2. exfalso. apply Emul.
    assert (A = B) by lia. congruence.
Qed.

(* ================================================================== *)
(** ** M3 non-vacuity: each theorem's hypotheses hold for concrete data and
    both sides compute the SAME (non-constant) verdict by vm_compute. *)

(** A port set `{ 22, 80-88 }`: 84 is IN (both sides true), 200 is OUT. *)
Example set_interval_exercised :
  let ivs := [([0;22],[0;22]); ([0;80],[0;88])] in
  (set_mem [0;84] ivs = set_mem_N (data_to_N [0;84]) ivs)
  /\ set_mem [0;84] ivs = true
  /\ (set_mem [0;200] ivs = set_mem_N (data_to_N [0;200]) ivs)
  /\ set_mem [0;200] ivs = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** A concat set `1.2.3.4 . 70-90` (ip4 . port): the padded 8-byte key
    membership = the per-field cross product; 1.2.3.4 . 80 is IN. *)
Example concat_key_exercised :
  let vals := [[1;2;3;4]; [0;80]] in
  let los := [[1;2;3;4]; [0;70]] in
  let his := [[1;2;3;4]; [0;90]] in
  (concat_in_iv vals (List.concat (map pad_slot los), List.concat (map pad_slot his))
   = forallb (fun t => let '(val, (lo, hi)) := t in field_in_iv val (lo, hi))
             (combine vals (combine los his)))
  /\ concat_in_iv vals (List.concat (map pad_slot los), List.concat (map pad_slot his))
     = true
  (* a DIFFERENT-slot value (port 100) is OUT — the padding did not smear
     across the ip4 slot *)
  /\ concat_in_iv [[1;2;3;4]; [0;100]]
       (List.concat (map pad_slot los), List.concat (map pad_slot his)) = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** `192.168.0.0/16`: 192.168.5.7 matches the masked prefix AND lies in the
    net..broadcast interval (both true); 10.0.0.0 matches neither (both false). *)
Example cidr_agree_exercised :
  let v := VIpv4 [192;168;0;0] in let plen := 16%nat in
  (data_in_iv [192;168;5;7] (cidr_interval v plen)
   = data_eqb (data_and [192;168;5;7] (prefix_mask 4 plen))
              (fst (cidr_interval v plen)))
  /\ data_in_iv [192;168;5;7] (cidr_interval v plen) = true
  /\ (data_in_iv [10;0;0;0] (cidr_interval v plen)
      = data_eqb (data_and [10;0;0;0] (prefix_mask 4 plen))
                 (fst (cidr_interval v plen)))
  /\ data_in_iv [10;0;0;0] (cidr_interval v plen) = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Axiom-freedom guards (informational; the enforcement point is
    `make axioms`). *)
Print Assumptions eq_erasure.
Print Assumptions neq_erasure.
Print Assumptions prefix_erasure.
Print Assumptions wildcard_erasure.
Print Assumptions range_erasure_be.
Print Assumptions range_erasure_host.
Print Assumptions bitmask_erasure.
Print Assumptions bitfield_erasure.
Print Assumptions bitwise_erasure.
Print Assumptions flag_erasure.
Print Assumptions txmatch_erasure.
Print Assumptions set_interval_erasure.
Print Assumptions concat_key_erasure.
Print Assumptions cidr_interval_agrees_prefix_expand.
