(** * The limiter over/invert bit flips the match verdict

    Real nftables limit / quota / connlimit each carry an "over" (invert) bit
    (NFT_LIMIT_F_INV / NFT_QUOTA_F_INV / NFT_CONNLIMIT_F_INV = bit 0 of the
    flags field).  The kernel XORs the under/not-exceeded test with that bit:
      nft_limit.c:48,52    return [invert] when tokens remain, [!invert] when
                           exhausted (caller BREAKs on a true return),
      nft_quota.c:43       [if (nft_overquota(...) ^ nft_quota_invert(priv)) BREAK],
      nft_connlimit.c:47   [if ((count > limit) ^ priv->invert) BREAK].

    Before the fix [eval_matchcond_body] used the SAME non-inverted form for all
    three and never inspected the flag, so an `over`/inverted limiter matched
    identically to the non-inverted form — the model PASSED the flood and
    DROPPED the conforming traffic, the exact opposite of the kernel.

    These theorems pin the corrected behaviour: for a FIXED oracle value, the
    `over` and non-`over` specs give OPPOSITE match verdicts (the negation of the
    red agent's "flag ignored" theorems, which are now unprovable). *)
From Stdlib Require Import List NArith Bool.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Semantics.

(* Specs differing ONLY in the over-bit (bit 0 of the flags field). *)
Definition q_under : quota_spec := {| q_bytes := 1000; q_consumed := 0; q_flags := 0 |}.
Definition q_over  : quota_spec := {| q_bytes := 1000; q_consumed := 0; q_flags := 1 |}.

Definition l_under : limit_spec :=
  {| ls_rate := 10; ls_unit := 0; ls_burst := 5; ls_bytes := false; ls_flags := 0 |}.
Definition l_over  : limit_spec :=
  {| ls_rate := 10; ls_unit := 0; ls_burst := 5; ls_bytes := false; ls_flags := 1 |}.

Definition c_under : connlimit_spec := {| cl_count := 5; cl_flags := 0 |}.
Definition c_over  : connlimit_spec := {| cl_count := 5; cl_flags := 1 |}.

(** For the SAME oracle reading, the over form matches iff the non-over form
    does NOT.  (Contrast the pre-fix [*_over_flag_ignored] theorems, which
    asserted EQUAL results — no longer provable.) *)

Theorem quota_over_flag_flips : forall p,
  e_quota (pkt_env p) q_under = e_quota (pkt_env p) q_over ->
  eval_matchcond_body (MQuota q_over) p
    = negb (eval_matchcond_body (MQuota q_under) p).
Proof.
  intros p H. cbn [eval_matchcond_body q_under q_over].
  rewrite H. cbn [Nat.land Nat.eqb].
  destruct (Nat.ltb 0 (e_quota (pkt_env p) q_over)); reflexivity.
Qed.

Theorem limit_over_flag_flips : forall p,
  e_limit (pkt_env p) l_under = e_limit (pkt_env p) l_over ->
  eval_matchcond_body (MLimit l_over) p
    = negb (eval_matchcond_body (MLimit l_under) p).
Proof.
  intros p H. cbn [eval_matchcond_body l_under l_over].
  rewrite H. cbn [Nat.land Nat.eqb].
  destruct (Nat.ltb 0 (e_limit (pkt_env p) l_over)); reflexivity.
Qed.

Theorem connlimit_over_flag_flips : forall p,
  e_connlimit (pkt_env p) c_under = e_connlimit (pkt_env p) c_over ->
  eval_matchcond_body (MConnlimit c_over) p
    = negb (eval_matchcond_body (MConnlimit c_under) p).
Proof.
  intros p H. cbn [eval_matchcond_body c_under c_over].
  rewrite H. cbn [Nat.land Nat.eqb].
  destruct (Nat.ltb 0 (e_connlimit (pkt_env p) c_over)); reflexivity.
Qed.

(** Concretely: when the resource is EXCEEDED (oracle remaining = 0), the
    non-over form does NOT match (kernel BREAKs the flood under a plain
    `quota X`) while the `over` form DOES (the `quota over X drop` idiom fires
    exactly on the traffic that exceeds the limit). *)
Theorem over_matches_when_exceeded : forall p,
  e_quota (pkt_env p) q_over = 0 ->
  eval_matchcond_body (MQuota q_over) p = true.
Proof.
  intros p H. cbn [eval_matchcond_body q_over]. rewrite H. reflexivity.
Qed.

Theorem nonover_misses_when_exceeded : forall p,
  e_quota (pkt_env p) q_under = 0 ->
  eval_matchcond_body (MQuota q_under) p = false.
Proof.
  intros p H. cbn [eval_matchcond_body q_under]. rewrite H. reflexivity.
Qed.
