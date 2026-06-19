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
From Stdlib Require Import List NArith Bool PeanoNat.
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
  (* the under-test [quota_under] depends only on the packet length and the
     remaining bytes (NOT the flag); q_under/q_over share q_bytes and (by H) the
     same remaining reading, so [quota_under] agrees and only the over-bit flips. *)
  assert (Hu : quota_under p q_over = quota_under p q_under).
  { unfold quota_under. rewrite H. reflexivity. }
  rewrite Hu. cbn [Nat.land Nat.eqb].
  destruct (quota_under p q_under); reflexivity.
Qed.

Theorem limit_over_flag_flips : forall p,
  e_limit (pkt_env p) l_under = e_limit (pkt_env p) l_over ->
  eval_matchcond_body (MLimit l_over) p
    = negb (eval_matchcond_body (MLimit l_under) p).
Proof.
  intros p H. cbn [eval_matchcond_body].
  (* the under-test [lim_under] depends only on rate/unit/burst/bytes (NOT the
     flag), and l_under / l_over agree on all of those, so it is the SAME value
     for both; only the over-bit differs and XOR flips the verdict. *)
  assert (Hu : lim_under p l_over = lim_under p l_under).
  { unfold lim_under, lim_avail, lim_cost, lim_max, lim_window, lim_rate.
    replace (ls_rate l_over) with (ls_rate l_under) by reflexivity.
    replace (ls_unit l_over) with (ls_unit l_under) by reflexivity.
    replace (ls_burst l_over) with (ls_burst l_under) by reflexivity.
    replace (ls_bytes l_over) with (ls_bytes l_under) by reflexivity.
    rewrite <- H. reflexivity. }
  rewrite Hu. cbn [l_under l_over ls_flags Nat.land Nat.eqb].
  destruct (lim_under p l_under); reflexivity.
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

(** Concretely: when the packet's byte length EXCEEDS the remaining quota
    ([quota_cost p > remaining], i.e. the kernel's [consumed + skb->len > quota]),
    the non-over form does NOT match (kernel BREAKs the flood under a plain
    `quota X`) while the `over` form DOES (the `quota over X drop` idiom fires
    exactly on the traffic that exceeds the limit).  This is the BYTE accounting:
    the verdict is driven by [meta len], not a fixed unit. *)
Lemma leb_false_of_lt : forall a b : nat, b < a -> Nat.leb a b = false.
Proof.
  intros a b H. apply Nat.leb_gt. exact H.
Qed.

Theorem over_matches_when_exceeded : forall p,
  e_quota (pkt_env p) q_over < quota_cost p ->
  eval_matchcond_body (MQuota q_over) p = true.
Proof.
  intros p H. cbn [eval_matchcond_body q_over]. unfold quota_under.
  rewrite (leb_false_of_lt _ _ H). reflexivity.
Qed.

Theorem nonover_misses_when_exceeded : forall p,
  e_quota (pkt_env p) q_under < quota_cost p ->
  eval_matchcond_body (MQuota q_under) p = false.
Proof.
  intros p H. cbn [eval_matchcond_body q_under]. unfold quota_under.
  rewrite (leb_false_of_lt _ _ H). reflexivity.
Qed.

(** ** The quota now consumes the PACKET LENGTH, not a fixed unit (the fix).

    Before the fix [env_quota_upd] decremented [e_quota] by exactly 1 per
    evaluation, so two packets of any size depleted the bucket identically and a
    quota of N "bytes" passed ~N packets regardless of size.  After the fix the
    bucket loses the packet's [meta len] (= skb->len) on every evaluation, exactly
    like byte-mode [limit].  These theorems pin the byte accounting:
    (1) the remaining bucket drops by the packet length, and
    (2) a single MTU-sized packet over-spends a small quota in ONE shot. *)
Definition q_bytes100 : quota_spec := {| q_bytes := 100; q_consumed := 0; q_flags := 0 |}.

(* The post-eval remaining = old remaining - (packet length), not old - 1. *)
Lemma quota_eqb_b100 : quota_eqb q_bytes100 q_bytes100 = true.
Proof. reflexivity. Qed.

Theorem quota_consumes_packet_len : forall p,
  e_quota (pkt_env (set_quota p q_bytes100)) q_bytes100
    = e_quota (pkt_env p) q_bytes100 - N.to_nat (data_to_N (pkt_meta p MKlen)).
Proof.
  intro p. unfold set_quota, env_quota_upd, quota_cost; cbn [pkt_env e_quota].
  rewrite quota_eqb_b100. reflexivity.
Qed.

(* A 1500-byte (MTU) packet exhausts a 100-byte quota in a SINGLE evaluation: the
   non-over `quota 100 bytes` BREAKs (does not match) on the first big packet,
   whereas the old pred-by-1 model would have passed ~100 packets. *)
Theorem mtu_packet_overspends_small_quota : forall p,
  pkt_meta p MKlen = [5; 220] ->     (* 5*256 + 220 = 1500 bytes, big-endian *)
  e_quota (pkt_env p) q_bytes100 = 100 ->
  eval_matchcond_body (MQuota q_bytes100) p = false.
Proof.
  intros p Hlen Hq. cbn [eval_matchcond_body q_bytes100]. unfold quota_under, quota_cost.
  rewrite Hlen, Hq. reflexivity.
Qed.

(** ** The configured RATE/UNIT/BURST are now LIVE in the data plane.

    Before the fix the limiter passed iff [0 < e_limit] — the configured
    rate/unit/burst were never consulted in the dynamics, so a 1/second and a
    1/hour limiter were observationally IDENTICAL at the same bucket level (the
    red agent's [Limit_Inert_RED.rate_is_inert]).  After the fix the per-packet
    COST and the bucket CAP are genuine functions of those parameters: a
    1/second packet costs [window(1s)/rate = 1] token while a 1/hour packet costs
    [window(1h)/rate = 3600], so at the SAME stored bucket level [= 1] the
    1/second limiter PASSES and the 1/hour limiter FAILS.  Distinct rates give
    distinct verdicts — the parameters are no longer inert. *)
Definition r_fast : limit_spec :=        (* 1/second burst 1 (packet rate) *)
  {| ls_rate := 1; ls_unit := 0; ls_burst := 1; ls_bytes := false; ls_flags := 0 |}.
Definition r_slow : limit_spec :=        (* 1/hour   burst 1 (packet rate) *)
  {| ls_rate := 1; ls_unit := 2; ls_burst := 1; ls_bytes := false; ls_flags := 0 |}.

(** At a bucket level of 1 token, the fast (1/second) limiter passes (cost 1 <= 1)
    while the slow (1/hour) limiter fails (cost 3600 > 1): OPPOSITE verdicts for the
    SAME bucket level — the rate is live. *)
Theorem rate_is_live : forall p,
  e_limit (pkt_env p) r_fast = 1 ->
  e_limit (pkt_env p) r_slow = 1 ->
  eval_matchcond_body (MLimit r_fast) p = true /\
  eval_matchcond_body (MLimit r_slow) p = false.
Proof.
  intros p Hf Hs. split.
  - cbn [eval_matchcond_body]. unfold lim_under, lim_avail, lim_cost, lim_max,
      lim_window, lim_rate, lim_unit_secs, lim_SCALE.
    rewrite Hf. unfold r_fast; cbn [ls_rate ls_unit ls_burst ls_bytes ls_flags]. reflexivity.
  - cbn [eval_matchcond_body]. unfold lim_under, lim_avail, lim_cost, lim_max,
      lim_window, lim_rate, lim_unit_secs, lim_SCALE.
    rewrite Hs. unfold r_slow; cbn [ls_rate ls_unit ls_burst ls_bytes ls_flags]. reflexivity.
Qed.

(** The byte-mode limiter's cost scales with the PACKET LENGTH (meta len): the
    kernel charges [nsecs * skb->len / rate].  A 1-byte packet costs less than a
    large one, so at a bucket holding [b_window] tokens a 1-byte packet passes
    while a [b_window+1]-byte packet exceeds the cost — the length is live too.
    [b_lim] = `limit rate 1 bytes/second burst 1`. *)
Definition b_lim : limit_spec :=
  {| ls_rate := 1; ls_unit := 0; ls_burst := 1; ls_bytes := true; ls_flags := 0 |}.

Theorem bytemode_length_is_live : forall p q,
  pkt_meta p MKlen = [1] ->            (* a 1-byte packet *)
  pkt_meta q MKlen = [3] ->            (* a 3-byte packet *)
  e_limit (pkt_env p) b_lim = 2 ->
  e_limit (pkt_env q) b_lim = 2 ->
  eval_matchcond_body (MLimit b_lim) p = true /\
  eval_matchcond_body (MLimit b_lim) q = false.
Proof.
  intros p q Hp Hq Hep Heq. split.
  - cbn [eval_matchcond_body]. unfold lim_under, lim_avail, lim_cost, lim_max,
      lim_window, lim_rate, lim_unit_secs, lim_SCALE.
    rewrite Hp, Hep. unfold b_lim; cbn [ls_rate ls_unit ls_burst ls_bytes ls_flags]. reflexivity.
  - cbn [eval_matchcond_body]. unfold lim_under, lim_avail, lim_cost, lim_max,
      lim_window, lim_rate, lim_unit_secs, lim_SCALE.
    rewrite Hq, Heq. unfold b_lim; cbn [ls_rate ls_unit ls_burst ls_bytes ls_flags]. reflexivity.
Qed.
