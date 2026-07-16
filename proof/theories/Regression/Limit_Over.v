(** * The limiter over/invert bit flips the match verdict

    Real nftables limit / quota / connlimit each carry an "over" (invert) bit
    (NFT_LIMIT_F_INV / NFT_QUOTA_F_INV / NFT_CONNLIMIT_F_INV = bit 0 of the
    flags field).  The kernel XORs the under/not-exceeded test with that bit:
      nft_limit.c:48,52    return [invert] when tokens remain, [!invert] when
                           exhausted (caller BREAKs on a true return),
      nft_quota.c:43       [if (nft_overquota(...) ^ nft_quota_invert(priv)) BREAK],
      nft_connlimit.c:47   [if ((count > limit) ^ priv->invert) BREAK].

    [eval_matchcond_body] XORs the same way.  A model that never inspects the
    flag matches an `over`/inverted limiter identically to the non-inverted form —
    PASSING the flood and DROPPING the conforming traffic, the exact opposite of
    the kernel.

    These theorems pin the behaviour: for a FIXED oracle value, the `over` and
    non-`over` specs give OPPOSITE match verdicts; a flag-blind model makes them
    unprovable. *)
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
    does NOT.  (A flag-blind model would prove EQUAL results instead.) *)

Theorem quota_over_flag_flips : forall e p,
  e_quota e q_under = e_quota e q_over ->
  eval_matchcond_body (MQuota q_over) e p
    = negb (eval_matchcond_body (MQuota q_under) e p).
Proof.
  intros e p H. cbn [eval_matchcond_body q_under q_over].
  (* the under-test [quota_under] depends only on the packet length and the
     remaining bytes (NOT the flag); q_under/q_over share q_bytes and (by H) the
     same remaining reading, so [quota_under] agrees and only the over-bit flips. *)
  assert (Hu : quota_under e p q_over = quota_under e p q_under).
  { unfold quota_under. rewrite H. reflexivity. }
  rewrite Hu. cbn [Nat.land Nat.eqb].
  destruct (quota_under e p q_under); reflexivity.
Qed.

Theorem limit_over_flag_flips : forall e p,
  e_limit e l_under = e_limit e l_over ->
  eval_matchcond_body (MLimit l_over) e p
    = negb (eval_matchcond_body (MLimit l_under) e p).
Proof.
  intros e p H. cbn [eval_matchcond_body].
  (* the under-test [lim_under] depends only on rate/unit/burst/bytes (NOT the
     flag), and l_under / l_over agree on all of those, so it is the SAME value
     for both; only the over-bit differs and XOR flips the verdict. *)
  assert (Hu : lim_under e p l_over = lim_under e p l_under).
  { unfold lim_under, lim_avail, lim_cost, lim_max, lim_window, lim_rate.
    replace (ls_rate l_over) with (ls_rate l_under) by reflexivity.
    replace (ls_unit l_over) with (ls_unit l_under) by reflexivity.
    replace (ls_burst l_over) with (ls_burst l_under) by reflexivity.
    replace (ls_bytes l_over) with (ls_bytes l_under) by reflexivity.
    rewrite <- H. reflexivity. }
  rewrite Hu. cbn [l_under l_over ls_flags Nat.land Nat.eqb].
  destruct (lim_under e p l_under); reflexivity.
Qed.

Theorem connlimit_over_flag_flips : forall e p,
  e_connlimit e c_under = e_connlimit e c_over ->
  eval_matchcond_body (MConnlimit c_over) e p
    = negb (eval_matchcond_body (MConnlimit c_under) e p).
Proof.
  intros e p H. cbn [eval_matchcond_body].
  unfold connlimit_under, connlimit_count, connlimit_after.
  rewrite <- H. unfold c_under, c_over. cbn [cl_count cl_flags Nat.land Nat.eqb].
  destruct (negb (Nat.ltb 5 _)); reflexivity.
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

Theorem over_matches_when_exceeded : forall e p,
  e_quota e q_over < quota_cost p ->
  eval_matchcond_body (MQuota q_over) e p = true.
Proof.
  intros e p H. cbn [eval_matchcond_body q_over]. unfold quota_under.
  rewrite (leb_false_of_lt _ _ H). reflexivity.
Qed.

Theorem nonover_misses_when_exceeded : forall e p,
  e_quota e q_under < quota_cost p ->
  eval_matchcond_body (MQuota q_under) e p = false.
Proof.
  intros e p H. cbn [eval_matchcond_body q_under]. unfold quota_under.
  rewrite (leb_false_of_lt _ _ H). reflexivity.
Qed.

(** ** The quota consumes the PACKET LENGTH, not a fixed unit.

    [env_quota_upd] decrements the bucket by the packet's [meta len] (= skb->len)
    on every evaluation, exactly like byte-mode [limit].  A fixed unit cost of 1
    per evaluation would deplete a quota of N "bytes" by ~N packets regardless of
    size.  These theorems pin the byte accounting:
    (1) the remaining bucket drops by the packet length, and
    (2) a single MTU-sized packet over-spends a small quota in ONE shot. *)
Definition q_bytes100 : quota_spec := {| q_bytes := 100; q_consumed := 0; q_flags := 0 |}.

(* The post-eval remaining = old remaining - (packet length), not old - 1. *)
Lemma quota_eqb_b100 : quota_eqb q_bytes100 q_bytes100 = true.
Proof. reflexivity. Qed.

Theorem quota_consumes_packet_len : forall e p,
  e_quota (set_quota e p q_bytes100) q_bytes100
    = e_quota e q_bytes100 - N.to_nat (data_to_N (pkt_meta p MKlen)).
Proof.
  intros e p. unfold set_quota, env_quota_upd, quota_cost;
    cbn [with_e_quota e_quota].
  rewrite quota_eqb_b100. reflexivity.
Qed.

(* A 1500-byte (MTU) packet exhausts a 100-byte quota in a SINGLE evaluation: the
   non-over `quota 100 bytes` BREAKs (does not match) on the first big packet,
   whereas the old pred-by-1 model would have passed ~100 packets. *)
Theorem mtu_packet_overspends_small_quota : forall e p,
  pkt_meta p MKlen = [5; 220] ->     (* 5*256 + 220 = 1500 bytes, big-endian *)
  e_quota e q_bytes100 = 100 ->
  eval_matchcond_body (MQuota q_bytes100) e p = false.
Proof.
  intros e p Hlen Hq. cbn [eval_matchcond_body q_bytes100]. unfold quota_under, quota_cost.
  rewrite Hlen, Hq. reflexivity.
Qed.

(** ** The configured RATE/UNIT/BURST are LIVE in the data plane.

    The per-packet COST and the bucket CAP are genuine functions of the
    configured parameters: a 1/second packet costs [window(1s)/rate = 1] token
    while a 1/hour packet costs [window(1h)/rate = 3600], so at the SAME stored
    bucket level [= 1] the 1/second limiter PASSES and the 1/hour limiter FAILS.
    Distinct rates give distinct verdicts — the parameters are not inert.  (A
    limiter that passed iff [0 < e_limit], never consulting rate/unit/burst,
    would make 1/second and 1/hour observationally identical, refuted below.) *)
Definition r_fast : limit_spec :=        (* 1/second burst 1 (packet rate) *)
  {| ls_rate := 1; ls_unit := 0; ls_burst := 1; ls_bytes := false; ls_flags := 0 |}.
Definition r_slow : limit_spec :=        (* 1/hour   burst 1 (packet rate) *)
  {| ls_rate := 1; ls_unit := 2; ls_burst := 1; ls_bytes := false; ls_flags := 0 |}.

(** At a bucket level of 1 token, the fast (1/second) limiter passes (cost 1 <= 1)
    while the slow (1/hour) limiter fails (cost 3600 > 1): OPPOSITE verdicts for the
    SAME bucket level — the rate is live. *)
Theorem rate_is_live : forall e p,
  e_limit e r_fast = 1 ->
  e_limit e r_slow = 1 ->
  eval_matchcond_body (MLimit r_fast) e p = true /\
  eval_matchcond_body (MLimit r_slow) e p = false.
Proof.
  intros e p Hf Hs. split.
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

Theorem bytemode_length_is_live : forall e p q,
  pkt_meta p MKlen = [1] ->            (* a 1-byte packet *)
  pkt_meta q MKlen = [3] ->            (* a 3-byte packet *)
  e_limit e b_lim = 2 ->
  eval_matchcond_body (MLimit b_lim) e p = true /\
  eval_matchcond_body (MLimit b_lim) e q = false.
Proof.
  intros e p q Hp Hq Hep. pose proof Hep as Heq. split.
  - cbn [eval_matchcond_body]. unfold lim_under, lim_avail, lim_cost, lim_max,
      lim_window, lim_rate, lim_unit_secs, lim_SCALE.
    rewrite Hp, Hep. unfold b_lim; cbn [ls_rate ls_unit ls_burst ls_bytes ls_flags]. reflexivity.
  - cbn [eval_matchcond_body]. unfold lim_under, lim_avail, lim_cost, lim_max,
      lim_window, lim_rate, lim_unit_secs, lim_SCALE.
    rewrite Hq, Heq. unfold b_lim; cbn [ls_rate ls_unit ls_burst ls_bytes ls_flags]. reflexivity.
Qed.

(** ** `connlimit` is a CONNECTION limiter, not a PACKET limiter.

    nft_connlimit.c calls nf_conncount_add_skb, which returns -EEXIST (no-op) for
    an already-counted connection, so [count] is the number of DISTINCT live
    connections and the rule BREAKs only when `count > limit` (STRICT >).  A
    per-instance remaining-slot counter decremented on EVERY passing packet would
    instead block the (N+1)-th packet of ONE connection — something the kernel
    never does.

    In the model [e_connlimit] is the flow-keyed SET of distinct counted
    connections, [set_connlimit] inserts [pkt_flow] IDEMPOTENTLY (the -EEXIST
    dedup), and [connlimit_under] tests [count <= limit].  These theorems pin the
    CONNECTION-keyed behaviour. *)
Definition cl1 : connlimit_spec := {| cl_count := 1; cl_flags := 0 |}.

(* Re-adding an already-counted connection is a NO-OP: the count is unchanged, so
   set_connlimit on a same-flow packet does not grow the instance's set. *)
Theorem connlimit_same_flow_idempotent : forall e p,
  data_mem (pkt_flow p) (e_connlimit e cl1) = true ->
  e_connlimit (set_connlimit e p cl1) cl1 = e_connlimit e cl1.
Proof.
  intros e p Hmem. unfold set_connlimit, env_connlimit_upd, connlimit_after;
    cbn [with_e_connlimit e_connlimit].
  replace (connlimit_eqb cl1 cl1) with true by (unfold connlimit_eqb, cl1; reflexivity).
  rewrite Hmem. reflexivity.
Qed.

(* Under `connlimit count 1`, the FIRST packet of a flow is counted
   (count = 1 <= 1, passes); the SECOND packet of the SAME connection reads the
   SAME count (the flow is already in the set: dedup), so it ALSO passes.  One
   connection is NEVER throttled by `connlimit 1` — a packet-decrement model
   would block the 2nd same-flow packet. *)
Theorem connlimit1_same_flow_both_pass : forall e p1 p2,
  pkt_flow p1 = pkt_flow p2 ->
  e_connlimit e cl1 = [] ->
  (* p2 is evaluated AFTER p1's connection was accounted: against the env
     [set_connlimit e p1 cl1] the first evaluation leaves (threaded env) *)
  eval_matchcond_body (MConnlimit cl1) e p1 = true /\
  eval_matchcond_body (MConnlimit cl1) (set_connlimit e p1 cl1) p2 = true.
Proof.
  intros e p1 p2 Hflow Hseed. split.
  - (* first packet: empty set -> count after insert = 1 <= 1 *)
    cbn [eval_matchcond_body]. unfold connlimit_under, connlimit_count, connlimit_after.
    rewrite Hseed. cbn [data_mem existsb List.length]. unfold cl1; cbn [cl_count cl_flags Nat.land Nat.eqb Nat.ltb]. reflexivity.
  - (* second, SAME-flow packet: pkt_flow p2 already counted -> count still 1 <= 1 *)
    cbn [eval_matchcond_body]. unfold connlimit_under, connlimit_count.
    unfold set_connlimit, env_connlimit_upd, connlimit_after;
      cbn [with_e_connlimit e_connlimit].
    replace (connlimit_eqb cl1 cl1) with true by (unfold connlimit_eqb, cl1; reflexivity).
    rewrite Hseed. cbn [data_mem existsb]. rewrite <- Hflow.
    rewrite data_eqb_refl. cbn [orb List.length]. unfold cl1; cbn [cl_count cl_flags Nat.land Nat.eqb Nat.ltb]. reflexivity.
Qed.

(* `connlimit count 1` PERMITS 2 distinct connections (count <= limit at 1 and at
   the moment a 2nd DISTINCT flow is inserted count = 2 > 1 breaks): the limiter is
   a CONNECTION threshold, breaking strictly above N.  Here the set already holds
   ONE distinct flow [f1] different from this packet's flow, so inserting this
   packet's flow makes count = 2 > 1 -> the rule does NOT match (BREAK). *)
Theorem connlimit1_breaks_on_second_distinct_flow : forall e p f1,
  data_eqb (pkt_flow p) f1 = false ->
  e_connlimit e cl1 = [f1] ->
  eval_matchcond_body (MConnlimit cl1) e p = false.
Proof.
  intros e p f1 Hne Hset. cbn [eval_matchcond_body].
  unfold connlimit_under, connlimit_count, connlimit_after.
  rewrite Hset. cbn [data_mem existsb]. rewrite Hne. cbn [orb List.length].
  unfold cl1; cbn [cl_count cl_flags Nat.land Nat.eqb Nat.ltb]. reflexivity.
Qed.
