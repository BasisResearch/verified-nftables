(** RED probe (now KERNEL-CORRECT, after the blue fix): `limit`/`quota`/`connlimit`
    are SHARED, CONSUMING token buckets threaded cross-packet, not stateless
    per-packet oracles.

    Kernel nft_limit.c nft_limit_eval:
      delta = tokens - cost;
      if (delta >= 0) { priv->limit->tokens = delta; return invert; }   // PASS, consume
      priv->limit->tokens = tokens; return !invert;                     // EXHAUSTED
    A matching packet SUBTRACTS cost from the running token count stored in the
    limiter object (refilling by elapsed time).  So `limit rate 1/second burst 1
    accept` PASSES packet 1 (one token) and, for packet 2 arriving back-to-back (no
    refill), is EXHAUSTED (delta < 0) so the rule does NOT continue -> the chain's
    DROP policy applies.  Consecutive packets get DIFFERENT verdicts — the entire
    purpose of a rate limit.  nft_quota.c / nft_connlimit.c likewise accumulate.

    BEFORE the fix the model made the limiter a STATELESS per-packet oracle:
    [e_limit : limit_spec -> nat] a fixed read, never decremented; two packets
    threaded through a rate-limit chain read the IDENTICAL token count and got the
    IDENTICAL verdict — UNSOUND (the model PROVED both packets accepted where the
    kernel accepts only the first) and TOO WEAK (it could not express "consecutive
    packets exceeding the rate are dropped").

    AFTER the fix [e_limit] is a SHARED, CONSUMING bucket: a passing `limit` match
    DECREMENTS it (cost = 1), and the consumption is threaded across rules and
    packets by [limit_sweep_body] (DSL) / [limit_sweep_prog] (VM) at the
    mutation-evaluator boundary — exactly the `numgen inc` (e_numgen) / ct-mark
    (e_ct) / NAT (e_nat) pattern.  This file proves the kernel-correct property the
    old model could not: with a bucket of exactly 1 token, packet 1 is ACCEPTED, the
    bucket is then EMPTY, and packet 2 of the depleted bucket is DROPPED (the chain's
    policy), so consecutive packets get DIFFERENT verdicts. *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics Compile.
Import ListNotations.

(* `limit rate 1/second burst 1` (packet-rate, no invert/over bit). *)
Definition lim1 : limit_spec :=
  {| ls_rate := 1; ls_unit := 0; ls_burst := 1; ls_bytes := false; ls_flags := 0 |}.

(* An env whose ONLY limiter [lim1] starts with exactly 1 token. *)
Definition env1 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => [];
     e_limit := fun _ => 1;                 (* exactly one token *)
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => []; e_nat := fun _ => None;
     e_numgen := fun _ => 0 |}.

Definition mkpkt (e : env) (flow : data) : packet :=
  {| pkt_env := e; pkt_meta := fun _ => [];
     pkt_ct := fun _ => []; pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => [];
     pkt_numgen := fun _ => [9;9;9;9];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := false; pkt_fragoff := 0;
     pkt_flow := flow; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* `limit rate 1/second burst 1 accept`: a one-rule chain, policy DROP. *)
Definition rule_lim : rule :=
  {| r_body := [BMatch (MLimit lim1)]; r_verdict := Accept;
     r_vmap := None; r_nat := None; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.
Definition chain_lim : chain := {| c_policy := Drop; c_rules := [rule_lim] |}.

(* Packet 1 of the flow, against the fresh (1 token) env. *)
Definition pk1 : packet := mkpkt env1 [1;1].

(* Run the chain on packet 1, threading the env it leaves (the consumed bucket). *)
Definition res1 : verdict * env := eval_chain_mut_env chain_lim pk1.

(* Packet 2 of the SAME flow, carrying the env packet 1 left (bucket now empty). *)
Definition pk2 : packet := mkpkt (snd res1) [1;1].
Definition v2 : verdict := fst (eval_chain_mut_env chain_lim pk2).

(* Packet 1 PASSES the limit and is ACCEPTED (one token available). *)
Lemma p1_accepted : fst res1 = Accept.
Proof. reflexivity. Qed.

(* The token bucket is CONSUMED: after packet 1 it holds 0 tokens (was 1). *)
Lemma limit_consumed : e_limit (snd res1) lim1 = 0.
Proof. reflexivity. Qed.

(* Packet 2 of the depleted bucket is DROPPED — the `limit` match fails (bucket
   empty), the rule does not continue, and the chain's DROP policy applies.  This is
   exactly the kernel verdict the OLD per-packet-oracle model could not produce. *)
Lemma p2_dropped : v2 = Drop.
Proof. reflexivity. Qed.

(* Consecutive packets through the rate limiter get DIFFERENT verdicts — the entire
   purpose of a rate limit (the old model PROVED they were identical: UNSOUND). *)
Lemma limit_actually_limits : fst res1 <> v2.
Proof. cbn. discriminate. Qed.

(* ---- The VM side agrees: the compiled bytecode consumes the same bucket. ---- *)
Definition prog_lim : program := compile_chain chain_lim.

Definition vres1 : verdict * env := run_chain_mut_env prog_lim Drop pk1.
Definition vpk2 : packet := mkpkt (snd vres1) [1;1].
Definition vv2 : verdict := fst (run_chain_mut_env prog_lim Drop vpk2).

Lemma vm_p1_accepted : fst vres1 = Accept.
Proof. reflexivity. Qed.
Lemma vm_limit_consumed : e_limit (snd vres1) lim1 = 0.
Proof. reflexivity. Qed.
Lemma vm_p2_dropped : vv2 = Drop.
Proof. reflexivity. Qed.
