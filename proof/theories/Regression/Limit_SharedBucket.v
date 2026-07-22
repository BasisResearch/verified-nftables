(** `limit`/`quota`/`connlimit` are SHARED, CONSUMING token buckets threaded
    cross-packet, not stateless per-packet oracles.

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

    In the model [e_limit] is that shared, consuming bucket: EVALUATING a
    `limit` match writes it at the match's own position inside the break-aware
    per-rule folds ([Semantics.body_step]'s [match_consume] /
    [run_rule_step]'s [ILimit]) — position-exact, exactly like the kernel's
    per-evaluation tokens store — and the consumption is threaded across
    rules and packets by the mutation evaluators, the same threading as the
    `numgen inc` (e_numgen) / ct-mark (e_ct) / NAT (e_nat) env writes.

    Regression gate: [p1_accepted], [limit_consumed], [p2_dropped], and
    [limit_actually_limits] (with their VM twins [vm_*]) lock in the
    consume-and-differ behaviour; a model regression to a stateless per-packet
    token read (both packets seeing the same count, hence the same verdict)
    makes them unprovable.  [limit_before_failing_match_consumed] (+ VM twin)
    locks in the POSITION of the write: a limiter BEFORE a failing match is
    evaluated and consumes even though the rule breaks afterwards — while a
    limiter AFTER a failing match consumes nothing
    (Known_Infidelities.v [gate_limit_undrained], the repaired entry 1). *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics Compile.
Import ListNotations.

(* Pins below hold at EVERY netfilter hook [h] (no rule here carries a NAT
   terminal, so the hook is inert); the section generalizes each statement. *)
Section AtHook.
Context (h : hook_id).

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

Definition mkpkt (flow : data) : packet :=
  {| pkt_meta := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => [];
     pkt_numgen := fun _ => [9;9;9;9];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := false; pkt_fragoff := 0;
     pkt_flow := flow; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* `limit rate 1/second burst 1 accept`: a one-rule chain, policy DROP. *)
Definition rule_lim : rule :=
  {| r_body := [BMatch (MLimit lim1)];
     r_outcome := OVerdict Accept; r_after := [] |}.
Definition chain_lim : chain := {| c_policy := Drop; c_rules := [rule_lim] |}.

(* Packet 1 of the flow, against the fresh (1 token) env. *)
Definition pk1 : packet := mkpkt [1;1].

(* Run the chain on packet 1, threading the env it leaves (the consumed bucket). *)
Definition res1 : verdict * env := eval_chain_flat_env h chain_lim env1 pk1.

(* Packet 2 of the SAME flow, carrying the env packet 1 left (bucket now empty). *)
Definition pk2 : packet := mkpkt [1;1].
Definition v2 : verdict := fst (eval_chain_flat_env h chain_lim (snd res1) pk2).

(* Packet 1 PASSES the limit and is ACCEPTED (one token available). *)
Lemma p1_accepted : fst res1 = Accept.
Proof. reflexivity. Qed.

(* The token bucket is CONSUMED: after packet 1 it holds 0 tokens (was 1). *)
Lemma limit_consumed : e_limit (snd res1) lim1 = 0.
Proof. reflexivity. Qed.

(* Packet 2 of the depleted bucket is DROPPED — the `limit` match fails (bucket
   empty), the rule does not continue, and the chain's DROP policy applies —
   exactly the kernel verdict (nft_limit_eval's EXHAUSTED branch). *)
Lemma p2_dropped : v2 = Drop.
Proof. reflexivity. Qed.

(* Consecutive packets through the rate limiter get DIFFERENT verdicts — the entire
   purpose of a rate limit; a stateless per-packet token read cannot produce this. *)
Lemma limit_actually_limits : fst res1 <> v2.
Proof. cbn. discriminate. Qed.

(* ---- The VM side agrees: the compiled bytecode consumes the same bucket. ---- *)
Definition prog_lim : program := compile_chain chain_lim.

Definition vres1 : verdict * env := run_chain_flat_env h prog_lim Drop env1 pk1.
Definition vpk2 : packet := mkpkt [1;1].
Definition vv2 : verdict := fst (run_chain_flat_env h prog_lim Drop (snd vres1) vpk2).

Lemma vm_p1_accepted : fst vres1 = Accept.
Proof. reflexivity. Qed.
Lemma vm_limit_consumed : e_limit (snd vres1) lim1 = 0.
Proof. reflexivity. Qed.
Lemma vm_p2_dropped : vv2 = Drop.
Proof. reflexivity. Qed.

(* ---- Position-exactness: a limiter BEFORE a failing match IS evaluated. ---- *)
(* `limit rate 1/second burst 1  meta mark 0x1  accept` on a packet whose mark
   does NOT match: the kernel evaluates the limiter (consuming the token),
   then the mark match sets NFT_BREAK — the rule yields no verdict but the
   bucket write already happened and persists. *)
Definition rule_lim_first : rule :=
  {| r_body := [ BMatch (MLimit lim1) ; BMatch (MEq FMetaMark [0;0;0;1]) ];
     r_outcome := OVerdict Accept; r_after := [] |}.
Definition chain_lim_first : chain := {| c_policy := Drop; c_rules := [rule_lim_first] |}.

Definition lf_res : verdict * env := eval_chain_flat_env h chain_lim_first env1 pk1.

(* The rule does not apply (the mark match fails) — the DROP policy verdict. *)
Lemma lim_first_policy : fst lf_res = Drop.
Proof. reflexivity. Qed.

(* But the limiter WAS evaluated before the break: its token is consumed. *)
Lemma limit_before_failing_match_consumed : e_limit (snd lf_res) lim1 = 0.
Proof. reflexivity. Qed.

(* VM twin: the compiled bytecode consumes the same bucket at the same position. *)
Definition vm_lf_res : verdict * env :=
  run_chain_flat_env h (compile_chain chain_lim_first) Drop env1 pk1.

Lemma vm_limit_before_failing_match_consumed : e_limit (snd vm_lf_res) lim1 = 0.
Proof. reflexivity. Qed.

End AtHook.
