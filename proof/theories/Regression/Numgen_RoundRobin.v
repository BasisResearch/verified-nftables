(** `numgen inc` is a SHARED, persistent round-robin counter, not a per-packet
    oracle.

    Kernel nft_numgen.c nft_ng_inc_gen: a SHARED atomic counter, incremented per
    evaluation:  nval = (oval + 1 < modulus) ? oval + 1 : 0;  return nval + offset.
    So consecutive `numgen inc mod N` evaluations are round-robin: for N>=2 two
    consecutive firings ALWAYS differ (…0,1,0,1… for N=2).  The counter is global
    and persistent across packets — this is what makes
    `numgen inc mod 2 ... map {0: A, 1: B}` a real per-connection load balancer.

    In the model `numgen inc` reads the SHARED counter [e_numgen] in the env and
    the VM mutation evaluator ([run_program_flat_env h]) ADVANCES it per evaluation,
    threading it across packets exactly like the ct/nat/dynset env writes.  (The
    RANDOM generator, ng_random = true, remains the per-packet oracle
    [pkt_numgen] — nft_ng_random_gen draws get_random_u32 per packet.)

    Regression gate: [consecutive_numgen_inc_differ], [counter_advanced],
    [numgen_is_round_robin], and [ng_p3_wraps] lock in the shared round-robin;
    a model regression to a per-packet numgen oracle (two distinct packets both
    reading 0) makes them unprovable. *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics Compile.
Import ListNotations.

(* Pins below hold at EVERY netfilter hook [h] (no rule here carries a NAT
   terminal, so the hook is inert); the section generalizes each statement. *)
Section AtHook.
Context (h : hook_id).

(* numgen inc mod 2 (ng_random=false, modulus=2, offset=0). *)
Definition ng2 : numgen_spec := {| ng_random := false; ng_mod := 2; ng_offset := 0 |}.

Definition env0 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => []; e_nat := fun _ => None;
     e_numgen := fun _ => 0 |}.

(* A packet carrying a given env.  pkt_numgen (the RANDOM oracle) is irrelevant for
   `numgen inc`; the inc value comes from [e_numgen] in the env. *)
Definition mkpkt (flow : data) : packet :=
  {| pkt_meta := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => [];
     pkt_numgen := fun _ => [9;9;9;9];   (* random oracle; NOT read by `numgen inc` *)
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := false; pkt_fragoff := 0;
     pkt_flow := flow; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* A one-rule VM program that LOADS `numgen inc mod 2` into reg 1 (the value a
   `numgen ... vmap/map {...}` would dispatch on), then is verdict-neutral
   (ICounter) so the traversal continues and the env it leaves is observable. *)
Definition prog_ng : rule_prog := [ INumgen ng2 1 ; ICounter 0 0 ].

(* The `numgen inc` value the model hands a packet (= the load the VM reads). *)
Definition ng_of (e : env) (p : packet) : data := do_load (LNumgen ng2) e p.

(* Packet 1 of the traversal, against the fresh (counter = 0) env. *)
Definition p1 : packet := mkpkt [1;1].

(* The env AFTER packet 1 has fired the numgen rule: its counter has ADVANCED. *)
Definition env_after_p1 : env := snd (run_program_flat_env h [prog_ng] env0 p1).

(* Packet 2 of the traversal, carrying the env packet 1 left (the threaded shared
   state) — exactly how [run_program_flat_env h]/[seq_eval_env] sequence packets. *)
Definition p2 : packet := mkpkt [2;2].

(* ---- The kernel-correct round-robin facts. ---- *)

(* Packet 1 (the first evaluation) reads numgen = 0 + offset = 0. *)
Theorem ng_p1 : ng_of env0 p1 = [0;0;0;0].
Proof. vm_compute. reflexivity. Qed.

(* Running the numgen rule ADVANCED the shared counter from 0 to 1. *)
Theorem counter_advanced : e_numgen env_after_p1 ng2 = 1.
Proof. vm_compute. reflexivity. Qed.

(* Packet 2 (the next evaluation, same traversal) reads the SUCCESSOR: 1 mod 2 = 1
   — the round-robin step, which requires the shared cross-packet counter. *)
Theorem ng_p2 : ng_of env_after_p1 p2 = [0;0;0;1].
Proof. vm_compute. reflexivity. Qed.

(* Headline: two CONSECUTIVE `numgen inc mod 2` evaluations DIFFER — the kernel's
   round-robin guarantee (nft_ng_inc_gen).  Axiom-free; a per-packet numgen oracle
   would instead let both evaluations read the same value. *)
Theorem consecutive_numgen_inc_differ : ng_of env0 p1 <> ng_of env_after_p1 p2.
Proof. rewrite ng_p1, ng_p2. discriminate. Qed.

(* Stronger: packet 2's value is exactly (packet 1's + 1) mod 2 — the kernel's
   nft_ng_inc_gen step.  (Here: 0 -> 1.) *)
Theorem numgen_is_round_robin :
  ng_of env_after_p1 p2 = numgen_inc_value ng2 (S (e_numgen env0 ng2)).
Proof. vm_compute. reflexivity. Qed.

(* And the cross-packet soundness: a THIRD packet wraps back to 0 (mod 2), so the
   sequence is genuinely 0,1,0,… — a real round-robin load balancer. *)
Definition env_after_p2 : env := snd (run_program_flat_env h [prog_ng] env_after_p1 p2).
Definition p3 : packet := mkpkt [3;3].
Theorem ng_p3_wraps : ng_of env_after_p2 p3 = [0;0;0;0].
Proof. vm_compute. reflexivity. Qed.

End AtHook.
