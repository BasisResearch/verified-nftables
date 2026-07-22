(** * SYN-proxy is verdict-bearing, NOT a no-op.

    A verdict-neutral `synproxy` statement would make a rule whose only action
    is `synproxy` a complete verdict no-op ([eval_chain_flat_verdict {synproxy} p = policy]
    for EVERY packet) — UNSOUND.  The kernel (net/netfilter/nft_synproxy.c,
    nft_synproxy_do_eval / _eval_v4) is verdict-bearing in every interesting
    case:

      - non-TCP packet  => NFT_BREAK (line 117): the rule does NOT apply;
      - TCP SYN         => NF_STOLEN (line 61): the SYN is answered with a
                           syncookie SYN+ACK and consumed — traversal STOPS;
      - TCP client ACK  => NF_STOLEN (valid) / NF_DROP (rejected) — STOPS;
      - other TCP       => implicit NFT_CONTINUE (fall through).

    The model captures the control-flow decision the single-packet semantics can see:
    a non-TCP packet makes the rule unloadable (NFT_BREAK, via the TCP-flags
    transport load), a SYN/ACK packet STOPS traversal — modelled as the terminal
    verdict [Drop] (the documented behaviour: doc/statements.txt:55, "reject and
    synproxy internally issue a drop verdict at the end of their respective
    actions"; the syncookie side effect of STOLEN is below the model's single-
    packet resolution, exactly as Reject's ICMP / Queue's hand-off are), and a
    non-SYN/non-ACK TCP packet falls through (NFT_CONTINUE).

    These theorems witness that the model is not a verdict no-op, and that the
    compiled bytecode agrees (via [compile_chain_flat_verdict_correct]). *)

From Stdlib Require Import List String Bool.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Compile Correct.
Import ListNotations.

Definition syn_env : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_limit := fun _ => 0; e_quota := fun _ => 0; e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

(** A 20-byte TCP header whose flags byte (offset 13) is [fl]. *)
Definition tcp_hdr (fl : nat) : list byte :=
  [0;0;0;0; 0;0;0;0; 0;0;0;0; 0; fl; 0;0; 0;0;0;0].

Definition mk_tcp_pkt (fl : nat) : packet :=
  {|
     pkt_meta := fun _ => []; pkt_sock := fun _ => [];
     pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := tcp_hdr fl; pkt_ih := []; pkt_tnl := [];
     pkt_fibkey := fun _ => []; pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => [];
     pkt_have_l2 := true; pkt_have_l4 := true;       (* a parsed TCP header *)
     pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := true |}.

(** A non-TCP packet: no L4 header parsed (the kernel's NFT_BREAK arm). *)
Definition non_tcp_pkt : packet :=
  {|
     pkt_meta := fun _ => []; pkt_sock := fun _ => [];
     pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := []; pkt_tnl := [];
     pkt_fibkey := fun _ => []; pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => [];
     pkt_have_l2 := true; pkt_have_l4 := false; pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := true |}.

Definition syn_pkt  : packet := mk_tcp_pkt 2.   (* SYN  = 0x02 *)
Definition ack_pkt  : packet := mk_tcp_pkt 16.  (* ACK  = 0x10 *)
Definition rst_pkt  : packet := mk_tcp_pkt 4.   (* RST  = 0x04 (neither SYN nor ACK) *)

(** A chain whose ONLY rule is `synproxy mss 1460 wscale 7`, with policy Accept.
    (Accept, not Drop, so that a [Drop] verdict can only come FROM the synproxy.) *)
Definition synproxy_rule : rule :=
  {| r_body := [ BStmt (SSynproxy 1460 7) ];
     r_outcome := ONone; r_after := [] |}.
Definition synproxy_chain : chain :=
  {| c_policy := Accept; c_rules := [ synproxy_rule ] |}.

(** *** A SYN packet STOPS at the synproxy — the statement is verdict-bearing. *)
Theorem syn_pkt_stopped : forall h, eval_chain_flat_verdict h synproxy_chain syn_env syn_pkt = Drop.
Proof. intro h. vm_compute. reflexivity. Qed.

(** An ACK packet likewise stops (kernel: STOLEN valid / DROP rejected). *)
Theorem ack_pkt_stopped : forall h, eval_chain_flat_verdict h synproxy_chain syn_env ack_pkt = Drop.
Proof. intro h. vm_compute. reflexivity. Qed.

(** A non-SYN/non-ACK TCP packet (a bare RST) falls through (NFT_CONTINUE) to the
    chain policy — the synproxy does not apply to it. *)
Theorem rst_pkt_continues : forall h, eval_chain_flat_verdict h synproxy_chain syn_env rst_pkt = Accept.
Proof. intro h. vm_compute. reflexivity. Qed.

(** A NON-TCP packet: the rule does not apply (NFT_BREAK), so the packet reaches
    the policy. *)
Theorem non_tcp_falls_through : forall h, eval_chain_flat_verdict h synproxy_chain syn_env non_tcp_pkt = Accept.
Proof. intro h. vm_compute. reflexivity. Qed.

(** The CENTRAL refutation: the synproxy rule is NOT a verdict no-op.  The
    no-op property ([forall p, eval_chain_flat_verdict h synproxy_chain e p = <policy>]) is
    FALSE — the SYN packet is a counterexample. *)
Theorem synproxy_is_NOT_verdict_noop :
  ~ (forall h e p, eval_chain_flat_verdict h synproxy_chain e p = c_policy synproxy_chain).
Proof.
  intro H. specialize (H Hinput syn_env syn_pkt). cbn [c_policy synproxy_chain] in H.
  rewrite (syn_pkt_stopped Hinput) in H. discriminate H.
Qed.

(** And it genuinely DECIDES the verdict differently for different packets — it is
    not constant. *)
Theorem synproxy_not_constant : forall h,
  eval_chain_flat_verdict h synproxy_chain syn_env syn_pkt <> eval_chain_flat_verdict h synproxy_chain syn_env rst_pkt.
Proof. intro h. rewrite (syn_pkt_stopped h), (rst_pkt_continues h). discriminate. Qed.

(** The compiled bytecode agrees (via [compile_chain_flat_verdict_correct]): the installed
    netlink program also stops the SYN packet, falls through the RST packet, and
    does not apply to a non-TCP packet. *)
Theorem syn_pkt_stopped_bytecode : forall h,
  run_chain_flat_verdict h (compile_chain synproxy_chain) (c_policy synproxy_chain) syn_env syn_pkt = Drop.
Proof.
  intro h. rewrite (compile_chain_flat_verdict_correct h) by (vm_compute; reflexivity).
  exact (syn_pkt_stopped h).
Qed.

Theorem rst_pkt_continues_bytecode : forall h,
  run_chain_flat_verdict h (compile_chain synproxy_chain) (c_policy synproxy_chain) syn_env rst_pkt = Accept.
Proof.
  intro h. rewrite (compile_chain_flat_verdict_correct h) by (vm_compute; reflexivity).
  exact (rst_pkt_continues h).
Qed.

Theorem non_tcp_falls_through_bytecode : forall h,
  run_chain_flat_verdict h (compile_chain synproxy_chain) (c_policy synproxy_chain) syn_env non_tcp_pkt = Accept.
Proof.
  intro h. rewrite (compile_chain_flat_verdict_correct h) by (vm_compute; reflexivity).
  exact (non_tcp_falls_through h).
Qed.
