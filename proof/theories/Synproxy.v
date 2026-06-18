(** * SYN-proxy is verdict-bearing, NOT a no-op.

    The red agent showed the model was UNSOUND: the `synproxy` statement was
    verdict-neutral, so a rule whose only action is `synproxy` was a complete
    verdict no-op ([eval_chain {synproxy} p = policy] for EVERY packet).  The
    kernel (net/netfilter/nft_synproxy.c, nft_synproxy_do_eval / _eval_v4)
    disagrees in every interesting case:

      - non-TCP packet  => NFT_BREAK (line 117): the rule does NOT apply;
      - TCP SYN         => NF_STOLEN (line 61): the SYN is answered with a
                           syncookie SYN+ACK and consumed — traversal STOPS;
      - TCP client ACK  => NF_STOLEN (valid) / NF_DROP (rejected) — STOPS;
      - other TCP       => implicit NFT_CONTINUE (fall through).

    The fix models the control-flow outcome the single-packet semantics can see:
    a non-TCP packet makes the rule unloadable (NFT_BREAK, via the TCP-flags
    transport load), a SYN/ACK packet STOPS traversal — modelled as the terminal
    verdict [Drop] (the documented behaviour: doc/statements.txt:55, "reject and
    synproxy internally issue a drop verdict at the end of their respective
    actions"; the syncookie side effect of STOLEN is below the model's single-
    packet resolution, exactly as Reject's ICMP / Queue's hand-off are), and a
    non-SYN/non-ACK TCP packet falls through (NFT_CONTINUE).

    These theorems witness that the model is no longer the verdict no-op the red
    agent exploited, and that the compiled bytecode agrees (via
    [compile_chain_correct]). *)

From Stdlib Require Import List String Bool.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Compile Correct.
Import ListNotations.

Definition syn_env : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_ifaddr := fun _ => []; e_ifaddr6 := fun _ => [];
     e_limit := fun _ => 0; e_quota := fun _ => 0; e_connlimit := fun _ => 0 |}.

(** A 20-byte TCP header whose flags byte (offset 13) is [fl]. *)
Definition tcp_hdr (fl : nat) : list byte :=
  [0;0;0;0; 0;0;0;0; 0;0;0;0; 0; fl; 0;0; 0;0;0;0].

Definition mk_tcp_pkt (fl : nat) : packet :=
  {| pkt_env := syn_env;
     pkt_meta := fun _ => []; pkt_ct := fun _ => []; pkt_sock := fun _ => [];
     pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := tcp_hdr fl; pkt_ih := []; pkt_tnl := [];
     pkt_fibkey := fun _ => []; pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => [];
     pkt_have_l4 := true;       (* a parsed TCP header *)
     pkt_fragoff := 0 |}.

(** A non-TCP packet: no L4 header parsed (the kernel's NFT_BREAK arm). *)
Definition non_tcp_pkt : packet :=
  {| pkt_env := syn_env;
     pkt_meta := fun _ => []; pkt_ct := fun _ => []; pkt_sock := fun _ => [];
     pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := []; pkt_tnl := [];
     pkt_fibkey := fun _ => []; pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => [];
     pkt_have_l4 := false; pkt_fragoff := 0 |}.

Definition syn_pkt  : packet := mk_tcp_pkt 2.   (* SYN  = 0x02 *)
Definition ack_pkt  : packet := mk_tcp_pkt 16.  (* ACK  = 0x10 *)
Definition rst_pkt  : packet := mk_tcp_pkt 4.   (* RST  = 0x04 (neither SYN nor ACK) *)

(** A chain whose ONLY rule is `synproxy mss 1460 wscale 7`, with policy Accept.
    (Accept, not Drop, so that a [Drop] outcome can only come FROM the synproxy.) *)
Definition synproxy_rule : rule :=
  {| r_body := [ BStmt (SSynproxy 1460 7) ]; r_verdict := Continue;
     r_vmap := None; r_nat := None; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.
Definition synproxy_chain : chain :=
  {| c_policy := Accept; c_rules := [ synproxy_rule ] |}.

(** *** The red agent's no-op is gone: a SYN packet STOPS at the synproxy. *)
Theorem syn_pkt_stopped : eval_chain synproxy_chain syn_pkt = Drop.
Proof. reflexivity. Qed.

(** An ACK packet likewise stops (kernel: STOLEN valid / DROP rejected). *)
Theorem ack_pkt_stopped : eval_chain synproxy_chain ack_pkt = Drop.
Proof. reflexivity. Qed.

(** A non-SYN/non-ACK TCP packet (a bare RST) falls through (NFT_CONTINUE) to the
    chain policy — the synproxy does not apply to it. *)
Theorem rst_pkt_continues : eval_chain synproxy_chain rst_pkt = Accept.
Proof. reflexivity. Qed.

(** A NON-TCP packet: the rule does not apply (NFT_BREAK), so the packet reaches
    the policy. *)
Theorem non_tcp_falls_through : eval_chain synproxy_chain non_tcp_pkt = Accept.
Proof. reflexivity. Qed.

(** The CENTRAL refutation of the red agent's incorrect property: the synproxy
    rule is NOT a verdict no-op.  The analogue of [synproxy_is_verdict_noop]
    ([forall p, eval_chain synproxy_chain p = <policy>]) is FALSE — the SYN packet
    is a counterexample. *)
Theorem synproxy_is_NOT_verdict_noop :
  ~ (forall p, eval_chain synproxy_chain p = c_policy synproxy_chain).
Proof.
  intro H. specialize (H syn_pkt). cbn [c_policy synproxy_chain] in H.
  rewrite syn_pkt_stopped in H. discriminate H.
Qed.

(** And it genuinely DECIDES the verdict differently for different packets — it is
    not constant. *)
Theorem synproxy_not_constant :
  eval_chain synproxy_chain syn_pkt <> eval_chain synproxy_chain rst_pkt.
Proof. rewrite syn_pkt_stopped, rst_pkt_continues. discriminate. Qed.

(** The compiled bytecode agrees (via [compile_chain_correct]): the installed
    netlink program also stops the SYN packet, falls through the RST packet, and
    does not apply to a non-TCP packet. *)
Theorem syn_pkt_stopped_bytecode :
  run_chain (compile_chain synproxy_chain) (c_policy synproxy_chain) syn_pkt = Drop.
Proof. rewrite compile_chain_correct. apply syn_pkt_stopped. Qed.

Theorem rst_pkt_continues_bytecode :
  run_chain (compile_chain synproxy_chain) (c_policy synproxy_chain) rst_pkt = Accept.
Proof. rewrite compile_chain_correct. apply rst_pkt_continues. Qed.

Theorem non_tcp_falls_through_bytecode :
  run_chain (compile_chain synproxy_chain) (c_policy synproxy_chain) non_tcp_pkt = Accept.
Proof. rewrite compile_chain_correct. apply non_tcp_falls_through. Qed.
