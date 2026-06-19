(** RED probe (now BLUE-corrected): single-rule `ct notrack ct state untracked accept`.

    Kernel: a rule's expressions run LEFT TO RIGHT against the running packet
    (nf_tables_core.c nft_rule_dp_for_each_expr).  `ct notrack` sets
    ctinfo=IP_CT_UNTRACKED (nft_notrack_eval, nft_ct.c), then the SAME rule's
    `ct state untracked` match (nft_ct_get_eval NFT_CT_STATE, nft_ct.c) reads
    NF_CT_STATE_UNTRACKED_BIT (=64) and SUCCEEDS.  => the kernel ACCEPTS every
    packet, regardless of its prior tracking state.

    BEFORE the fix the model SKIPPED the `notrack` statement when walking a rule's
    matches ([rule_applies_walk]), so `ct state untracked` read the stale per-packet
    ct oracle (here `new`=8), the match FAILED, and the chain fell through to its
    Drop policy — a provable kernel-false DROP.

    The fix threads [set_untracked] into a rule's OWN later matches/terminal
    ([rule_applies_walk]/[outcome]/[run_rule] all thread it past [SNotrack]/[INotrack]),
    so the model now ACCEPTS, matching the kernel.  The OLD Drop theorems are now
    UNPROVABLE; below are the corrected kernel-faithful ACCEPT theorems, proved
    axiom-free by [vm_compute]. *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Packet Verdict Syntax Semantics.
Import ListNotations.

Definition untracked_bytes : data := [0;0;0;64].

Definition m_untracked : matchcond :=
  MMasked FCtState true untracked_bytes [0;0;0;0] [0;0;0;0].

(* ONE rule: notrack THEN ct state untracked accept (statement before match). *)
Definition intra_rule : rule :=
  {| r_body := [ BStmt SNotrack ; BMatch m_untracked ];
     r_verdict := Accept; r_vmap := None; r_nat := None; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.

Definition intra_chain : chain :=
  {| c_policy := Drop; c_rules := [ intra_rule ] |}.

Definition env0 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddr := fun _ => []; e_ifaddr6 := fun _ => [];
     e_connlimit := fun _ => 0; e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

(* ct oracle = new (8): a genuinely tracked, new connection. *)
Definition pkt_new : packet :=
  {| pkt_env := env0; pkt_meta := fun _ => [];
     pkt_ct := fun k => match k with CKstate => [0;0;0;8] | _ => [] end;
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := false; pkt_fragoff := 0;
     pkt_flow := [7;7]; pkt_untracked := false; pkt_ctdir_orig := true |}.

(* The intra-rule `notrack` now latches IP_CT_UNTRACKED before the SAME rule's
   `ct state untracked` match, which therefore SUCCEEDS — the rule applies. *)
Lemma intra_match_succeeds_after_notrack :
  rule_applies intra_rule pkt_new = true.
Proof. vm_compute. reflexivity. Qed.

(* KERNEL-FAITHFUL: the model now ACCEPTS the packet the kernel ACCEPTS. *)
Theorem model_accepts_like_kernel_eval_chain :
  eval_chain intra_chain pkt_new = Accept.
Proof. vm_compute. reflexivity. Qed.

(* The stateful threading evaluator agrees. *)
Theorem model_accepts_like_kernel_eval_chain_mut :
  eval_chain_mut intra_chain pkt_new = Accept.
Proof. vm_compute. reflexivity. Qed.

(* The accept holds REGARDLESS of the packet's prior ct-state oracle: even a packet
   whose oracle is some arbitrary tracked value is accepted (the kernel forces
   untracked).  We demonstrate with a second oracle value (`established`=2). *)
Definition pkt_est : packet :=
  {| pkt_env := env0; pkt_meta := fun _ => [];
     pkt_ct := fun k => match k with CKstate => [0;0;0;2] | _ => [] end;
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := false; pkt_fragoff := 0;
     pkt_flow := [9;9]; pkt_untracked := false; pkt_ctdir_orig := true |}.

Theorem model_accepts_regardless_of_prior_state :
  eval_chain intra_chain pkt_est = Accept.
Proof. vm_compute. reflexivity. Qed.
