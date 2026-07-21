(** Intra-rule statement threading: single-rule `ct notrack ct state untracked
    accept` — the `notrack` latch is visible to the SAME rule's later matches.

    SCOPE: since the single-fold rule semantics ([rule_step]/[run_rule_step],
    Semantics.v) EVERY intra-rule write is threaded — meta/ct sets and dynset
    env writes included (positive pins: Regression/Setread_IntraRule.v).
    This file pins the `notrack` instance specifically, including its
    entry-present NO-OP kernel guard; Notrack_CrossRule.v is the cross-rule
    analogue.

    Kernel: a rule's expressions run LEFT TO RIGHT against the running packet
    (nf_tables_core.c nft_rule_dp_for_each_expr).  `ct notrack` (nft_notrack_eval,
    nft_ct.c:860-874) is GUARDED:
        ct = nf_ct_get(pkt->skb, &ctinfo);
        if (ct || ctinfo == IP_CT_UNTRACKED) return;   // entry present => NO-OP
        nf_ct_set(skb, ct, IP_CT_UNTRACKED);
    so it sets ctinfo=IP_CT_UNTRACKED ONLY on a packet that has NO conntrack entry
    yet (ct == NULL).  On such a no-entry packet the SAME rule's `ct state untracked`
    match (nft_ct_get_eval NFT_CT_STATE) then reads NF_CT_STATE_UNTRACKED_BIT (=64)
    and SUCCEEDS, so the kernel ACCEPTS.  On a packet that ALREADY has an entry the
    `notrack` is a no-op and `ct state untracked` reads the entry's real state.

    In the model, [body_step]/[rule_step]/[run_rule_step] all thread
    [set_untracked] past [SNotrack]/[INotrack] into the rule's OWN later
    matches/terminal, and [set_untracked] mirrors the kernel guard exactly (it is
    a NO-OP when [pkt_ct_present = true]) — so the model ACCEPTS a NO-ENTRY packet
    and leaves an entry-present packet's state untouched.  All theorems below are
    proved axiom-free by [vm_compute].

    Regression gate: [model_accepts_like_kernel_eval_chain_mut] and
    [model_drops_entry_present_packet] lock in the intra-rule threading + guard;
    a model that skips statements when walking a rule's matches (the `ct state
    untracked` match never seeing the same rule's `notrack` latch) makes them
    unprovable. *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Packet Verdict Bytecode Syntax Semantics.
Import ListNotations.

(* Pins below hold at EVERY netfilter hook [h] (no rule here carries a NAT
   terminal, so the hook is inert); the section generalizes each statement. *)
Section AtHook.
Context (h : hook_id).

Definition untracked_bytes : data := [0;0;0;64].

Definition m_untracked : matchcond :=
  MMasked FCtState CNe untracked_bytes [0;0;0;0] [0;0;0;0].

(* ONE rule: notrack THEN ct state untracked accept (statement before match). *)
Definition intra_rule : rule :=
  {| r_body := [ BStmt SNotrack ; BMatch m_untracked ];
     r_outcome := OVerdict Accept; r_after := [] |}.

Definition intra_chain : chain :=
  {| c_policy := Drop; c_rules := [ intra_rule ] |}.

Definition env0 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

(* A NO-ENTRY packet ([pkt_ct_present := false]): nf_ct_get returns NULL, so this
   is exactly the case where `notrack` HAS an effect (ct == NULL).  Its ct-state
   oracle is irrelevant on this branch (do_load's CKstate reads the UNTRACKED latch,
   not the [pkt_ct_present = false] INVALID value, once notrack has run). *)
Definition pkt_noentry : packet :=
  {| pkt_meta := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := false; pkt_fragoff := 0;
     pkt_flow := [7;7]; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := false |}.

(* On the NO-ENTRY packet the intra-rule `notrack` latches IP_CT_UNTRACKED before
   the SAME rule's `ct state untracked` match, which therefore SUCCEEDS, so the
   rule fires (its [rule_step] produces a verdict). *)
Lemma intra_match_succeeds_after_notrack :
  fst (rule_step h intra_rule env0 pkt_noentry) = Some Accept.
Proof. vm_compute. reflexivity. Qed.

(* KERNEL-FAITHFUL: the model ACCEPTS the no-entry packet the kernel ACCEPTS, on
   the canonical stateful threading evaluator. *)
Theorem model_accepts_like_kernel_eval_chain_mut :
  eval_chain_mut h intra_chain env0 pkt_noentry = Accept.
Proof. vm_compute. reflexivity. Qed.

(* KERNEL GUARD: on a packet that ALREADY has a conntrack ENTRY
   ([pkt_ct_present := true], here ESTABLISHED=2), `notrack` is a NO-OP — the
   `ct state untracked` match reads the entry's REAL state (not the UNTRACKED bit),
   the match FAILS, and the chain falls through to its Drop policy.  This is exactly
   nft_notrack_eval's `if (ct || ctinfo == IP_CT_UNTRACKED) return;`. *)
(* Env recording the live conntrack entry's state as ESTABLISHED ([0;0;0;2]);
   [do_load (LCt CKstate)] reads [e_ct e] at the packet's flow, so the
   live state lives in the shared flow-keyed table. *)
Definition env_est : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => [];
     e_ct := fun _ k => match k with CKstate => [0;0;0;2] | _ => [] end;
     e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

Definition pkt_est : packet :=
  {| pkt_meta := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := false; pkt_fragoff := 0;
     pkt_flow := [9;9]; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* notrack is a no-op on the entry-present packet: its ct state is read as the live
   ESTABLISHED value, so `ct state untracked` does NOT match and the rule is
   skipped (its [rule_step] produces no verdict). *)
Lemma intra_match_noop_on_entry :
  fst (rule_step h intra_rule env_est pkt_est) = None.
Proof. vm_compute. reflexivity. Qed.

Theorem model_drops_entry_present_packet :
  eval_chain_mut h intra_chain env_est pkt_est = Drop.
Proof. vm_compute. reflexivity. Qed.

End AtHook.
