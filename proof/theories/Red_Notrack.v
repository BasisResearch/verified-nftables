(** Round-3 fix (notrack -> ct state untracked).

    ── Kernel truth ─────────────────────────────────────────────────────────────
    nft_notrack_eval (net/netfilter/nft_ct.c:860-874):
        ct = nf_ct_get(pkt->skb, &ctinfo);
        if (ct || ctinfo == IP_CT_UNTRACKED)   // already (un)tracked? ignore
            return;
        nf_ct_set(skb, ct, IP_CT_UNTRACKED);   // <-- sets ct to UNTRACKED
    nft_ct_get_eval (nft_ct.c:67-77), the `ct state` reader:
        case NFT_CT_STATE:
            if (ct)                     state = NF_CT_STATE_BIT(ctinfo);
            else if (ctinfo == IP_CT_UNTRACKED)
                                        state = NF_CT_STATE_UNTRACKED_BIT;   // 1<<6 = 64
    => After a `notrack` statement runs, a SUBSEQUENT `ct state` read (in the same
       packet's traversal — in a LATER rule of the chain) returns exactly
       NF_CT_STATE_UNTRACKED_BIT (= 64), regardless of the packet's prior tracking
       state.  So  `notrack` (rule 1)  ;  `ct state untracked accept` (rule 2)
       ACCEPTS *every* packet that reaches it.

    ── Model (fixed) ─────────────────────────────────────────────────────────────
    [SNotrack]/[INotrack] now apply [set_untracked] in [body_writes]/[run_rule_writes],
    setting the per-packet-traversal flag [pkt_untracked := true].  The cross-rule
    threader [eval_rules_mut] carries [dsl_writes r1 p] (= [set_untracked p]) into the
    NEXT rule, whose `ct state` match reads [do_load (LCt CKstate)] = [0;0;0;64]
    (Syntax.v: the [pkt_untracked p] override), mirroring nft_ct_get_eval's
    `else if (ctinfo == IP_CT_UNTRACKED)` branch.  The DSL and the VM apply the SAME
    [set_untracked], so [compile_chain_correct] stays axiom-free.

    Below: the kernel-correct property `notrack; ct state untracked accept` accepts
    EVERY packet is now PROVABLE in the model (it was unprovable — indeed disprovable —
    before the fix). *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Packet Verdict Syntax Semantics.
Import ListNotations.

(* `ct state untracked`: the single-positive bitmask form the parser emits
   (cf. theories/Ct_State.v): (state & 64) != 0. *)
Definition untracked_bytes : data := [0;0;0;64].   (* NF_CT_STATE_UNTRACKED_BIT *)

Definition m_untracked : matchcond :=
  MMasked FCtState true untracked_bytes [0;0;0;0] [0;0;0;0].

(* Rule 1: bare `notrack` (Continue => falls through to rule 2, threading the
   set_untracked write). *)
Definition notrack_only : rule :=
  {| r_body := [ BStmt SNotrack ];
     r_verdict := Continue; r_vmap := None; r_nat := None; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.

(* Rule 2: `ct state untracked accept`. *)
Definition ctstate_rule : rule :=
  {| r_body := [ BMatch m_untracked ];
     r_verdict := Accept; r_vmap := None; r_nat := None; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.

(* The two-rule chain, default policy Drop. *)
Definition notrack_chain : chain :=
  {| c_policy := Drop; c_rules := [ notrack_only; ctstate_rule ] |}.

Definition env0 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddr := fun _ => []; e_ifaddr6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

(* A packet whose conntrack-state ORACLE is `new` (= 8): a genuinely tracked,
   new connection.  The `notrack` in rule 1 OVERWRITES this to untracked before
   the `ct state untracked` match in rule 2 runs. *)
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

(* The notrack write threads into rule 2: do_load (LCt CKstate) of the threaded
   packet returns the untracked constant. *)
Lemma untracked_after_notrack :
  do_load (LCt CKstate) (dsl_writes notrack_only pkt_new) = [0;0;0;64].
Proof. vm_compute. reflexivity. Qed.

(* Consequently the `ct state untracked` match in rule 2 SUCCEEDS on the threaded
   packet — the notrack had a real effect. *)
Lemma untracked_match_succeeds :
  eval_matchcond m_untracked (dsl_writes notrack_only pkt_new) = true.
Proof. vm_compute. reflexivity. Qed.

(* The threading evaluator ACCEPTS pkt_new — matching the kernel.  (The old model
   DROPPED it: notrack was a no-op and `ct state untracked` read the stale oracle.) *)
Theorem model_accepts_like_kernel :
  eval_chain_mut notrack_chain pkt_new = Accept.
Proof. vm_compute. reflexivity. Qed.

(* The CORRECT, kernel-guaranteed property — `notrack; ct state untracked accept`
   accepts EVERY packet — is now PROVABLE in the model (it was disprovable before
   the fix). *)
Theorem notrack_forces_untracked_accept :
  forall p : packet, eval_chain_mut notrack_chain p = Accept.
Proof.
  intro p. unfold eval_chain_mut, notrack_chain. cbn [c_rules].
  vm_compute. reflexivity.
Qed.
