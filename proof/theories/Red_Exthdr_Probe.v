(** An exthdr / TCP-option / IPv6-extension-header VALUE load HAS a not-present
    guard.  The kernel BREAKs the rule (it does not match) when the requested
    option / extension header is ABSENT, but ONLY for a VALUE load; an existence
    check (NFT_EXTHDR_F_PRESENT) stores 0 and never breaks
    (linux net/netfilter/nft_exthdr.c nft_exthdr_{tcp,ipv6,ipv4}_eval err path).

    In the model, [load_ok (LExthdr ep h _ _ pr)] is [true] for an existence load
    (pr=true) and [exthdr_present p ep h] for a VALUE load (pr=false), where
    [exthdr_present] is derived from the SAME existence oracle the F_PRESENT load
    reports on — so the impossible kernel state "option absent yet value=v" cannot
    fire a match.  Both DSL and VM route exthdr loads through this shared
    predicate (compile_chain_correct stays axiom-free).

    Regression gate: [exthdr_value_not_loadable_when_absent],
    [model_accepts_like_kernel]/[_mut], and [exthdr_existence_always_loadable]
    lock in the guard; a model regression to an always-succeeding exthdr value
    oracle (`tcp option maxseg size 1460 drop` matching a packet WITHOUT a maxseg
    option) makes them unprovable. *)
From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Packet Verdict Syntax Semantics.
Import ListNotations.

(* `tcp option maxseg size 1460` : a VALUE load of the maxseg option (htype=2),
   offset 2, length 2.  present=false => read the option's data bytes.
   1460 = 0x05B4 big-endian = [5;180]. *)
Definition maxseg_val : data := [5;180].
Definition F_maxseg : field := FExthdr EPtcpopt 2 2 2 false.

Definition maxseg_drop : rule :=
  {| r_body := [ BMatch (MEq F_maxseg maxseg_val) ];
     r_verdict := Drop; r_vmap := None; r_nat := None; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.

Definition filter_chain : chain :=
  {| c_policy := Accept; c_rules := [ maxseg_drop ] |}.

Definition env0 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => []; e_nat := fun _ => None;
     e_numgen := fun _ => 0 |}.

(* A packet WITHOUT a maxseg TCP option: the existence oracle (present=true)
   reports ABSENT ([0]).  In the kernel nft_exthdr_tcp_eval would `goto err`
   (NFT_BREAK) on the VALUE load, so the rule is SKIPPED and the chain ACCEPTS
   via its policy.  We deliberately make the value oracle return the matching
   bytes too (the impossible-in-kernel state "absent yet value matches") — the
   model must STILL accept, because the not-present guard refuses to load the
   value at all. *)
Definition pkt_no_maxseg : packet :=
  {| pkt_meta := fun _ => [];
     pkt_sock := fun _ => [];
     pkt_eh := fun _ _ _ _ pr => if pr then [0] else maxseg_val;
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => [];
     pkt_have_l2 := true; pkt_have_l4 := true; pkt_fragoff := 0;
     pkt_flow := [1;2;3;4]; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* A packet WITH a maxseg option present and value 1460: existence oracle returns
   [1] (present), value oracle returns the bytes.  The kernel matches -> DROP. *)
Definition pkt_with_maxseg : packet :=
  {| pkt_meta := fun _ => [];
     pkt_sock := fun _ => [];
     pkt_eh := fun _ _ _ _ pr => if pr then [1] else maxseg_val;
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => [];
     pkt_have_l2 := true; pkt_have_l4 := true; pkt_fragoff := 0;
     pkt_flow := [1;2;3;4]; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* The not-present guard: a VALUE load of the ABSENT option is NOT loadable. *)
Lemma exthdr_value_not_loadable_when_absent :
  field_loadable F_maxseg pkt_no_maxseg = false.
Proof. vm_compute. reflexivity. Qed.

(* The existence oracle reports the option ABSENT for this packet. *)
Lemma maxseg_option_is_absent :
  do_load (LExthdr EPtcpopt 2 0 0 true) env0 pkt_no_maxseg = [0].
Proof. vm_compute. reflexivity. Qed.

(* KERNEL-CORRECT: an absent maxseg option BREAKs the value load -> the rule does
   not match -> the chain ACCEPTS via its policy.  Holds via BOTH the pure
   evaluator and the stateful (mutation) evaluator. *)
Theorem model_accepts_like_kernel :
  eval_chain filter_chain env0 pkt_no_maxseg = Accept.
Proof. vm_compute. reflexivity. Qed.

Theorem model_accepts_like_kernel_mut :
  eval_chain_mut filter_chain env0 pkt_no_maxseg = Accept.
Proof. vm_compute. reflexivity. Qed.

(* KERNEL-CORRECT: a PRESENT maxseg option whose value matches 1460 DROPs. *)
Theorem model_drops_when_present :
  eval_chain filter_chain env0 pkt_with_maxseg = Drop.
Proof. vm_compute. reflexivity. Qed.

Theorem model_drops_when_present_mut :
  eval_chain_mut filter_chain env0 pkt_with_maxseg = Drop.
Proof. vm_compute. reflexivity. Qed.

(* An EXISTENCE check (present=true) is always loadable even when absent — the
   kernel stores 0 on the err path under F_PRESENT, it never breaks. *)
Lemma exthdr_existence_always_loadable :
  field_loadable (FExthdr EPtcpopt 2 0 0 true) pkt_no_maxseg = true.
Proof. vm_compute. reflexivity. Qed.
