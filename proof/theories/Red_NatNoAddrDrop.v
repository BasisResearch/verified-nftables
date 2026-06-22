(** * NAT-core NF_DROP when the interface has no usable address (Round-3 fix)

    The kernel's NAT core DROPS a packet when the interface it must take an address
    FROM has no usable address:

    - [nf_nat_redirect_ipv4] (PREROUTING branch): computes [newdst] from the inbound
      device's primary IPv4 address and `if (!newdst.ip) return NF_DROP;`
      (net/netfilter/nf_nat_redirect.c:71-74).  At the OUTPUT hook redirect always
      targets the loopback address, so it never drops there.

    - [nf_nat_masquerade_ipv4] (POSTROUTING): `newsrc = inet_select_addr(out,...)`
      and `if (!newsrc) { ...; return NF_DROP; }`
      (net/netfilter/nf_nat_masquerade.c:54-58); the IPv6 path likewise drops on
      [nat_ipv6_dev_get_saddr] < 0.

    Before this fix the Rocq trace had NO drop path: [apply_nat] unconditionally
    spliced the (possibly EMPTY) interface address into the dest/source slot and the
    rule's terminal verdict was returned verbatim — so `redirect; accept` /
    `masquerade; accept` always yielded Accept even when the interface had no
    address, AND wrote a corrupt zero-length address.

    This theory proves the FIXED behaviour: at PREROUTING/POSTROUTING with an
    address-less interface ([e_ifaddr _ = []]) the trace verdict is now [Drop], and
    no corrupt address is spliced (the packet is left unrewritten).  It also confirms
    the kernel's NON-drop cases stay Accept: redirect at OUTPUT (loopback target), and
    redirect/masquerade when the interface HAS an address. *)
From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Packet Verdict Syntax Semantics.
Import ListNotations.

(* ---- redirect; accept at PREROUTING ---- *)
Definition redir_spec : nat_spec :=
  {| nat_imms := []; nat_field := None; nat_map := None;
     nat_src := None; nat_kind := nat_redir_kind; nat_family := nat_fam_ip4;
     nat_amin := None; nat_amax := None; nat_pmin := None; nat_pmax := None;
     nat_flags := 0 |}.
Definition redir_rule : rule :=
  {| r_body := []; r_verdict := Accept; r_vmap := None;
     r_nat := Some redir_spec; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.
Definition redir_chain : chain := {| c_policy := Drop; c_rules := [ redir_rule ] |}.

(* ---- masquerade; accept at POSTROUTING ---- *)
Definition masq_spec : nat_spec :=
  {| nat_imms := []; nat_field := None; nat_map := None;
     nat_src := None; nat_kind := nat_masq_kind; nat_family := nat_fam_ip4;
     nat_amin := None; nat_amax := None; nat_pmin := None; nat_pmax := None;
     nat_flags := 0 |}.
Definition masq_rule : rule :=
  {| r_body := []; r_verdict := Accept; r_vmap := None;
     r_nat := Some masq_spec; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.
Definition masq_chain : chain := {| c_policy := Drop; c_rules := [ masq_rule ] |}.

(* env where NO interface has an IPv4 address: e_ifaddr _ = [].  This is exactly the
   kernel's `if (!newdst.ip)` / `if (!newsrc)` condition. *)
Definition env_noaddr : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddr := fun _ => []; e_ifaddr6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => []; e_nat := fun _ => None;
     e_numgen := fun _ => 0 |}.

(* env where the interface HAS an address (1.2.3.4) — the kernel's non-drop case. *)
Definition env_withaddr : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddr := fun _ => [1;2;3;4]; e_ifaddr6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => []; e_nat := fun _ => None;
     e_numgen := fun _ => 0 |}.

Definition mk_pkt (e : env) : packet :=
  {| pkt_env := e; pkt_meta := fun _ => []; pkt_ct := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := [];
     pkt_nh := [69;0;0;20; 0;0;0;0; 64;6; 0;0] ++ [1;1;1;1] ++ [9;9;9;9];
     pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := false;
     pkt_fragoff := 0;
     pkt_flow := [7;7]; pkt_untracked := false; pkt_ctdir_orig := true;
     pkt_ct_present := true |}.

Definition pkt_noaddr   : packet := mk_pkt env_noaddr.
Definition pkt_withaddr : packet := mk_pkt env_withaddr.

(** ** The FIX: address-less interface => the kernel's NF_DROP, modelled. *)

(* redirect at PREROUTING over an address-less interface now DROPS. *)
Theorem redirect_no_inbound_address_drops :
  eval_chain_trace Hprerouting redir_chain pkt_noaddr = (Drop, pkt_noaddr).
Proof. vm_compute. reflexivity. Qed.

(* masquerade at POSTROUTING over an address-less interface now DROPS. *)
Theorem masquerade_no_exit_address_drops :
  eval_chain_trace Hpostrouting masq_chain pkt_noaddr = (Drop, pkt_noaddr).
Proof. vm_compute. reflexivity. Qed.

(* and the packet is left UNREWRITTEN — no corrupt empty address spliced into the
   destination slot (the drop happens before the address is applied). *)
Theorem redirect_drop_leaves_packet_unrewritten :
  snd (eval_chain_trace Hprerouting redir_chain pkt_noaddr) = pkt_noaddr.
Proof. vm_compute. reflexivity. Qed.

(** ** The kernel's NON-drop cases stay Accept. *)

(* redirect at the OUTPUT hook always targets the loopback address, so it never
   drops even with an address-less interface (nf_nat_redirect_ipv4 LOCAL_OUT). *)
Theorem redirect_output_loopback_accepts :
  fst (eval_chain_trace Houtput redir_chain pkt_noaddr) = Accept.
Proof. vm_compute. reflexivity. Qed.

(* with an interface that HAS an address, redirect/masquerade accept (and rewrite). *)
Theorem redirect_with_address_accepts :
  fst (eval_chain_trace Hprerouting redir_chain pkt_withaddr) = Accept.
Proof. vm_compute. reflexivity. Qed.

Theorem masquerade_with_address_accepts :
  fst (eval_chain_trace Hpostrouting masq_chain pkt_withaddr) = Accept.
Proof. vm_compute. reflexivity. Qed.

(* The control-plane (compiler / [eval_chain_mut]) verdict is UNAFFECTED: the NAT
   drop is a pure DATA-PLANE refinement living only in the trace, so the verified
   mut verdict (what [compile_chain_correct] is about) still says Accept.  This is
   exactly the gap the trace now closes. *)
Theorem mut_unaffected_still_accepts :
  eval_chain_mut redir_chain pkt_noaddr = Accept
  /\ eval_chain_mut masq_chain pkt_noaddr = Accept.
Proof. split; vm_compute; reflexivity. Qed.

(* And the trace/mut verdicts now genuinely DIFFER on this packet, tracked exactly
   by [trace_nat_drops] (the conditional in the corrected [eval_chain_trace_verdict]). *)
Theorem trace_diverges_from_mut_via_nat_drop :
  trace_nat_drops Hprerouting (c_rules redir_chain) pkt_noaddr = true
  /\ fst (eval_chain_trace Hprerouting redir_chain pkt_noaddr) <> eval_chain_mut redir_chain pkt_noaddr.
Proof. split; [reflexivity | vm_compute; discriminate]. Qed.
