(** Round-2 NAT-flow-state fix demonstration (was: RED audit probe).

    ── Kernel truth ─────────────────────────────────────────────────────────────
    nft_nat_eval (net/netfilter/nft_nat.c:103-126):
        struct nf_conn *ct = nf_ct_get(pkt->skb, &ctinfo);   // :109
        ...
        regs->verdict.code = nf_nat_setup_info(ct, &range, priv->type);  // :125
    nf_nat_setup_info (net/netfilter/nf_nat_core.c:771-836) opens with:
        // Can't setup nat info for confirmed ct.
        if (nf_ct_is_confirmed(ct))                 // :779
            return NF_ACCEPT;                       // :780
        ...
        get_unique_tuple(&new_tuple, &curr_tuple, range, ct, maniptype); // :796
        nf_conntrack_alter_reply(ct, &reply);       // :803  -- STORE mapping
    => The NAT mapping (new tuple) is computed from the rule operand and STORED into
       the conntrack entry on the FIRST (unconfirmed) packet of the flow ONLY.  Every
       LATER packet of the same flow is already CONFIRMED, so nf_nat_setup_info
       returns NF_ACCEPT immediately WITHOUT recomputing; the rewrite then comes from
       the STORED tuple (nf_nat_manip_pkt), INDEPENDENT of what the rule operand would
       evaluate to now.  Hence for `dnat to ip saddr`, every same-flow packet gets the
       destination chosen on packet 1, even if a later packet carries a different saddr.

    ── Model (AFTER the Round-2 fix) ────────────────────────────────────────────
    NAT is now FLOW-STATEFUL.  [env] carries a shared, flow-keyed NAT-mapping table
    [e_nat : data -> option (option data * option nat)].  [apply_nat] (Semantics.v)
    looks up [e_nat (pkt_flow p)]:
      - [None]  (first packet of the flow): compute the tuple from the operand
        ([nat_operand_addr]/[nat_pmin]), apply it, AND store it into [e_nat] —
        the kernel's get_unique_tuple + nf_conntrack_alter_reply on the unconfirmed
        packet.
      - [Some m] (every later, confirmed packet): apply the STORED tuple [m]
        verbatim, WITHOUT re-reading the operand — the kernel's
        `if (nf_ct_is_confirmed) return NF_ACCEPT` + nf_nat_manip_pkt-from-stored.
    So two same-flow packets with different saddrs both get the destination chosen on
    packet 1.  The old per-packet divergence is gone; below we PROVE the kernel-correct
    "same-flow packets share the stored mapping" property, axiom-free.

    This is the exact analogue of the Round-1 conntrack-mark fix, now for the NAT
    tuple. *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Packet Verdict Syntax Semantics.
Import ListNotations.

(* `dnat to ip saddr; accept`: destination-NAT the IPv4 dst to the packet's OWN
   source address (operand = a packet FIELD, so it varies per packet). *)
Definition dnat_to_saddr : nat_spec :=
  {| nat_imms := []; nat_field := Some (FIp4Saddr, []); nat_map := None;
     nat_src := None; nat_kind := nat_dnat_kind; nat_family := nat_fam_ip4;
     nat_amin := None; nat_amax := None; nat_pmin := None; nat_pmax := None;
     nat_flags := 0 |}.
Definition dnat_rule : rule :=
  {| r_body := []; r_verdict := Accept; r_vmap := None;
     r_nat := Some dnat_to_saddr; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.
Definition dnat_chain : chain := {| c_policy := Drop; c_rules := [ dnat_rule ] |}.

Definition out_daddr (p : packet) : data :=
  slice (pkt_nh (chain_out Hprerouting dnat_chain p)) 16 4.

(* A shared, empty env (so e_ct defaults to [], e_nat defaults to None — no NAT
   state established for any flow yet). *)
Definition env0 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddr := fun _ => []; e_ifaddr6 := fun _ => [];
     e_connlimit := fun _ => 0; e_ct := fun _ _ => []; e_nat := fun _ => None |}.

(* Two packets of the SAME flow (pkt_flow := [7;7]) but DIFFERENT source addresses
   (saddr @12..15): packet 1 = 1.1.1.1, packet 2 = 2.2.2.2.  A 20-byte IPv4 header;
   no L4 (pkt_have_l4 := false) so no checksum fixup confuses the daddr slot. *)
Definition mkpkt (e : env) (saddr : data) : packet :=
  {| pkt_env := e; pkt_meta := fun _ => []; pkt_ct := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := [];
     pkt_nh := [69;0;0;20; 0;0;0;0; 64;6; 0;0] ++ saddr ++ [9;9;9;9];
     pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l4 := false; pkt_fragoff := 0;
     pkt_flow := [7;7]; pkt_untracked := false |}.

(* Packet 1 of the flow, evaluated against the fresh (no-mapping) env. *)
Definition p1 : packet := mkpkt env0 [1;1;1;1].

(* The shared env AFTER packet 1 has been NAT'd: it now carries the established
   mapping at flow [7;7] (the dnat-to-saddr tuple computed from p1's saddr). *)
Definition env_after_p1 : env := pkt_env (chain_out Hprerouting dnat_chain p1).

(* Packet 2 of the SAME flow, but with a DIFFERENT source address (2.2.2.2), and —
   crucially — carrying the env produced by packet 1 (i.e. evaluated in the same
   flow context, exactly as [seq_eval_env]/[set_env] thread the shared state). *)
Definition p2 : packet := mkpkt env_after_p1 [2;2;2;2].

(* Same flow. *)
Lemma same_flow : pkt_flow p2 = pkt_flow p1.
Proof. reflexivity. Qed.

(* Packet 1 (first of the flow): the model dnat's destination to its OWN saddr
   (1.1.1.1) and STORES that mapping. *)
Lemma out_daddr_p1 : out_daddr p1 = [1;1;1;1].
Proof. vm_compute. reflexivity. Qed.

(* The mapping really was stored at flow [7;7] after packet 1. *)
Lemma mapping_stored_after_p1 :
  e_nat env_after_p1 [7;7] = Some (Some [1;1;1;1], None).
Proof. vm_compute. reflexivity. Qed.

(* KERNEL-CORRECT, and now PROVABLE: packet 2 of the SAME flow gets packet 1's
   stored destination (1.1.1.1), NOT its own saddr (2.2.2.2).  The model reuses the
   tuple established on packet 1 — exactly what the kernel does (confirmed ct ->
   rewrite from stored tuple).  This was UNPROVABLE before the Round-2 fix. *)
Lemma out_daddr_p2 : out_daddr p2 = [1;1;1;1].
Proof. vm_compute. reflexivity. Qed.

(* The headline property: two same-flow packets, despite different source
   addresses, receive the SAME dnat destination — the one established on packet 1. *)
Theorem same_flow_shares_stored_nat_mapping :
  pkt_flow p2 = pkt_flow p1 /\ out_daddr p1 = out_daddr p2.
Proof.
  split; [exact same_flow|].
  rewrite out_daddr_p1, out_daddr_p2. reflexivity.
Qed.

(* And explicitly: packet 2's destination is packet 1's saddr (the stored mapping),
   NOT packet 2's own saddr — the model now follows the stored tuple. *)
Theorem packet2_uses_packet1_mapping :
  out_daddr p2 = [1;1;1;1]            (* = packet 1's saddr, the stored mapping *)
  /\ out_daddr p2 <> [2;2;2;2].       (* NOT packet 2's own saddr *)
Proof.
  rewrite out_daddr_p2. split; [reflexivity | discriminate].
Qed.
