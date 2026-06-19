(** RED audit probe (Round 5), NOW the BLUE kernel-correct gate: NAT reply-direction
    is modelled FAITHFULLY (direction-aware un-NAT).

    ── Kernel truth ─────────────────────────────────────────────────────────────
    A NAT translation is DIRECTION-DEPENDENT.  nf_nat_packet (net/netfilter/
    nf_nat_core.c) runs on EVERY packet of a NATed (confirmed) flow and, for the
    REPLY direction, applies the INVERSE manip:

        enum ip_conntrack_dir dir = CTINFO2DIR(ctinfo);
        if (mtype == NF_NAT_MANIP_SRC) statusbit = IPS_SRC_NAT;
        else                           statusbit = IPS_DST_NAT;
        if (dir == IP_CT_DIR_REPLY) statusbit ^= IPS_NAT_MASK;   // INVERT for reply
        if (ct->status & statusbit) verdict = nf_nat_manip_pkt(skb, ct, mtype, dir);

    So for a `dnat to 8.8.8.8` established on the ORIGINAL-direction packet
    (client -> router; router's dst rewritten to 8.8.8.8), the REPLY packet
    (server 8.8.8.8 -> client) has its SOURCE un-DNAT'd from 8.8.8.8 back to the
    router address the client originally addressed (9.9.9.9).  The reply's
    DESTINATION (the client 1.1.1.1) is left untouched by a dnat.

    ── Model (AFTER the Round-5 fix) ────────────────────────────────────────────
    [e_nat] now stores the triple [(orig_addr, new_addr, port)] and the packet
    carries a direction bit [pkt_ctdir_orig] (the kernel's CTINFO2DIR(ctinfo)).
    [apply_nat]/[apply_nat_tuple] apply the stored tuple FORWARD on an
    original-direction packet and the INVERSE on a reply: a dnat restores the
    reply's SOURCE to [orig_addr] and leaves its DESTINATION untouched.  The
    formerly-provable backwards behaviour (re-applying the forward dnat on the
    reply destination, leaving the reply source stale) is now UNPROVABLE; the
    kernel-correct behaviour is proved below, axiom-free, by [vm_compute]. *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Packet Verdict Syntax Semantics.
Import ListNotations.

(* `dnat to 8.8.8.8; accept` — a FIXED destination NAT (immediate operand,
   reg 1 = 8.8.8.8), so the operand does not vary per packet. *)
Definition dnat_fixed : nat_spec :=
  {| nat_imms := [(1, [8;8;8;8])]; nat_field := None; nat_map := None;
     nat_src := None; nat_kind := nat_dnat_kind; nat_family := nat_fam_ip4;
     nat_amin := None; nat_amax := None; nat_pmin := None; nat_pmax := None;
     nat_flags := 0 |}.
Definition dnat_rule : rule :=
  {| r_body := []; r_verdict := Accept; r_vmap := None;
     r_nat := Some dnat_fixed; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.
Definition dnat_chain : chain := {| c_policy := Drop; c_rules := [ dnat_rule ] |}.

Definition out_daddr (p : packet) : data :=
  slice (pkt_nh (chain_out Hprerouting dnat_chain p)) 16 4.
Definition out_saddr (p : packet) : data :=
  slice (pkt_nh (chain_out Hprerouting dnat_chain p)) 12 4.

Definition env0 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddr := fun _ => []; e_ifaddr6 := fun _ => [];
     e_connlimit := fun _ => 0; e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

(* Build a packet with given env, source addr (@12..15), dest addr (@16..19), and
   conntrack direction [dir] ([true] = original, [false] = reply).  pkt_flow is
   DIRECTION-NORMALISED, so both the forward and reply packets of the connection
   carry the SAME flow id [7;7] (per Packet.v's contract) — direction is carried
   SEPARATELY by [pkt_ctdir_orig], exactly as the kernel keys by tuple but applies
   the manip by CTINFO2DIR. *)
Definition mkpkt (e : env) (saddr daddr : data) (dir : bool) : packet :=
  {| pkt_env := e; pkt_meta := fun _ => []; pkt_ct := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := [];
     pkt_nh := [69;0;0;20; 0;0;0;0; 64;6; 0;0] ++ saddr ++ daddr;
     pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l4 := false; pkt_fragoff := 0;
     pkt_flow := [7;7]; pkt_untracked := false; pkt_ctdir_orig := dir |}.

(* FORWARD (ORIGINAL) packet: client 1.1.1.1 -> router 9.9.9.9, direction = original. *)
Definition fwd : packet := mkpkt env0 [1;1;1;1] [9;9;9;9] true.

(* The shared env AFTER the forward packet has been dnat'd: it carries the
   established mapping at flow [7;7]. *)
Definition env_after_fwd : env := pkt_env (chain_out Hprerouting dnat_chain fwd).

(* Forward packet: dnat rewrites the DESTINATION 9.9.9.9 -> 8.8.8.8 (correct). *)
Lemma fwd_daddr : out_daddr fwd = [8;8;8;8].
Proof. vm_compute. reflexivity. Qed.

(* Mapping stored at the flow after the forward packet: the ORIGINAL destination
   (9.9.9.9, captured for the inverse) and the new destination (8.8.8.8). *)
Lemma mapping_stored : e_nat env_after_fwd [7;7] = Some (Some [9;9;9;9], Some [8;8;8;8], None).
Proof. vm_compute. reflexivity. Qed.

(* REPLY packet of the SAME flow: server 8.8.8.8 -> client 1.1.1.1, direction =
   reply ([pkt_ctdir_orig := false]), carrying the env established by the forward
   packet.  In the kernel this packet's SOURCE 8.8.8.8 is un-DNAT'd back to the
   router 9.9.9.9, and its DESTINATION (1.1.1.1) left UNTOUCHED. *)
Definition reply : packet := mkpkt env_after_fwd [8;8;8;8] [1;1;1;1] false.

(* Same flow (direction-normalised), per Packet.v's contract. *)
Lemma reply_same_flow : pkt_flow reply = pkt_flow fwd.
Proof. reflexivity. Qed.

(* ── THE KERNEL-CORRECT BEHAVIOUR (now PROVABLE, formerly false) ──────────────

   (A) The reply's SOURCE 8.8.8.8 is un-DNAT'd back to the router 9.9.9.9 — the
       inverse manip the kernel applies for the reply direction. *)
Lemma reply_saddr_undone : out_saddr reply = [9;9;9;9].
Proof. vm_compute. reflexivity. Qed.

(* (B) The reply's DESTINATION (the client 1.1.1.1) is LEFT UNTOUCHED — a dnat
       never rewrites the reply's destination. *)
Lemma reply_daddr_untouched : out_daddr reply = [1;1;1;1].
Proof. vm_compute. reflexivity. Qed.

(* Headline: the model's reply-direction NAT now MATCHES the kernel exactly.
   Kernel on the reply: saddr 8.8.8.8 -> 9.9.9.9, daddr 1.1.1.1 untouched.
   Model  on the reply: saddr 8.8.8.8 -> 9.9.9.9, daddr 1.1.1.1 untouched. *)
Theorem reply_nat_is_correct :
  out_saddr reply = [9;9;9;9]            (* un-DNAT'd back to the original address *)
  /\ out_daddr reply = [1;1;1;1].        (* destination left alone *)
Proof. split; [exact reply_saddr_undone | exact reply_daddr_untouched]. Qed.

(* The reply is NOT translated backwards anymore: its source is NO LONGER left at
   the dnat target, and its destination is NOT re-rewritten to the dnat target. *)
Theorem reply_nat_not_backwards :
  out_saddr reply <> [8;8;8;8]           (* source no longer stuck at the NAT target *)
  /\ out_daddr reply <> [8;8;8;8].       (* destination not re-NAT'd forward *)
Proof.
  split; [ rewrite reply_saddr_undone | rewrite reply_daddr_untouched ]; discriminate.
Qed.

(* Soundness corner: a reply-direction packet of a flow with NO established mapping
   ([e_nat = None]) is NOT translated at all (the kernel establishes the tuple only
   on the original-direction packet; an un-confirmed reply has no tuple to invert). *)
Definition reply_no_mapping : packet := mkpkt env0 [8;8;8;8] [1;1;1;1] false.
Theorem reply_unestablished_not_natted :
  out_saddr reply_no_mapping = [8;8;8;8] /\ out_daddr reply_no_mapping = [1;1;1;1].
Proof. split; vm_compute; reflexivity. Qed.
