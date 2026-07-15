(** NAT reply-direction: a stored NAT tuple is applied FORWARD on
    original-direction packets and INVERTED on reply-direction packets
    (direction-aware un-NAT).

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

    ── Model ────────────────────────────────────────────────────────────────────
    [e_nat] stores the tuple [(orig_addr, new_addr, new_port, orig_port)] and the
    packet carries a direction bit [pkt_ctdir_orig] (the kernel's
    CTINFO2DIR(ctinfo)).  [apply_nat]/[apply_nat_tuple] apply the stored tuple
    FORWARD on an original-direction packet and the INVERSE on a reply: a dnat
    restores the reply's SOURCE to [orig_addr] and leaves its DESTINATION
    untouched.

    Regression gate: [reply_nat_is_correct], [reply_nat_not_backwards], and
    [reply_sport_undone] lock in the direction-aware inverse; a model regression
    to direction-blind NAT (re-applying the forward dnat on the reply destination
    and leaving the reply source/port stale at the NAT target) makes them
    unprovable. *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Packet Verdict Syntax Semantics.
Import ListNotations.

(* `dnat to 8.8.8.8; accept` — a FIXED destination NAT (immediate operand,
   reg 1 = 8.8.8.8), so the operand does not vary per packet. *)
Definition dnat_fixed : nat_spec :=
  {| nat_addr_imm := Some [8;8;8;8]; nat_field := None; nat_map := None;
     nat_src := None; nat_kind := nat_dnat_kind; nat_family := nat_fam_ip4;
     nat_extra := NXnone;
     nat_flags := 0 |}.
Definition dnat_rule : rule :=
  {| r_body := []; r_verdict := Accept; r_vmap := None;
     r_nat := Some dnat_fixed; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.
Definition dnat_chain : chain := {| c_policy := Drop; c_rules := [ dnat_rule ] |}.

Definition out_daddr (e : env) (p : packet) : data :=
  slice (pkt_nh (chain_out Hprerouting dnat_chain e p)) 16 4.
Definition out_saddr (e : env) (p : packet) : data :=
  slice (pkt_nh (chain_out Hprerouting dnat_chain e p)) 12 4.

Definition env0 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

(* Build a packet with given env, source addr (@12..15), dest addr (@16..19), and
   conntrack direction [dir] ([true] = original, [false] = reply).  pkt_flow is
   DIRECTION-NORMALISED, so both the forward and reply packets of the connection
   carry the SAME flow id [7;7] (per Packet.v's contract) — direction is carried
   SEPARATELY by [pkt_ctdir_orig], exactly as the kernel keys by tuple but applies
   the manip by CTINFO2DIR. *)
Definition mkpkt (saddr daddr : data) (dir : bool) : packet :=
  {| pkt_meta := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := [];
     pkt_nh := [69;0;0;20; 0;0;0;0; 64;6; 0;0] ++ saddr ++ daddr;
     pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := false; pkt_fragoff := 0;
     pkt_flow := [7;7]; pkt_untracked := false; pkt_ctdir_orig := dir; pkt_ct_present := true |}.

(* FORWARD (ORIGINAL) packet: client 1.1.1.1 -> router 9.9.9.9, direction = original. *)
Definition fwd : packet := mkpkt [1;1;1;1] [9;9;9;9] true.

(* The shared env AFTER the forward packet has been dnat'd: it carries the
   established mapping at flow [7;7]. *)
Definition env_after_fwd : env := chain_out_env Hprerouting dnat_chain env0 fwd.

(* Forward packet: dnat rewrites the DESTINATION 9.9.9.9 -> 8.8.8.8 (correct). *)
Lemma fwd_daddr : out_daddr env0 fwd = [8;8;8;8].
Proof. vm_compute. reflexivity. Qed.

(* Mapping stored at the flow after the forward packet: the ORIGINAL destination
   (9.9.9.9, captured for the inverse) and the new destination (8.8.8.8). *)
Lemma mapping_stored : e_nat env_after_fwd [7;7] = Some (Some [9;9;9;9], Some [8;8;8;8], None, None).
Proof. vm_compute. reflexivity. Qed.

(* REPLY packet of the SAME flow: server 8.8.8.8 -> client 1.1.1.1, direction =
   reply ([pkt_ctdir_orig := false]), carrying the env established by the forward
   packet.  In the kernel this packet's SOURCE 8.8.8.8 is un-DNAT'd back to the
   router 9.9.9.9, and its DESTINATION (1.1.1.1) left UNTOUCHED. *)
Definition reply : packet := mkpkt [8;8;8;8] [1;1;1;1] false.

(* Same flow (direction-normalised), per Packet.v's contract. *)
Lemma reply_same_flow : pkt_flow reply = pkt_flow fwd.
Proof. reflexivity. Qed.

(* ── THE KERNEL-CORRECT BEHAVIOUR ──────────────────────────────────────────────

   (A) The reply's SOURCE 8.8.8.8 is un-DNAT'd back to the router 9.9.9.9 — the
       inverse manip the kernel applies for the reply direction. *)
Lemma reply_saddr_undone : out_saddr env_after_fwd reply = [9;9;9;9].
Proof. vm_compute. reflexivity. Qed.

(* (B) The reply's DESTINATION (the client 1.1.1.1) is LEFT UNTOUCHED — a dnat
       never rewrites the reply's destination. *)
Lemma reply_daddr_untouched : out_daddr env_after_fwd reply = [1;1;1;1].
Proof. vm_compute. reflexivity. Qed.

(* Headline: the model's reply-direction NAT MATCHES the kernel exactly.
   Kernel on the reply: saddr 8.8.8.8 -> 9.9.9.9, daddr 1.1.1.1 untouched.
   Model  on the reply: saddr 8.8.8.8 -> 9.9.9.9, daddr 1.1.1.1 untouched. *)
Theorem reply_nat_is_correct :
  out_saddr env_after_fwd reply = [9;9;9;9]            (* un-DNAT'd back to the original address *)
  /\ out_daddr env_after_fwd reply = [1;1;1;1].        (* destination left alone *)
Proof. split; [exact reply_saddr_undone | exact reply_daddr_untouched]. Qed.

(* The reply is NOT translated backwards: its source is not left at the dnat
   target, and its destination is NOT re-rewritten to the dnat target. *)
Theorem reply_nat_not_backwards :
  out_saddr env_after_fwd reply <> [8;8;8;8]           (* source not left at the NAT target *)
  /\ out_daddr env_after_fwd reply <> [8;8;8;8].       (* destination not re-NAT'd forward *)
Proof.
  split; [ rewrite reply_saddr_undone | rewrite reply_daddr_untouched ]; discriminate.
Qed.

(* Soundness corner: a reply-direction packet of a flow with NO established mapping
   ([e_nat = None]) is NOT translated at all (the kernel establishes the tuple only
   on the original-direction packet; an un-confirmed reply has no tuple to invert). *)
Definition reply_no_mapping : packet := mkpkt [8;8;8;8] [1;1;1;1] false.
Theorem reply_unestablished_not_natted :
  out_saddr env0 reply_no_mapping = [8;8;8;8]
  /\ out_daddr env0 reply_no_mapping = [1;1;1;1].
Proof. split; vm_compute; reflexivity. Qed.

(** ── PORT-NAT REPLY ────────────────────────────────────────────────────────────

    A `dnat to 8.8.8.8:8080` rewrites BOTH the destination address AND the
    DESTINATION port on the forward packet.  The kernel's nf_nat_packet runs
    nf_nat_manip_pkt(REPLY) on the reply, which (after inverting the maniptype)
    rewrites the reply's SOURCE port from the dnat target (8080) back to the
    connection's ORIGINAL (pre-DNAT) destination port — tcp_manip_pkt /
    __udp_manip_pkt: `*portptr = newport` (nf_nat_proto.c).

    The model stores the original port as the 4th component of the [e_nat] tuple
    (mirroring the kernel's reply tuple) and un-rewrites it on the reply; a reply
    source port stuck at the dnat target 8080 is a packet the kernel can never
    emit on that flow. *)

(* `dnat to 8.8.8.8:8080`: dest addr 8.8.8.8 (reg 1) + dest port 8080. *)
Definition dnat_port : nat_spec :=
  {| nat_addr_imm := Some [8;8;8;8]; nat_field := None; nat_map := None;
     nat_src := None; nat_kind := nat_dnat_kind; nat_family := nat_fam_ip4;
     nat_extra := NXimm None (Some (N_to_data 2 (N.of_nat 8080))) None;
     nat_flags := 0 |}.
Definition dnat_port_rule : rule :=
  {| r_body := []; r_verdict := Accept; r_vmap := None;
     r_nat := Some dnat_port; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.
Definition dnat_port_chain : chain := {| c_policy := Drop; c_rules := [ dnat_port_rule ] |}.

(* Build a TCP-bearing packet: a transport header with a real sport/dport
   ([sport ++ dport ++ payload]).  pkt_have_l4 is irrelevant to the port splice. *)
Definition mkpkt_p (saddr daddr sport dport : data) (dir : bool) : packet :=
  {| pkt_meta := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := [];
     pkt_nh := [69;0;0;20; 0;0;0;0; 64;6; 0;0] ++ saddr ++ daddr;
     pkt_th := sport ++ dport ++ [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0];
     pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := false; pkt_fragoff := 0;
     pkt_flow := [7;7]; pkt_untracked := false; pkt_ctdir_orig := dir; pkt_ct_present := true |}.

Definition out_sport (e : env) (p : packet) : data :=
  slice (pkt_th (snd (snd (eval_chain_trace Hprerouting dnat_port_chain e p)))) 0 2.
Definition out_dport (e : env) (p : packet) : data :=
  slice (pkt_th (snd (snd (eval_chain_trace Hprerouting dnat_port_chain e p)))) 2 2.

(* FORWARD packet: client (sport 4444) -> router:80 ([0;80]).  dnat to 8.8.8.8:8080
   rewrites the DESTINATION port 80 -> 8080 ([31;144]). *)
Definition fwd_p : packet := mkpkt_p [1;1;1;1] [9;9;9;9] [17;92] [0;80] true.
Lemma fwd_dport_rewritten : out_dport env0 fwd_p = [31;144].   (* 8080 big-endian *)
Proof. vm_compute. reflexivity. Qed.

(* The env after the forward packet records the ORIGINAL dest port ([0;80]) as the
   4th tuple component, alongside the new port 8080. *)
Definition env_after_fwd_p : env :=
  fst (snd (eval_chain_trace Hprerouting dnat_port_chain env0 fwd_p)).
Lemma mapping_port_stored :
  e_nat env_after_fwd_p [7;7]
    = Some (Some [9;9;9;9], Some [8;8;8;8], Some 8080, Some [0;80]).
Proof. vm_compute. reflexivity. Qed.

(* REPLY packet of the SAME flow: server 8.8.8.8:8080 -> client.  Its SOURCE port
   is the dnat target 8080 ([31;144]).  The kernel un-rewrites it back to the
   original 80.  Carries the env established by the forward packet. *)
Definition reply_p : packet :=
  mkpkt_p [8;8;8;8] [1;1;1;1] [31;144] [17;92] false.

(* The reply's SOURCE port is un-DNAT'd from 8080 back to the original 80
   ([0;80]) — the inverse port manip. *)
Theorem reply_sport_undone : out_sport env_after_fwd_p reply_p = [0;80].
Proof. vm_compute. reflexivity. Qed.

(* Dually: the reply's source port is NOT stuck at the dnat target 8080 (a
   direction-blind model would leave it there byte-for-byte). *)
Theorem reply_sport_not_target : out_sport env_after_fwd_p reply_p <> [31;144].
Proof. rewrite reply_sport_undone. discriminate. Qed.

(* A dnat never rewrites the reply's DESTINATION port: it is left untouched
   ([17;92], the client's port). *)
Theorem reply_dport_untouched : out_dport env_after_fwd_p reply_p = [17;92].
Proof. vm_compute. reflexivity. Qed.
