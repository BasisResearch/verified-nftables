(** * Family-aware NAT address rewrite (IPv6 snat/dnat)

    [apply_nat] dispatches the address geometry on [nat_family]: "ip" rewrites the
    32-bit IPv4 slot, "ip6" the 128-bit IPv6 slot — the kernel chooses 32 vs 128
    bits by family ([nat_addrlen], netlink_linearize.c:1237).  Before the fix
    [set_saddr]/[set_daddr] hardcoded the IPv4 slots (src @12 len 4, dst @16 len
    4), so an ip6 NAT spliced a 16-byte literal into a 4-byte IPv4 slot: the IPv6
    address (at network offsets 8..23 / 24..39, where [FIp6Saddr]/[FIp6Daddr]
    read) was NEVER set, and the header was shifted/corrupted by 12 bytes.  These
    theorems prove the fixed behaviour: an ip6 dnat sets the 16-byte IPv6
    destination to the target (and an ip6 snat sets the IPv6 source), with the
    network-header length preserved. *)
From Stdlib Require Import List String NArith Lia.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Semantics.
Open Scope string_scope.

(* A 16-byte IPv6 NAT target (all 0xAA). *)
Definition tgt6 : data := List.repeat 170 16.

Definition ip6_dnat_spec : nat_spec :=
  {| nat_imms := [(1, tgt6)]; nat_map := None; nat_field := None;
     nat_src := None; nat_kind := nat_dnat_kind; nat_family := nat_fam_ip6;
     nat_amin := None; nat_amax := None; nat_pmin := None; nat_pmax := None;
     nat_flags := 0 |}.
Definition ip6_dnat_rule : rule :=
  {| r_body := []; r_verdict := Continue; r_vmap := None;
     r_nat := Some ip6_dnat_spec; r_tproxy := None; r_fwd := None;
     r_queue := None; r_after := [] |}.

Definition ip6_snat_spec : nat_spec :=
  {| nat_imms := [(1, tgt6)]; nat_map := None; nat_field := None;
     nat_src := None; nat_kind := nat_snat_kind; nat_family := nat_fam_ip6;
     nat_amin := None; nat_amax := None; nat_pmin := None; nat_pmax := None;
     nat_flags := 0 |}.
Definition ip6_snat_rule : rule :=
  {| r_body := []; r_verdict := Continue; r_vmap := None;
     r_nat := Some ip6_snat_spec; r_tproxy := None; r_fwd := None;
     r_queue := None; r_after := [] |}.

(* The IPv6 dnat NAT effect destination-rewrites the IPv6 dest slot (off 24,
   len 16) to the target operand. *)
Lemma ip6_dnat_apply : forall h p, apply_nat h ip6_dnat_rule p = set_daddr "ip6" p tgt6.
Proof. reflexivity. Qed.

Lemma ip6_snat_apply : forall h p, apply_nat h ip6_snat_rule p = set_saddr "ip6" p tgt6.
Proof. reflexivity. Qed.

(* Reading the IPv6 destination back: after the ip6 dnat, `ip6 daddr` IS the
   16-byte target (for a well-formed IPv6 header, >= 40 bytes). *)
Lemma ip6_daddr_after_set : forall p v,
  40 <= List.length (pkt_nh p) -> List.length v = 16 ->
  field_value FIp6Daddr (set_daddr "ip6" p v) = v.
Proof.
  intros p v Hlen Hv.
  unfold field_value; cbn [field_load do_load]; unfold read_payload, set_daddr;
    change (daddr_slot "ip6") with (24, 16); cbn [set_nh_field pkt_nh].
    unfold slice, splice.
  assert (H24 : List.length (firstn 24 (pkt_nh p)) = 24)
    by (rewrite firstn_length_le; [reflexivity | lia]).
  rewrite skipn_app, H24.
  rewrite (skipn_all2 (firstn 24 (pkt_nh p))) by lia.
  replace (24 - 24) with 0 by lia. cbn [skipn app].
  rewrite firstn_app, Hv. replace (16 - 16) with 0 by lia.
  rewrite firstn_O, app_nil_r, firstn_all2 by lia. reflexivity.
Qed.

Lemma ip6_saddr_after_set : forall p v,
  40 <= List.length (pkt_nh p) -> List.length v = 16 ->
  field_value FIp6Saddr (set_saddr "ip6" p v) = v.
Proof.
  intros p v Hlen Hv.
  unfold field_value; cbn [field_load do_load]; unfold read_payload, set_saddr;
    change (saddr_slot "ip6") with (8, 16); cbn [set_nh_field pkt_nh].
    unfold slice, splice.
  assert (H8 : List.length (firstn 8 (pkt_nh p)) = 8)
    by (rewrite firstn_length_le; [reflexivity | lia]).
  rewrite skipn_app, H8.
  rewrite (skipn_all2 (firstn 8 (pkt_nh p))) by lia.
  replace (8 - 8) with 0 by lia. cbn [skipn app].
  rewrite firstn_app, Hv. replace (16 - 16) with 0 by lia.
  rewrite firstn_O, app_nil_r, firstn_all2 by lia. reflexivity.
Qed.

(* The header length is preserved (no shift/corruption): the network header is
   the same length after the ip6 NAT.  Before the fix it grew by 12 bytes. *)
Lemma ip6_dnat_nh_len_preserved : forall p,
  40 <= List.length (pkt_nh p) ->
  List.length (pkt_nh (set_daddr "ip6" p tgt6)) = List.length (pkt_nh p).
Proof.
  intros p Hlen.
  unfold set_daddr; change (daddr_slot "ip6") with (24, 16); cbn [set_nh_field pkt_nh].
  unfold splice. rewrite !app_length, firstn_length_le by lia.
  rewrite skipn_length. unfold tgt6. rewrite repeat_length. lia.
Qed.

(* THE FIX, on a concrete 40-byte IPv6 packet: the IPv6 destination IS now set
   to the target (the property the red agent proved FALSE before the fix). *)
Definition e0 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddr := fun _ => []; e_connlimit := fun _ => 0 |}.
Definition pkt6 : packet :=
  {| pkt_env := e0; pkt_meta := fun _ => []; pkt_ct := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := seq 0 40; pkt_th := []; pkt_ih := []; pkt_tnl := [];
     pkt_fibkey := fun _ => []; pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l4 := false; pkt_fragoff := 0 |}.

Theorem ip6_dnat_dest_is_target :
  field_value FIp6Daddr (apply_nat Hprerouting ip6_dnat_rule pkt6) = tgt6.
Proof. vm_compute. reflexivity. Qed.

Theorem ip6_snat_src_is_target :
  field_value FIp6Saddr (apply_nat Hprerouting ip6_snat_rule pkt6) = tgt6.
Proof. vm_compute. reflexivity. Qed.
