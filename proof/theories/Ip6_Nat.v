(** * Family-aware NAT address rewrite (IPv6 snat/dnat)

    [apply_nat] dispatches the address geometry on [nat_family]: "ip" rewrites the
    32-bit IPv4 slot (src @12 len 4, dst @16 len 4), "ip6" the 128-bit IPv6 slot
    (network offsets 8..23 / 24..39, where [FIp6Saddr]/[FIp6Daddr] read) — the
    kernel chooses 32 vs 128 bits by family ([nat_addrlen],
    netlink_linearize.c:1237).  A family-blind splice of a 16-byte literal into
    the 4-byte IPv4 slot would leave the IPv6 address unset and shift/corrupt the
    header by 12 bytes.  These theorems pin the family dispatch: an ip6 dnat sets
    the 16-byte IPv6 destination to the target (and an ip6 snat the IPv6 source),
    with the network-header length preserved. *)
From Stdlib Require Import List String NArith Lia.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Semantics.
Open Scope string_scope.

(* A 16-byte IPv6 NAT target (all 0xAA). *)
Definition tgt6 : data := List.repeat 170 16.

Definition ip6_dnat_spec : nat_spec :=
  {| nat_addr_imm := Some tgt6; nat_map := None; nat_field := None;
     nat_src := None; nat_kind := nat_dnat_kind; nat_family := nat_fam_ip6;
     nat_extra := NXnone;
     nat_flags := 0 |}.
Definition ip6_dnat_rule : rule :=
  {| r_body := []; r_verdict := Continue; r_vmap := None;
     r_nat := Some ip6_dnat_spec; r_tproxy := None; r_fwd := None;
     r_queue := None; r_after := [] |}.

Definition ip6_snat_spec : nat_spec :=
  {| nat_addr_imm := Some tgt6; nat_map := None; nat_field := None;
     nat_src := None; nat_kind := nat_snat_kind; nat_family := nat_fam_ip6;
     nat_extra := NXnone;
     nat_flags := 0 |}.
Definition ip6_snat_rule : rule :=
  {| r_body := []; r_verdict := Continue; r_vmap := None;
     r_nat := Some ip6_snat_spec; r_tproxy := None; r_fwd := None;
     r_queue := None; r_after := [] |}.

(* The IPv6 dnat NAT effect destination-rewrites the IPv6 dest slot (off 24,
   len 16) to the target operand.  NAT is FLOW-STATEFUL ([e_nat], Packet.v): on the first
   packet of a flow ([e_nat .. = None]) the address rewrite is exactly as before AND
   the mapping is stored; the network header is unchanged by that env write. *)
Lemma ip6_dnat_apply : forall h e p,
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  snd (apply_nat h ip6_dnat_rule e p) = set_daddr "ip6" p tgt6.
Proof.
  intros h e p Horig Hnone. unfold apply_nat, ip6_dnat_rule, ip6_dnat_spec.
  cbn -[set_daddr store_nat_mapping e_nat pkt_flow tgt6 slice pkt_nh].
  rewrite Hnone.
  unfold apply_nat_tuple, nat_orig_addr, nat_is_src, nat_addrfamily, nat_operand_addr.
  cbn -[set_daddr store_nat_mapping tgt6 slice pkt_nh]. rewrite ?Horig; reflexivity.
Qed.

Lemma ip6_snat_apply : forall h e p,
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  snd (apply_nat h ip6_snat_rule e p) = set_saddr "ip6" p tgt6.
Proof.
  intros h e p Horig Hnone. unfold apply_nat, ip6_snat_rule, ip6_snat_spec.
  cbn -[set_saddr store_nat_mapping e_nat pkt_flow tgt6 slice pkt_nh].
  rewrite Hnone.
  unfold apply_nat_tuple, nat_orig_addr, nat_is_src, nat_addrfamily, nat_operand_addr.
  cbn -[set_saddr store_nat_mapping tgt6 slice pkt_nh]. rewrite ?Horig; reflexivity.
Qed.

(* Reading the IPv6 destination back: after the ip6 dnat, `ip6 daddr` IS the
   16-byte target (for a well-formed IPv6 header, >= 40 bytes). *)
Lemma ip6_daddr_after_set : forall e p v,
  40 <= List.length (pkt_nh p) -> List.length v = 16 ->
  field_value FIp6Daddr e (set_daddr "ip6" p v) = v.
Proof.
  intros e p v Hlen Hv.
  unfold field_value; cbn [field_load do_load]; unfold read_payload.
  rewrite set_daddr_nh;
    change (daddr_slot "ip6") with (24, 16);
    change (String.eqb "ip6" nat_fam_ip6) with true; cbv iota;
    cbn [set_nh_field with_pkt_nh pkt_nh].
    unfold slice, splice.
  assert (H24 : List.length (firstn 24 (pkt_nh p)) = 24)
    by (rewrite firstn_length_le; [reflexivity | lia]).
  rewrite skipn_app, H24.
  rewrite (skipn_all2 (firstn 24 (pkt_nh p))) by lia.
  replace (24 - 24) with 0 by lia. cbn [skipn app].
  rewrite firstn_app, Hv. replace (16 - 16) with 0 by lia.
  rewrite firstn_O, app_nil_r, firstn_all2 by lia. reflexivity.
Qed.

Lemma ip6_saddr_after_set : forall e p v,
  40 <= List.length (pkt_nh p) -> List.length v = 16 ->
  field_value FIp6Saddr e (set_saddr "ip6" p v) = v.
Proof.
  intros e p v Hlen Hv.
  unfold field_value; cbn [field_load do_load]; unfold read_payload.
  rewrite set_saddr_nh;
    change (saddr_slot "ip6") with (8, 16);
    change (String.eqb "ip6" nat_fam_ip6) with true; cbv iota;
    cbn [set_nh_field with_pkt_nh pkt_nh].
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
   the same length after the ip6 NAT (an IPv4-slot splice would grow it by 12). *)
Lemma ip6_dnat_nh_len_preserved : forall p,
  40 <= List.length (pkt_nh p) ->
  List.length (pkt_nh (set_daddr "ip6" p tgt6)) = List.length (pkt_nh p).
Proof.
  intros p Hlen.
  rewrite set_daddr_nh; change (daddr_slot "ip6") with (24, 16);
    change (String.eqb "ip6" nat_fam_ip6) with true; cbv iota;
    cbn [set_nh_field with_pkt_nh pkt_nh].
  unfold splice. rewrite !length_app, firstn_length_le by lia.
  rewrite length_skipn. unfold tgt6. rewrite repeat_length. lia.
Qed.

(* On a concrete 40-byte IPv6 packet: the IPv6 destination IS set to the
   target (an ip4-only splice would leave it untouched). *)
Definition e0 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => []; e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.
Definition pkt6 : packet :=
  {| pkt_meta := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := seq 0 40; pkt_th := []; pkt_ih := []; pkt_tnl := [];
     pkt_fibkey := fun _ => []; pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := false; pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := true |}.

Theorem ip6_dnat_dest_is_target :
  field_value FIp6Daddr e0 (snd (apply_nat Hprerouting ip6_dnat_rule e0 pkt6)) = tgt6.
Proof. vm_compute. reflexivity. Qed.

Theorem ip6_snat_src_is_target :
  field_value FIp6Saddr e0 (snd (apply_nat Hprerouting ip6_snat_rule e0 pkt6)) = tgt6.
Proof. vm_compute. reflexivity. Qed.

(** ** IPv6 masquerade rewrites the FULL 16-byte IPv6 source (family-aware).

    The kernel dispatches masquerade BY FAMILY (nft_masq.c:113-121:
    NFPROTO_IPV6 -> nf_nat_masquerade_ipv6, nf_nat_masquerade.c:241-262), computing
    a 128-bit IPv6 source via ipv6_dev_get_saddr and rewriting the whole 16-byte
    source — a DIFFERENT value from the IPv4 interface address.  The model's
    masquerade carries a real [nat_family] (the parser threads the ip6 table
    family) and a family-indexed source ([masq_saddr] picks the 16-byte
    [e_ifaddr6] for ip6).  A family-blind masquerade ([nat_family = ""] -> "ip")
    would splice the 4-byte IPv4 [e_ifaddr] into bytes 12..15 (the middle of the
    IPv6 source) and leave the IPv6 source slot (bytes 8..23) unrewritten.
    `ip6 masquerade` is valid and in the corpus (tests/py/ip6/masquerade.t). *)

(* The exit interface's IPv6 source (a 16-byte in6_addr), all 0xBB. *)
Definition if6 : data := List.repeat 187 16.

Definition masq6_spec : nat_spec :=
  {| nat_addr_imm := None; nat_map := None; nat_field := None;
     nat_src := None; nat_kind := nat_masq_kind; nat_family := nat_fam_ip6;
     nat_extra := NXnone;
     nat_flags := 0 |}.
Definition masq6_rule : rule :=
  {| r_body := []; r_verdict := Continue; r_vmap := None;
     r_nat := Some masq6_spec; r_tproxy := None; r_fwd := None;
     r_queue := None; r_after := [] |}.

(* An env whose IPv6 interface address (e_ifaddr6) is [if6] for every interface,
   and whose IPv4 e_ifaddr is a DIFFERENT 4-byte value — to prove masquerade picks
   the IPv6 one, not the IPv4 one. *)
Definition e6 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => ifaddrs_of [9;9;9;9];
     e_ifaddrs6 := fun _ => ifaddrs_of if6; e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

(* A 40-byte IPv6 packet whose source slot (bytes 8..23) holds distinguishable
   markers 108..123, so an untouched source is detectable byte-for-byte. *)
Definition pkt6m : packet :=
  {| pkt_meta := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := seq 100 40; pkt_th := []; pkt_ih := []; pkt_tnl := [];
     pkt_fibkey := fun _ => []; pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := false; pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* An ip6 masquerade rewrites the whole 16-byte IPv6 source to the exit
   interface's IPv6 address [if6] (= ipv6_dev_get_saddr), reading back via
   FIp6Saddr (network bytes 8..23). *)
Theorem masq6_src_is_ipv6_ifaddr :
  field_value FIp6Saddr e6 (snd (apply_nat Hpostrouting masq6_rule e6 pkt6m)) = if6.
Proof. vm_compute. reflexivity. Qed.

(* Dually: bytes 8..11 of the IPv6 source are NOT the original markers
   [108;109;110;111] — they are the new IPv6 ifaddr's first 4 bytes.  (Under an
   ip4-width splice the markers would survive, proving the source untouched.) *)
Theorem masq6_does_rewrite_ipv6_source_prefix :
  firstn 4 (skipn 8 (pkt_nh (snd (apply_nat Hpostrouting masq6_rule e6 pkt6m))))
    <> [108;109;110;111].
Proof. vm_compute. discriminate. Qed.

(* The full 16-byte IPv6 source slot (8..23) is exactly [if6] — including the tail
   bytes 16..23 the family-blind model left untouched. *)
Theorem masq6_full_source_slot :
  firstn 16 (skipn 8 (pkt_nh (snd (apply_nat Hpostrouting masq6_rule e6 pkt6m)))) = if6.
Proof. vm_compute. reflexivity. Qed.

(* The network-header length is preserved (no 12-byte shift/corruption). *)
Theorem masq6_nh_len_preserved :
  List.length (pkt_nh (snd (apply_nat Hpostrouting masq6_rule e6 pkt6m))) = 40.
Proof. vm_compute. reflexivity. Qed.
