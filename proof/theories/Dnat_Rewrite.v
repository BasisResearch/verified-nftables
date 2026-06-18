(** * Destination-NAT data-plane rewrite (dnat / redirect)

    A `dnat to <addr>` rule is a terminal Accept whose data-plane effect is to
    rewrite the packet's IPv4 DESTINATION address (network-header bytes 16..19,
    where [FIp4Daddr] reads) to the target operand — the kernel's
    [NF_NAT_MANIP_DST] from [NFTNL_EXPR_NAT_REG_ADDR_MIN]
    (nf_tables.h NFT_NAT_DNAT; netlink_linearize.c:1304).  Before the fix the
    whole-chain trace ([eval_chain_trace] / [apply_nat]) left a dnat packet
    UNCHANGED — `chain_out dnat_chain p = p` was provable.  These theorems prove
    the opposite: the trace now performs the destination rewrite, and the formerly
    "total no-op" property is refuted on a concrete packet. *)
From Stdlib Require Import List String NArith Lia.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Semantics.

(* A `dnat to 10.0.0.1` rule: target address in register 1, family ip. *)
Definition dnat_spec : nat_spec :=
  {| nat_imms := [(1, [10;0;0;1])]; nat_field := None; nat_map := None; nat_src := None;
     nat_kind := "dnat"; nat_family := "ip";
     nat_amin := None; nat_amax := None; nat_pmin := None; nat_pmax := None; nat_flags := 0 |}.
Definition dnat_rule : rule :=
  {| r_body := []; r_verdict := Continue; r_vmap := None; r_nat := Some dnat_spec;
     r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.
Definition dnat_chain : chain := {| c_policy := Accept; c_rules := [dnat_rule] |}.

Definition chain_out (c : chain) (p : packet) : packet := snd (eval_chain_trace c p).

(* The dnat rule's terminal outcome is Accept (verdict component unchanged). *)
Lemma dnat_outcome_accept : forall p, outcome dnat_rule p = Some Accept.
Proof. reflexivity. Qed.

(* The target operand the dnat statement loads into register 1. *)
Lemma dnat_addr_target : forall p, nat_addr dnat_spec p = [10;0;0;1].
Proof. reflexivity. Qed.

(* The dnat NAT effect destination-rewrites to the target operand. *)
Lemma dnat_apply : forall p, apply_nat dnat_rule p = set_daddr "ip" p [10;0;0;1].
Proof. reflexivity. Qed.

(* THE OUTPUT PACKET of the dnat chain: the input with its destination address
   set to the target (= what dnat does). *)
Theorem dnat_output : forall p,
  eval_chain_trace dnat_chain p = (Accept, set_daddr "ip" p [10;0;0;1]).
Proof.
  intro p. unfold eval_chain_trace, dnat_chain. cbn [c_rules eval_rules_trace].
  reflexivity.
Qed.

(* Reading the destination address back: after dnat, `ip daddr` IS the target
   (for a well-formed IPv4 header). *)
Lemma daddr_after_set : forall p v,
  20 <= List.length (pkt_nh p) -> List.length v = 4 ->
  field_value FIp4Daddr (set_daddr "ip" p v) = v.
Proof.
  intros p v Hlen Hv.
  unfold field_value; cbn [field_load do_load]; unfold read_payload, set_daddr;
    change (daddr_slot "ip") with (16, 4); cbn [set_nh_field pkt_nh].
    unfold slice, splice.
  assert (H16 : List.length (firstn 16 (pkt_nh p)) = 16)
    by (rewrite firstn_length_le; [reflexivity | lia]).
  rewrite skipn_app, H16.
  rewrite (skipn_all2 (firstn 16 (pkt_nh p))) by lia.
  replace (16 - 16) with 0 by lia. cbn [skipn app].
  rewrite firstn_app, Hv. replace (4 - 4) with 0 by lia.
  rewrite firstn_O, app_nil_r, firstn_all2 by lia. reflexivity.
Qed.

Theorem dnat_dest_is_target : forall p,
  20 <= List.length (pkt_nh p) ->
  field_value FIp4Daddr (chain_out dnat_chain p) = [10;0;0;1].
Proof.
  intros p Hnh. unfold chain_out. rewrite dnat_output. cbn [snd].
  apply daddr_after_set; [assumption | reflexivity].
Qed.

(* The infidelity is REFUTED: any packet whose current destination differs from
   the dnat target (and whose IPv4 header is well-formed) is NOT returned verbatim
   by the dnat chain — the destination IS rewritten.  This is the analogue of the
   formerly-provable (and false) `chain_out dnat_chain p = p`. *)
Theorem dnat_is_not_noop : forall p,
  20 <= List.length (pkt_nh p) ->
  field_value FIp4Daddr p <> [10;0;0;1] ->
  chain_out dnat_chain p <> p.
Proof.
  intros p Hnh Hne H.
  apply Hne. rewrite <- (dnat_dest_is_target p Hnh), H. reflexivity.
Qed.
