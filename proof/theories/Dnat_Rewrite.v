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

(* dnat is hook-invariant; evaluate the trace at the prerouting hook. *)
Definition chain_out (c : chain) (p : packet) : packet := snd (eval_chain_trace Hprerouting c p).

(* The dnat rule's terminal outcome is Accept (verdict component unchanged). *)
Lemma dnat_outcome_accept : forall p, outcome dnat_rule p = Some Accept.
Proof. reflexivity. Qed.

(* The target operand the dnat statement loads into register 1. *)
Lemma dnat_addr_target : forall p, nat_addr dnat_spec p = [10;0;0;1].
Proof. reflexivity. Qed.

(* The dnat NAT effect destination-rewrites to the target operand. *)
Lemma dnat_apply : forall h p, apply_nat h dnat_rule p = set_daddr "ip" p [10;0;0;1].
Proof. reflexivity. Qed.

(* THE OUTPUT PACKET of the dnat chain: the input with its destination address
   set to the target (= what dnat does). *)
Theorem dnat_output : forall h p,
  eval_chain_trace h dnat_chain p = (Accept, set_daddr "ip" p [10;0;0;1]).
Proof.
  intros h p. unfold eval_chain_trace, dnat_chain. cbn [c_rules eval_rules_trace].
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

(** * Redirect is hook-dependent (kernel [nf_nat_redirect_ipv4]/[ipv6]).

    A `redirect` is a destination-NAT whose target the kernel core picks by the
    hook: at the OUTPUT hook (NF_INET_LOCAL_OUT) "local packets go to loopback"
    (IPv4 127.0.0.1 / IPv6 ::1), while at PRE_ROUTING it uses the inbound
    interface's primary address.  The model's [apply_nat] now threads the hook and
    mirrors this exactly; the old behaviour (always the iif address) was
    kernel-incorrect for the output hook. *)
Definition redir_spec (fam : string) : nat_spec :=
  {| nat_imms := []; nat_field := None; nat_map := None; nat_src := None;
     nat_kind := "redir"; nat_family := fam;
     nat_amin := None; nat_amax := None; nat_pmin := None; nat_pmax := None; nat_flags := 0 |}.
Definition redir_rule (fam : string) : rule :=
  {| r_body := []; r_verdict := Continue; r_vmap := None; r_nat := Some (redir_spec fam);
     r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.

(* At the OUTPUT hook, redirect rewrites the destination to the LOOPBACK constant
   (127.0.0.1 for ip, ::1 for ip6), INDEPENDENT of the inbound-interface address. *)
Theorem redir_output_ip4_loopback : forall p,
  apply_nat Houtput (redir_rule "ip") p = set_daddr "ip" p [127;0;0;1].
Proof. reflexivity. Qed.

Theorem redir_output_ip6_loopback : forall p,
  apply_nat Houtput (redir_rule "ip6") p
    = set_daddr "ip6" p [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;1].
Proof. reflexivity. Qed.

(* At PRE_ROUTING, redirect still uses the inbound-interface address. *)
Theorem redir_prerouting_iifaddr : forall p,
  apply_nat Hprerouting (redir_rule "ip") p
    = set_daddr "ip" p (e_ifaddr (pkt_env p) (field_value FMetaIifname p)).
Proof. reflexivity. Qed.

(* The fix is observable on a well-formed IPv4 packet: when the inbound-interface
   address is NOT the loopback (the usual case) and the address slot is 4 bytes,
   reading `ip daddr` back after an OUTPUT-hook redirect yields 127.0.0.1, whereas
   after a PRE_ROUTING redirect it yields the iif address — so the two hooks
   diverge.  Before the fix [apply_nat] was hook-blind and these coincided. *)
Theorem redir_output_differs_from_prerouting : forall p,
  20 <= List.length (pkt_nh p) ->
  List.length (e_ifaddr (pkt_env p) (field_value FMetaIifname p)) = 4 ->
  e_ifaddr (pkt_env p) (field_value FMetaIifname p) <> [127;0;0;1] ->
  apply_nat Houtput (redir_rule "ip") p <> apply_nat Hprerouting (redir_rule "ip") p.
Proof.
  intros p Hnh Hlen Hne Heq.
  apply Hne.
  assert (Hread :
    field_value FIp4Daddr (apply_nat Houtput (redir_rule "ip") p)
    = field_value FIp4Daddr (apply_nat Hprerouting (redir_rule "ip") p))
    by (rewrite Heq; reflexivity).
  rewrite redir_output_ip4_loopback, redir_prerouting_iifaddr in Hread.
  rewrite (daddr_after_set p [127;0;0;1] Hnh eq_refl) in Hread.
  rewrite (daddr_after_set p _ Hnh Hlen) in Hread.
  symmetry; exact Hread.
Qed.

(** * L4 PORT rewrite (`dnat to A:PORT` / `snat ... :PORT`).

    A `dnat to A.B.C.D:PORT` rewrites BOTH the L3 destination address AND the L4
    DESTINATION port (TCP/UDP header bytes 2..3).  The kernel loads [PORT] into the
    proto-min register and [nf_nat_proto.c]/[tcp_manip_pkt] writes it into the
    header (`*portptr = newport`, nf_nat_proto.c:163-172).  Before the fix the model
    ignored [nat_pmin]/[nat_pmax] entirely, so the transport header (and hence the
    port) was provably left byte-for-byte unchanged — `pkt_th (chain_out …) = pkt_th p`.
    These theorems prove the opposite: the port IS now rewritten, and the
    formerly-provable no-op is refuted. *)

(* `dnat to 10.0.0.1:8080`: same address operand, plus port 8080 in nat_pmin. *)
Definition dnat_port_spec : nat_spec :=
  {| nat_imms := [(1, [10;0;0;1])]; nat_field := None; nat_map := None; nat_src := None;
     nat_kind := "dnat"; nat_family := "ip";
     nat_amin := None; nat_amax := None;
     nat_pmin := Some 8080; nat_pmax := Some 8080; nat_flags := 0 |}.
Definition dnat_port_rule : rule :=
  {| r_body := []; r_verdict := Continue; r_vmap := None; r_nat := Some dnat_port_spec;
     r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.
Definition dnat_port_chain : chain := {| c_policy := Accept; c_rules := [dnat_port_rule] |}.

(* 8080 = 0x1f90 -> big-endian [0x1f; 0x90] = [31; 144]. *)
Lemma dnat_port_bytes_8080 : nat_port_bytes 8080 = [31; 144].
Proof. reflexivity. Qed.

(* The dnat-with-port effect: address rewrite followed by the L4 dest-port write. *)
Lemma dnat_port_apply : forall h p,
  apply_nat h dnat_port_rule p
    = set_dport (set_daddr "ip" p [10;0;0;1]) [31; 144].
Proof. reflexivity. Qed.

(* THE OUTPUT PACKET: dnat to A:PORT sets both the destination address and dport. *)
Theorem dnat_port_output : forall h p,
  eval_chain_trace h dnat_port_chain p
    = (Accept, set_dport (set_daddr "ip" p [10;0;0;1]) [31; 144]).
Proof.
  intros h p. unfold eval_chain_trace, dnat_port_chain. cbn [c_rules eval_rules_trace].
  reflexivity.
Qed.

(* Reading the destination port back: after `dnat to A:8080`, `th dport` IS 8080
   (= big-endian [31;144]), for a transport header with at least 4 bytes. *)
Lemma dport_after_set : forall p v,
  4 <= List.length (pkt_th p) -> List.length v = 2 ->
  read_payload PTransport 2 2 (set_dport p v) = v.
Proof.
  intros p v Hlen Hv.
  unfold read_payload, set_dport, set_th_field; cbn [pkt_th].
  unfold slice, splice.
  assert (H2 : List.length (firstn 2 (pkt_th p)) = 2)
    by (rewrite firstn_length_le; [reflexivity | lia]).
  rewrite skipn_app, H2.
  rewrite (skipn_all2 (firstn 2 (pkt_th p))) by lia.
  replace (2 - 2) with 0 by lia. cbn [skipn app].
  rewrite firstn_app, Hv. replace (2 - 2) with 0 by lia.
  rewrite firstn_O, app_nil_r, firstn_all2 by lia. reflexivity.
Qed.

Theorem dnat_port_dport_is_8080 : forall p,
  20 <= List.length (pkt_nh p) ->
  4 <= List.length (pkt_th p) ->
  read_payload PTransport 2 2 (chain_out dnat_port_chain p) = [31; 144].
Proof.
  intros p Hnh Hth. unfold chain_out. rewrite dnat_port_output. cbn [snd].
  (* set_daddr touches pkt_nh only, so pkt_th length is preserved. *)
  apply dport_after_set; [cbn [set_daddr set_nh_field pkt_th]; exact Hth | reflexivity].
Qed.

(* The infidelity is REFUTED: the dnat-with-port chain does NOT leave the transport
   header unchanged (the red agent's [dnat_port_NOT_rewritten] is now false) — the
   L4 destination port IS rewritten whenever the current dport differs from 8080. *)
Theorem dnat_port_rewrites_th : forall p,
  20 <= List.length (pkt_nh p) ->
  4 <= List.length (pkt_th p) ->
  read_payload PTransport 2 2 p <> [31; 144] ->
  pkt_th (chain_out dnat_port_chain p) <> pkt_th p.
Proof.
  intros p Hnh Hth Hne Heq.
  apply Hne.
  rewrite <- (dnat_port_dport_is_8080 p Hnh Hth).
  unfold read_payload. rewrite Heq. reflexivity.
Qed.

(** A `snat ... :PORT` rewrites the L4 SOURCE port (transport bytes 0..1), not the
    destination — the [NF_NAT_MANIP_SRC] half.  A dnat with NO port operand
    ([nat_pmin] = None, the address-only case) leaves the transport header
    untouched, mirroring `if (priv->sreg_proto_min)` (nft_nat.c:120). *)
Definition snat_port_spec : nat_spec :=
  {| nat_imms := [(1, [192;168;0;1])]; nat_field := None; nat_map := None; nat_src := None;
     nat_kind := "snat"; nat_family := "ip";
     nat_amin := None; nat_amax := None;
     nat_pmin := Some 4000; nat_pmax := Some 4000; nat_flags := 0 |}.
Definition snat_port_rule : rule :=
  {| r_body := []; r_verdict := Continue; r_vmap := None; r_nat := Some snat_port_spec;
     r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.

(* snat to A:PORT writes the SOURCE port (offset 0), leaving the dest port alone. *)
Theorem snat_port_writes_sport : forall h p,
  apply_nat h snat_port_rule p
    = set_sport (set_saddr "ip" p [192;168;0;1]) (nat_port_bytes 4000).
Proof. reflexivity. Qed.

(* The address-only dnat ([nat_pmin]=None) is a pure L3 rewrite: pkt_th preserved. *)
Theorem dnat_addronly_th_preserved : forall h p,
  pkt_th (apply_nat h dnat_rule p) = pkt_th p.
Proof. reflexivity. Qed.
