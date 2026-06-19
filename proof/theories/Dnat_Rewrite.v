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

(* The dnat NAT effect destination-rewrites to the target operand.  NAT is now
   FLOW-STATEFUL (Round-2): on the first packet of a flow ([e_nat .. = None]) the
   destination is rewritten exactly as before AND the mapping is stored; the
   observable network header is unchanged by the [store_nat_mapping] env write. *)
Lemma dnat_apply : forall h p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  apply_nat h dnat_rule p
    = store_nat_mapping (set_daddr "ip" p [10;0;0;1])
        (Some (slice (pkt_nh p) 16 4), Some [10;0;0;1], None).
Proof.
  intros h p Horig Hnone. unfold apply_nat, dnat_rule, dnat_spec.
  cbn -[set_daddr store_nat_mapping e_nat pkt_env pkt_flow slice pkt_nh
        apply_nat_tuple nat_orig_addr nat_operand_addr].
  rewrite Hnone.
  unfold apply_nat_tuple, nat_orig_addr, nat_is_src, nat_addrfamily, nat_operand_addr.
  cbn -[set_daddr store_nat_mapping slice pkt_nh]. rewrite !Horig. reflexivity.
Qed.

(* [store_nat_mapping] is observationally invisible on the network header. *)
Lemma store_nat_nh : forall p m, pkt_nh (store_nat_mapping p m) = pkt_nh p.
Proof. reflexivity. Qed.
Lemma store_nat_th : forall p m, pkt_th (store_nat_mapping p m) = pkt_th p.
Proof. reflexivity. Qed.
(* …hence reading any IPv4 address field back through it is the read on the
   underlying packet (the env write is below the header-read resolution). *)
Lemma store_nat_daddr : forall p m,
  field_value FIp4Daddr (store_nat_mapping p m) = field_value FIp4Daddr p.
Proof.
  intros p m. unfold field_value; cbn [field_load do_load]; unfold read_payload.
  rewrite store_nat_nh. reflexivity.
Qed.

(* THE OUTPUT PACKET of the dnat chain (first packet of the flow): the input with
   its destination address set to the target (= what dnat does), plus the stored
   mapping in [e_nat]. *)
Theorem dnat_output : forall h p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  eval_chain_trace h dnat_chain p
    = (Accept, store_nat_mapping (set_daddr "ip" p [10;0;0;1])
                 (Some (slice (pkt_nh p) 16 4), Some [10;0;0;1], None)).
Proof.
  intros h p Horig Hnone.
  assert (Hw : dsl_writes dnat_rule p = p) by reflexivity.
  unfold eval_chain_trace, dnat_chain. cbn [c_rules eval_rules_trace].
  cbn -[apply_nat dnat_rule dsl_writes]. rewrite Hw.
  rewrite (dnat_apply h p Horig Hnone). reflexivity.
Qed.

(* Reading the destination address back: after dnat, `ip daddr` IS the target
   (for a well-formed IPv4 header). *)
Lemma daddr_after_set : forall p v,
  20 <= List.length (pkt_nh p) -> List.length v = 4 ->
  field_value FIp4Daddr (set_daddr "ip" p v) = v.
Proof.
  intros p v Hlen Hv.
  unfold field_value; cbn [field_load do_load]; unfold read_payload.
  apply slice_set_daddr_ip4_same; [exact Hlen | exact Hv].
Qed.

Theorem dnat_dest_is_target : forall p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  20 <= List.length (pkt_nh p) ->
  field_value FIp4Daddr (chain_out dnat_chain p) = [10;0;0;1].
Proof.
  intros p Horig Hnone Hnh. unfold chain_out.
  rewrite (dnat_output Hprerouting p Horig Hnone). cbn [snd].
  rewrite store_nat_daddr.
  apply daddr_after_set; [assumption | reflexivity].
Qed.

(* The infidelity is REFUTED: any packet whose current destination differs from
   the dnat target (and whose IPv4 header is well-formed) is NOT returned verbatim
   by the dnat chain — the destination IS rewritten.  This is the analogue of the
   formerly-provable (and false) `chain_out dnat_chain p = p`. *)
Theorem dnat_is_not_noop : forall p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  20 <= List.length (pkt_nh p) ->
  field_value FIp4Daddr p <> [10;0;0;1] ->
  chain_out dnat_chain p <> p.
Proof.
  intros p Horig Hnone Hnh Hne H.
  apply Hne. rewrite <- (dnat_dest_is_target p Horig Hnone Hnh), H. reflexivity.
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
   (127.0.0.1 for ip, ::1 for ip6), INDEPENDENT of the inbound-interface address.
   On the first packet of a flow the mapping is also stored; the network header is
   unchanged by that env write. *)
Theorem redir_output_ip4_loopback : forall p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  apply_nat Houtput (redir_rule "ip") p
    = store_nat_mapping (set_daddr "ip" p [127;0;0;1])
        (Some (slice (pkt_nh p) 16 4), Some [127;0;0;1], None).
Proof.
  intros p Horig Hnone. unfold apply_nat, redir_rule, redir_spec.
  cbn -[set_daddr store_nat_mapping e_nat pkt_env pkt_flow slice pkt_nh redir_daddr].
  rewrite Hnone.
  unfold apply_nat_tuple, nat_orig_addr, nat_is_src, nat_addrfamily, nat_operand_addr,
    redir_daddr.
  cbn -[set_daddr store_nat_mapping slice pkt_nh]. rewrite ?Horig; reflexivity.
Qed.

Theorem redir_output_ip6_loopback : forall p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  apply_nat Houtput (redir_rule "ip6") p
    = store_nat_mapping (set_daddr "ip6" p [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;1])
        (Some (slice (pkt_nh p) 24 16), Some [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;1], None).
Proof.
  intros p Horig Hnone. unfold apply_nat, redir_rule, redir_spec.
  cbn -[set_daddr store_nat_mapping e_nat pkt_env pkt_flow slice pkt_nh redir_daddr].
  rewrite Hnone.
  unfold apply_nat_tuple, nat_orig_addr, nat_is_src, nat_addrfamily, nat_operand_addr,
    redir_daddr.
  cbn -[set_daddr store_nat_mapping slice pkt_nh]. rewrite ?Horig; reflexivity.
Qed.

(* At PRE_ROUTING, redirect still uses the inbound-interface address. *)
Theorem redir_prerouting_iifaddr : forall p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  apply_nat Hprerouting (redir_rule "ip") p
    = store_nat_mapping
        (set_daddr "ip" p (e_ifaddr (pkt_env p) (field_value FMetaIifname p)))
        (Some (slice (pkt_nh p) 16 4),
         Some (e_ifaddr (pkt_env p) (field_value FMetaIifname p)), None).
Proof.
  intros p Horig Hnone. unfold apply_nat, redir_rule, redir_spec.
  cbn -[set_daddr store_nat_mapping e_nat pkt_env pkt_flow e_ifaddr field_value redir_daddr
        slice pkt_nh].
  rewrite Hnone.
  unfold apply_nat_tuple, nat_is_src, nat_operand_addr, nat_addrfamily, redir_daddr,
    nat_orig_addr.
  cbn -[set_daddr store_nat_mapping e_ifaddr field_value slice pkt_nh]. rewrite ?Horig.
  reflexivity.
Qed.

(* The fix is observable on a well-formed IPv4 packet: when the inbound-interface
   address is NOT the loopback (the usual case) and the address slot is 4 bytes,
   reading `ip daddr` back after an OUTPUT-hook redirect yields 127.0.0.1, whereas
   after a PRE_ROUTING redirect it yields the iif address — so the two hooks
   diverge.  Before the fix [apply_nat] was hook-blind and these coincided. *)
Theorem redir_output_differs_from_prerouting : forall p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  20 <= List.length (pkt_nh p) ->
  List.length (e_ifaddr (pkt_env p) (field_value FMetaIifname p)) = 4 ->
  e_ifaddr (pkt_env p) (field_value FMetaIifname p) <> [127;0;0;1] ->
  apply_nat Houtput (redir_rule "ip") p <> apply_nat Hprerouting (redir_rule "ip") p.
Proof.
  intros p Horig Hnone Hnh Hlen Hne Heq.
  apply Hne.
  assert (Hread :
    field_value FIp4Daddr (apply_nat Houtput (redir_rule "ip") p)
    = field_value FIp4Daddr (apply_nat Hprerouting (redir_rule "ip") p))
    by (rewrite Heq; reflexivity).
  rewrite (redir_output_ip4_loopback p Horig Hnone),
          (redir_prerouting_iifaddr p Horig Hnone) in Hread.
  rewrite !store_nat_daddr in Hread.
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

(* The dnat-with-port effect: address rewrite followed by the L4 dest-port write,
   plus the stored flow mapping (Round-2).  The stored tuple records both the
   address and the port operand. *)
Lemma dnat_port_apply : forall h p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  apply_nat h dnat_port_rule p
    = store_nat_mapping (set_dport (set_daddr "ip" p [10;0;0;1]) [31; 144])
        (Some (slice (pkt_nh p) 16 4), Some [10;0;0;1], Some 8080).
Proof.
  intros h p Horig Hnone. unfold apply_nat, dnat_port_rule, dnat_port_spec.
  cbn -[set_dport set_daddr store_nat_mapping e_nat pkt_env pkt_flow slice pkt_nh].
  rewrite Hnone.
  unfold apply_nat_tuple, nat_orig_addr, nat_is_src, nat_addrfamily, nat_operand_addr.
  cbn -[set_dport set_daddr store_nat_mapping slice pkt_nh]. rewrite ?Horig; reflexivity.
Qed.

(* THE OUTPUT PACKET: dnat to A:PORT sets both the destination address and dport. *)
Theorem dnat_port_output : forall h p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  eval_chain_trace h dnat_port_chain p
    = (Accept, store_nat_mapping (set_dport (set_daddr "ip" p [10;0;0;1]) [31; 144])
                 (Some (slice (pkt_nh p) 16 4), Some [10;0;0;1], Some 8080)).
Proof.
  intros h p Horig Hnone.
  assert (Hw : dsl_writes dnat_port_rule p = p) by reflexivity.
  unfold eval_chain_trace, dnat_port_chain. cbn [c_rules eval_rules_trace].
  cbn -[apply_nat dnat_port_rule dsl_writes]. rewrite Hw.
  rewrite (dnat_port_apply h p Horig Hnone). reflexivity.
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
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  20 <= List.length (pkt_nh p) ->
  4 <= List.length (pkt_th p) ->
  read_payload PTransport 2 2 (chain_out dnat_port_chain p) = [31; 144].
Proof.
  intros p Horig Hnone Hnh Hth. unfold chain_out.
  rewrite (dnat_port_output Hprerouting p Horig Hnone). cbn [snd].
  (* set_daddr touches pkt_nh + (the disjoint L4 csum slot); pkt_th length preserved;
     store_nat_mapping leaves pkt_th untouched. *)
  unfold read_payload at 1. rewrite store_nat_th.
  fold (read_payload PTransport 2 2 (set_dport (set_daddr "ip" p [10;0;0;1]) [31;144])).
  apply dport_after_set; [rewrite set_daddr_th_len; exact Hth | reflexivity].
Qed.

(* The infidelity is REFUTED: the dnat-with-port chain does NOT leave the transport
   header unchanged (the red agent's [dnat_port_NOT_rewritten] is now false) — the
   L4 destination port IS rewritten whenever the current dport differs from 8080. *)
Theorem dnat_port_rewrites_th : forall p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  20 <= List.length (pkt_nh p) ->
  4 <= List.length (pkt_th p) ->
  read_payload PTransport 2 2 p <> [31; 144] ->
  pkt_th (chain_out dnat_port_chain p) <> pkt_th p.
Proof.
  intros p Horig Hnone Hnh Hth Hne Heq.
  apply Hne.
  rewrite <- (dnat_port_dport_is_8080 p Horig Hnone Hnh Hth).
  unfold read_payload. rewrite Heq. reflexivity.
Qed.

(** A `snat ... :PORT` rewrites the L4 SOURCE port (transport bytes 0..1), not the
    destination — the [NF_NAT_MANIP_SRC] half.  A dnat with NO port operand
    ([nat_pmin] = None, the address-only case) leaves the transport-header PORT
    bytes untouched (mirroring `if (priv->sreg_proto_min)`, nft_nat.c:120) — but
    NOT the transport header in full: see below, the L4 CHECKSUM is still updated
    for the address change. *)
Definition snat_port_spec : nat_spec :=
  {| nat_imms := [(1, [192;168;0;1])]; nat_field := None; nat_map := None; nat_src := None;
     nat_kind := "snat"; nat_family := "ip";
     nat_amin := None; nat_amax := None;
     nat_pmin := Some 4000; nat_pmax := Some 4000; nat_flags := 0 |}.
Definition snat_port_rule : rule :=
  {| r_body := []; r_verdict := Continue; r_vmap := None; r_nat := Some snat_port_spec;
     r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.

(* snat to A:PORT writes the SOURCE port (offset 0), leaving the dest port alone,
   and stores the (addr, port) mapping for the flow. *)
Theorem snat_port_writes_sport : forall h p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  apply_nat h snat_port_rule p
    = store_nat_mapping
        (set_sport (set_saddr "ip" p [192;168;0;1]) (nat_port_bytes 4000))
        (Some (slice (pkt_nh p) 12 4), Some [192;168;0;1], Some 4000).
Proof.
  intros h p Horig Hnone. unfold apply_nat, snat_port_rule, snat_port_spec.
  cbn -[set_sport set_saddr store_nat_mapping e_nat pkt_env pkt_flow slice pkt_nh].
  rewrite Hnone.
  unfold apply_nat_tuple, nat_orig_addr, nat_is_src, nat_addrfamily, nat_operand_addr.
  cbn -[set_sport set_saddr store_nat_mapping slice pkt_nh]. rewrite ?Horig; reflexivity.
Qed.

(* The address-only dnat ([nat_pmin]=None) leaves the L4 PORT bytes (transport
   slots 0..1 / 2..3) byte-for-byte unchanged — the kernel's
   `if (priv->sreg_proto_min)` is NOT taken — even though it does touch the L4
   CHECKSUM slot for the address change (see [dnat_addronly_updates_l4_csum]).
   The [store_nat_mapping] env write preserves [pkt_th]. *)
Theorem dnat_addronly_ports_preserved : forall h p poff plen,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  poff + plen <= 6 ->
  slice (pkt_th (apply_nat h dnat_rule p)) poff plen = slice (pkt_th p) poff plen.
Proof.
  intros h p poff plen Horig Hnone Hle.
  rewrite (dnat_apply h p Horig Hnone), store_nat_th.
  apply set_daddr_th_port; exact Hle.
Qed.

(** * Port-only NAT preserves the L3 address (independent address/proto guards).

    A `dnat to :PORT` (`snat to :PORT`) sets ONLY the proto-min register, never the
    addr-min register, so the kernel's [nft_nat_eval] takes the
    `if (priv->sreg_proto_min)` branch but NOT `if (priv->sreg_addr_min)`
    (nft_nat.c:114 vs :120): it rewrites ONLY the L4 port and leaves the L3
    destination/source address byte-for-byte UNCHANGED.  In the model such a spec
    has [nat_has_addr = false] (no register-1 immediate, no field/map/src), so
    [apply_nat] skips [set_daddr]/[set_saddr] entirely — preserving [pkt_nh] (hence
    the address and the header length) — and applies only [apply_nat_port].

    Before the address guard was added, [apply_nat] always did
    [set_daddr "ip" p (nat_addr ns p)] = [set_daddr "ip" p []], which SPLICED AN
    EMPTY list into the 4-byte daddr slot: it deleted 4 bytes of the IP header and
    shifted the rest left, corrupting/destroying the destination address. *)
Definition dnat_portonly_spec : nat_spec :=
  {| nat_imms := []; nat_field := None; nat_map := None; nat_src := None;
     nat_kind := "dnat"; nat_family := "ip";
     nat_amin := None; nat_amax := None;
     nat_pmin := Some 80; nat_pmax := Some 80; nat_flags := 0 |}.
Definition dnat_portonly_rule : rule :=
  {| r_body := []; r_verdict := Continue; r_vmap := None;
     r_nat := Some dnat_portonly_spec;
     r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.

(* The port-only spec carries NO address operand (kernel: no addr register). *)
Lemma dnat_portonly_no_addr : nat_has_addr dnat_portonly_spec = false.
Proof. reflexivity. Qed.

(* So [apply_nat] is a PURE L4 rewrite (plus the env store): it touches only the
   dest port, NOT the network header.  Contrast the old (buggy)
   [set_dport (set_daddr "ip" p [])].  The stored mapping carries NO address
   ([fst = None]) — only the port. *)
Theorem dnat_portonly_apply : forall h p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  apply_nat h dnat_portonly_rule p
    = store_nat_mapping (set_dport p (nat_port_bytes 80))
        (Some (slice (pkt_nh p) 16 4), None, Some 80).
Proof.
  intros h p Horig Hnone. unfold apply_nat, dnat_portonly_rule, dnat_portonly_spec.
  cbn -[set_dport store_nat_mapping e_nat pkt_env pkt_flow nat_port_bytes slice pkt_nh].
  rewrite Hnone.
  unfold apply_nat_tuple, nat_orig_addr, nat_is_src, nat_addrfamily, nat_operand_addr,
    nat_has_addr.
  cbn -[set_dport store_nat_mapping nat_port_bytes slice pkt_nh]. rewrite ?Horig.
  reflexivity.
Qed.

(* The network header is PRESERVED byte-for-byte (no splice, no truncation): the
   destination address — and the whole IP header — survives unchanged. *)
Theorem dnat_portonly_preserves_nh : forall h p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  pkt_nh (apply_nat h dnat_portonly_rule p) = pkt_nh p.
Proof.
  intros h p Horig Hnone.
  rewrite (dnat_portonly_apply h p Horig Hnone), store_nat_nh. reflexivity.
Qed.

(* Hence `ip daddr` reads back EXACTLY the input destination (the kernel guarantee
   the buggy model violated by deleting the slot). *)
Theorem dnat_portonly_preserves_daddr : forall h p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  field_value FIp4Daddr (apply_nat h dnat_portonly_rule p) = field_value FIp4Daddr p.
Proof.
  intros h p Horig Hnone. unfold field_value; cbn [field_load do_load].
  unfold read_payload, slice.
  rewrite (dnat_portonly_preserves_nh h p Horig Hnone). reflexivity.
Qed.

(* And it DOES rewrite the L4 destination port (the proto half still fires). *)
Theorem dnat_portonly_writes_dport : forall h p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  pkt_th (apply_nat h dnat_portonly_rule p) = splice (pkt_th p) 2 2 (nat_port_bytes 80).
Proof.
  intros h p Horig Hnone.
  rewrite (dnat_portonly_apply h p Horig Hnone), store_nat_th. reflexivity.
Qed.

(** * The IPv4 header checksum is NOT left stale after a NAT address rewrite.

    The kernel's [nf_nat_ipv4_manip_pkt] (nf_nat_proto.c:329-333) runs
    [csum_replace4(&iph->check, old_addr, new_addr)] in the SAME step as writing
    the new address, so the IPv4 header checksum (network bytes 10..11) is updated
    incrementally (RFC 1624).  The model now mirrors this in [set_daddr]/[set_saddr]
    (via [set_nh_addr_ip4] -> [csum_update_field]).  A red probe of the form
    `ip_csum (chain_out dnat_chain p) = ip_csum p` — asserting the checksum is
    UNCHANGED after a rewrite — is therefore now provably FALSE on a packet whose
    destination actually changes.

    [ip_csum] names the IPv4 header checksum slot (bytes 10..11). *)
Definition ip_csum (p : packet) : data := List.firstn 2 (List.skipn 10 (pkt_nh p)).

(* A concrete, well-formed 20-byte IPv4 header whose destination is 1.2.3.4 and
   whose checksum field starts at [0;0] (the slot we observe being updated). *)
Definition ip4_hdr : data :=
  [ 69; 0; 0; 20            (* ver/ihl, tos, total length *)
  ; 0; 0; 0; 0              (* id, frag *)
  ; 64; 6                   (* ttl, proto=TCP *)
  ; 0; 0                    (* header checksum (bytes 10..11) — observed *)
  ; 10; 0; 0; 2             (* source 10.0.0.2 *)
  ; 1; 2; 3; 4 ].           (* destination 1.2.3.4 -> dnat to 10.0.0.1 *)
Definition env0 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddr := fun _ => []; e_ifaddr6 := fun _ => [];
     e_connlimit := fun _ => 0;
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.
Definition pkt4 : packet :=
  {| pkt_env := env0; pkt_meta := fun _ => []; pkt_ct := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := ip4_hdr; pkt_th := [0;0;0;0;0;0;0;0]; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l4 := true; pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false; pkt_ctdir_orig := true |}.

(* The dnat rewrites the destination 1.2.3.4 -> 10.0.0.1, so the IPv4 header
   checksum slot MUST change.  The red property [ip_csum out = ip_csum p] is FALSE. *)
Theorem dnat_updates_ip_checksum :
  ip_csum (chain_out dnat_chain pkt4) <> ip_csum pkt4.
Proof. vm_compute. discriminate. Qed.

(* And the new checksum is exactly the RFC-1624 incremental update of the old
   checksum for the (old daddr -> new daddr) change — i.e. [csum_replace4]. *)
Theorem dnat_ip_checksum_is_incremental :
  ip_csum (chain_out dnat_chain pkt4)
    = csum_update_field (ip_csum pkt4) [1;2;3;4] [10;0;0;1].
Proof. vm_compute. reflexivity. Qed.

(** * The L4 (TCP/UDP) checksum is NOT left stale after an ADDRESS-ONLY NAT.

    The L4 (TCP/UDP) checksum covers the IPv4/IPv6 PSEUDO-HEADER, which includes
    the L3 addresses, so a `dnat`/`snat` that changes ONLY the address still
    changes the L4 checksum in real nftables.  The kernel's [nf_nat_ipv4_manip_pkt]
    (nf_nat_proto.c:324) ALWAYS runs [l4proto_manip_pkt] BEFORE the address splice;
    for TCP, [tcp_manip_pkt] (nf_nat_proto.c:177) calls [nf_csum_update] ->
    [inet_proto_csum_replace4(&hdr->check, ..., oldip, newip, true)]
    (nf_nat_proto.c:417), INDEPENDENT of any port change.  The model now mirrors
    this: [set_daddr]/[set_saddr] thread [set_l4_csum_addr], which updates the L4
    checksum slot (TCP @ transport 16..17, UDP @ 6..7) for the address delta.  A
    red probe `tcp_csum (chain_out dnat_chain p) = tcp_csum p` — asserting the TCP
    checksum is UNCHANGED after an address-only dnat — is now provably FALSE.

    [tcp_csum] names the TCP checksum slot (transport bytes 16..17). *)
Definition tcp_csum (p : packet) : data := slice (pkt_th p) 16 2.

(* A TCP-bearing packet: l4proto = TCP (6) in the meta oracle, and a 20-byte
   transport header so the TCP checksum slot (bytes 16..17) exists.  The checksum
   field starts at [0;0] (bytes 16..17 of pkt_th). *)
Definition pkt4tcp : packet :=
  {| pkt_env := env0;
     pkt_meta := fun k => if meta_eqb k MKl4proto then [6] else [];
     pkt_ct := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := ip4_hdr;
     pkt_th := [ 0;80; 0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0; 0;0; 0;0 ]; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l4 := true; pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false; pkt_ctdir_orig := true |}.

(* The dnat changes the destination 1.2.3.4 -> 10.0.0.1, so the TCP checksum slot
   MUST change (the pseudo-header covers the address).  The red property
   [tcp_csum out = tcp_csum p] — the certified falsehood — is now FALSE. *)
Theorem dnat_updates_tcp_checksum :
  tcp_csum (chain_out dnat_chain pkt4tcp) <> tcp_csum pkt4tcp.
Proof. vm_compute. discriminate. Qed.

(* The new TCP checksum is exactly the RFC-1624 incremental update of the old
   checksum for the (old daddr -> new daddr) change — i.e. the address delta
   folded into the L4 checksum, modelling [inet_proto_csum_replace4]. *)
Theorem dnat_tcp_checksum_is_incremental :
  tcp_csum (chain_out dnat_chain pkt4tcp)
    = csum_update_field (tcp_csum pkt4tcp) [1;2;3;4] [10;0;0;1].
Proof. vm_compute. reflexivity. Qed.

(* The L4 PORT bytes (transport slots 0..1 sport / 2..3 dport) are NOT disturbed
   by the address-only dnat — only the address-driven L4 checksum is. *)
Theorem dnat_addronly_tcp_ports_unchanged :
  slice (pkt_th (chain_out dnat_chain pkt4tcp)) 0 4
    = slice (pkt_th pkt4tcp) 0 4.
Proof. vm_compute. reflexivity. Qed.

(** * A ZERO UDP checksum ("checksum disabled", RFC 768) is LEFT UNTOUCHED by NAT.

    A UDP checksum field of 0 means "no checksum" — legal for IPv4 UDP (RFC 768).
    The kernel's [udp_manip_pkt] (nf_nat_proto.c:65) passes `do_csum = !!hdr->check`
    and [__udp_manip_pkt] (nf_nat_proto.c:55) guards the ENTIRE checksum update
    (`nf_csum_update` + `inet_proto_csum_replace2` + the CSUM_MANGLED_0 fixup) under
    `if (do_csum)`.  So a dnat/snat changing the L3 address on a UDP packet whose
    checksum is 0 leaves that field byte-for-byte 0.  The model now mirrors this:
    [set_l4_csum_addr] gates the UDP (mandatory=false) update on a non-zero existing
    checksum, so a zero stays zero.

    [udp_csum] names the UDP checksum slot (transport bytes 6..7). *)
Definition udp_csum (p : packet) : data := slice (pkt_th p) 6 2.

(* A UDP packet with the checksum field (bytes 6..7) ZERO ("checksum disabled"). *)
Definition pkt4udp0 : packet :=
  {| pkt_env := env0;
     pkt_meta := fun k => if meta_eqb k MKl4proto then [17] else [];
     pkt_ct := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := ip4_hdr;
     (* UDP header: sport=0;80  dport=0;0  len=0;8  check=0;0 *)
     pkt_th := [ 0;80; 0;0; 0;8; 0;0 ]; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l4 := true; pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false; pkt_ctdir_orig := true |}.

(* CORRECTED behavior: the zero UDP checksum is LEFT ZERO after an address dnat
   (the kernel's do_csum=false path).  This is the property the old red probe
   showed UNPROVABLE before the fix; it now holds by reflexivity. *)
Theorem dnat_leaves_zero_udp_checksum_zero :
  udp_csum (chain_out dnat_chain pkt4udp0) = udp_csum pkt4udp0.
Proof. vm_compute. reflexivity. Qed.

(* Stated absolutely: the field stays exactly [0;0]. *)
Theorem dnat_zero_udp_checksum_is_zero :
  udp_csum (chain_out dnat_chain pkt4udp0) = [0;0].
Proof. vm_compute. reflexivity. Qed.

(* A UDP packet with a NON-ZERO checksum IS updated for the address delta (the
   kernel's do_csum=true path), so the gate is non-vacuous — it discriminates on
   the checksum value, not the protocol. *)
Definition pkt4udpc : packet :=
  {| pkt_env := env0;
     pkt_meta := fun k => if meta_eqb k MKl4proto then [17] else [];
     pkt_ct := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := ip4_hdr;
     (* UDP header with a non-zero checksum field (bytes 6..7 = [171;205]) *)
     pkt_th := [ 0;80; 0;0; 0;8; 171;205 ]; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l4 := true; pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false; pkt_ctdir_orig := true |}.

Theorem dnat_updates_nonzero_udp_checksum :
  udp_csum (chain_out dnat_chain pkt4udpc) <> udp_csum pkt4udpc.
Proof. vm_compute. discriminate. Qed.

Theorem dnat_nonzero_udp_checksum_is_incremental :
  udp_csum (chain_out dnat_chain pkt4udpc)
    = csum_update_field (udp_csum pkt4udpc) [1;2;3;4] [10;0;0;1].
Proof. vm_compute. reflexivity. Qed.
