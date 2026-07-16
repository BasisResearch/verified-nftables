(** * Verified packet properties of the PARSED ruleset.nft.

    Same worked example as [Example_Ruleset.v], but with the crucial difference
    that the AST here is NOT hand-translated: [Ruleset_Gen.v] is the Menhir
    frontend's output on ../../rulesets/ruleset.nft (the chains [firewall_inbound], ... and
    the verdict maps / sets in [gen_env]).  These theorems are therefore about the
    parser's actual output — closing the one previously-eyeballed link ("the AST
    mirrors the .nft text").  Via [compile_table_correct] each property holds of
    the installed netlink bytecode too. *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Ruleset_Gen Nftval Eval_Fw.
Import ListNotations.
Open Scope string_scope.

(** Concrete wire values (only equality/order matters).  The ct-state values are
    routed through the central typed nft constructors + [encode] (as
    [Example_Ruleset]/[Nftval] do) so the byte literals cannot drift from the
    central conntrack-state encoding; [Eval compute] reduces each to the very
    literal the [cbn]-based proofs match against. *)
Definition cts_invalid     : data := Eval compute in encode ct_invalid.      (* [0;0;0;1] *)
Definition cts_established : data := Eval compute in encode ct_established.   (* [0;0;0;2] *)
Definition cts_related     : data := Eval compute in encode ct_related.      (* [0;0;0;4] *)
Definition cts_new         : data := Eval compute in encode ct_new.          (* [0;0;0;8] *)
Definition eth_ip  : data := [8;0].
Definition eth_ip6 : data := [134;221].
Definition l4_tcp   : data := [6].
Definition l4_icmp6 : data := [58].
Definition port (n : nat) : data := [Nat.div n 256; Nat.modulo n 256].
Definition icmp6_nd_nsol : data := [135].
(* ifname registers are fixed 16-byte (IFNAMSIZ) zero-padded buffers; the
   kernel compares the full 16-byte buffer for an exact name match. *)
Definition if_lo  : data := [108;111; 0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0].  (* "lo" *)
Definition if_eth : data := [101;116;104;48; 0;0;0;0; 0;0;0;0; 0;0;0;0].  (* "eth0" *)

Definition fw_fuel : nat := 8.

(** Symbolically evaluate the parsed table: unfold this module's parser-emitted
    chain definitions, then run the shared [eval_fw_core] engine (Eval_Fw.v).
    [erj_nil]/[erj_cons] and [Global Opaque eval_rules_j] live in Eval_Fw.v. *)
Ltac eval_fw Hpe :=
  unfold eval_table, fw_fuel, firewall_chains,
         firewall_inbound, firewall_inbound_ipv4, firewall_inbound_ipv6,
         firewall_forward;
  eval_fw_core Hpe.

(** ** The properties (each universally quantified over the packet).

    NOTE — twin theorem names: [established_accepted], [invalid_dropped] and
    [loopback_accepted] also exist in [Example_Ruleset.v].  These are NOT
    duplicates: the [Example_Ruleset.v] copies are the hand-written baseline
    (eval_table over [fw_chains]/[inbound]); the copies HERE are over the
    parser-emitted chains ([firewall_chains]/[firewall_inbound], from
    [Ruleset_Gen.v]).  A grep by name finds both — this one is the
    parser-output witness.

    M4 KNOWN GAP — as in the baseline file: the [e = gen_env] pin makes the
    established/related/new ct-state theorems below vacuous as stated
    ([gen_env] has an empty [e_ct]; proof shape
    [Router_Realistic.ctstate_under_genenv_never_new]); invalid/non-ct
    theorems are unaffected.  Recipe + status: Example_Ruleset.v's M4 note,
    CONFIG_PROOFS.md § "Pin only what the lookups read", THEOREMS.md §5. *)

(* Established connections are accepted (the ct-state vmap hit). *)
Theorem established_accepted : forall e p,
  e = gen_env ->
  field_value FCtState e p = cts_established ->
  eval_table fw_fuel firewall_chains firewall_inbound e p = Accept.
Proof. intros e p Hpe Hct. eval_fw Hpe. Qed.

(* Invalid-state packets are dropped (the `invalid : drop` vmap entry). *)
Theorem invalid_dropped : forall e p,
  e = gen_env ->
  field_value FCtState e p = cts_invalid ->
  eval_table fw_fuel firewall_chains firewall_inbound e p = Drop.
Proof. intros e p Hpe Hct. eval_fw Hpe. Qed.

(* Loopback traffic is accepted (new connection -> vmap misses -> iifname lo). *)
Theorem loopback_accepted : forall e p,
  e = gen_env ->
  field_value FCtState e p = cts_new ->
  field_value FMetaIifname e p = if_lo ->
  eval_table fw_fuel firewall_chains firewall_inbound e p = Accept.
Proof. intros e p Hpe Hct Hiif. eval_fw Hpe. Qed.

(* SSH (TCP/22) over IPv4, new connection, real interface: accepted via the jump
   into inbound_ipv4 (empty) and the `tcp dport {22,80,443}` set. *)
Theorem ssh_accepted : forall e p,
  e = gen_env ->
  field_value FCtState e p = cts_new ->
  field_value FMetaIifname e p = if_eth ->
  field_value FMetaProtocol e p = eth_ip ->
  field_value FMetaL4proto e p = l4_tcp ->
  field_value FThDport e p = port 22 ->
  read_payload_ok PTransport 2 2 p = true ->
  eval_table fw_fuel firewall_chains firewall_inbound e p = Accept.
Proof. intros e p Hpe Hct Hiif Hpr Hl4 Hdp Hok. eval_fw Hpe. Qed.

(* A closed TCP port (SMTP/25), new IPv4 connection: dropped by `policy drop` —
   the security guarantee (unsolicited traffic to closed ports is denied). *)
Theorem smtp_dropped : forall e p,
  e = gen_env ->
  field_value FCtState e p = cts_new ->
  field_value FMetaIifname e p = if_eth ->
  field_value FMetaProtocol e p = eth_ip ->
  field_value FMetaL4proto e p = l4_tcp ->
  field_value FThDport e p = port 25 ->
  read_payload_ok PTransport 2 2 p = true ->
  eval_table fw_fuel firewall_chains firewall_inbound e p = Drop.
Proof. intros e p Hpe Hct Hiif Hpr Hl4 Hdp Hok. eval_fw Hpe. Qed.

(* IPv6 neighbour discovery is accepted via the jump into inbound_ipv6.
   In the inet table the `icmpv6 type {...}` rule carries the implicit
   `meta nfproto == 10` (NFPROTO_IPV6) network guard that real nft inserts before
   every icmpv6 match (icmpv6 is an IPv6-only L4 protocol), so a genuine IPv6 ND
   packet (nfproto = 10) is required for the match to fire. *)
Definition nfproto_ip6 : data := [10].
Theorem ipv6_nd_accepted : forall e p,
  e = gen_env ->
  field_value FCtState e p = cts_new ->
  field_value FMetaIifname e p = if_eth ->
  field_value FMetaProtocol e p = eth_ip6 ->
  field_value FMetaNfproto e p = nfproto_ip6 ->
  field_value FMetaL4proto e p = l4_icmp6 ->
  field_value FIcmpType e p = icmp6_nd_nsol ->
  read_payload_ok PTransport 2 2 p = true ->
  read_payload_ok PTransport 0 1 p = true ->
  eval_table fw_fuel firewall_chains firewall_inbound e p = Accept.
Proof. intros e p Hpe Hct Hiif Hpr Hnfp Hl4 Hty Hok Hok2. eval_fw Hpe. Qed.

(* The forward hook drops everything (no rules, policy drop). *)
Theorem forward_drops_all : forall e p,
  eval_table fw_fuel firewall_chains firewall_forward e p = Drop.
Proof.
  intros e p. unfold eval_table, fw_fuel, firewall_forward.
  cbn -[eval_rules_j]. rewrite erj_nil. reflexivity.
Qed.
