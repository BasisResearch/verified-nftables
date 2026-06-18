(** * Verified packet properties of the PARSED ruleset.nft.

    Same worked example as [Example_Ruleset.v], but with the crucial difference
    that the AST here is NOT hand-translated: [Ruleset_Gen.v] is the Menhir
    frontend's output on ../../ruleset.nft (the chains [firewall_inbound], ... and
    the verdict maps / sets in [gen_env]).  These theorems are therefore about the
    parser's actual output — closing the one previously-eyeballed link ("the AST
    mirrors the .nft text").  Via [compile_table_correct] each property holds of
    the installed netlink bytecode too. *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Ruleset_Gen.
Import ListNotations.
Open Scope string_scope.

(** Concrete wire values (only equality/order matters). *)
Definition cts_invalid     : data := [0;0;0;1].
Definition cts_established : data := [0;0;0;2].
Definition cts_related     : data := [0;0;0;4].
Definition cts_new         : data := [0;0;0;8].
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

(** One-step unfolding lemmas for the fuel-recursive interpreter (kept opaque
    during evaluation so [cbn] reduces only the current rule). *)
Lemma erj_nil : forall n cs p, eval_rules_j (S n) cs [] p = None.
Proof. reflexivity. Qed.

Lemma erj_cons : forall n cs r rest p,
  eval_rules_j (S n) cs (r :: rest) p =
  (if andb (rule_loadable r p) (rule_applies r p)
   then match outcome r p with
        | None => eval_rules_j n cs rest p
        | Some Return => None
        | Some (Jump m) =>
            match chain_lookup cs m with
            | Some ch => match eval_rules_j n cs (c_rules ch) p with
                         | Some v => Some v | None => eval_rules_j n cs rest p end
            | None => eval_rules_j n cs rest p
            end
        | Some (Goto m) =>
            match chain_lookup cs m with
            | Some ch => eval_rules_j n cs (c_rules ch) p | None => None end
        | Some Continue => eval_rules_j n cs rest p
        | Some v => Some v
        end
   else eval_rules_j n cs rest p).
Proof. reflexivity. Qed.

Opaque eval_rules_j.

(** Symbolically evaluate the parsed table, stepping one rule at a time and
    rewriting field values from the hypotheses as each match is reached. *)
Ltac eval_fw Hpe :=
  unfold eval_table, fw_fuel, firewall_chains,
         firewall_inbound, firewall_inbound_ipv4, firewall_inbound_ipv6,
         firewall_forward;
  repeat first
    [ rewrite Hpe
    | rewrite erj_nil
    | rewrite erj_cons
    | match goal with H : field_value _ _ = _ |- _ => rewrite H end
    | match goal with H : read_payload_ok _ _ _ _ = _ |- _ => rewrite H end
    | progress unfold rule_loadable, rule_applies, end_loadable, tail_loadable,
        terminal_loadable, vmap_loadable, body_item_loadable, match_loadable,
        fields_loadable, field_loadable, load_ok, eval_matchcond, eval_matchcond_body
    | progress cbn -[eval_rules_j field_value read_payload_ok pkt_env] ];
  reflexivity.

(** ** The properties (each universally quantified over the packet). *)

(* Established connections are accepted (the ct-state vmap hit). *)
Theorem established_accepted : forall p,
  pkt_env p = gen_env ->
  field_value FCtState p = cts_established ->
  eval_table fw_fuel firewall_chains firewall_inbound p = Accept.
Proof. intros p Hpe Hct. eval_fw Hpe. Qed.

(* Invalid-state packets are dropped (the `invalid : drop` vmap entry). *)
Theorem invalid_dropped : forall p,
  pkt_env p = gen_env ->
  field_value FCtState p = cts_invalid ->
  eval_table fw_fuel firewall_chains firewall_inbound p = Drop.
Proof. intros p Hpe Hct. eval_fw Hpe. Qed.

(* Loopback traffic is accepted (new connection -> vmap misses -> iifname lo). *)
Theorem loopback_accepted : forall p,
  pkt_env p = gen_env ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_lo ->
  eval_table fw_fuel firewall_chains firewall_inbound p = Accept.
Proof. intros p Hpe Hct Hiif. eval_fw Hpe. Qed.

(* SSH (TCP/22) over IPv4, new connection, real interface: accepted via the jump
   into inbound_ipv4 (empty) and the `tcp dport {22,80,443}` set. *)
Theorem ssh_accepted : forall p,
  pkt_env p = gen_env ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_eth ->
  field_value FMetaProtocol p = eth_ip ->
  field_value FMetaL4proto p = l4_tcp ->
  field_value FThDport p = port 22 ->
  read_payload_ok PTransport 2 2 p = true ->
  eval_table fw_fuel firewall_chains firewall_inbound p = Accept.
Proof. intros p Hpe Hct Hiif Hpr Hl4 Hdp Hok. eval_fw Hpe. Qed.

(* A closed TCP port (SMTP/25), new IPv4 connection: dropped by `policy drop` —
   the security guarantee (unsolicited traffic to closed ports is denied). *)
Theorem smtp_dropped : forall p,
  pkt_env p = gen_env ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_eth ->
  field_value FMetaProtocol p = eth_ip ->
  field_value FMetaL4proto p = l4_tcp ->
  field_value FThDport p = port 25 ->
  read_payload_ok PTransport 2 2 p = true ->
  eval_table fw_fuel firewall_chains firewall_inbound p = Drop.
Proof. intros p Hpe Hct Hiif Hpr Hl4 Hdp Hok. eval_fw Hpe. Qed.

(* IPv6 neighbour discovery is accepted via the jump into inbound_ipv6. *)
Theorem ipv6_nd_accepted : forall p,
  pkt_env p = gen_env ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_eth ->
  field_value FMetaProtocol p = eth_ip6 ->
  field_value FMetaL4proto p = l4_icmp6 ->
  field_value FIcmpType p = icmp6_nd_nsol ->
  read_payload_ok PTransport 2 2 p = true ->
  read_payload_ok PTransport 0 1 p = true ->
  eval_table fw_fuel firewall_chains firewall_inbound p = Accept.
Proof. intros p Hpe Hct Hiif Hpr Hl4 Hty Hok Hok2. eval_fw Hpe. Qed.

(* The forward hook drops everything (no rules, policy drop). *)
Theorem forward_drops_all : forall p,
  eval_table fw_fuel firewall_chains firewall_forward p = Drop.
Proof.
  intros p. unfold eval_table, fw_fuel, firewall_forward.
  cbn -[eval_rules_j]. rewrite erj_nil. reflexivity.
Qed.
