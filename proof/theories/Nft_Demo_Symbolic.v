(** * Nft_Demo_Symbolic: re-express SYMBOLIC per-config theorems with Nft_Tactics.

    [Ruleset_Verified.v] proves properties of the PARSER-emitted firewall chains
    for a packet [p] constrained only by [pkt_env]/[field_value] hypotheses, with
    the per-module [eval_fw] ritual.  Here we re-state the SAME theorems through
    the [Nft_Tactics] layer:

      - the conclusion reads [firewall_inbound accepts p under firewall_chains
        budget fw_fuel] instead of the raw [eval_table … = Accept];
      - the hypotheses read [fieldof FCtState p === ct_established] — routed
        through the central [Nftval] typed constructor [ct_established] — instead
        of a raw [field_value … = [0;0;0;2]];
      - the proof is a single [nft_eval Hpe] instead of the unfold list +
        [eval_fw_core].

    SOUNDNESS: [demo_*_def] prove the readable conclusion / hypothesis are
    DEFINITIONALLY the raw statements ([reflexivity]); [demo_recovers_original]
    re-derives the ORIGINAL [Ruleset_Verified]-shaped statement (raw [eval_table],
    raw [cts_established]) from the readable one — so nothing was weakened.  Both
    headline demos are guarded axiom-free by [Print Assumptions]. *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Nftval Eval_Fw
                       Ruleset_Gen Ruleset_Verified Nft_Tactics.
Import ListNotations.
Open Scope string_scope.

(** Register this ruleset's chains so [nft_eval] needs no per-module unfold list. *)
#[local] Hint Unfold fw_fuel firewall_chains firewall_inbound
  firewall_inbound_ipv4 firewall_inbound_ipv6 firewall_forward : nft_chains.

(* ------------------------------------------------------------------ *)
(** ** The readable layer is DEFINITIONALLY the raw statement. *)

Example demo_accepts_def : forall p,
  (firewall_inbound accepts p under firewall_chains budget fw_fuel)
  = (eval_table fw_fuel firewall_chains firewall_inbound p = Accept).
Proof. reflexivity. Qed.

Example demo_denies_def : forall p,
  (firewall_inbound denies p under firewall_chains budget fw_fuel)
  = (eval_table fw_fuel firewall_chains firewall_inbound p = Drop).
Proof. reflexivity. Qed.

Example demo_fieldis_def : forall p,
  (fieldof FCtState p === ct_established)
  = (field_value FCtState p = encode ct_established).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** Re-expressed theorems (same content as [Ruleset_Verified], readable). *)

(** Established connections are accepted (the ct-state vmap hit).  Mirrors
    [Ruleset_Verified.established_accepted]. *)
Theorem demo_established_accepted : forall p,
  pkt_env p = gen_env ->
  fieldof FCtState p === ct_established ->
  firewall_inbound accepts p under firewall_chains budget fw_fuel.
Proof. intros p Hpe Hct. nft_eval Hpe. Qed.
Print Assumptions demo_established_accepted.

(** A closed TCP port (SMTP/25), new IPv4 connection, is DROPPED by policy.
    Mirrors [Ruleset_Verified.smtp_dropped]. *)
Theorem demo_smtp_dropped : forall p,
  pkt_env p = gen_env ->
  fieldof FCtState p === ct_new ->
  fieldof FMetaIifname p === ifname "eth0" ->
  field_value FMetaProtocol p = eth_ip ->
  field_value FMetaL4proto p = l4_tcp ->
  field_value FThDport p = port 25 ->
  read_payload_ok PTransport 2 2 p = true ->
  firewall_inbound denies p under firewall_chains budget fw_fuel.
Proof. intros p Hpe Hct Hiif Hpr Hl4 Hdp Hok. nft_eval Hpe. Qed.
Print Assumptions demo_smtp_dropped.

(* ------------------------------------------------------------------ *)
(** ** The readable theorem RE-DERIVES the original (nothing weakened).

    [demo_established_accepted]'s typed hypothesis [fieldof FCtState p ===
    ct_established] is convertible to [Ruleset_Verified]'s raw
    [field_value FCtState p = cts_established] (as [cts_established :=
    encode ct_established]); and its conclusion is convertible to the raw
    [eval_table … = Accept].  So the original statement follows by [apply]. *)
Theorem demo_recovers_original : forall p,
  pkt_env p = gen_env ->
  field_value FCtState p = cts_established ->
  eval_table fw_fuel firewall_chains firewall_inbound p = Accept.
Proof. intros p Hpe Hct. apply demo_established_accepted; assumption. Qed.
