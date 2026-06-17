(** * Example: verifying properties of a real ruleset (../../ruleset.nft).

    This file demonstrates the use case from the project's brief: a user has a
    ruleset, already in AST form, and wants to *prove* which packets it accepts
    and rejects given the set/map state it declares.

    [ruleset.nft] is the stock nftables "workstation" ruleset.  We translate its
    base chain `inbound` (and the chains it jumps to) by hand into the DSL AST of
    [Syntax.v], then prove packet-level security properties against the
    [eval_table] semantics of [Semantics.v] — first-match evaluation with
    jump/return and a default policy.

    Two things make these proofs meaningful:
      - They are stated against the *specification* ([eval_table]), not the
        compiler, so they are claims about what the ruleset *means*.
      - [compile_table_correct] proves the compiled netlink bytecode reproduces
        [eval_table] exactly, so every property here transports to the installed
        ruleset (we show the transport once, in [smtp_dropped_in_bytecode]).

    ----------------------------------------------------------------------------
    FAITHFULNESS OF THE TRANSLATION (checked against the source and nft's lowering)

    The source `inbound` chain (ruleset.nft:25-46) is:

        type filter hook input priority 0; policy drop;
        ct state vmap { established : accept, related : accept, invalid : drop }
        iifname lo accept
        meta protocol vmap { ip : jump inbound_ipv4, ip6 : jump inbound_ipv6 }
        tcp dport { 22, 80, 443 } accept

    Translation decisions, each matching how nft actually lowers the rule:
      - `tcp dport {…}` / `icmpv6 type {…}` carry the implicit L4-protocol
        dependency nft inserts (`meta l4proto tcp` / `… ipv6-icmp`), modelled as a
        leading [MEq FMetaL4proto _] before the set-membership match.
      - the inline *anonymous* sets/maps (`{22,80,443}`, the two vmaps) have
        contents fixed by the rule text, so we pin them in [fw_env]; a property is
        stated "under the sets this ruleset declares" via [pkt_env p = fw_env].
      - `meta protocol` is the L3 ethertype (0x0800 / 0x86dd); `ct state` values
        are the kernel NF_CT_STATE bits; ports/types are their wire bytes.  These
        are the genuinely packet-/kernel-provided fields, hypothesised per theorem.
      - exact-match equalities (`iifname lo`, the L4-proto deps) use the model's
        [MEq], which compares the first [length v] bytes (the project's
        wildcard-aware equality; for a non-wildcard short ifname the kernel does a
        full 16-byte compare — a documented minor infidelity, see DEVELOPMENT.md).
        Every value we compare here is given at its exact wire width, so the
        comparison is exact. *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Compile Correct.
Import ListNotations.
Open Scope string_scope.

(** ** Concrete wire values (bytes are [nat]; only equality/order matters). *)

(* ct state: the NF_CT_STATE_BIT_* values, as 4-byte conntrack-state words. *)
Definition cts_invalid     : data := [0;0;0;1].
Definition cts_established : data := [0;0;0;2].
Definition cts_related     : data := [0;0;0;4].
Definition cts_new         : data := [0;0;0;8].

(* meta protocol = L3 ethertype. *)
Definition eth_ip  : data := [8;0].      (* 0x0800 *)
Definition eth_ip6 : data := [134;221].  (* 0x86dd *)

(* meta l4proto (IP protocol number). *)
Definition l4_tcp   : data := [6].
Definition l4_icmp6 : data := [58].      (* ipv6-icmp *)

(* tcp dport, 2 bytes big-endian. *)
Definition port (n : nat) : data := [Nat.div n 256; Nat.modulo n 256].

(* icmpv6 ND types, 1 byte. *)
Definition icmp6_nd_nsol : data := [135]. (* nd-neighbor-solicit *)
Definition icmp6_nd_radv : data := [134]. (* nd-router-advert *)
Definition icmp6_nd_nadv : data := [136]. (* nd-neighbor-advert *)

(* interface names, as their leading bytes. *)
Definition if_lo  : data := [108;111].          (* "lo"   *)
Definition if_eth : data := [101;116;104;48].   (* "eth0" *)

(** ** The set/map state the ruleset declares (inline anonymous sets/maps).

    A set element is a closed interval [lo,hi]; an exact element is [x,x]. *)
Definition dports_set : list (data * data) :=
  [ (port 22, port 22); (port 80, port 80); (port 443, port 443) ].
Definition nd_types_set : list (data * data) :=
  [ (icmp6_nd_nsol, icmp6_nd_nsol)
  ; (icmp6_nd_radv, icmp6_nd_radv)
  ; (icmp6_nd_nadv, icmp6_nd_nadv) ].
Definition ctstate_vmap : list (data * verdict) :=
  [ (cts_established, Accept); (cts_related, Accept); (cts_invalid, Drop) ].
Definition protocol_vmap : list (data * verdict) :=
  [ (eth_ip, Jump "inbound_ipv4"); (eth_ip6, Jump "inbound_ipv6") ].

(** The evaluation environment: the sets/maps above, looked up by name; the
    other state (routes, limiters) is irrelevant to these rules. *)
Definition fw_env : env :=
  {| e_set := fun n => if String.eqb n "dports" then dports_set
                       else if String.eqb n "nd_types" then nd_types_set
                       else [];
     e_vmap := fun n => if String.eqb n "ctstate" then ctstate_vmap
                        else if String.eqb n "protocol" then protocol_vmap
                        else [];
     e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => [];
     e_ifaddr := (fun _ => []);
     e_limit := fun _ => 0; e_quota := fun _ => 0; e_connlimit := fun _ => 0 |}.

(** ** The chains, translated rule-for-rule from ruleset.nft. *)

(* a rule with only a body and a static verdict (no vmap/nat/…). *)
Definition simple_rule (body : list body_item) (v : verdict) : rule :=
  {| r_body := body; r_verdict := v;
     r_vmap := None; r_nat := None; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.

(* a rule whose verdict comes from a vmap keyed on a single field. *)
Definition vmap_rule (key : field) (name : string) : rule :=
  {| r_body := []; r_verdict := Continue;
     r_vmap := Some {| vm_fields := []; vm_keyf := Some (key, []); vm_name := name |};
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.

(* inbound (ruleset.nft:25-46) — the input base chain, policy drop. *)
Definition inbound : chain :=
  {| c_policy := Drop;
     c_rules :=
       [ (* ct state vmap { established:accept, related:accept, invalid:drop } *)
         vmap_rule FCtState "ctstate"
       ; (* iifname lo accept *)
         simple_rule [BMatch (MEq FMetaIifname if_lo)] Accept
       ; (* meta protocol vmap { ip: jump inbound_ipv4, ip6: jump inbound_ipv6 } *)
         vmap_rule FMetaProtocol "protocol"
       ; (* tcp dport { 22, 80, 443 } accept  (with the l4proto dependency) *)
         simple_rule [ BMatch (MEq FMetaL4proto l4_tcp)
                     ; BMatch (MConcatSet [FThDport] false "dports") ] Accept
       ] |}.

(* inbound_ipv4 (ruleset.nft:5-11) — empty (only commented-out rules). *)
Definition inbound_ipv4 : chain := {| c_policy := Continue; c_rules := [] |}.

(* inbound_ipv6 (ruleset.nft:13-23) — accept ND, rest commented out.
   `icmpv6 type {…}` carries the `meta l4proto ipv6-icmp` dependency; icmpv6 type
   is the 1-byte field at the start of the transport header. *)
Definition inbound_ipv6 : chain :=
  {| c_policy := Continue;
     c_rules :=
       [ simple_rule [ BMatch (MEq FMetaL4proto l4_icmp6)
                     ; BMatch (MConcatSet [FIcmpType] false "nd_types") ] Accept ] |}.

(* forward (ruleset.nft:48-51) — drop everything. *)
Definition forward : chain := {| c_policy := Drop; c_rules := [] |}.

(* the jump-target chain environment for the input hook. *)
Definition fw_chains : list (string * chain) :=
  [ ("inbound_ipv4", inbound_ipv4); ("inbound_ipv6", inbound_ipv6) ].

(* fuel: an upper bound on chain-traversal depth (4 rules + one jump).  Kept
   tight because [cbn] symbolically expands the fuel-recursion tree. *)
Definition fw_fuel : nat := 8.

(** One-step unfolding lemmas for the fuel-recursive chain interpreter.  We keep
    [eval_rules_j] opaque during evaluation and step it with these, so [cbn] only
    ever reduces the *current* rule (rather than symbolically expanding the whole
    fuel-bounded traversal tree, which blows up). *)
Lemma erj_nil : forall n cs p, eval_rules_j (S n) cs [] p = None.
Proof. reflexivity. Qed.

Lemma erj_cons : forall n cs r rest p,
  eval_rules_j (S n) cs (r :: rest) p =
  (if rule_applies r p
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

Global Opaque eval_rules_j.

(** Symbolically evaluate [eval_table] over the concrete chains, stepping one
    rule at a time and rewriting the per-packet field values from the hypotheses
    as each match is reached.  [field_value]/[pkt_env]/[eval_rules_j] are kept
    folded so the field hypotheses can rewrite [field_value _ p], [pkt_env p]
    resolves to [fw_env], and the recursion does not explode. *)
Ltac eval_fw Hpe :=
  unfold eval_table, fw_fuel, fw_chains, inbound, inbound_ipv4, inbound_ipv6;
  repeat first
    [ rewrite Hpe
    | rewrite erj_nil
    | rewrite erj_cons
    | match goal with H : field_value _ _ = _ |- _ => rewrite H end
    | progress cbn -[eval_rules_j field_value pkt_env] ];
  reflexivity.

(** ** The properties.

    Each is universally quantified over the packet [p]; the only hypotheses are
    the field values the verdict actually depends on (and that [p] is evaluated
    under the sets this ruleset declares). *)

(* Established connections are accepted (the first rule's vmap hit). *)
Theorem established_accepted : forall p,
  pkt_env p = fw_env ->
  field_value FCtState p = cts_established ->
  eval_table fw_fuel fw_chains inbound p = Accept.
Proof. intros p Hpe Hct. eval_fw Hpe. Qed.

(* Invalid-state packets are dropped, regardless of anything else — the vmap
   `invalid : drop` in the first rule short-circuits the whole chain. *)
Theorem invalid_dropped : forall p,
  pkt_env p = fw_env ->
  field_value FCtState p = cts_invalid ->
  eval_table fw_fuel fw_chains inbound p = Drop.
Proof. intros p Hpe Hct. eval_fw Hpe. Qed.

(* Loopback traffic is accepted (for a fresh/new connection, so the ct-state
   vmap misses and rule 2 is reached). *)
Theorem loopback_accepted : forall p,
  pkt_env p = fw_env ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_lo ->
  eval_table fw_fuel fw_chains inbound p = Accept.
Proof. intros p Hpe Hct Hiif. eval_fw Hpe. Qed.

(* SSH (TCP/22) over IPv4 from a new connection on a real interface is accepted:
   ct-state miss -> not loopback -> jump inbound_ipv4 (empty, returns) ->
   tcp dport 22 is in {22,80,443} -> accept. *)
Theorem ssh_accepted : forall p,
  pkt_env p = fw_env ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_eth ->
  field_value FMetaProtocol p = eth_ip ->
  field_value FMetaL4proto p = l4_tcp ->
  field_value FThDport p = port 22 ->
  eval_table fw_fuel fw_chains inbound p = Accept.
Proof. intros p Hpe Hct Hiif Hpr Hl4 Hdp. eval_fw Hpe. Qed.

(* A closed TCP port (e.g. 25/SMTP) on a new IPv4 connection is dropped: every
   rule falls through and the chain's `policy drop` applies.  This is the
   security guarantee — unsolicited traffic to closed ports is denied. *)
Theorem smtp_dropped : forall p,
  pkt_env p = fw_env ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_eth ->
  field_value FMetaProtocol p = eth_ip ->
  field_value FMetaL4proto p = l4_tcp ->
  field_value FThDport p = port 25 ->
  eval_table fw_fuel fw_chains inbound p = Drop.
Proof. intros p Hpe Hct Hiif Hpr Hl4 Hdp. eval_fw Hpe. Qed.

(* The IPv6 path: a new IPv6 TCP connection to a closed port is also dropped.
   meta protocol = ip6 -> jump inbound_ipv6, whose only rule matches ICMPv6 ND
   (not TCP), so it returns; back in `inbound`, the dport rule misses -> drop. *)
Theorem ipv6_closed_port_dropped : forall p,
  pkt_env p = fw_env ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_eth ->
  field_value FMetaProtocol p = eth_ip6 ->
  field_value FMetaL4proto p = l4_tcp ->
  field_value FThDport p = port 25 ->
  eval_table fw_fuel fw_chains inbound p = Drop.
Proof. intros p Hpe Hct Hiif Hpr Hl4 Hdp. eval_fw Hpe. Qed.

(* IPv6 neighbour discovery is accepted via the jump into inbound_ipv6. *)
Theorem ipv6_nd_accepted : forall p,
  pkt_env p = fw_env ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_eth ->
  field_value FMetaProtocol p = eth_ip6 ->
  field_value FMetaL4proto p = l4_icmp6 ->
  field_value FIcmpType p = icmp6_nd_nsol ->
  eval_table fw_fuel fw_chains inbound p = Accept.
Proof. intros p Hpe Hct Hiif Hpr Hl4 Hty. eval_fw Hpe. Qed.

(* The forward hook drops everything (it has no rules and `policy drop`), for
   every packet and every set/map state — no hypotheses needed. *)
Theorem forward_drops_all : forall p,
  eval_table fw_fuel fw_chains forward p = Drop.
Proof.
  intros p. unfold eval_table, fw_fuel, forward.
  cbn -[eval_rules_j]. rewrite erj_nil. reflexivity.
Qed.

(** ** Transport to the compiled bytecode.

    Every property above is about [eval_table], the specification.  Via
    [compile_table_correct], the compiled netlink bytecode evaluated by
    [run_table] computes the identical verdict — so the property holds of the
    ruleset that actually gets installed.  We show it once for [smtp_dropped]. *)
Theorem smtp_dropped_in_bytecode : forall p,
  pkt_env p = fw_env ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_eth ->
  field_value FMetaProtocol p = eth_ip ->
  field_value FMetaL4proto p = l4_tcp ->
  field_value FThDport p = port 25 ->
  run_table fw_fuel (compile_env fw_chains) (compile_chain inbound)
            (c_policy inbound) p = Drop.
Proof.
  intros p Hpe Hct Hiif Hpr Hl4 Hdp.
  rewrite compile_table_correct. apply smtp_dropped; assumption.
Qed.
