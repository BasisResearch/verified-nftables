(** * Adversarial analysis: where optiplex.nft's anti-spoofing does NOT hold.

    [Optiplex_Antispoof.v] proves the positive guarantee: a frame to a protected
    VM address, leaving br.20 on the wrong interface, is dropped.  But the dropping
    rule

      meta obrname br.20  ip daddr @vmaddrs  ip daddr . oifname != @vmantispoof  drop

    fires only when BOTH guards hold: the egress bridge port is br.20 AND the
    destination is enumerated in @vmaddrs.  Either guard failing disables the
    binding check entirely.  Here we prove three concrete BYPASSES are real — each
    is an honest theorem about the parser-generated chain [vmfilter_output], so
    these are properties of the actual ruleset, not hypothetical.

    These are genuine findings: the anti-spoofing protects only the enumerated
    addresses, and only on egress port br.20. *)

From Stdlib Require Import List String Ascii NArith.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Optiplex_Gen Optiplex_Antispoof.
Import ListNotations.
Open Scope string_scope.

(** ** Risk 1 (coverage gap): any destination NOT in @vmaddrs is unconstrained.

    A frame leaving br.20 to an address that is not one of the enumerated VM
    addresses is ACCEPTED — for ANY output interface, including a deliberately
    mismatched one.  The `ip daddr @vmaddrs` guard short-circuits the rule, so the
    (daddr . oifname) binding is never checked.  Stated for every such packet. *)
Theorem unlisted_daddr_unconstrained : forall e p,
  e = gen_env ->
  field_value Fobrname e p = ifreg "br.20" ->
  read_payload_ok PNetwork 16 4 p = true ->
  set_mem (field_value FIp4Daddr e p) (e_set e "vmaddrs") = false ->
  forall h, fst (eval_table h vm_fuel vmfilter_chains vmfilter_output e p) = Accept.
Proof.
  intros e p Henv Hobr Hok Hnotin h. clear Henv. unfold Fobrname in Hobr.
  unfold eval_table, vm_fuel, vmfilter_output. cbn [c_rules c_policy].
  (* the antispoof rule does NOT fire: `ip daddr @vmaddrs` is false, so the body
     BREAKs at that match and [rule_step] yields no verdict. *)
  erewrite eru_skip by rstep_reduce.
  (* the hass rule does not fire either (its guard is obrname br.1, not br.20) *)
  erewrite eru_skip by rstep_reduce.
  cbn [fst]. reflexivity.
Qed.

(** A concrete free spoof: 192.168.51.13 is NOT in @vmaddrs (it sits between
    gentoo's .12 and vikunja's .14).  A frame to .13 may leave br.20 on budget's
    own interface inc-budge — a pairing that WOULD be blocked for a listed
    address — yet it is accepted, because .13 is unprotected. *)
Theorem spoof_to_unlisted_address : forall e p,
  e = gen_env ->
  field_value Fobrname e p = ifreg "br.20" ->
  read_payload_ok PNetwork 16 4 p = true ->
  field_value FIp4Daddr e p = ip4 192 168 51 13 ->        (* not a registered VM *)
  field_value FMetaOifname e p = ifreg "inc-budge" ->     (* a mismatched interface *)
  forall h, fst (eval_table h vm_fuel vmfilter_chains vmfilter_output e p) = Accept.
Proof.
  intros e p Henv Hobr Hok Hdaddr Hoif.
  apply unlisted_daddr_unconstrained; auto.
  rewrite Hdaddr, Henv. vm_compute. reflexivity.
Qed.

(** ** Risk 2 (egress-port gap): the binding is enforced only on bridge port br.20.

    The same protected VM address, when it egresses a DIFFERENT bridge port, is
    accepted regardless of the output interface — because the rule's first guard
    is `meta obrname br.20`.  If an attacker on another bridge segment causes
    budget's address (.20) to egress br.3 (e.g. via MAC/FDB poisoning), the
    binding check is bypassed even though .20 is a registered VM address and the
    interface (vb-evil) is not its bound one. *)
Theorem other_bridge_port_bypasses_binding : forall e p,
  e = gen_env ->
  field_value Fobrname e p = ifreg "br.3" ->            (* NOT br.20 *)
  field_value FIp4Daddr e p = ip4 192 168 51 20 ->        (* budget's PROTECTED address *)
  field_value FMetaOifname e p = ifreg "vb-evil" ->       (* not budget's interface *)
  forall h, fst (eval_table h vm_fuel vmfilter_chains vmfilter_output e p) = Accept.
Proof.
  intros e p Henv Hobr Hdaddr Hoif h. clear Henv. unfold Fobrname in Hobr.
  unfold eval_table, vm_fuel, vmfilter_output. cbn [c_rules c_policy].
  (* antispoof rule: its `meta obrname br.20` guard is false (we are on br.3) *)
  erewrite eru_skip by rstep_reduce.
  (* hass rule: its `meta obrname br.1` guard is also false *)
  erewrite eru_skip by rstep_reduce.
  cbn [fst]. reflexivity.
Qed.

(** ** Risk 3 (the gap is exactly characterised): protection holds IFF both guards.

    Combining with [Optiplex_Antispoof.antispoof_general], the rule drops a frame
    precisely when egress is br.20 AND the destination is in @vmaddrs AND the
    (daddr.oifname) pair is unbound.  The two theorems above witness that dropping
    *fails* as soon as either of the first two conjuncts is removed — so the
    enumeration in @vmaddrs and the single egress port br.20 are load-bearing: any
    address or bridge port outside them is unprotected.  (Mitigation: gate on
    `ip daddr` family membership / a default-deny per egress port, not on an
    explicit address allow-list.) *)
