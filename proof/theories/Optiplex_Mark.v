(** * Firewall mark (0x99) properties of the parsed optiplex.nft.

    optiplex.nft uses a packet mark to steer RDP / game-streaming traffic:

      chain prerouting (nat, hook prerouting):
        iifname home fib daddr type local meta l4proto {tcp,udp} th dport 3389
          mark set 0x99 log … dnat …
      chain postrouting (nat, hook postrouting):
        mark 0x99 log … masquerade

    The prerouting chain SETS `meta mark` to 0x99 on matching traffic; the
    postrouting chain READS it to decide whether to masquerade.  We prove this
    mark machinery is correct, against the parser-generated chains
    [filter_prerouting] / [filter_postrouting] in [Optiplex_Gen.v] — i.e. about
    the parser's actual output, not a hand copy.

    The model threads a `meta` `set` to later rules via the write semantics
    [body_writes]/[dsl_writes] (the basis of `compile_chain_mut_correct`).  We use
    those to state exactly what the mark does. *)

From Stdlib Require Import List String Ascii NArith.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Optiplex_Gen Optiplex_Antispoof.
Import ListNotations.
Open Scope string_scope.

(** The firewall mark, 0x99 = 153, as the 4-byte word the rules use. *)
Definition mark99 : data := [0; 0; 0; 153].

(** The two rules of interest, taken straight from the generated chains. *)
Definition dflt : rule :=
  {| r_body := []; r_verdict := Continue; r_vmap := None; r_nat := None;
     r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.
Definition pre1  : rule := List.nth 0 (c_rules filter_prerouting)  dflt.  (* RDP/3389 *)
Definition post1 : rule := List.nth 0 (c_rules filter_postrouting) dflt.  (* masquerade *)

(** Reading [meta mark] right after `mark set v` yields [v]. *)
Lemma mark_after_set : forall p v, field_value FMetaMark (set_meta p MKmark v) = v.
Proof. intros p v. reflexivity. Qed.

(** ** Property 1 — the prerouting chain MARKS matching RDP traffic.

    A packet from `home`, to a local route, tcp, dport 3389 leaves the prerouting
    rule's body carrying mark 0x99 (the `mark set 0x99` write took effect). *)
Theorem rdp_traffic_marked : forall p,
  pkt_env p = gen_env ->
  field_value FMetaIifname p = sbytes "home" ->
  field_value (FFib "daddr" FRtype) p = [0;0;0;2] ->   (* fib daddr type local *)
  field_value FMetaL4proto p = [6] ->                   (* tcp ∈ {tcp,udp} *)
  field_value FThDport p = [13;61] ->                   (* dport 3389 = 0x0d3d *)
  field_value FMetaMark (dsl_writes pre1 p) = mark99.
Proof.
  intros p Henv Hiif Hfib Hl4 Hdport.
  unfold dsl_writes, pre1, filter_prerouting. cbn -[field_value pkt_env set_meta].
  rewrite Hiif, Hfib, Hl4, Hdport, Henv. vm_compute. reflexivity.
Qed.

(** ** Property 1b — the marking is PRECISE: non-RDP traffic is not marked.

    The same packet but to a different port (22) fails the `th dport 3389` match,
    so the `mark set` (which follows it in the rule) never runs — the mark is left
    untouched. *)
Theorem non_rdp_not_marked : forall p,
  pkt_env p = gen_env ->
  field_value FMetaIifname p = sbytes "home" ->
  field_value (FFib "daddr" FRtype) p = [0;0;0;2] ->
  field_value FMetaL4proto p = [6] ->
  field_value FThDport p = [0;22] ->                    (* dport 22, not 3389 *)
  field_value FMetaMark (dsl_writes pre1 p) = field_value FMetaMark p.
Proof.
  intros p Henv Hiif Hfib Hl4 Hdport.
  unfold dsl_writes, pre1, filter_prerouting. cbn -[field_value pkt_env set_meta].
  rewrite Hiif, Hfib, Hl4, Hdport, Henv. vm_compute. reflexivity.
Qed.

(** ** Property 2 — the postrouting masquerade is GATED on the mark.

    The masquerade rule applies exactly when the packet carries mark 0x99. *)
Theorem marked_is_masqueraded : forall p,
  field_value FMetaMark p = mark99 ->
  rule_applies post1 p = true.
Proof.
  intros p Hm. unfold rule_applies, post1, filter_postrouting.
  cbn -[field_value]. rewrite Hm. vm_compute. reflexivity.
Qed.

Theorem unmarked_not_masqueraded : forall p,
  field_value FMetaMark p = [0;0;0;0] ->                 (* no mark *)
  rule_applies post1 p = false.
Proof.
  intros p Hm. unfold rule_applies, post1, filter_postrouting.
  cbn -[field_value]. rewrite Hm. vm_compute. reflexivity.
Qed.

(** ** Property 3 — end-to-end: prerouting's mark drives postrouting's masquerade.

    Composing 1 and 2: an RDP packet, after the prerouting chain marks it, is
    matched by the postrouting masquerade rule.  This is the mark's whole purpose
    — carrying a decision from the prerouting hook to the postrouting hook.  We
    thread the marked packet explicitly (as the kernel threads the skb mark across
    hooks; the single-packet model does not auto-thread per-packet meta between
    base chains). *)
Theorem rdp_flow_marks_and_masquerades : forall p,
  pkt_env p = gen_env ->
  field_value FMetaIifname p = sbytes "home" ->
  field_value (FFib "daddr" FRtype) p = [0;0;0;2] ->
  field_value FMetaL4proto p = [6] ->
  field_value FThDport p = [13;61] ->
  rule_applies post1 (dsl_writes pre1 p) = true.
Proof.
  intros p Henv Hiif Hfib Hl4 Hdport.
  apply marked_is_masqueraded.
  apply rdp_traffic_marked; assumption.
Qed.
