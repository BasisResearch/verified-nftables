(** * Firewall mark (0x99): a packet traversing optiplex.nft end-to-end.

    optiplex.nft uses a packet mark to steer RDP / game-streaming traffic:

      chain prerouting (nat, hook prerouting):
        iifname home   fib daddr type local meta l4proto {tcp,udp} th dport 3389        mark set 0x99 … dnat …   (rule 1)
        iifname {lan,home} fib daddr type local meta l4proto {tcp,udp} th dport {47984,…,48010,…} mark set 0x99 … dnat …  (rule 2)
      chain postrouting (nat, hook postrouting):
        mark 0x99 log … masquerade

    The prerouting chain SETS `meta mark` to 0x99 on matching traffic; the
    postrouting chain READS it.  We prove the mark machinery against the
    parser-generated chains [filter_prerouting] / [filter_postrouting] in
    [Optiplex_Gen.v] — about the parser's actual output, not a hand copy.

    The headline is [streaming_flow_whole_ruleset]: a game-streaming packet (dport
    48010) goes IN, traverses the WHOLE prerouting chain — flowing past rule 1
    (the 3389 rule, which does not match) and being marked by rule 2 — and the
    packet that comes OUT is exactly the input with `meta mark` set to 0x99 and
    nothing else changed; carried to the postrouting hook, that mark drives the
    masquerade.  [eval_chain_trace] runs a whole chain threading the mutated packet
    rule-by-rule (its verdict is the verified [eval_chain_mut], by
    [eval_chain_trace_verdict]); [chain_out] is the packet it leaves. *)

From Stdlib Require Import List String Ascii NArith.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Optiplex_Gen.
Import ListNotations.

(** ** Wire constants (literal bytes, so [cbn] fully reduces the matches). *)
Definition mark99    : data := [0; 0; 0; 153].   (* the 0x99 firewall mark *)
Definition if_home   : data := [104; 111; 109; 101].  (* "home" *)
Definition fib_local : data := [0; 0; 0; 2].      (* fib … type local (RTN_LOCAL) *)
Definition l4_tcp    : data := [6].
Definition port3389  : data := [13; 61].          (* 0x0d3d — RDP *)
Definition port48010 : data := [187; 138].        (* 0xbb8a — a Sunshine stream port *)

(** The rules of interest, taken straight from the generated chains. *)
Definition dflt : rule :=
  {| r_body := []; r_verdict := Continue; r_vmap := None; r_nat := None;
     r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.
Definition pre1  : rule := List.nth 0 (c_rules filter_prerouting)  dflt.  (* RDP/3389 *)
Definition pre2  : rule := List.nth 1 (c_rules filter_prerouting)  dflt.  (* streaming ports *)
Definition post1 : rule := List.nth 0 (c_rules filter_postrouting) dflt.  (* masquerade *)

(* the prerouting chain has exactly these three rules (rule 3 duplicates rule 2) *)
Lemma prerouting_rules_eq :
  c_rules filter_prerouting = [pre1; pre2; List.nth 2 (c_rules filter_prerouting) dflt].
Proof. reflexivity. Qed.

(** Reading [meta mark] right after `mark set v` yields [v]. *)
Lemma mark_after_set : forall p v, field_value FMetaMark (set_meta p MKmark v) = v.
Proof. intros p v. reflexivity. Qed.

(** ** What each prerouting rule does to the packet (the per-rule writes).

    These characterise the OUTPUT of running one rule's body on the packet — the
    heart of "what comes out".  [cbn -[…set_meta]] reduces the matches but keeps
    [set_meta] folded, so the result is stated as the input packet with exactly the
    mark changed. *)

(* rule 1 (the 3389 rule) does NOT match a streaming packet — its `th dport 3389`
   fails, so the `mark set` after it never runs and the packet is unchanged. *)
Lemma pre1_streaming_noop : forall p,
  pkt_env p = gen_env ->
  field_value FMetaIifname p = if_home ->
  field_value (FFib "daddr" FRtype) p = fib_local ->
  field_value FMetaL4proto p = l4_tcp ->
  field_value FThDport p = port48010 ->
  dsl_writes pre1 p = p.
Proof.
  intros p Henv Hiif Hfib Hl4 Hdport.
  unfold dsl_writes, pre1, filter_prerouting. cbn -[field_value pkt_env set_meta].
  rewrite !Hiif, !Hfib, !Hl4, !Hdport, !Henv. cbn -[set_meta]. reflexivity.
Qed.

(* rule 2 matches a streaming packet and sets the mark: the packet that comes out
   is the input with meta mark := 0x99 (and nothing else). *)
Lemma pre2_streaming_marks : forall p,
  pkt_env p = gen_env ->
  field_value FMetaIifname p = if_home ->
  field_value (FFib "daddr" FRtype) p = fib_local ->
  field_value FMetaL4proto p = l4_tcp ->
  field_value FThDport p = port48010 ->
  dsl_writes pre2 p = set_meta p MKmark mark99.
Proof.
  intros p Henv Hiif Hfib Hl4 Hdport.
  unfold dsl_writes, pre2, filter_prerouting. cbn -[field_value pkt_env set_meta].
  rewrite !Hiif, !Hfib, !Hl4, !Hdport, !Henv. cbn -[set_meta]. reflexivity.
Qed.

Lemma pre1_streaming_skips : forall p,
  pkt_env p = gen_env ->
  field_value FMetaIifname p = if_home ->
  field_value (FFib "daddr" FRtype) p = fib_local ->
  field_value FMetaL4proto p = l4_tcp ->
  field_value FThDport p = port48010 ->
  rule_applies pre1 p = false.
Proof.
  intros p Henv Hiif Hfib Hl4 Hdport.
  unfold rule_applies, pre1, filter_prerouting. cbn -[field_value pkt_env].
  rewrite !Hiif, !Hfib, !Hl4, !Hdport, !Henv. vm_compute. reflexivity.
Qed.

Lemma pre2_streaming_applies : forall p,
  pkt_env p = gen_env ->
  field_value FMetaIifname p = if_home ->
  field_value (FFib "daddr" FRtype) p = fib_local ->
  field_value FMetaL4proto p = l4_tcp ->
  field_value FThDport p = port48010 ->
  rule_applies pre2 p = true.
Proof.
  intros p Henv Hiif Hfib Hl4 Hdport.
  unfold rule_applies, pre2, filter_prerouting. cbn -[field_value pkt_env].
  rewrite !Hiif, !Hfib, !Hl4, !Hdport, !Henv. vm_compute. reflexivity.
Qed.

Lemma pre2_outcome_accept : forall p, outcome pre2 p = Some Accept.
Proof. intros p. reflexivity. Qed.

(** ** What comes out of the prerouting chain.

    Run the WHOLE prerouting chain on a streaming packet: it traverses rule 1
    (skipped, packet unchanged) and is marked by rule 2 (terminal accept).  The
    output is [(Accept, p with meta mark := 0x99)] — packet in, packet out. *)
Theorem streaming_prerouting_io : forall p,
  pkt_env p = gen_env ->
  field_value FMetaIifname p = if_home ->
  field_value (FFib "daddr" FRtype) p = fib_local ->
  field_value FMetaL4proto p = l4_tcp ->
  field_value FThDport p = port48010 ->
  eval_chain_trace filter_prerouting p = (Accept, set_meta p MKmark mark99).
Proof.
  intros p Henv Hiif Hfib Hl4 Hdport.
  unfold eval_chain_trace. rewrite prerouting_rules_eq.
  (* rule 1: traversed but does not match; threads its (no-op) writes *)
  cbn [eval_rules_trace]. rewrite pre1_streaming_skips by assumption.
  rewrite pre1_streaming_noop by assumption.
  (* rule 2: matches, terminal accept, leaves the marked packet *)
  cbn [eval_rules_trace]. rewrite pre2_streaming_applies by assumption.
  rewrite pre2_outcome_accept. cbn [terminal].
  rewrite pre2_streaming_marks by assumption. reflexivity.
Qed.

(** ** The mark is read by the postrouting masquerade rule. *)
Theorem masquerade_gated_on_mark : forall p,
  field_value FMetaMark p = mark99 -> rule_applies post1 p = true.
Proof.
  intros p Hm. unfold rule_applies, post1, filter_postrouting.
  cbn -[field_value]. rewrite Hm. vm_compute. reflexivity.
Qed.

Theorem unmarked_not_masqueraded : forall p,
  field_value FMetaMark p = [0;0;0;0] -> rule_applies post1 p = false.
Proof.
  intros p Hm. unfold rule_applies, post1, filter_postrouting.
  cbn -[field_value]. rewrite Hm. vm_compute. reflexivity.
Qed.

(** ** End-to-end: a streaming packet across the WHOLE ruleset.

    The packet goes in; out of prerouting comes the same packet with mark 0x99;
    that packet, carried to the postrouting hook (as the kernel carries the skb
    mark), is matched by the masquerade rule and the postrouting chain accepts it.
    No rule is applied by hand — each chain is run whole by [eval_chain_trace] /
    [eval_chain_mut]. *)
Theorem streaming_flow_whole_ruleset : forall p,
  pkt_env p = gen_env ->
  field_value FMetaIifname p = if_home ->
  field_value (FFib "daddr" FRtype) p = fib_local ->
  field_value FMetaL4proto p = l4_tcp ->
  field_value FThDport p = port48010 ->
  (* prerouting: packet in p -> (Accept, p with mark 0x99) out *)
  eval_chain_trace filter_prerouting p = (Accept, set_meta p MKmark mark99)
  (* postrouting reads the mark and masquerades (terminal accept) *)
  /\ rule_applies post1 (set_meta p MKmark mark99) = true
  /\ eval_chain_mut filter_postrouting (set_meta p MKmark mark99) = Accept.
Proof.
  intros p Henv Hiif Hfib Hl4 Hdport.
  assert (Hmark : field_value FMetaMark (set_meta p MKmark mark99) = mark99)
    by apply mark_after_set.
  split; [ now apply streaming_prerouting_io | split ].
  - now apply masquerade_gated_on_mark.
  - unfold eval_chain_mut, filter_postrouting. cbn -[field_value].
    rewrite Hmark. vm_compute. reflexivity.
Qed.
