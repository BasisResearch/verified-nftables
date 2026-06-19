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

From Stdlib Require Import List String Ascii NArith Lia.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Optiplex_Gen.
Import ListNotations.

(** ** Wire constants (literal bytes, so [cbn] fully reduces the matches). *)
Definition mark99    : data := [153; 0; 0; 0].   (* the 0x99 firewall mark, host-endian (LE) *)
(* "home" in a 16-byte IFNAMSIZ zero-padded ifname register (the kernel
   compares the full 16-byte buffer for an exact name match). *)
Definition if_home   : data := [104; 111; 109; 101; 0;0;0;0; 0;0;0;0; 0;0;0;0].
Definition fib_local : data := [2; 0; 0; 0].      (* fib … type local (RTN_LOCAL); host-endian u32 on LE *)
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
  read_payload_ok PTransport 2 2 p = true ->
  dsl_writes pre1 p = p.
Proof.
  intros p Henv Hiif Hfib Hl4 Hdport Hok.
  unfold dsl_writes, pre1, filter_prerouting.
  cbn -[field_value pkt_env set_meta read_payload_ok].
  unfold eval_matchcond, match_loadable, eval_matchcond_body, fields_loadable,
    field_loadable, load_ok.
  cbn -[field_value pkt_env set_meta read_payload_ok].
  rewrite ?Hok, !Hiif, !Hfib, !Hl4, !Hdport, !Henv.
  cbn -[set_meta read_payload_ok]. rewrite ?Hok. cbn -[set_meta]. reflexivity.
Qed.

(* rule 2 matches a streaming packet and sets the mark: the packet that comes out
   is the input with meta mark := 0x99 (and nothing else). *)
Lemma pre2_streaming_marks : forall p,
  pkt_env p = gen_env ->
  field_value FMetaIifname p = if_home ->
  field_value (FFib "daddr" FRtype) p = fib_local ->
  field_value FMetaL4proto p = l4_tcp ->
  field_value FThDport p = port48010 ->
  read_payload_ok PTransport 2 2 p = true ->
  dsl_writes pre2 p = set_meta p MKmark mark99.
Proof.
  intros p Henv Hiif Hfib Hl4 Hdport Hok.
  unfold dsl_writes, pre2, filter_prerouting.
  cbn -[field_value pkt_env set_meta read_payload_ok].
  unfold eval_matchcond, match_loadable, eval_matchcond_body, fields_loadable,
    field_loadable, load_ok.
  cbn -[field_value pkt_env set_meta read_payload_ok].
  rewrite ?Hok, !Hiif, !Hfib, !Hl4, !Hdport, !Henv.
  cbn -[set_meta read_payload_ok]. rewrite ?Hok. cbn -[set_meta]. reflexivity.
Qed.

Lemma pre1_streaming_skips : forall p,
  pkt_env p = gen_env ->
  field_value FMetaIifname p = if_home ->
  field_value (FFib "daddr" FRtype) p = fib_local ->
  field_value FMetaL4proto p = l4_tcp ->
  field_value FThDport p = port48010 ->
  read_payload_ok PTransport 2 2 p = true ->
  rule_applies pre1 p = false.
Proof.
  intros p Henv Hiif Hfib Hl4 Hdport Hok.
  unfold rule_applies, rule_applies_walk, pre1, filter_prerouting.
  cbn -[field_value pkt_env read_payload_ok].
  unfold eval_matchcond, match_loadable, eval_matchcond_body, fields_loadable,
    field_loadable, load_ok.
  cbn -[field_value pkt_env read_payload_ok].
  rewrite ?Hok, !Hiif, !Hfib, !Hl4, !Hdport, !Henv. vm_compute. reflexivity.
Qed.

Lemma pre2_streaming_applies : forall p,
  pkt_env p = gen_env ->
  field_value FMetaIifname p = if_home ->
  field_value (FFib "daddr" FRtype) p = fib_local ->
  field_value FMetaL4proto p = l4_tcp ->
  field_value FThDport p = port48010 ->
  read_payload_ok PTransport 2 2 p = true ->
  rule_applies pre2 p = true.
Proof.
  intros p Henv Hiif Hfib Hl4 Hdport Hok.
  unfold rule_applies, rule_applies_walk, pre2, filter_prerouting.
  cbn -[field_value pkt_env read_payload_ok].
  unfold eval_matchcond, match_loadable, eval_matchcond_body, fields_loadable,
    field_loadable, load_ok.
  cbn -[field_value pkt_env read_payload_ok].
  rewrite ?Hok, !Hiif, !Hfib, !Hl4, !Hdport, !Henv. vm_compute. reflexivity.
Qed.

Lemma pre2_outcome_accept : forall p, outcome pre2 p = Some Accept.
Proof. intros p. reflexivity. Qed.

(* the streaming rule is loadable: its only payload read is the th-dport set key *)
Lemma pre2_loadable : forall p,
  read_payload_ok PTransport 2 2 p = true -> rule_loadable pre2 p = true.
Proof.
  intros p Hok. unfold rule_loadable, pre2, filter_prerouting, end_loadable,
    tail_loadable, terminal_loadable, body_item_loadable, match_loadable,
    stmt_loadable, vsrc_loadable, fields_loadable, field_loadable, load_ok.
  cbn -[read_payload_ok]. rewrite ?Hok. reflexivity.
Qed.

(* the prerouting streaming rule is a dnat, not a masquerade — so the trace's
   source-NAT step [apply_masq] is a no-op on it *)
Lemma pre2_no_masq : r_nat pre2 = None.
Proof. reflexivity. Qed.
Lemma apply_masq_none : forall h r p, r_nat r = None -> apply_nat h r p = p.
Proof. intros h r p H. unfold apply_nat. rewrite H. reflexivity. Qed.

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
  read_payload_ok PTransport 2 2 p = true ->
  eval_chain_trace Hprerouting filter_prerouting p = (Accept, set_meta p MKmark mark99).
Proof.
  intros p Henv Hiif Hfib Hl4 Hdport Hok.
  unfold eval_chain_trace. rewrite prerouting_rules_eq.
  (* rule 1: traversed but does not match; threads its (no-op) writes *)
  cbn [eval_rules_trace]. rewrite pre1_streaming_skips by assumption.
  rewrite Bool.andb_false_r.
  rewrite (dsl_step_limit_free pre1 p) by reflexivity.
  rewrite pre1_streaming_noop by assumption.
  (* rule 2: matches, terminal accept, leaves the marked packet (it is a dnat,
     so apply_masq is a no-op — the source rewrite happens at postrouting) *)
  cbn [eval_rules_trace]. rewrite pre2_streaming_applies by assumption.
  rewrite (pre2_loadable p Hok).
  rewrite pre2_outcome_accept. cbn [terminal].
  rewrite (dsl_step_limit_free pre2 p) by reflexivity.
  rewrite (apply_masq_none Hprerouting pre2 _ pre2_no_masq).
  rewrite pre2_streaming_marks by assumption. reflexivity.
Qed.

(** ** The mark is read by the postrouting masquerade rule. *)
Theorem masquerade_gated_on_mark : forall p,
  field_value FMetaMark p = mark99 -> rule_applies post1 p = true.
Proof.
  intros p Hm. unfold rule_applies, rule_applies_walk, post1, filter_postrouting.
  cbn -[field_value]. rewrite Hm. vm_compute. reflexivity.
Qed.

Theorem unmarked_not_masqueraded : forall p,
  field_value FMetaMark p = [0;0;0;0] -> rule_applies post1 p = false.
Proof.
  intros p Hm. unfold rule_applies, rule_applies_walk, post1, filter_postrouting.
  cbn -[field_value]. rewrite Hm. vm_compute. reflexivity.
Qed.

(** ** What `masquerade` does to the SOURCE address.

    The postrouting rule is `mark 0x99 … masquerade`.  Masquerade is source-NAT:
    it rewrites the packet's IPv4 source address to the address of the interface
    the packet exits — `e_ifaddr (oifname)` in the model.  We prove the OUTPUT
    packet of the postrouting chain is exactly the input with its source address
    so rewritten, and (reading it back) that its `ip saddr` field is that
    interface's address. *)

Lemma postrouting_rules_eq : c_rules filter_postrouting = [post1].
Proof. reflexivity. Qed.

(* the masquerade rule is a terminal NAT (accepts) carrying r_nat = Some masq *)
Lemma post1_outcome_accept : forall p, outcome post1 p = Some Accept.
Proof. reflexivity. Qed.

(* its body (a mark match + log) writes nothing to the packet *)
Lemma post1_dsl_noop : forall p,
  field_value FMetaMark p = mark99 -> dsl_writes post1 p = p.
Proof.
  intros p Hm. unfold dsl_writes, post1, filter_postrouting.
  cbn -[field_value pkt_env]. rewrite Hm. vm_compute. reflexivity.
Qed.

(* applying its NAT effect source-rewrites to the exit interface's address AND
   stores that established mapping in the flow-keyed [e_nat] table.  NAT is now
   FLOW-STATEFUL (Round-2 fix): on the FIRST packet of a flow ([e_nat .. = None])
   the mapping is computed from the exit interface and STORED; the source address
   is rewritten exactly as before. *)
Lemma post1_apply_masq : forall h p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  apply_nat h post1 p
    = store_nat_mapping
        (set_saddr "ip" p (e_ifaddr (pkt_env p) (field_value FMetaOifname p)))
        (Some (slice (pkt_nh p) 12 4),
         Some (e_ifaddr (pkt_env p) (field_value FMetaOifname p)), None, None).
Proof.
  intros h p Horig Hnone. unfold apply_nat, post1, filter_postrouting.
  cbn -[set_saddr e_ifaddr field_value pkt_env e_nat store_nat_mapping
        apply_nat_tuple nat_orig_addr nat_operand_addr nat_pmin].
  rewrite Hnone, Horig.
  unfold apply_nat_tuple, nat_is_src, nat_operand_addr, nat_addrfamily, nat_orig_addr.
  cbn -[set_saddr e_ifaddr field_value pkt_env store_nat_mapping slice pkt_nh].
  rewrite Horig. reflexivity.
Qed.

(* THE OUTPUT PACKET of the postrouting chain (first packet of the flow): the input
   with its source address set to the exit interface's address (= what masquerade
   does), and the mapping recorded in [e_nat]. *)
Theorem masquerade_output : forall p ifaddr,
  field_value FMetaMark p = mark99 ->
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  e_ifaddr (pkt_env p) (field_value FMetaOifname p) = ifaddr ->
  eval_chain_trace Hpostrouting filter_postrouting p
    = (Accept, store_nat_mapping (set_saddr "ip" p ifaddr)
                 (Some (slice (pkt_nh p) 12 4), Some ifaddr, None, None)).
Proof.
  intros p ifaddr Hmark Horig Hnone Hifa.
  unfold eval_chain_trace. rewrite postrouting_rules_eq. cbn [eval_rules_trace].
  rewrite (masquerade_gated_on_mark p Hmark), post1_outcome_accept. cbn [terminal].
  rewrite (dsl_step_limit_free post1 p) by reflexivity.
  rewrite (post1_dsl_noop p Hmark), (post1_apply_masq Hpostrouting p Horig Hnone), Hifa.
  reflexivity.
Qed.

(* reading the source address back: after masquerade, `ip saddr` IS the exit
   interface's address (for a well-formed IPv4 header and a 4-byte address).  The
   [store_nat_mapping] env write preserves [pkt_nh], so the read-back is unchanged. *)
Lemma saddr_after_set : forall p v,
  16 <= List.length (pkt_nh p) -> List.length v = 4 ->
  field_value FIp4Saddr (set_saddr "ip" p v) = v.
Proof.
  intros p v Hlen Hv.
  unfold field_value; cbn [field_load do_load]; unfold read_payload.
  apply slice_set_saddr_ip4_same; [exact Hlen | exact Hv].
Qed.

Theorem masquerade_source_is_exit_iface : forall p ifaddr,
  field_value FMetaMark p = mark99 ->
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  e_ifaddr (pkt_env p) (field_value FMetaOifname p) = ifaddr ->
  List.length ifaddr = 4 -> 16 <= List.length (pkt_nh p) ->
  field_value FIp4Saddr (snd (eval_chain_trace Hpostrouting filter_postrouting p)) = ifaddr.
Proof.
  intros p ifaddr Hmark Horig Hnone Hifa Hlen Hnh.
  rewrite (masquerade_output p ifaddr Hmark Horig Hnone Hifa). cbn [snd].
  (* [store_nat_mapping] preserves pkt_nh, so saddr read-back is the spliced value *)
  unfold field_value; cbn [field_load do_load]; unfold read_payload.
  cbn [store_nat_mapping pkt_nh].
  fold (read_payload PNetwork 12 4 (set_saddr "ip" p ifaddr)).
  fold (field_value FIp4Saddr (set_saddr "ip" p ifaddr)).
  apply saddr_after_set; assumption.
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
  read_payload_ok PTransport 2 2 p = true ->
  (* prerouting: packet in p -> (Accept, p with mark 0x99) out *)
  eval_chain_trace Hprerouting filter_prerouting p = (Accept, set_meta p MKmark mark99)
  (* postrouting reads the mark and masquerades (terminal accept) *)
  /\ rule_applies post1 (set_meta p MKmark mark99) = true
  /\ eval_chain_mut filter_postrouting (set_meta p MKmark mark99) = Accept.
Proof.
  intros p Henv Hiif Hfib Hl4 Hdport Hok.
  assert (Hmark : field_value FMetaMark (set_meta p MKmark mark99) = mark99)
    by apply mark_after_set.
  split; [ now apply streaming_prerouting_io | split ].
  - now apply masquerade_gated_on_mark.
  - unfold eval_chain_mut, filter_postrouting. cbn -[field_value].
    rewrite Hmark. vm_compute. reflexivity.
Qed.
