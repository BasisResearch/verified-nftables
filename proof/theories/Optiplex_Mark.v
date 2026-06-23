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

(* the prerouting streaming rule carries a real terminal `dnat ip to $windows`
   (= 192.168.51.186); the `define windows` line is live again, so the parser now
   lowers it to a destination-NAT.  These helpers characterise what that dnat does
   and show the firewall mark set by the body SURVIVES it. *)
Definition windows_ip : data := [192; 168; 51; 186].

(* [set_l4_csum_addr] / [set_daddr] touch only header bytes (+ the env), never the
   metadata, so a `meta mark` set before a dnat is read back intact. *)
Lemma set_l4_csum_addr_meta : forall p old new k,
  pkt_meta (set_l4_csum_addr p old new) k = pkt_meta p k.
Proof.
  intros p old new k. unfold set_l4_csum_addr.
  destruct (l4_csum_slot (pkt_meta p MKl4proto)) as [[[coff clen] mand]|]; [|reflexivity].
  destruct (andb (pkt_have_l4 p) (Nat.leb (coff + clen) (List.length (pkt_th p)))); [|reflexivity].
  destruct (andb (negb mand) (N.eqb (data_to_N (slice (pkt_th p) coff clen)) 0)); reflexivity.
Qed.

Lemma set_daddr_meta : forall fam p v k, pkt_meta (set_daddr fam p v) k = pkt_meta p k.
Proof.
  intros fam p v k. unfold set_daddr.
  destruct (daddr_slot fam) as [off len].
  rewrite set_l4_csum_addr_meta.
  destruct (String.eqb fam nat_fam_ip6); reflexivity.
Qed.

(* applying pre2's dnat to a FIRST-flow, original-direction packet rewrites the
   DESTINATION address to the windows box and records the flow-keyed mapping. *)
Lemma pre2_apply_dnat : forall h p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  apply_nat h pre2 p
    = store_nat_mapping (set_daddr "ip" p windows_ip)
        (Some (slice (pkt_nh p) 16 4), Some windows_ip, None, None).
Proof.
  intros h p Horig Hnone. unfold apply_nat, pre2, filter_prerouting.
  cbn -[set_daddr field_value pkt_env e_nat store_nat_mapping
        apply_nat_tuple nat_orig_addr nat_operand_addr nat_pmin nat_orig_port slice pkt_nh].
  rewrite Hnone, Horig.
  unfold apply_nat_tuple, nat_is_src, nat_operand_addr, nat_addrfamily_pkt,
    nat_addrfamily, nat_orig_addr, nat_addr, nat_has_addr, nat_orig_port.
  cbn -[set_daddr field_value pkt_env store_nat_mapping slice pkt_nh].
  rewrite Horig. reflexivity.
Qed.

(* the firewall mark set by the body survives the terminal dnat. *)
Lemma mark_through_dnat : forall h p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  field_value FMetaMark (apply_nat h pre2 p) = field_value FMetaMark p.
Proof.
  intros h p Horig Hnone. rewrite (pre2_apply_dnat h p Horig Hnone).
  unfold field_value. cbn [field_load do_load pkt_meta store_nat_mapping].
  apply set_daddr_meta.
Qed.

(* pre2's dnat never NAT-drops: [nat_iface_addr_absent] only fires for
   masquerade/redirect (a source/dest taken from an interface); a `dnat` to an
   explicit address has no interface to lack, so [nat_drops] is unconditionally
   [false] and the trace takes the apply-NAT branch, not the NF_DROP one. *)
Lemma pre2_no_natdrop : forall p, nat_drops Hprerouting pre2 p = false.
Proof.
  intros p. unfold nat_drops, pre2, filter_prerouting.
  cbn -[e_nat pkt_ctdir_orig nat_iface_addr_absent].
  unfold nat_iface_addr_absent. cbn -[e_nat pkt_ctdir_orig].
  destruct (e_nat (pkt_env p) (pkt_flow p)); [reflexivity | apply Bool.andb_false_r].
Qed.

(** ** What comes out of the prerouting chain.

    Run the WHOLE prerouting chain on a streaming packet: it traverses rule 1
    (skipped, packet unchanged) and is matched by rule 2 (terminal accept), which
    BOTH sets the mark (the body) AND destination-NATs the packet (the terminal
    `dnat ip to $windows`).  The output is [(Accept, dnat applied to the marked
    packet)] — packet in, packet out.  [pre2_apply_dnat] characterises the dnat
    (daddr rewritten to [windows_ip]); [streaming_prerouting_mark] shows the mark
    survives it. *)
Theorem streaming_prerouting_io : forall p,
  pkt_env p = gen_env ->
  field_value FMetaIifname p = if_home ->
  field_value (FFib "daddr" FRtype) p = fib_local ->
  field_value FMetaL4proto p = l4_tcp ->
  field_value FThDport p = port48010 ->
  read_payload_ok PTransport 2 2 p = true ->
  eval_chain_trace Hprerouting filter_prerouting p
    = (Accept, apply_nat Hprerouting pre2 (set_meta p MKmark mark99)).
Proof.
  intros p Henv Hiif Hfib Hl4 Hdport Hok.
  unfold eval_chain_trace. rewrite prerouting_rules_eq.
  (* rule 1: traversed but does not match; threads its (no-op) writes *)
  cbn [eval_rules_trace]. rewrite pre1_streaming_skips by assumption.
  rewrite Bool.andb_false_r.
  rewrite (dsl_step_limit_free pre1 p) by reflexivity.
  rewrite pre1_streaming_noop by assumption.
  (* rule 2: matches, terminal accept; the body marks the packet and the terminal
     dnat rewrites the destination — the output is [apply_nat pre2 (marked packet)] *)
  cbn [eval_rules_trace]. rewrite pre2_streaming_applies by assumption.
  rewrite (pre2_loadable p Hok).
  rewrite pre2_outcome_accept. cbn [terminal].
  rewrite pre2_no_natdrop.
  rewrite (dsl_step_limit_free pre2 p) by reflexivity.
  rewrite pre2_streaming_marks by assumption. reflexivity.
Qed.

(** The firewall mark survives the terminal dnat: the packet leaving prerouting
    still has `meta mark` = 0x99 (so the postrouting masquerade still fires). *)
Theorem streaming_prerouting_mark : forall p,
  pkt_env p = gen_env ->
  field_value FMetaIifname p = if_home ->
  field_value (FFib "daddr" FRtype) p = fib_local ->
  field_value FMetaL4proto p = l4_tcp ->
  field_value FThDport p = port48010 ->
  read_payload_ok PTransport 2 2 p = true ->
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  field_value FMetaMark (snd (eval_chain_trace Hprerouting filter_prerouting p)) = mark99.
Proof.
  intros p Henv Hiif Hfib Hl4 Hdport Hok Horig Hnone.
  rewrite (streaming_prerouting_io p Henv Hiif Hfib Hl4 Hdport Hok). cbn [snd].
  rewrite (mark_through_dnat Hprerouting (set_meta p MKmark mark99) Horig Hnone).
  apply mark_after_set.
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
(* The masquerade is in an `inet` table, so its [nat_family] is "inet" and the L3
   family is resolved PER PACKET ([nat_addrfamily_pkt] = [pkt_l3_family p], the
   audit's inet-runtime-dispatch fidelity fix).  For the IPv4 streaming flow
   [pkt_l3_family p = "ip"], so the masquerade rewrites the IPv4 source slot. *)
Lemma post1_apply_masq : forall h p,
  pkt_l3_family p = "ip"%string ->
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  apply_nat h post1 p
    = store_nat_mapping
        (set_saddr "ip" p (e_ifaddr (pkt_env p) (field_value FMetaOifname p)))
        (Some (slice (pkt_nh p) 12 4),
         Some (e_ifaddr (pkt_env p) (field_value FMetaOifname p)), None, None).
Proof.
  intros h p Hfam Horig Hnone. unfold apply_nat, post1, filter_postrouting.
  cbn -[set_saddr e_ifaddr field_value pkt_env e_nat store_nat_mapping
        apply_nat_tuple nat_orig_addr nat_operand_addr nat_pmin pkt_l3_family].
  rewrite Hnone, Horig.
  unfold apply_nat_tuple, nat_is_src, nat_operand_addr, nat_addrfamily_pkt,
    nat_addrfamily, nat_orig_addr, masq_saddr, saddr_slot.
  cbn -[set_saddr e_ifaddr field_value pkt_env store_nat_mapping slice pkt_nh pkt_l3_family].
  rewrite !Hfam.
  cbn -[set_saddr e_ifaddr field_value pkt_env store_nat_mapping slice pkt_nh].
  rewrite Horig. reflexivity.
Qed.

(* THE OUTPUT PACKET of the postrouting chain (first packet of the flow): the input
   with its source address set to the exit interface's address (= what masquerade
   does), and the mapping recorded in [e_nat]. *)
(* The masquerade does NOT NAT-drop precisely when the exit interface HAS an
   address (ifaddr <> []) — mirroring the kernel's `if (!newsrc) return NF_DROP;`
   (nf_nat_masquerade.c:54-58).  Since post1's body is a no-op on a mark99 packet,
   [nat_drops] reads the exit-interface address straight off [p]. *)
Lemma post1_nat_no_drop : forall p ifaddr,
  pkt_l3_family p = "ip"%string ->
  field_value FMetaMark p = mark99 ->
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  e_ifaddr (pkt_env p) (field_value FMetaOifname p) = ifaddr ->
  ifaddr <> [] ->
  nat_drops Hpostrouting post1 (dsl_step post1 p) = false.
Proof.
  intros p ifaddr Hfam Hmark Horig Hnone Hifa Hne.
  rewrite (dsl_step_limit_free post1 p) by reflexivity.
  rewrite (post1_dsl_noop p Hmark).
  unfold nat_drops, post1, filter_postrouting.
  cbn -[e_nat e_ifaddr field_value pkt_env masq_saddr pkt_l3_family].
  rewrite Hnone, Horig. cbn [andb].
  unfold nat_iface_addr_absent. cbn -[e_ifaddr field_value pkt_env masq_saddr pkt_l3_family].
  unfold masq_saddr, nat_addrfamily_pkt, nat_addrfamily. cbn -[e_ifaddr field_value pkt_env pkt_l3_family].
  rewrite Hfam. cbn -[e_ifaddr field_value pkt_env].
  rewrite Hifa. destruct ifaddr; [contradiction|reflexivity].
Qed.

Theorem masquerade_output : forall p ifaddr,
  pkt_l3_family p = "ip"%string ->
  field_value FMetaMark p = mark99 ->
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  e_ifaddr (pkt_env p) (field_value FMetaOifname p) = ifaddr ->
  ifaddr <> [] ->
  eval_chain_trace Hpostrouting filter_postrouting p
    = (Accept, store_nat_mapping (set_saddr "ip" p ifaddr)
                 (Some (slice (pkt_nh p) 12 4), Some ifaddr, None, None)).
Proof.
  intros p ifaddr Hfam Hmark Horig Hnone Hifa Hne.
  unfold eval_chain_trace. rewrite postrouting_rules_eq. cbn [eval_rules_trace].
  rewrite (masquerade_gated_on_mark p Hmark), post1_outcome_accept. cbn [terminal].
  rewrite (post1_nat_no_drop p ifaddr Hfam Hmark Horig Hnone Hifa Hne).
  rewrite (dsl_step_limit_free post1 p) by reflexivity.
  rewrite (post1_dsl_noop p Hmark), (post1_apply_masq Hpostrouting p Hfam Horig Hnone), Hifa.
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
  pkt_l3_family p = "ip"%string ->
  field_value FMetaMark p = mark99 ->
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  e_ifaddr (pkt_env p) (field_value FMetaOifname p) = ifaddr ->
  List.length ifaddr = 4 -> 16 <= List.length (pkt_nh p) ->
  field_value FIp4Saddr (snd (eval_chain_trace Hpostrouting filter_postrouting p)) = ifaddr.
Proof.
  intros p ifaddr Hfam Hmark Horig Hnone Hifa Hlen Hnh.
  assert (Hne : ifaddr <> []) by (destruct ifaddr; [discriminate Hlen | discriminate]).
  rewrite (masquerade_output p ifaddr Hfam Hmark Horig Hnone Hifa Hne). cbn [snd].
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
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  (* [q] is the packet that leaves prerouting: the input marked AND dnat'd *)
  let q := snd (eval_chain_trace Hprerouting filter_prerouting p) in
  (* prerouting: packet in p -> (Accept, q) out, with q still carrying mark 0x99 *)
  fst (eval_chain_trace Hprerouting filter_prerouting p) = Accept
  /\ field_value FMetaMark q = mark99
  (* postrouting reads the surviving mark and masquerades (terminal accept) *)
  /\ rule_applies post1 q = true
  /\ eval_chain_mut filter_postrouting q = Accept.
Proof.
  intros p Henv Hiif Hfib Hl4 Hdport Hok Horig Hnone q.
  assert (Hmark : field_value FMetaMark q = mark99)
    by (apply streaming_prerouting_mark; assumption).
  split; [| split; [exact Hmark | split]].
  - unfold q. rewrite (streaming_prerouting_io p Henv Hiif Hfib Hl4 Hdport Hok).
    reflexivity.
  - now apply masquerade_gated_on_mark.
  - unfold eval_chain_mut, filter_postrouting. cbn -[field_value].
    rewrite Hmark. vm_compute. reflexivity.
Qed.
