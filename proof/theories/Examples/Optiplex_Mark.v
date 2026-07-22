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

    The headline is [streaming_flow_whole_ruleset_real]: a game-streaming packet
    (dport 48010) goes IN, traverses the WHOLE prerouting chain — flowing past
    rule 1 (the 3389 rule, which does not match) and being marked by rule 2 — and
    the packet that comes OUT is exactly the input with `meta mark` set to 0x99 and
    nothing else changed; carried to the postrouting hook, that mark drives the
    masquerade.  [eval_chain] runs a whole chain threading the mutated packet
    rule-by-rule through the SINGLE fold (the NAT data plane included — there is
    no side trace evaluator since M3); [chain_out] is the packet it leaves.

    M4 NOTE — [_real] vs the SUPERSEDED-vacuous originals: the pre-M4 theorems
    pinned the WHOLE env ([e = gen_env]) while also hypothesising a firing
    `fib daddr type local` — jointly unsatisfiable, since [gen_env] has no
    routes ([genenv_fib_local_contradiction] below).  The [_real] forms relax
    the pin to exactly the three [e_set] contents the chain's lookups read
    (the Router_Realistic.v pattern; recipe in proof/CONFIG_PROOFS.md), the
    originals survive verbatim as corollaries of the contradiction, and a
    concrete witness (env WITH a local route + streaming packet) discharges
    every [_real] hypothesis at once at the end of the file. *)

From Stdlib Require Import List String Ascii NArith Lia.
From Nft Require Import Bytes Verdict Packet Bytecode Syntax Semantics Optiplex_Gen Nftval.
Import ListNotations.

(** ** Wire constants (literal bytes, so [cbn] fully reduces the matches). *)
Definition mark99    : data := [153; 0; 0; 0].   (* the 0x99 firewall mark, host-endian (LE) *)
(* "home" in a 16-byte IFNAMSIZ zero-padded ifname register (the kernel
   compares the full 16-byte buffer for an exact name match). *)
Definition if_home   : data := Eval vm_compute in encode (ifname "home"%string).
Definition fib_local : data := Eval vm_compute in encode (fib_type_val FAlocal). (* fib… type local (RTN_LOCAL); host-endian u32 on LE *)
Definition l4_tcp    : data := Eval vm_compute in encode (inet_proto 6).
Definition port3389  : data := Eval vm_compute in encode (Nftval.port 3389). (* 0x0d3d— RDP *)
Definition port48010 : data := Eval vm_compute in encode (Nftval.port 48010). (* 0xbb8a— a Sunshine stream port *)

(** Each wire constant IS the register bytes of its central typed nft value. *)
Lemma fib_local_typed : fib_local = encode (fib_type_val FAlocal). Proof. reflexivity. Qed.
Lemma l4_tcp_typed    : l4_tcp    = encode (inet_proto 6).         Proof. reflexivity. Qed.
Lemma port3389_typed  : port3389  = encode (Nftval.port 3389).     Proof. reflexivity. Qed.
Lemma port48010_typed : port48010 = encode (Nftval.port 48010).    Proof. reflexivity. Qed.
Lemma if_home_typed   : if_home   = encode (ifname "home"%string). Proof. reflexivity. Qed.

(* ================================================================== *)
(** ** M4: the whole-env pin [e = gen_env] made these theorems VACUOUS.

    The prerouting rules match `fib daddr type local`, so every theorem below
    hypothesises [field_value (FFib "daddr" FRtype) e p = fib_local].  But the
    parser-emitted [gen_env] pins [e_routes = []] (a parser knows the SETS a
    ruleset declares, not the host's routing table), and the fib load is
    COMPUTED from the routes ([do_load (LFib …)] = [lpm_fib (e_routes e) …]),
    so under [e = gen_env] it can only ever return [] — never [fib_local].
    The two hypotheses are jointly UNSATISFIABLE: every [e = gen_env] theorem
    in this file certified ZERO packets.  [genenv_fib_local_contradiction]
    machine-checks that (the same shape as
    [Router_Realistic.ctstate_under_genenv_never_new] for the ct pin).

    THE FIX (same recipe as Router_Realistic.v, the documented pattern in
    proof/CONFIG_PROOFS.md § "Pin only what the lookups read"): the chain's
    lookups read exactly the THREE named sets below — so the [_real] theorems
    relax [e = gen_env] to those three [e_set] equations, leaving [e_routes]
    (hence the fib hypothesis) and [e_nat] free to be REAL.  The original
    statements survive VERBATIM below, each derived from the contradiction
    (SUPERSEDED-vacuous); the [_real] forms take the headline slot
    (THEOREMS.md, `make axioms`), and the § "Non-vacuity witness" at the end
    of the file exhibits a concrete env+packet satisfying every [_real]
    hypothesis at once. *)

(** What the prerouting chain's lookups actually read: the l4proto set, the
    iifname set, and the streaming-dport set the parser emitted. *)
Definition set_l4proto : list (data * data) := e_set gen_env "__set0".
Definition set_iif     : list (data * data) := e_set gen_env "__set1".
Definition set_sports  : list (data * data) := e_set gen_env "__set2".

(** Under the whole-env pin the fib load is [] — the fib hypothesis of every
    pinned theorem below is unsatisfiable. *)
Lemma genenv_fib_daddr_empty : forall p,
  field_value (FFib "daddr" FRtype) gen_env p = [].
Proof. reflexivity. Qed.

Theorem genenv_fib_local_contradiction : forall e p,
  e = gen_env ->
  field_value (FFib "daddr" FRtype) e p = fib_local ->
  False.
Proof.
  intros e p -> H. rewrite genenv_fib_daddr_empty in H. discriminate.
Qed.

(** The rules of interest, taken straight from the generated chains. *)
Definition dflt : rule :=
  {| r_body := [];
     r_outcome := ONone; r_after := [] |}.
Definition pre1  : rule := List.nth 0 (c_rules filter_prerouting)  dflt.  (* RDP/3389 *)
Definition pre2  : rule := List.nth 1 (c_rules filter_prerouting)  dflt.  (* streaming ports *)
Definition post1 : rule := List.nth 0 (c_rules filter_postrouting) dflt.  (* masquerade *)

(* the prerouting chain has exactly these three rules (rule 3 duplicates rule 2) *)
Lemma prerouting_rules_eq :
  c_rules filter_prerouting = [pre1; pre2; List.nth 2 (c_rules filter_prerouting) dflt].
Proof. reflexivity. Qed.

(** Reading [meta mark] right after `mark set v` yields the REGISTER-normalised
    [v]: [do_load]/[meta_load] normalises a `meta mark` read to the kernel's
    fixed u32 slot — 4 bytes ([Bytes.fit]), each an octet ([Bytes.octets]) — so
    the read-back is [fit 4 (octets v)], UNCONDITIONALLY (no width or byte
    hypothesis; for every concrete mark here, e.g. [mark99], that computes to
    [v] itself).  Supersedes the earlier width-hypothesis form
    ([length v = 4 -> read-back = v]), which the octet clamp makes both
    unnecessary (no hypotheses at all now) and too weak (it said nothing about
    off-width or out-of-range writes). *)
Lemma mark_after_set : forall e p v,
  field_value FMetaMark e (set_meta p MKmark v) = fit 4 (octets v).
Proof.
  intros e p v. unfold field_value, do_load, read_meta, meta_load,
    set_meta, with_pkt_meta. cbn. reflexivity.
Qed.

(** ** What each prerouting rule does to the packet (the per-rule writes).

    These characterise the OUTPUT of running one rule's body on the packet — the
    heart of "what comes out".  [cbn -[…set_meta]] reduces the matches but keeps
    [set_meta] folded, so the result is stated as the input packet with exactly the
    mark changed. *)

(* rule 1 (the 3389 rule) does NOT match a streaming packet — its `th dport 3389`
   fails, so the `mark set` after it never runs and the packet is unchanged.
   [_real]: env relaxed to the one set rule 1's lookups read ([__set0]). *)
Lemma pre1_streaming_noop_real : forall e p,
  e_set e "__set0" = set_l4proto ->
  field_value FMetaIifname e p = if_home ->
  field_value (FFib "daddr" FRtype) e p = fib_local ->
  field_value FMetaL4proto e p = l4_tcp ->
  field_value FThDport e p = port48010 ->
  read_payload_ok PTransport 2 2 p = true ->
  dsl_writes pre1 e p = (e, p).
Proof.
  intros e p Hs0 Hiif Hfib Hl4 Hdport Hok.
  unfold dsl_writes, pre1, filter_prerouting.
  cbn -[field_value set_meta read_payload_ok].
  unfold eval_matchcond, match_loadable, eval_matchcond_body, fields_loadable,
    field_loadable, load_ok.
  cbn -[field_value set_meta read_payload_ok].
  rewrite ?Hok, !Hiif, !Hfib, !Hl4, !Hdport, !Hs0.
  cbn -[set_meta read_payload_ok]. rewrite ?Hok. cbn -[set_meta]. reflexivity.
Qed.

(** SUPERSEDED-vacuous (M4): the original whole-env-pinned statement, kept
    VERBATIM; its [e = gen_env] + fib hypotheses are jointly unsatisfiable
    ([genenv_fib_local_contradiction]), so it is derived from the
    contradiction.  Successor: [pre1_streaming_noop_real]. *)
Lemma pre1_streaming_noop : forall e p,
  e = gen_env ->
  field_value FMetaIifname e p = if_home ->
  field_value (FFib "daddr" FRtype) e p = fib_local ->
  field_value FMetaL4proto e p = l4_tcp ->
  field_value FThDport e p = port48010 ->
  read_payload_ok PTransport 2 2 p = true ->
  dsl_writes pre1 e p = (e, p).
Proof.
  intros e p Henv Hiif Hfib Hl4 Hdport Hok.
  exact (False_ind _ (genenv_fib_local_contradiction e p Henv Hfib)).
Qed.

(* rule 2 matches a streaming packet and sets the mark: the packet that comes out
   is the input with meta mark := 0x99 (and nothing else).  [_real]: env relaxed
   to the three sets rule 2's lookups read. *)
Lemma pre2_streaming_marks_real : forall e p,
  e_set e "__set0" = set_l4proto ->
  e_set e "__set1" = set_iif ->
  e_set e "__set2" = set_sports ->
  field_value FMetaIifname e p = if_home ->
  field_value (FFib "daddr" FRtype) e p = fib_local ->
  field_value FMetaL4proto e p = l4_tcp ->
  field_value FThDport e p = port48010 ->
  read_payload_ok PTransport 2 2 p = true ->
  dsl_writes pre2 e p = (e, set_meta p MKmark mark99).
Proof.
  intros e p Hs0 Hs1 Hs2 Hiif Hfib Hl4 Hdport Hok.
  unfold dsl_writes, pre2, filter_prerouting.
  cbn -[field_value set_meta read_payload_ok].
  unfold eval_matchcond, match_loadable, eval_matchcond_body, fields_loadable,
    field_loadable, load_ok.
  cbn -[field_value set_meta read_payload_ok].
  rewrite ?Hok, !Hiif, !Hfib, !Hl4, !Hdport, ?Hs0, ?Hs1, ?Hs2.
  cbn -[set_meta read_payload_ok]. rewrite ?Hok. cbn -[set_meta]. reflexivity.
Qed.

(** SUPERSEDED-vacuous (M4); successor [pre2_streaming_marks_real]. *)
Lemma pre2_streaming_marks : forall e p,
  e = gen_env ->
  field_value FMetaIifname e p = if_home ->
  field_value (FFib "daddr" FRtype) e p = fib_local ->
  field_value FMetaL4proto e p = l4_tcp ->
  field_value FThDport e p = port48010 ->
  read_payload_ok PTransport 2 2 p = true ->
  dsl_writes pre2 e p = (e, set_meta p MKmark mark99).
Proof.
  intros e p Henv Hiif Hfib Hl4 Hdport Hok.
  exact (False_ind _ (genenv_fib_local_contradiction e p Henv Hfib)).
Qed.






(* the streaming rule is loadable: its only payload read is the th-dport set key *)
Lemma pre2_loadable : forall e p,
  read_payload_ok PTransport 2 2 p = true -> rule_loadable pre2 e p = true.
Proof.
  intros e p Hok. unfold rule_loadable, pre2, filter_prerouting, end_loadable,
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
  destruct (l4_csum_slot (read_meta p MKl4proto)) as [[[coff clen] mand]|]; [|reflexivity].
  destruct (andb (pkt_have_l4 p) (Nat.leb (coff + clen) (List.length (pkt_th p)))); [|reflexivity].
  destruct (andb (negb mand) (N.eqb (data_to_N (slice (pkt_th p) coff clen)) 0)); reflexivity.
Qed.

Lemma set_daddr_meta : forall fam p v k, pkt_meta (set_daddr fam p v) k = pkt_meta p k.
Proof.
  intros fam p v k. unfold set_daddr.
  destruct (daddr_slot fam) as [off len].
  rewrite set_l4_csum_addr_meta.
  destruct (nataf_eqb fam nat_fam_ip6); reflexivity.
Qed.

(* applying pre2's dnat to a FIRST-flow, original-direction packet rewrites the
   DESTINATION address to the windows box and records the flow-keyed mapping. *)
Lemma pre2_apply_dnat : forall h e p,
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  apply_nat h pre2 e p
    = (store_nat_mapping e p
         (Some (slice (pkt_nh p) 16 4), Some windows_ip, None, None),
       set_daddr nat_fam_ip4 p windows_ip).
Proof.
  intros h e p Horig Hnone. unfold apply_nat, pre2, filter_prerouting.
  cbn -[set_daddr field_value e_nat store_nat_mapping
        apply_nat_tuple nat_orig_addr nat_operand_addr nat_port_num nat_orig_port slice pkt_nh].
  rewrite Hnone, Horig.
  unfold apply_nat_tuple, apply_nat_tuple_c, nat_is_src, nat_kind_src,
    nat_operand_addr, nat_new_addr, nat_opnd, nat_addrfamily_pkt, nat_af_pkt,
    nat_af_norm, nat_addrfamily, nat_orig_addr, nat_orig_addr_c, nat_addr,
    nat_has_addr, nat_portonly, nat_orig_port, nat_orig_port_c,
    nat_port_num, nat_port_val.
  cbn -[set_daddr field_value store_nat_mapping slice pkt_nh].
  rewrite Horig. reflexivity.
Qed.

(* the firewall mark set by the body survives the terminal dnat. *)
Lemma mark_through_dnat : forall h e p,
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  field_value FMetaMark e (snd (apply_nat h pre2 e p)) = field_value FMetaMark e p.
Proof.
  intros h e p Horig Hnone. rewrite (pre2_apply_dnat h e p Horig Hnone).
  cbn [snd]. unfold field_value. cbn [field_load do_load].
  unfold read_meta, meta_load. f_equal. f_equal. apply set_daddr_meta.
Qed.

(* pre2's dnat never NAT-drops: [nat_iface_addr_absent] only fires for
   masquerade/redirect (a source/dest taken from an interface); a `dnat` to an
   explicit address has no interface to lack, so [nat_drops] is unconditionally
   [false] and the trace takes the apply-NAT branch, not the NF_DROP one. *)
Lemma pre2_no_natdrop : forall e p, nat_drops Hprerouting pre2 e p = false.
Proof.
  intros e p. unfold nat_drops, nat_drops_c, pre2, filter_prerouting.
  cbn -[e_nat pkt_ctdir_orig nat_iface_addr_absent].
  unfold nat_iface_addr_absent. cbn -[e_nat pkt_ctdir_orig].
  destruct (e_nat e (pkt_flow p)); [reflexivity | apply Bool.andb_false_r].
Qed.

(** Single-fold per-rule STEPS of the two prerouting rules on a streaming packet:
    rule 1 breaks at its `th dport 3389` compare (no verdict, state kept), rule 2
    walks to its terminal dnat with the mark written — verdict and state from ONE
    traversal ([rule_step]). *)
Lemma pre1_streaming_step_real : forall h e p,
  e_set e "__set0" = set_l4proto ->
  field_value FMetaIifname e p = if_home ->
  field_value (FFib "daddr" FRtype) e p = fib_local ->
  field_value FMetaL4proto e p = l4_tcp ->
  field_value FThDport e p = port48010 ->
  read_payload_ok PTransport 2 2 p = true ->
  rule_step h pre1 e p = (None, (e, p)).
Proof.
  intros h e p Hs0 Hiif Hfib Hl4 Hdport Hok.
  unfold rule_step, pre1, filter_prerouting.
  cbn -[field_value set_meta read_payload_ok].
  unfold eval_matchcond, match_loadable, eval_matchcond_body, fields_loadable,
    field_loadable, load_ok.
  cbn -[field_value set_meta read_payload_ok].
  rewrite ?Hok, !Hiif, !Hfib, !Hl4, !Hdport, ?Hs0.
  cbn -[set_meta read_payload_ok]. rewrite ?Hok. cbn -[set_meta].
  vm_compute. reflexivity.
Qed.

(* pre2 is a dnat: its NAT core NEVER drops (any hook, env, packet). *)
Lemma pre2_no_natdrop_any : forall h e q, nat_drops h pre2 e q = false.
Proof.
  intros h e q. unfold nat_drops, nat_drops_c, pre2, filter_prerouting.
  cbn -[e_nat pkt_ctdir_orig nat_iface_addr_absent].
  unfold nat_iface_addr_absent. cbn -[e_nat pkt_ctdir_orig].
  destruct (e_nat e (pkt_flow q)); [reflexivity | apply Bool.andb_false_r].
Qed.

Lemma pre2_streaming_step_real : forall h e p,
  e_set e "__set0" = set_l4proto ->
  e_set e "__set1" = set_iif ->
  e_set e "__set2" = set_sports ->
  field_value FMetaIifname e p = if_home ->
  field_value (FFib "daddr" FRtype) e p = fib_local ->
  field_value FMetaL4proto e p = l4_tcp ->
  field_value FThDport e p = port48010 ->
  read_payload_ok PTransport 2 2 p = true ->
  rule_step h pre2 e p
  = (Some Accept, apply_nat h pre2 e (set_meta p MKmark mark99)).
Proof.
  intros h e p Hs0 Hs1 Hs2 Hiif Hfib Hl4 Hdport Hok.
  unfold rule_step, pre2, filter_prerouting.
  cbn -[field_value set_meta read_payload_ok apply_nat nat_drops].
  unfold eval_matchcond, match_loadable, eval_matchcond_body, fields_loadable,
    field_loadable, load_ok.
  cbn -[field_value set_meta read_payload_ok apply_nat nat_drops].
  rewrite ?Hok, !Hiif, !Hfib, !Hl4, !Hdport, ?Hs0, ?Hs1, ?Hs2.
  cbn -[set_meta read_payload_ok apply_nat nat_drops]. rewrite ?Hok.
  cbn -[set_meta apply_nat nat_drops].
  rewrite pre2_no_natdrop_any. reflexivity.
Qed.

(** ** What comes out of the prerouting chain.

    Run the WHOLE prerouting chain on a streaming packet: it traverses rule 1
    (skipped, packet unchanged) and is matched by rule 2 (terminal accept), which
    BOTH sets the mark (the body) AND destination-NATs the packet (the terminal
    `dnat ip to $windows`).  The output is [(Accept, dnat applied to the marked
    packet)] — packet in, packet out.  [pre2_apply_dnat] characterises the dnat
    (daddr rewritten to [windows_ip]); [streaming_prerouting_mark] shows the mark
    survives it. *)
Theorem streaming_prerouting_io_real : forall e p,
  e_set e "__set0" = set_l4proto ->
  e_set e "__set1" = set_iif ->
  e_set e "__set2" = set_sports ->
  field_value FMetaIifname e p = if_home ->
  field_value (FFib "daddr" FRtype) e p = fib_local ->
  field_value FMetaL4proto e p = l4_tcp ->
  field_value FThDport e p = port48010 ->
  read_payload_ok PTransport 2 2 p = true ->
  eval_chain Hprerouting filter_prerouting e p
    = (Accept, apply_nat Hprerouting pre2 e (set_meta p MKmark mark99)).
Proof.
  intros e p Hs0 Hs1 Hs2 Hiif Hfib Hl4 Hdport Hok.
  unfold eval_chain, eval_table. rewrite prerouting_rules_eq.
  cbn [List.length eval_rules].
  (* rule 1: traversed but breaks at its dport compare; state kept *)
  rewrite pre1_streaming_step_real by assumption.
  (* rule 2: walks to its terminal dnat with the mark written; the NAT effect
     is the fold's own (no side trace strand) *)
  rewrite pre2_streaming_step_real by assumption.
  destruct (apply_nat Hprerouting pre2 e (set_meta p MKmark mark99)) as [e2 p2]
    eqn:HA.
  reflexivity.
Qed.

(** SUPERSEDED-vacuous (M4): kept verbatim, derived from the contradiction;
    successor [streaming_prerouting_io_real]. *)
Theorem streaming_prerouting_io : forall e p,
  e = gen_env ->
  field_value FMetaIifname e p = if_home ->
  field_value (FFib "daddr" FRtype) e p = fib_local ->
  field_value FMetaL4proto e p = l4_tcp ->
  field_value FThDport e p = port48010 ->
  read_payload_ok PTransport 2 2 p = true ->
  eval_chain Hprerouting filter_prerouting e p
    = (Accept, apply_nat Hprerouting pre2 e (set_meta p MKmark mark99)).
Proof.
  intros e p Henv Hiif Hfib Hl4 Hdport Hok.
  exact (False_ind _ (genenv_fib_local_contradiction e p Henv Hfib)).
Qed.

(** The firewall mark survives the terminal dnat: the packet leaving prerouting
    still has `meta mark` = 0x99 (so the postrouting masquerade still fires). *)
Theorem streaming_prerouting_mark_real : forall e p,
  e_set e "__set0" = set_l4proto ->
  e_set e "__set1" = set_iif ->
  e_set e "__set2" = set_sports ->
  field_value FMetaIifname e p = if_home ->
  field_value (FFib "daddr" FRtype) e p = fib_local ->
  field_value FMetaL4proto e p = l4_tcp ->
  field_value FThDport e p = port48010 ->
  read_payload_ok PTransport 2 2 p = true ->
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  field_value FMetaMark e
    (snd (snd (eval_chain Hprerouting filter_prerouting e p))) = mark99.
Proof.
  intros e p Hs0 Hs1 Hs2 Hiif Hfib Hl4 Hdport Hok Horig Hnone.
  rewrite (streaming_prerouting_io_real e p Hs0 Hs1 Hs2 Hiif Hfib Hl4 Hdport Hok).
  cbn [snd].
  rewrite (mark_through_dnat Hprerouting e (set_meta p MKmark mark99) Horig Hnone).
  rewrite mark_after_set. reflexivity.
Qed.

(** SUPERSEDED-vacuous (M4): kept verbatim, derived from the contradiction;
    successor [streaming_prerouting_mark_real]. *)
Theorem streaming_prerouting_mark : forall e p,
  e = gen_env ->
  field_value FMetaIifname e p = if_home ->
  field_value (FFib "daddr" FRtype) e p = fib_local ->
  field_value FMetaL4proto e p = l4_tcp ->
  field_value FThDport e p = port48010 ->
  read_payload_ok PTransport 2 2 p = true ->
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  field_value FMetaMark e
    (snd (snd (eval_chain Hprerouting filter_prerouting e p))) = mark99.
Proof.
  intros e p Henv Hiif Hfib Hl4 Hdport Hok Horig Hnone.
  exact (False_ind _ (genenv_fib_local_contradiction e p Henv Hfib)).
Qed.

(** ** The mark is read by the postrouting masquerade rule: on a 0x99-marked
    packet the rule's body WALKS to its end ([BRdone] — the `mark 0x99` match
    passes, the trailing `log` writes nothing), so the masquerade terminal is
    reached; on an unmarked packet the body BREAKs (state kept), so it is not. *)
Theorem masquerade_gated_on_mark : forall e p,
  field_value FMetaMark e p = mark99 -> body_step (r_body post1) e p = BRdone e p.
Proof.
  intros e p Hm. unfold post1, filter_postrouting.
  cbn -[field_value]. rewrite Hm. vm_compute. reflexivity.
Qed.

Theorem unmarked_not_masqueraded : forall e p,
  field_value FMetaMark e p = [0;0;0;0] -> body_step (r_body post1) e p = BRbreak e p.
Proof.
  intros e p Hm. unfold post1, filter_postrouting.
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


(* its body (a mark match + log) writes nothing to the packet *)
Lemma post1_dsl_noop : forall e p,
  field_value FMetaMark e p = mark99 -> dsl_writes post1 e p = (e, p).
Proof.
  intros e p Hm. unfold dsl_writes, post1, filter_postrouting.
  cbn -[field_value]. rewrite Hm. vm_compute. reflexivity.
Qed.

(* applying its NAT effect source-rewrites to the exit interface's address AND
   stores that established mapping in the flow-keyed [e_nat] table.  NAT is
   FLOW-STATEFUL ([e_nat], Packet.v): on the FIRST packet of a flow ([e_nat .. = None])
   the mapping is computed from the exit interface and STORED; the source address
   is rewritten as on any later same-flow packet. *)
(* The masquerade is in an `inet` table, so its [nat_family] is "inet" and the L3
   family is resolved PER PACKET ([nat_addrfamily_pkt] = [pkt_l3_family p], the
   kernel's runtime dispatch for inet tables).  For the IPv4 streaming flow
   [pkt_l3_family p = nat_fam_ip4], so the masquerade rewrites the IPv4 source slot. *)
Lemma post1_apply_masq : forall h e p,
  pkt_l3_family p = nat_fam_ip4 ->
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  apply_nat h post1 e p
    = (store_nat_mapping e p
         (Some (slice (pkt_nh p) 12 4),
          Some (e_ifaddr e (field_value FMetaOifname e p)), None, None),
       set_saddr nat_fam_ip4 p (e_ifaddr e (field_value FMetaOifname e p))).
Proof.
  intros h e p Hfam Horig Hnone. unfold apply_nat, post1, filter_postrouting.
  cbn -[set_saddr e_ifaddr field_value e_nat store_nat_mapping
        apply_nat_tuple nat_orig_addr nat_operand_addr nat_port_num pkt_l3_family].
  rewrite Hnone, Horig.
  unfold apply_nat_tuple, apply_nat_tuple_c, nat_is_src, nat_kind_src,
    nat_operand_addr, nat_new_addr, nat_opnd, nat_addrfamily_pkt, nat_af_pkt,
    nat_af_norm, nat_addrfamily, nat_orig_addr, nat_orig_addr_c, masq_saddr,
    saddr_slot, nat_portonly, nat_has_addr, nat_orig_port, nat_orig_port_c,
    nat_port_num, nat_port_val, nat_addr.
  cbn -[set_saddr e_ifaddr field_value store_nat_mapping slice pkt_nh pkt_l3_family].
  rewrite !Hfam.
  cbn -[set_saddr e_ifaddr field_value store_nat_mapping slice pkt_nh].
  rewrite Horig. reflexivity.
Qed.

(* THE OUTPUT PACKET of the postrouting chain (first packet of the flow): the input
   with its source address set to the exit interface's address (= what masquerade
   does), and the mapping recorded in [e_nat]. *)
(* The masquerade does NOT NAT-drop precisely when the exit interface HAS an
   address (ifaddr <> []) — mirroring the kernel's `if (!newsrc) return NF_DROP;`
   (nf_nat_masquerade.c:54-58).  Since post1's body is a no-op on a mark99 packet,
   [nat_drops] reads the exit-interface address straight off [p]. *)
Lemma post1_nat_no_drop : forall e p ifaddr,
  pkt_l3_family p = nat_fam_ip4 ->
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  e_ifaddr e (field_value FMetaOifname e p) = ifaddr ->
  ifaddr <> [] ->
  nat_drops Hpostrouting post1 e p = false.
Proof.
  intros e p ifaddr Hfam Horig Hnone Hifa Hne.
  unfold nat_drops, nat_drops_c, post1, filter_postrouting.
  cbn -[e_nat e_ifaddr field_value masq_saddr pkt_l3_family].
  rewrite Hnone, Horig. cbn [andb].
  unfold nat_iface_addr_absent. cbn -[e_ifaddr field_value masq_saddr pkt_l3_family].
  unfold masq_saddr, nat_addrfamily_pkt, nat_addrfamily.
  cbn -[e_ifaddr field_value pkt_l3_family].
  rewrite Hfam. cbn -[e_ifaddr field_value].
  rewrite Hifa. destruct ifaddr; [contradiction|reflexivity].
Qed.

(* THE single-fold step of the masquerade rule on a marked packet: the body
   is a pure match (mark test + log), the NAT terminal performs the data-plane
   effect — NF_DROP or Accept+[apply_nat] — in the fold itself. *)
Lemma post1_rule_step : forall h e p,
  field_value FMetaMark e p = mark99 ->
  rule_step h post1 e p
  = (if nat_drops h post1 e p then (Some Drop, (e, p))
     else (Some Accept, apply_nat h post1 e p)).
Proof.
  intros h e p Hm.
  unfold rule_step, post1, filter_postrouting.
  cbn -[field_value apply_nat nat_drops].
  rewrite Hm. vm_compute (data_eqb _ _). cbn -[apply_nat nat_drops].
  reflexivity.
Qed.

Theorem masquerade_output : forall e p ifaddr,
  pkt_l3_family p = nat_fam_ip4 ->
  field_value FMetaMark e p = mark99 ->
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  e_ifaddr e (field_value FMetaOifname e p) = ifaddr ->
  ifaddr <> [] ->
  eval_chain Hpostrouting filter_postrouting e p
    = (Accept, (store_nat_mapping e p
                  (Some (slice (pkt_nh p) 12 4), Some ifaddr, None, None),
                set_saddr nat_fam_ip4 p ifaddr)).
Proof.
  intros e p ifaddr Hfam Hmark Horig Hnone Hifa Hne.
  unfold eval_chain, eval_table. rewrite postrouting_rules_eq.
  cbn [List.length eval_rules].
  rewrite (post1_rule_step Hpostrouting e p Hmark).
  rewrite (post1_nat_no_drop e p ifaddr Hfam Horig Hnone Hifa Hne).
  rewrite (post1_apply_masq Hpostrouting e p Hfam Horig Hnone), Hifa.
  reflexivity.
Qed.

(* reading the source address back: after masquerade, `ip saddr` IS the exit
   interface's address (for a well-formed IPv4 header and a 4-byte address).  The
   [store_nat_mapping] env write preserves [pkt_nh], so the read-back is unchanged. *)
Lemma saddr_after_set : forall e p v,
  16 <= List.length (pkt_nh p) -> List.length v = 4 ->
  field_value FIp4Saddr e (set_saddr nat_fam_ip4 p v) = v.
Proof.
  intros e p v Hlen Hv.
  unfold field_value; cbn [field_load do_load]; unfold read_payload.
  apply slice_set_saddr_ip4_same; [exact Hlen | exact Hv].
Qed.

Theorem masquerade_source_is_exit_iface : forall e p ifaddr,
  pkt_l3_family p = nat_fam_ip4 ->
  field_value FMetaMark e p = mark99 ->
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  e_ifaddr e (field_value FMetaOifname e p) = ifaddr ->
  List.length ifaddr = 4 -> 16 <= List.length (pkt_nh p) ->
  field_value FIp4Saddr e
    (snd (snd (eval_chain Hpostrouting filter_postrouting e p))) = ifaddr.
Proof.
  intros e p ifaddr Hfam Hmark Horig Hnone Hifa Hlen Hnh.
  assert (Hne : ifaddr <> []) by (destruct ifaddr; [discriminate Hlen | discriminate]).
  rewrite (masquerade_output e p ifaddr Hfam Hmark Horig Hnone Hifa Hne). cbn [snd].
  apply saddr_after_set; assumption.
Qed.

(** ** End-to-end: a streaming packet across the WHOLE ruleset.

    The packet goes in; out of prerouting comes the same packet with mark 0x99;
    that packet, carried to the postrouting hook (as the kernel carries the skb
    mark), is matched by the masquerade rule and the postrouting chain accepts it.
    No rule is applied by hand — each chain is run whole by [eval_chain] /
    [eval_chain_flat_verdict]. *)
Theorem streaming_flow_whole_ruleset_real : forall e p,
  e_set e "__set0" = set_l4proto ->
  e_set e "__set1" = set_iif ->
  e_set e "__set2" = set_sports ->
  field_value FMetaIifname e p = if_home ->
  field_value (FFib "daddr" FRtype) e p = fib_local ->
  field_value FMetaL4proto e p = l4_tcp ->
  field_value FThDport e p = port48010 ->
  read_payload_ok PTransport 2 2 p = true ->
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  (* [q] is the packet that leaves prerouting (the input marked AND dnat'd);
     [e'] the env it leaves (the stored dnat mapping) *)
  let q := snd (snd (eval_chain Hprerouting filter_prerouting e p)) in
  let e' := fst (snd (eval_chain Hprerouting filter_prerouting e p)) in
  (* prerouting: packet in p -> (Accept, q) out, with q still carrying mark 0x99 *)
  fst (eval_chain Hprerouting filter_prerouting e p) = Accept
  /\ field_value FMetaMark e' q = mark99
  (* postrouting reads the surviving mark and masquerades: terminal accept,
     UNLESS the kernel NAT core drops for want of a usable exit address —
     the fold carries that data-plane drop too (M3) *)
  /\ body_step (r_body post1) e' q = BRdone e' q
  /\ eval_chain_flat_verdict Hpostrouting filter_postrouting e' q
     = (if nat_drops Hpostrouting post1 e' q then Drop else Accept).
Proof.
  intros e p Hs0 Hs1 Hs2 Hiif Hfib Hl4 Hdport Hok Horig Hnone q e'.
  assert (Hmark : field_value FMetaMark e' q = mark99).
  { unfold q. rewrite <- (streaming_prerouting_mark_real e p); try assumption.
    reflexivity. }
  split; [| split; [exact Hmark | split]].
  - unfold q.
    rewrite (streaming_prerouting_io_real e p Hs0 Hs1 Hs2 Hiif Hfib Hl4 Hdport Hok).
    reflexivity.
  - now apply masquerade_gated_on_mark.
  - unfold eval_chain_flat_verdict. rewrite postrouting_rules_eq. rewrite ?eval_rules_flat_verdict_cons, ?eval_rules_flat_verdict_nil.
    rewrite (post1_rule_step Hpostrouting e' q Hmark).
    destruct (nat_drops Hpostrouting post1 e' q); [reflexivity|].
    destruct (apply_nat Hpostrouting post1 e' q) as [e2 q2]. reflexivity.
Qed.

(** SUPERSEDED-vacuous (M4): the pre-M4 headline, kept verbatim, derived from
    the contradiction; the headline slot (THEOREMS.md, `make axioms`) now
    belongs to [streaming_flow_whole_ruleset_real]. *)
Theorem streaming_flow_whole_ruleset : forall e p,
  e = gen_env ->
  field_value FMetaIifname e p = if_home ->
  field_value (FFib "daddr" FRtype) e p = fib_local ->
  field_value FMetaL4proto e p = l4_tcp ->
  field_value FThDport e p = port48010 ->
  read_payload_ok PTransport 2 2 p = true ->
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  (* [q] is the packet that leaves prerouting (the input marked AND dnat'd);
     [e'] the env it leaves (the stored dnat mapping) *)
  let q := snd (snd (eval_chain Hprerouting filter_prerouting e p)) in
  let e' := fst (snd (eval_chain Hprerouting filter_prerouting e p)) in
  (* prerouting: packet in p -> (Accept, q) out, with q still carrying mark 0x99 *)
  fst (eval_chain Hprerouting filter_prerouting e p) = Accept
  /\ field_value FMetaMark e' q = mark99
  (* postrouting reads the surviving mark and masquerades (terminal accept) *)
  /\ body_step (r_body post1) e' q = BRdone e' q
  /\ eval_chain_flat_verdict Hpostrouting filter_postrouting e' q = Accept.
Proof.
  intros e p Henv Hiif Hfib Hl4 Hdport Hok Horig Hnone q e'.
  exact (False_ind _ (genenv_fib_local_contradiction e p Henv Hfib)).
Qed.

(* ================================================================== *)
(** ** Non-vacuity witness: a concrete env+packet satisfying EVERY [_real]
    hypothesis at once.

    [env_stream] carries the parser's sets (via [env_with_sets … decls], so
    the three [e_set] pins hold by computation) AND a real routing table: one
    host-local route for 192.168.51.1 whose FRtype answer is [fib_local] —
    the component [gen_env] pinned to [] (the vacuity source).  [pkt_stream]
    is a TCP packet from the home bridge to 192.168.51.1, dport 48010, with a
    wf fib key (the oracle returns the packet's real daddr bytes, the
    [Fib_Local.fibkey_wf] discipline).  The [Example]s discharge each [_real]
    hypothesis by [vm_compute] and then INSTANTIATE the repaired heads — the
    hypotheses are jointly satisfiable, so the theorems constrain real
    packets.  (Contrast [genenv_fib_local_contradiction]: the SUPERSEDED
    originals provably constrain none.) *)

Definition daddr_stream : data := [192; 168; 51; 1].

Definition env_stream : env :=
  env_with_sets
    {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
       e_routes := [(daddr_stream, daddr_stream,
                     fun res => match res with FRtype => fib_local | _ => [] end)];
       e_rt := fun _ => []; e_limit := fun _ => 0; e_quota := fun _ => 0;
       (* the exit interface carries a usable address, so the postrouting
          masquerade FIRES instead of taking the kernel's no-usable-address
          NF_DROP (nat_drops, in-fold since M3) *)
       e_ifaddrs := fun _ => ifaddrs_of [203; 0; 113; 9]; e_ifaddrs6 := fun _ => [];
       e_connlimit := fun _ => [];
       e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}
    decls.

Definition pkt_stream : packet :=
  {| pkt_meta := fun k => match k with
                          | MKiifname => if_home
                          | MKl4proto => l4_tcp
                          | _ => []
                          end;
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := [];
     (* a 20-byte IPv4 header: saddr 192.168.20.7 at 12, daddr 192.168.51.1 at 16 *)
     pkt_nh := [69; 0; 0; 40; 0; 0; 0; 0; 64; 6; 0; 0;
                192; 168; 20; 7; 192; 168; 51; 1];
     (* transport header: sport 40000 (156;64), dport 48010 (187;138) *)
     pkt_th := [156; 64; 187; 138];
     pkt_ih := []; pkt_tnl := [];
     (* wf fib key: the oracle returns the REAL daddr bytes (Fib_Local.fibkey_wf) *)
     pkt_fibkey := fun sel =>
       if (String.eqb sel "daddr" || String.eqb sel "daddr . iif")%bool
       then daddr_stream else [];
     pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => [];
     pkt_have_l2 := true; pkt_have_l4 := true; pkt_fragoff := 0;
     pkt_flow := []; pkt_untracked := false;
     pkt_ctdir_orig := true; pkt_ct_present := true |}.

(** Every [_real] hypothesis holds on the witness pair (joint satisfiability). *)
Example witness_sets :
  e_set env_stream "__set0" = set_l4proto
  /\ e_set env_stream "__set1" = set_iif
  /\ e_set env_stream "__set2" = set_sports.
Proof. repeat split; vm_compute; reflexivity. Qed.

Example witness_fields :
  field_value FMetaIifname env_stream pkt_stream = if_home
  /\ field_value (FFib "daddr" FRtype) env_stream pkt_stream = fib_local
  /\ field_value FMetaL4proto env_stream pkt_stream = l4_tcp
  /\ field_value FThDport env_stream pkt_stream = port48010.
Proof. repeat split; vm_compute; reflexivity. Qed.

Example witness_flow :
  read_payload_ok PTransport 2 2 pkt_stream = true
  /\ pkt_ctdir_orig pkt_stream = true
  /\ e_nat env_stream (pkt_flow pkt_stream) = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** The repaired heads, INSTANTIATED on the witness — non-vacuity of each. *)
Theorem streaming_io_witnessed :
  eval_chain Hprerouting filter_prerouting env_stream pkt_stream
    = (Accept,
       apply_nat Hprerouting pre2 env_stream (set_meta pkt_stream MKmark mark99)).
Proof.
  destruct witness_sets as (Hs0 & Hs1 & Hs2).
  destruct witness_fields as (Hiif & Hfib & Hl4 & Hdport).
  destruct witness_flow as (Hok & _ & _).
  exact (streaming_prerouting_io_real env_stream pkt_stream
           Hs0 Hs1 Hs2 Hiif Hfib Hl4 Hdport Hok).
Qed.

Theorem streaming_whole_ruleset_witnessed :
  let q := snd (snd (eval_chain Hprerouting filter_prerouting
                       env_stream pkt_stream)) in
  let e' := fst (snd (eval_chain Hprerouting filter_prerouting
                        env_stream pkt_stream)) in
  fst (eval_chain Hprerouting filter_prerouting env_stream pkt_stream) = Accept
  /\ field_value FMetaMark e' q = mark99
  /\ body_step (r_body post1) e' q = BRdone e' q
  (* concrete: the exit interface HAS an address, so the masquerade fires and
     the postrouting verdict is a genuine Accept (no NAT drop) *)
  /\ eval_chain_flat_verdict Hpostrouting filter_postrouting e' q = Accept.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(** And a raw evaluator pin, independent of the theorems: the mark on the
    packet that actually leaves prerouting IS 0x99 (vm_compute end to end). *)
Example streaming_mark_pin :
  field_value FMetaMark env_stream
    (snd (snd (eval_chain Hprerouting filter_prerouting
                 env_stream pkt_stream))) = mark99.
Proof. vm_compute. reflexivity. Qed.
