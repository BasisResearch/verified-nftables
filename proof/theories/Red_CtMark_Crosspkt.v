(** Conntrack `ct mark set` PERSISTS across packets of a flow (kernel-faithful).

    Kernel truth (net/netfilter/nft_ct.c:288-299): nft_ct_set_eval does
    `ct = nf_ct_get(skb,&ctinfo); ... WRITE_ONCE(ct->mark, value)`, i.e. it writes
    the mark into the SHARED conntrack entry, which every later packet of the same
    flow reads back via nft_ct_get_eval (`ct = nf_ct_get(skb,&ctinfo); ...
    *dest = READ_ONCE(ct->mark)`).  So `ct mark set 0x1` on packet 1 IS observable
    as `ct mark == 0x1` on packet 2 of the same flow.

    This file used to be the RED audit probe demonstrating the OPPOSITE (the model
    treated conntrack as a per-packet oracle, so the write left no cross-packet
    trace).  The BLUE fix made the writable+persistent conntrack keys ([ct_writable]:
    mark/label) part of the SHARED, flow-keyed env table [e_ct]: [set_ct] now writes
    [e_ct (pkt_flow p) CKmark] and [do_load (LCt CKmark)] reads it back, so
    [eval_chain_mut_env]/[set_env] (which already thread [pkt_env]) carry the mark
    to the next packet.  The three theorems below are the kernel-CORRECT facts the
    fix makes provable; the old (kernel-false) `..._leaves_env_unchanged` /
    `packet2_ignores_packet1_ctmark_set` are now UNPROVABLE, as they should be.

    SECOND KERNEL GUARD (nft_ct.c:288-290): nft_ct_set_eval FIRST does
    `ct = nf_ct_get(skb, &ctinfo); if (ct == NULL || ...) return;` — so the WRITE is a
    NO-OP when the packet has NO conntrack entry.  [set_ct] gates on [pkt_ct_present];
    the persistence theorems below therefore carry the hypothesis
    [pkt_ct_present p1 = true] (an entry-present packet, the only case the kernel
    writes), and [ctmark_set_no_entry_is_noop] proves the dual: an entryless packet's
    `ct mark set` leaves [e_ct] unchanged, so a later same-flow read sees the original
    mark, not a bogus value. *)

From Stdlib Require Import List NArith String.
From Nft Require Import Bytes Verdict Packet Syntax Semantics.
Import ListNotations.

(* A chain with a single rule: `ct mark set 0x1; accept`. *)
Definition ctmark_set_rule : rule :=
  {| r_body := [ BStmt (SCtSet CKmark (VImm [1])) ];
     r_verdict := Accept;
     r_vmap := None; r_nat := None; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.

Definition ctmark_chain : chain :=
  {| c_policy := Drop; c_rules := [ ctmark_set_rule ] |}.

(* KERNEL-CORRECT (now provable): after packet 1 runs `ct mark set 0x1`, the
   threaded env records mark 0x1 in the SHARED conntrack table at packet 1's flow.
   (Before the fix this was [pkt_env p1] verbatim — no trace.) *)
Theorem ctmark_set_persists_in_env :
  forall p1 : packet,
    pkt_ct_present p1 = true ->
    let e1 := snd (eval_chain_mut_env ctmark_chain p1) in
    e_ct e1 (pkt_flow p1) CKmark = [1].
Proof.
  intros p1 Hpres. cbn. unfold set_ct. rewrite Hpres. cbn.
  rewrite data_eqb_refl. reflexivity.
Qed.

(* Therefore packet 2 of the SAME flow ([pkt_flow p2 = pkt_flow p1]), threaded
   through that env the way seq_eval feeds it, reads the mark 0x1 that packet 1
   set — REGARDLESS of packet 2's own per-packet ct oracle.  This is exactly the
   kernel's nf_ct_get(skb) selecting the shared entry by tuple and reading ct->mark. *)
Theorem packet2_sees_packet1_ctmark_set :
  forall (p1 p2 : packet),
    pkt_ct_present p1 = true ->
    pkt_flow p2 = pkt_flow p1 ->
    let e1 := snd (eval_chain_mut_env ctmark_chain p1) in
    field_value FCtMark (set_env p2 e1) = [1].
Proof.
  intros p1 p2 Hpres Hflow. cbn - [eval_chain_mut_env].
  unfold field_value, do_load. cbn. unfold set_ct. rewrite Hpres. cbn.
  rewrite Hflow. rewrite data_eqb_refl. reflexivity.
Qed.

(* And the mark packet 1 set OVERRIDES packet 2's own (arbitrary) oracle: even if
   packet 2's per-packet ct mark were 0x9, a same-flow packet 2 reads 0x1 (the flow
   mark), not 0x9 — the cross-packet conntrack-mark firewall the per-packet oracle
   could not express. *)
Theorem flow_mark_overrides_packet2_oracle :
  forall (p1 p2 : packet),
    pkt_ct_present p1 = true ->
    pkt_flow p2 = pkt_flow p1 ->
    pkt_ct p2 CKmark = [9] ->
    let e1 := snd (eval_chain_mut_env ctmark_chain p1) in
    field_value FCtMark (set_env p2 e1) = [1] /\
    field_value FCtMark (set_env p2 e1) <> [9].
Proof.
  intros p1 p2 Hpres Hflow _. split.
  - apply (packet2_sees_packet1_ctmark_set p1 p2 Hpres Hflow).
  - rewrite (packet2_sees_packet1_ctmark_set p1 p2 Hpres Hflow). discriminate.
Qed.

(* A DIFFERENT flow does NOT see packet 1's mark: a packet 2 on another flow reads
   its own conntrack entry (here the env's default [e_ct] for that flow), so the
   persistence is correctly flow-SCOPED, not global.  This rules out the dual
   over-approximation (every packet inheriting every mark). *)
Theorem other_flow_unaffected :
  forall (p1 p2 : packet),
    pkt_ct_present p1 = true ->
    pkt_flow p2 <> pkt_flow p1 ->
    let e1 := snd (eval_chain_mut_env ctmark_chain p1) in
    field_value FCtMark (set_env p2 e1) = e_ct (pkt_env p1) (pkt_flow p2) CKmark.
Proof.
  intros p1 p2 Hpres Hflow. cbn - [eval_chain_mut_env].
  unfold field_value, do_load. cbn. unfold set_ct. rewrite Hpres. cbn.
  destruct (data_eqb (pkt_flow p1) (pkt_flow p2)) eqn:Heq.
  - apply data_eqb_true_iff in Heq. symmetry in Heq. contradiction.
  - reflexivity.
Qed.

(* SECOND KERNEL GUARD — the actual Round-4 fix demonstration.  On a packet with NO
   conntrack entry ([pkt_ct_present = false]), nft_ct_set_eval returns immediately
   (`if (ct == NULL || ...) return;`), so `ct mark set` is a NO-OP: it must NOT write
   the shared flow table.  Before the fix [set_ct] wrote unconditionally, so a later
   same-flow entry-bearing packet read back a mark the kernel never wrote.  Now: *)

(* (a) running the chain on an ENTRYLESS packet leaves e_ct at its prior value. *)
Theorem ctmark_set_no_entry_is_noop :
  forall p1 : packet,
    pkt_ct_present p1 = false ->
    let e1 := snd (eval_chain_mut_env ctmark_chain p1) in
    e_ct e1 (pkt_flow p1) CKmark = e_ct (pkt_env p1) (pkt_flow p1) CKmark.
Proof.
  intros p1 Hpres. cbn. unfold set_ct. rewrite Hpres. cbn. reflexivity.
Qed.

(* (b) therefore a later same-flow ENTRY-PRESENT packet 2, threaded through the env
   packet 1 left, reads ITS OWN entry's mark (the env default for that flow), NOT a
   bogus [1] — exactly the kernel no-op behavior.  Here the env's e_ct default for the
   flow is [], so the read is [] (not [1]); the verdict-level upshot is that a later
   `ct mark 0x1 accept` does NOT spuriously match. *)
Theorem no_entry_set_invisible_to_packet2 :
  forall (p1 p2 : packet),
    pkt_ct_present p1 = false ->
    pkt_flow p2 = pkt_flow p1 ->
    let e1 := snd (eval_chain_mut_env ctmark_chain p1) in
    field_value FCtMark (set_env p2 e1) = e_ct (pkt_env p1) (pkt_flow p1) CKmark.
Proof.
  intros p1 p2 Hpres Hflow. cbn - [eval_chain_mut_env].
  unfold field_value, do_load. cbn. unfold set_ct. rewrite Hpres. cbn.
  rewrite Hflow. reflexivity.
Qed.
