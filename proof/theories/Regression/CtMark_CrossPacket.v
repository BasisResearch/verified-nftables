(** Conntrack `ct mark set` PERSISTS across packets of a flow (kernel-faithful).

    Kernel truth (net/netfilter/nft_ct.c:288-299): nft_ct_set_eval does
    `ct = nf_ct_get(skb,&ctinfo); ... WRITE_ONCE(ct->mark, value)`, i.e. it writes
    the mark into the SHARED conntrack entry, which every later packet of the same
    flow reads back via nft_ct_get_eval (`ct = nf_ct_get(skb,&ctinfo); ...
    *dest = READ_ONCE(ct->mark)`).  So `ct mark set 0x1` on packet 1 IS observable
    as `ct mark == 0x1` on packet 2 of the same flow.

    In the model the writable+persistent conntrack keys ([ct_writable]: mark/label)
    live in the SHARED, flow-keyed env table [e_ct]: [set_ct] writes
    [e_ct (pkt_flow p) CKmark] and [do_load (LCt CKmark)] reads it back, so
    [eval_chain_mut_env h] (which RETURNS the env the traversal leaves) carries the
    mark to the next packet of the flow.

    Regression gate: [ctmark_set_persists_in_env], [packet2_sees_packet1_ctmark_set],
    and [ctmark_set_no_entry_is_noop] lock in flow-keyed persistence; a model
    regression to a per-packet conntrack oracle (a `ct mark set` leaving no
    cross-packet trace) makes them unprovable.

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

(* Pins below hold at EVERY netfilter hook [h] (no rule here carries a NAT
   terminal, so the hook is inert); the section generalizes each statement. *)
Section AtHook.
Context (h : hook_id).

(* A chain with a single rule: `ct mark set 0x1; accept`. *)
Definition ctmark_set_rule : rule :=
  {| r_body := [ BStmt (SCtSet CKmark (VImm [1])) ];
     r_outcome := OVerdict Accept; r_after := [] |}.

Definition ctmark_chain : chain :=
  {| c_policy := Drop; c_rules := [ ctmark_set_rule ] |}.

(* After packet 1 runs `ct mark set 0x1`, the threaded env records mark 0x1 in the
   SHARED conntrack table at packet 1's flow — the write leaves a cross-packet
   trace, as nft_ct_set_eval's WRITE_ONCE(ct->mark, value) does. *)
Theorem ctmark_set_persists_in_env :
  forall (e : env) (p1 : packet),
    pkt_ct_present p1 = true ->
    let e1 := snd (eval_chain_mut_env h ctmark_chain e p1) in
    e_ct e1 (pkt_flow p1) CKmark = [1].
Proof.
  intros e p1 Hpres. cbn. unfold set_ct. rewrite Hpres. cbn.
  rewrite data_eqb_refl. reflexivity.
Qed.

(* Therefore packet 2 of the SAME flow ([pkt_flow p2 = pkt_flow p1]), threaded
   through that env the way seq_eval feeds it, reads the mark 0x1 that packet 1
   set — REGARDLESS of packet 2's own per-packet ct oracle.  This is exactly the
   kernel's nf_ct_get(skb) selecting the shared entry by tuple and reading ct->mark. *)
Theorem packet2_sees_packet1_ctmark_set :
  forall (e : env) (p1 p2 : packet),
    pkt_ct_present p1 = true ->
    pkt_flow p2 = pkt_flow p1 ->
    let e1 := snd (eval_chain_mut_env h ctmark_chain e p1) in
    field_value FCtMark e1 p2 = [1;0;0;0].
Proof.
  intros e p1 p2 Hpres Hflow. cbn - [eval_chain_mut_env].
  unfold field_value, do_load, ct_load. cbn. unfold set_ct. rewrite Hpres. cbn.
  rewrite Hflow. rewrite data_eqb_refl. reflexivity.
Qed.

(* The mark a same-flow packet 2 reads is DETERMINED by the flow table alone:
   nothing per-packet about p2 (beyond its flow id) can change the read.  The
   conntrack mark is a function of the FLOW, so packet 2 reads 0x1 — never some
   other per-packet value such as 0x9. *)
Theorem flow_mark_overrides_packet2_oracle :
  forall (e : env) (p1 p2 : packet),
    pkt_ct_present p1 = true ->
    pkt_flow p2 = pkt_flow p1 ->
    let e1 := snd (eval_chain_mut_env h ctmark_chain e p1) in
    field_value FCtMark e1 p2 = [1;0;0;0] /\
    field_value FCtMark e1 p2 <> [9].
Proof.
  intros e p1 p2 Hpres Hflow. split.
  - apply (packet2_sees_packet1_ctmark_set e p1 p2 Hpres Hflow).
  - rewrite (packet2_sees_packet1_ctmark_set e p1 p2 Hpres Hflow). discriminate.
Qed.

(* A DIFFERENT flow does NOT see packet 1's mark: a packet 2 on another flow reads
   its own conntrack entry (here the env's default [e_ct] for that flow), so the
   persistence is correctly flow-SCOPED, not global.  This rules out the dual
   over-approximation (every packet inheriting every mark). *)
Theorem other_flow_unaffected :
  forall (e : env) (p1 p2 : packet),
    pkt_ct_present p1 = true ->
    pkt_flow p2 <> pkt_flow p1 ->
    let e1 := snd (eval_chain_mut_env h ctmark_chain e p1) in
    field_value FCtMark e1 p2 = ct_load CKmark (e_ct e (pkt_flow p2) CKmark).
Proof.
  intros e p1 p2 Hpres Hflow. cbn - [eval_chain_mut_env].
  unfold field_value, do_load. cbn. unfold set_ct. rewrite Hpres. cbn.
  destruct (data_eqb (pkt_flow p1) (pkt_flow p2)) eqn:Heq.
  - apply data_eqb_true_iff in Heq. symmetry in Heq. contradiction.
  - reflexivity.
Qed.

(* SECOND KERNEL GUARD.  On a packet with NO conntrack entry
   ([pkt_ct_present = false]), nft_ct_set_eval returns immediately
   (`if (ct == NULL || ...) return;`, nft_ct.c:288-290), so `ct mark set` is a
   NO-OP: it must NOT write the shared flow table.  [set_ct] gates on
   [pkt_ct_present]; an unconditional write would let a later same-flow
   entry-bearing packet read back a mark the kernel never wrote. *)

(* (a) running the chain on an ENTRYLESS packet leaves e_ct at its prior value. *)
Theorem ctmark_set_no_entry_is_noop :
  forall (e : env) (p1 : packet),
    pkt_ct_present p1 = false ->
    let e1 := snd (eval_chain_mut_env h ctmark_chain e p1) in
    e_ct e1 (pkt_flow p1) CKmark = e_ct e (pkt_flow p1) CKmark.
Proof.
  intros e p1 Hpres. cbn. unfold set_ct. rewrite Hpres. cbn. reflexivity.
Qed.

(* (b) therefore a later same-flow ENTRY-PRESENT packet 2, threaded through the env
   packet 1 left, reads ITS OWN entry's mark (the env default for that flow), NOT a
   bogus [1] — exactly the kernel no-op behavior.  Here the env's e_ct default for the
   flow is [], so the read is [] (not [1]); the verdict-level upshot is that a later
   `ct mark 0x1 accept` does NOT spuriously match. *)
Theorem no_entry_set_invisible_to_packet2 :
  forall (e : env) (p1 p2 : packet),
    pkt_ct_present p1 = false ->
    pkt_flow p2 = pkt_flow p1 ->
    let e1 := snd (eval_chain_mut_env h ctmark_chain e p1) in
    field_value FCtMark e1 p2 = ct_load CKmark (e_ct e (pkt_flow p1) CKmark).
Proof.
  intros e p1 p2 Hpres Hflow. cbn - [eval_chain_mut_env].
  unfold field_value, do_load. cbn. unfold set_ct. rewrite Hpres. cbn.
  rewrite Hflow. reflexivity.
Qed.

End AtHook.
