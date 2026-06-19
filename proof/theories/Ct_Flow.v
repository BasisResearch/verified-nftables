(** Conntrack state is FLOW-KEYED, not a free per-packet oracle (kernel-faithful).

    ── The infidelity this file closes ───────────────────────────────────────────
    Before this fix, [do_load (LCt CKstate) p] read [pkt_ct p CKstate], a FREE field
    of [packet] with no flow history: a single fabricated packet could report
    ESTABLISHED with no prior packet ever establishing the flow, so a stateful
    firewall property ("an unsolicited inbound packet is NEW, not ESTABLISHED") was
    not even stateable, and the unsound dual ("a fabricated packet matches
    `ct state established`") was trivially inhabited.

    ── Kernel truth (net/netfilter/nft_ct.c:65-76) ────────────────────────────────
        ct = nf_ct_get(pkt->skb, &ctinfo);          // select the FLOW's entry
        ...
        case NFT_CT_STATE:
            if (ct)      state = NF_CT_STATE_BIT(ctinfo);   // from the flow entry
            else if (ctinfo == IP_CT_UNTRACKED)
                         state = NF_CT_STATE_UNTRACKED_BIT;
            else         state = NF_CT_STATE_INVALID_BIT;
            *dest = state;
    The state is derived from the conntrack ENTRY selected by the skb's tuple, so it
    is a function of the FLOW (and accumulated flow history), not of the individual
    skb.

    ── Model (fixed) ──────────────────────────────────────────────────────────────
    [do_load (LCt CKstate) p] now reads [e_ct (pkt_env p) (pkt_flow p) CKstate] (the
    SHARED, flow-keyed conntrack table), with the per-traversal [pkt_untracked]
    override unchanged.  Every read-only ct key is likewise a function of the flow
    table.  Consequences proven below:
      - the value depends ONLY on the flow's table entry, not a free per-packet field
        ([ct_state_flow_keyed]);
      - two packets of the SAME flow read CONSISTENT ct state ([same_flow_same_state]);
      - under the well-formedness invariant "the flow's entry is NEW"
        ([flow_is_new]), a `ct state established accept` rule does NOT accept — so the
        unsoundness (fabricated packet matches established with no history) is GONE
        ([new_flow_not_established], [unsolicited_new_packet_dropped]). *)

From Stdlib Require Import List Bool.
From Nft Require Import Bytes Packet Verdict Syntax Semantics.
Import ListNotations.

(* NF_CT_STATE bitmask values the parser lowers `ct state X` to (cf. Ct_State.v):
   new = 1<<3 = 8, established = 1<<1 = 2 (big-endian 4-byte). *)
Definition st_new   : data := [0;0;0;8].
Definition st_estab : data := [0;0;0;2].

(* The single-positive bitmask matchcond for `ct state established`. *)
Definition m_estab : matchcond := MMasked FCtState true st_estab [0;0;0;0] [0;0;0;0].

(** ── 1. ct state is now a FUNCTION OF THE FLOW TABLE, not a free per-packet field.

    Two packets that agree on (the conntrack table component of) their env, their
    flow id, and their untracked flag read the SAME ct state — regardless of any
    other per-packet difference.  This is what "flow-keyed, not a per-packet oracle"
    means: there is no longer a free [pkt_ct] field through which the value enters. *)
Theorem ct_state_flow_keyed :
  forall p q : packet,
    e_ct (pkt_env p) = e_ct (pkt_env q) ->
    pkt_flow p = pkt_flow q ->
    pkt_untracked p = pkt_untracked q ->
    do_load (LCt CKstate) p = do_load (LCt CKstate) q.
Proof.
  intros p q Hct Hflow Hunt. unfold do_load. cbn.
  rewrite Hunt, Hflow, Hct. reflexivity.
Qed.

(* The same holds for every other read-only ct key (expiration/counters/zone/...)
   EXCEPT [CKdirection], which is NOT flow-keyed: it is the per-packet
   CTINFO2DIR(ctinfo) bit, modelled by [pkt_ctdir_orig] (see [ct_direction_is_ctdir]
   below).  So two packets that additionally agree on [pkt_ctdir_orig] read the same
   value for EVERY key, direction included. *)
Theorem ct_key_flow_keyed :
  forall (k : ct_key) (p q : packet),
    e_ct (pkt_env p) = e_ct (pkt_env q) ->
    pkt_flow p = pkt_flow q ->
    pkt_untracked p = pkt_untracked q ->
    pkt_ctdir_orig p = pkt_ctdir_orig q ->
    do_load (LCt k) p = do_load (LCt k) q.
Proof.
  intros k p q Hct Hflow Hunt Hdir. unfold do_load. cbn.
  destruct k; rewrite ?Hunt, ?Hdir, ?Hflow, ?Hct; reflexivity.
Qed.

(** ── ct DIRECTION is the SAME value as the NAT manip direction (kernel CTINFO2DIR).

    In the kernel both the `ct direction` SELECTOR (nft_ct.c:86) and the NAT manip
    decision (nf_nat_core.c:872) are [CTINFO2DIR(ctinfo)] of the one skb, so they are
    GUARANTEED EQUAL.  This model represents that single value by [pkt_ctdir_orig],
    and [do_load (LCt CKdirection)] now DERIVES from it (Syntax.v), so the selector
    and [apply_nat]'s forward/reply decision can never disagree.

    Encoding (kernel nft_reg_store8, a single byte): IP_CT_DIR_ORIGINAL = 0 -> [0],
    IP_CT_DIR_REPLY = 1 -> [1]. *)
Definition ip_ct_dir_original : data := [0].
Definition ip_ct_dir_reply    : data := [1].

(* The selector reads ORIGINAL iff the packet is the NAT forward (original) direction. *)
Theorem ct_direction_matches_nat_dir :
  forall p,
    pkt_ctdir_orig p = true <-> do_load (LCt CKdirection) p = ip_ct_dir_original.
Proof.
  intro p. unfold do_load, ip_ct_dir_original. cbn.
  destruct (pkt_ctdir_orig p); split; intro H; congruence.
Qed.

(* Dually for the reply direction. *)
Theorem ct_direction_matches_nat_dir_reply :
  forall p,
    pkt_ctdir_orig p = false <-> do_load (LCt CKdirection) p = ip_ct_dir_reply.
Proof.
  intro p. unfold do_load, ip_ct_dir_reply. cbn.
  destruct (pkt_ctdir_orig p); split; intro H; congruence.
Qed.

(* THE REFUTATION of the red infidelity: a packet can NO LONGER be both NAT-reply
   ([pkt_ctdir_orig = false]) and read `ct direction original` ([0]).  The state the
   red probe constructed (pkt_ctdir_orig=false, e_ct ... CKdirection=[0]) is now
   impossible, because the selector ignores [e_ct] and reads [1] (reply) whenever the
   NAT layer treats the packet as reply.  The two are ONE source of truth. *)
Theorem ctdir_selector_agrees_with_nat :
  forall p,
    (pkt_ctdir_orig p = false -> do_load (LCt CKdirection) p <> ip_ct_dir_original)
    /\ (pkt_ctdir_orig p = true  -> do_load (LCt CKdirection) p <> ip_ct_dir_reply).
Proof.
  intro p. unfold do_load, ip_ct_dir_original, ip_ct_dir_reply. cbn.
  split; intro H; rewrite H; discriminate.
Qed.

(** ── 2. Two TRACKED packets of the SAME flow read CONSISTENT ct state. *)
Theorem same_flow_same_state :
  forall p q : packet,
    e_ct (pkt_env p) = e_ct (pkt_env q) ->
    pkt_flow p = pkt_flow q ->
    pkt_untracked p = false ->
    pkt_untracked q = false ->
    do_load (LCt CKstate) p = do_load (LCt CKstate) q.
Proof.
  intros p q Hct Hflow Hp Hq.
  apply ct_state_flow_keyed; [exact Hct | exact Hflow | rewrite Hp, Hq; reflexivity].
Qed.

(** ── 3. Well-formedness: a flow whose conntrack entry is NEW.

    [flow_is_new p] says the conntrack table records state NEW for THIS packet's
    flow.  This is the invariant the kernel maintains for the FIRST packet of a flow
    (no prior packet -> entry just created -> NF_CT_STATE_BIT(IP_CT_NEW): only the
    new bit set).  It is now EXPRESSIBLE because the state lives in the flow table. *)
Definition flow_is_new (p : packet) : Prop :=
  pkt_untracked p = false /\ e_ct (pkt_env p) (pkt_flow p) CKstate = st_new.

(* Under [flow_is_new], reading `ct state` (= [field_value FCtState]) yields NEW. *)
Lemma flow_is_new_reads_new :
  forall p, flow_is_new p -> field_value FCtState p = st_new.
Proof.
  intros p [Hunt Hentry]. unfold field_value, field_load, do_load. cbn.
  rewrite Hunt. exact Hentry.
Qed.

(* THE KEY SOUNDNESS FACT: a NEW-flow packet does NOT match `ct state established`.
   The established bit (2) is clear in NEW (8), so (8 & 2) = 0.  Before the fix this
   was unprovable — a fabricated packet could set its per-packet [pkt_ct CKstate] to
   anything, including established. *)
Theorem new_flow_not_established :
  forall p, flow_is_new p -> eval_matchcond m_estab p = false.
Proof.
  intros p Hnew. unfold m_estab, eval_matchcond, eval_matchcond_body, match_loadable.
  rewrite (flow_is_new_reads_new p Hnew).
  vm_compute. reflexivity.
Qed.

(** ── 4. A stateful firewall: `ct state established accept`, default Drop.

    On a NEW-flow (unsolicited inbound) packet this DROPS — the property that was
    not even stateable when ct state was a free oracle. *)
Definition estab_accept_rule : rule :=
  {| r_body := [ BMatch m_estab ];
     r_verdict := Accept; r_vmap := None; r_nat := None; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.

Definition stateful_chain : chain :=
  {| c_policy := Drop; c_rules := [ estab_accept_rule ] |}.

Theorem unsolicited_new_packet_dropped :
  forall p, flow_is_new p -> eval_chain_mut stateful_chain p = Drop.
Proof.
  intros p Hnew. unfold eval_chain_mut, stateful_chain. cbn [c_rules].
  (* the single rule's match fails on a NEW flow, so policy Drop stands. *)
  unfold estab_accept_rule.
  cbn [c_policy].
  (* reduce eval_rules_mut over the one rule *)
  cbn - [eval_matchcond].
  rewrite (new_flow_not_established p Hnew). reflexivity.
Qed.

(* Conversely, an ESTABLISHED-flow packet (a flow a prior packet established) IS
   accepted — the rule is not vacuous. *)
Definition flow_is_established (p : packet) : Prop :=
  pkt_untracked p = false /\ e_ct (pkt_env p) (pkt_flow p) CKstate = st_estab.

Theorem established_flow_accepted :
  forall p, flow_is_established p -> eval_chain_mut stateful_chain p = Accept.
Proof.
  intros p [Hunt Hentry]. unfold eval_chain_mut, stateful_chain. cbn [c_rules].
  unfold estab_accept_rule. cbn [c_policy]. cbn - [eval_matchcond].
  unfold m_estab, eval_matchcond, field_value.
  unfold do_load. cbn. rewrite Hunt, Hentry. vm_compute. reflexivity.
Qed.
