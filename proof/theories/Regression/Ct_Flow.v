(** Conntrack state is FLOW-KEYED, not a free per-packet oracle (kernel-faithful).

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

    ── Model ──────────────────────────────────────────────────────────────────────
    [do_load (LCt CKstate) e p] reads [e_ct e (pkt_flow p) CKstate] (the
    SHARED, flow-keyed conntrack table, passed explicitly), with the
    per-traversal [pkt_untracked] override.  Every read-only ct key is likewise a function of the flow table.
    Consequences proven below:
      - the value depends ONLY on the flow's table entry, not a free per-packet field
        ([ct_state_flow_keyed]);
      - two packets of the SAME flow read CONSISTENT ct state ([same_flow_same_state]);
      - under the well-formedness invariant "the flow's entry is NEW"
        ([flow_is_new]), a `ct state established accept` rule does NOT accept
        ([new_flow_not_established], [unsolicited_new_packet_dropped]).

    Regression gate: those four theorems lock in flow-keying; a model where ct state
    is a free per-packet field (a single fabricated packet reporting ESTABLISHED
    with no prior packet ever establishing the flow) makes them unprovable. *)

From Stdlib Require Import List Bool.
From Nft Require Import Bytes Packet Verdict Bytecode Syntax Semantics.
Import ListNotations.

(* Pins below hold at EVERY netfilter hook [h] (no rule here carries a NAT
   terminal, so the hook is inert); the section generalizes each statement. *)
Section AtHook.
Context (h : hook_id).

(* NF_CT_STATE bitmask values the parser lowers `ct state X` to (cf. Ct_State.v):
   new = 1<<3 = 8, established = 1<<1 = 2 (big-endian 4-byte). *)
Definition st_new   : data := [0;0;0;8].
Definition st_estab : data := [0;0;0;2].

(* The single-positive bitmask matchcond for `ct state established`. *)
Definition m_estab : matchcond := MMasked FCtState CNe st_estab [0;0;0;0] [0;0;0;0].

(** ── 1. ct state is a FUNCTION OF THE FLOW TABLE, not a free per-packet field.

    Two packets that agree on (the conntrack table component of) their env, their
    flow id, and their untracked flag read the SAME ct state — regardless of any
    other per-packet difference.  This is what "flow-keyed, not a per-packet oracle"
    means: no free per-packet field lets a value enter the read. *)
Theorem ct_state_flow_keyed :
  forall (e : env) (p q : packet),
    pkt_flow p = pkt_flow q ->
    pkt_untracked p = pkt_untracked q ->
    pkt_ct_present p = pkt_ct_present q ->
    do_load (LCt CKstate) e p = do_load (LCt CKstate) e q.
Proof.
  intros e p q Hflow Hunt Hpres. unfold do_load. cbn.
  rewrite Hunt, Hpres, Hflow. reflexivity.
Qed.

(* The same holds for every other read-only ct key (expiration/counters/zone/...)
   EXCEPT [CKdirection], which is NOT flow-keyed: it is the per-packet
   CTINFO2DIR(ctinfo) bit, modelled by [pkt_ctdir_orig] (see [ct_direction_is_ctdir]
   below).  So two packets that additionally agree on [pkt_ctdir_orig] read the same
   value for EVERY key, direction included. *)
Theorem ct_key_flow_keyed :
  forall (k : ct_key) (e : env) (p q : packet),
    pkt_flow p = pkt_flow q ->
    pkt_untracked p = pkt_untracked q ->
    pkt_ct_present p = pkt_ct_present q ->
    pkt_ctdir_orig p = pkt_ctdir_orig q ->
    do_load (LCt k) e p = do_load (LCt k) e q.
Proof.
  intros k e p q Hflow Hunt Hpres Hdir. unfold do_load. cbn.
  destruct k; rewrite ?Hunt, ?Hpres, ?Hdir, ?Hflow; reflexivity.
Qed.

(** ── ct DIRECTION is the SAME value as the NAT manip direction (kernel CTINFO2DIR).

    In the kernel both the `ct direction` SELECTOR (nft_ct.c:86) and the NAT manip
    decision (nf_nat_core.c:872) are [CTINFO2DIR(ctinfo)] of the one skb, so they are
    GUARANTEED EQUAL.  This model represents that single value by [pkt_ctdir_orig],
    and [do_load (LCt CKdirection)] DERIVES from it (Syntax.v), so the selector
    and [apply_nat]'s forward/reply decision can never disagree.

    Encoding (kernel nft_reg_store8, a single byte): IP_CT_DIR_ORIGINAL = 0 -> [0],
    IP_CT_DIR_REPLY = 1 -> [1]. *)
Definition ip_ct_dir_original : data := [0].
Definition ip_ct_dir_reply    : data := [1].

(* The selector reads ORIGINAL iff the packet is the NAT forward (original) direction. *)
Theorem ct_direction_matches_nat_dir :
  forall e p,
    pkt_ctdir_orig p = true <-> do_load (LCt CKdirection) e p = ip_ct_dir_original.
Proof.
  intros e p. unfold do_load, ct_load, fit, ip_ct_dir_original. cbn.
  destruct (pkt_ctdir_orig p); cbn; split; intro H;
    try reflexivity; discriminate H.
Qed.

(* Dually for the reply direction. *)
Theorem ct_direction_matches_nat_dir_reply :
  forall e p,
    pkt_ctdir_orig p = false <-> do_load (LCt CKdirection) e p = ip_ct_dir_reply.
Proof.
  intros e p. unfold do_load, ct_load, fit, ip_ct_dir_reply. cbn.
  destruct (pkt_ctdir_orig p); cbn; split; intro H;
    try reflexivity; discriminate H.
Qed.

(* Direction consistency: a packet cannot be both NAT-reply
   ([pkt_ctdir_orig = false]) and read `ct direction original` ([0]).  The
   inconsistent state (pkt_ctdir_orig=false with e_ct ... CKdirection=[0]) is
   unobservable, because the selector ignores [e_ct] and reads [1] (reply) whenever
   the NAT layer treats the packet as reply.  The two are ONE source of truth. *)
Theorem ctdir_selector_agrees_with_nat :
  forall e p,
    (pkt_ctdir_orig p = false -> do_load (LCt CKdirection) e p <> ip_ct_dir_original)
    /\ (pkt_ctdir_orig p = true  -> do_load (LCt CKdirection) e p <> ip_ct_dir_reply).
Proof.
  intros e p. unfold do_load, ct_load, fit, ip_ct_dir_original, ip_ct_dir_reply. cbn.
  split; intro H; rewrite H; cbn; discriminate.
Qed.

(** ── 2. Two TRACKED packets of the SAME flow read CONSISTENT ct state. *)
Theorem same_flow_same_state :
  forall (e : env) (p q : packet),
    pkt_flow p = pkt_flow q ->
    pkt_untracked p = false ->
    pkt_untracked q = false ->
    pkt_ct_present p = true ->
    pkt_ct_present q = true ->
    do_load (LCt CKstate) e p = do_load (LCt CKstate) e q.
Proof.
  intros e p q Hflow Hp Hq Hpp Hqp.
  apply ct_state_flow_keyed;
    [exact Hflow | rewrite Hp, Hq; reflexivity | rewrite Hpp, Hqp; reflexivity].
Qed.

(** ── 3. Well-formedness: a flow whose conntrack entry is NEW.

    [flow_is_new p] says the conntrack table records state NEW for THIS packet's
    flow.  This is the invariant the kernel maintains for the FIRST packet of a flow
    (no prior packet -> entry just created -> NF_CT_STATE_BIT(IP_CT_NEW): only the
    new bit set).  It is EXPRESSIBLE precisely because the state lives in the flow table. *)
Definition flow_is_new (e : env) (p : packet) : Prop :=
  pkt_untracked p = false /\ pkt_ct_present p = true
  /\ e_ct e (pkt_flow p) CKstate = st_new.

(* Under [flow_is_new], reading `ct state` (= [field_value FCtState]) yields NEW. *)
Lemma flow_is_new_reads_new :
  forall e p, flow_is_new e p -> field_value FCtState e p = st_new.
Proof.
  intros e p [Hunt [Hpres Hentry]]. unfold field_value, field_load, do_load. cbn.
  rewrite Hunt, Hpres, Hentry. reflexivity.
Qed.

(* THE KEY SOUNDNESS FACT: a NEW-flow packet does NOT match `ct state established`.
   The established bit (2) is clear in NEW (8), so (8 & 2) = 0.  This is provable
   only because ct state is flow-keyed ([e_ct] at [pkt_flow]): a free per-packet
   ct-state value could report anything, including established. *)
Theorem new_flow_not_established :
  forall e p, flow_is_new e p -> eval_matchcond m_estab e p = false.
Proof.
  intros e p Hnew. unfold m_estab, eval_matchcond, eval_matchcond_body, match_loadable.
  rewrite (flow_is_new_reads_new e p Hnew).
  vm_compute. reflexivity.
Qed.

(** ── 4. A stateful firewall: `ct state established accept`, default Drop.

    On a NEW-flow (unsolicited inbound) packet this DROPS — the property that was
    not even stateable when ct state was a free oracle. *)
Definition estab_accept_rule : rule :=
  {| r_body := [ BMatch m_estab ];
     r_outcome := OVerdict Accept; r_after := [] |}.

Definition stateful_chain : chain :=
  {| c_policy := Drop; c_rules := [ estab_accept_rule ] |}.

Theorem unsolicited_new_packet_dropped :
  forall e p, flow_is_new e p -> eval_chain_mut h stateful_chain e p = Drop.
Proof.
  intros e p Hnew.
  pose proof (new_flow_not_established e p Hnew) as Hf.
  unfold eval_chain_mut, stateful_chain. cbn [c_rules c_policy eval_rules_mut].
  assert (Hov : fst (rule_step h estab_accept_rule e p) = None).
  { unfold rule_step.
    cbn [estab_accept_rule r_body body_step match_consume]. rewrite Hf. reflexivity. }
  destruct (rule_step h estab_accept_rule e p) as [ov [e' p']].
  cbn [fst] in Hov. subst ov. reflexivity.
Qed.

(* Conversely, an ESTABLISHED-flow packet (a flow a prior packet established) IS
   accepted — the rule is not vacuous. *)
Definition flow_is_established (e : env) (p : packet) : Prop :=
  pkt_untracked p = false /\ pkt_ct_present p = true
  /\ e_ct e (pkt_flow p) CKstate = st_estab.

Theorem established_flow_accepted :
  forall e p, flow_is_established e p -> eval_chain_mut h stateful_chain e p = Accept.
Proof.
  intros e p [Hunt [Hpres Hentry]].
  assert (Hm : eval_matchcond m_estab e p = true).
  { unfold m_estab, eval_matchcond, eval_matchcond_body, match_loadable, field_value, do_load.
    cbn. rewrite Hunt, Hpres, Hentry. vm_compute. reflexivity. }
  unfold eval_chain_mut, stateful_chain. cbn [c_rules c_policy eval_rules_mut].
  assert (Hov : fst (rule_step h estab_accept_rule e p) = Some Accept).
  { unfold rule_step.
    cbn [estab_accept_rule r_body body_step match_consume]. rewrite Hm. reflexivity. }
  destruct (rule_step h estab_accept_rule e p) as [ov [e' p']].
  cbn [fst] in Hov. subst ov. reflexivity.
Qed.

End AtHook.
