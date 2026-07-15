(* ============================================================================
   router.nft postrouting masquerade — DATA-PLANE HOOK BRIDGE (the parser's hook
   registration is load-bearing for NAT).

   THE GAP this file closes (the postrouting half of the chain<->hook bridge,
   for the DATA PLANE):

   [Router_Hooks] lifts the VERDICT-bearing input/forward security theorems to the
   hook level via [eval_hook hk_fuel global_hooks H...], so a wrong-hook swap of
   those chains is observable.  But the masquerade NAT — the entire security reason
   the postrouting chain exists, the crux [Router_Reach] proves — is not, by
   itself, connected to the parser's registration [global_hooks].  Every masquerade
   theorem in Router_Reach.v is stated as

       chain_out Hpostrouting global_postrouting p     (Hpostrouting hand-supplied,
                                                         global_postrouting hand-named)

   and [eval_hook]/[eval_ruleset] are VERDICT-ONLY (they thread no packet), so the
   model could not even *express* "the masquerade chain is the one netfilter runs at
   postrouting".  Consequently a planted bug that registers masquerade at the WRONG
   hook, or drops its postrouting registration entirely, leaks every internal
   192.168.0.0/16 source address un-NATted to the WAN yet satisfies every proven NAT
   property verbatim ([select_postrouting] in Router_Hooks.v is a DEAD lemma — no NAT
   theorem uses it).

   THE FIX: a DATA-PLANE hook evaluator [chain_out_at_hook] that DERIVES the hook_id
   and the base chain from the PARSED registration [rs] and threads the PACKET (not
   just a verdict) through it — selecting the base chain(s) registered at [h] and
   running [eval_chain_trace h base] with THAT [h] as the [apply_nat] hook.  Then:

     - [postrouting_hook_masquerades] : the masquerade crux proven THROUGH
       [global_hooks Hpostrouting] (no hand-supplied hook): a private source
       egressing ppp0 on a fresh flow with a usable exit address [wan] has its source
       slot rewritten to [wan].

     - [postrouting_hook_no_leak] : the dual — a non-private source OR a non-ppp0
       egress is returned source-UNCHANGED through the hook (no leak).

     - [natbug_observable] : a registration that DROPS the postrouting entry
       ([global_hooks_natbug]) dispatches NOTHING at postrouting, so the private
       source LEAKS un-NATted — observably different from the parser's registration on
       a real packet.  This makes [select_postrouting] load-bearing and closes the
       postrouting half of the chain<->hook bridge for the data plane, exactly as
       [input_hook_world_locked] closed it for verdicts.
   ========================================================================== *)

From Stdlib Require Import List String NArith ZArith Lia.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Semantics Router_Gen.
From Nft Require Import Router_Reach Router_Hooks.

Open Scope string_scope.
Local Open Scope bool_scope.

(* ------------------------------------------------------------------ *)
(** ** The data-plane hook evaluator.

    [select_hook rs h] is the (env, base-chain) list netfilter dispatches at hook
    [h], in priority order (Semantics.v).  The VERDICT evaluator [eval_ruleset]
    folds verdicts over it; here we fold the PACKET: each base chain that does not
    terminate-drop passes its OUTPUT packet ([chain_out h base], the data-plane
    trace) to the next, threading NAT rewrites through the hook.  [h] — the hook the
    packet ACTUALLY hits per the parsed registration — is supplied to [chain_out] as
    the [apply_nat] hook_id, so a wrong-hook registration changes which hook drives
    the rewrite. *)
Fixpoint chain_out_bases (h : hook_id)
    (bases : list (list (String.string * chain) * chain)) (p : packet) : packet :=
  match bases with
  | [] => p
  | (_, base) :: rest =>
      let v := fst (eval_chain_trace h base p) in
      let q := snd (eval_chain_trace h base p) in
      if base_continues v then chain_out_bases h rest q else q
  end.

Definition chain_out_at_hook (rs : list hooked_chain) (h : hook_id) (p : packet) : packet :=
  chain_out_bases h (select_hook rs h) p.

(* At a hook with EXACTLY ONE registered base chain [b], the data-plane hook output
   is exactly that base chain's trace output [chain_out h b] — independent of the
   chain's verdict (Accept continues to [] which returns the packet; a terminal
   verdict returns the same packet [q]). *)
Lemma chain_out_at_hook_singleton : forall rs h cs b p,
  select_hook rs h = [(cs, b)] ->
  chain_out_at_hook rs h p = chain_out h b p.
Proof.
  intros rs h cs b p Hsel. unfold chain_out_at_hook, chain_out. rewrite Hsel.
  cbn [chain_out_bases]. destruct (base_continues (fst (eval_chain_trace h b p)));
    cbn [chain_out_bases]; reflexivity.
Qed.

(* The postrouting hook of the PARSER's registration resolves to global_postrouting,
   and its data-plane output is exactly the trace output Router_Reach characterises
   — but now with [Hpostrouting] DERIVED from [select_postrouting], not hand-given. *)
Lemma chain_out_postrouting_hook : forall p,
  chain_out_at_hook global_hooks Hpostrouting p
    = chain_out Hpostrouting global_postrouting p.
Proof.
  intro p. apply (chain_out_at_hook_singleton global_hooks Hpostrouting
                    global_chains global_postrouting p).
  apply select_postrouting.
Qed.

(* ================================================================== *)
(** ** The masquerade crux, proven THROUGH the parser's registration. *)

(* (a) FIRES — a private source (192.168.0.0/16) egressing ppp0, on the first
   (unconfirmed, original-direction) packet of its flow with a usable exit address
   [wan], has its source slot rewritten to [wan] — by whatever chain the PARSER
   registered at the postrouting hook.  No [Hpostrouting] is supplied by hand: it is
   the hook_id the registration binds to global_postrouting. *)
Theorem postrouting_hook_masquerades : forall p wan,
  saddr_private p = true ->
  oif_ppp0 p = true ->
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  e_ifaddr (pkt_env p) (field_value FMetaOifname p) = wan ->
  wan <> [] ->
  16 <= List.length (pkt_nh p) ->
  List.length wan = 4 ->
  saddr4 (chain_out_at_hook global_hooks Hpostrouting p) = wan.
Proof.
  intros p wan Hpriv Hppp Horig Hnone Hwan Hne Hnh Hwl.
  rewrite chain_out_postrouting_hook.
  apply (proj1 (nat_masquerade_fires p wan Hpriv Hppp Horig Hnone Hwan Hne Hnh Hwl)).
Qed.

(* (b) NO-LEAK (the security half) — a packet whose source is NOT private OR whose
   egress is NOT ppp0 is returned source-UNCHANGED through the postrouting hook: no
   internal-address leak.  Also stated for the parser-derived hook. *)
Theorem postrouting_hook_no_leak : forall p,
  (saddr_private p = false \/ oif_ppp0 p = false) ->
  saddr4 (chain_out_at_hook global_hooks Hpostrouting p) = saddr4 p.
Proof.
  intros p Hor. rewrite chain_out_postrouting_hook.
  apply (proj1 (nat_no_leak p Hor)).
Qed.

(* CONFIRMED-FLOW stability through the hook: a later packet of an established masq
   flow is rewritten from the STORED wan ([Router_Reach]'s flow-stability crux),
   here through the parser's hook. *)
Theorem postrouting_hook_confirmed_reuses_stored : forall p oa wan,
  saddr_private p = true ->
  oif_ppp0 p = true ->
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = Some (Some oa, Some wan, None, None) ->
  16 <= List.length (pkt_nh p) ->
  List.length wan = 4 ->
  saddr4 (chain_out_at_hook global_hooks Hpostrouting p) = wan.
Proof.
  intros p oa wan Hpriv Hppp Horig Hsome Hnh Hwl.
  rewrite chain_out_postrouting_hook.
  apply (nat_masq_confirmed_reuses_stored p oa wan Hpriv Hppp Horig Hsome Hnh Hwl).
Qed.

(* ================================================================== *)
(** ** MUTATION KILL: a registration that DROPS the postrouting entry.

    [global_hooks_natbug] keeps input/forward but omits postrouting (the
    "dropped-registration" bug from the gap report).  Then netfilter dispatches
    NOTHING at postrouting — the private source LEAKS un-NATted. *)

Definition global_hooks_natbug : list hooked_chain :=
  [{| hc_hook := Hinput;   hc_prio := (0)%Z; hc_env := global_chains; hc_base := global_inbound |};
   {| hc_hook := Hforward; hc_prio := (0)%Z; hc_env := global_chains; hc_base := global_forward |}].

(* Under the bug, [select_hook] at postrouting is EMPTY (no chain registered). *)
Lemma bug_no_postrouting_chain :
  select_hook global_hooks_natbug Hpostrouting = [].
Proof.
  unfold select_hook, global_hooks_natbug.
  cbn [filter hook_eqb sort_hc insert_hc map hc_hook]. reflexivity.
Qed.

(* Consequently the bugged hook is the IDENTITY on the packet — masquerade never
   runs; the source slot is left as-is (the leak). *)
Lemma bug_postrouting_hook_id : forall p,
  chain_out_at_hook global_hooks_natbug Hpostrouting p = p.
Proof.
  intro p. unfold chain_out_at_hook. rewrite bug_no_postrouting_chain.
  reflexivity.
Qed.

(* On the firing witness [pkt_priv] (private source 192.168.1.5 out ppp0, fresh
   flow, usable WAN), the PARSER's registration source-NATs to the WAN address... *)
Lemma natbug_correct_fires :
  saddr4 (chain_out_at_hook global_hooks Hpostrouting pkt_priv) = wan_addr.
Proof.
  rewrite chain_out_postrouting_hook. exact witness_fires.
Qed.

(* ...while the bugged (postrouting-dropped) registration LEAKS the private source
   192.168.1.5 un-NATted. *)
Lemma natbug_leaks :
  saddr4 (chain_out_at_hook global_hooks_natbug Hpostrouting pkt_priv) = [192;168;1;5].
Proof.
  rewrite bug_postrouting_hook_id. vm_compute. reflexivity.
Qed.

(* THE OBSERVABLE: the parser's registration and the postrouting-dropped one disagree
   on a real packet's SOURCE SLICE — so [postrouting_hook_masquerades] genuinely
   depends on the registration the parser emitted ([select_postrouting] is now
   load-bearing), closing the postrouting half of the chain<->hook bridge. *)
Theorem natbug_observable :
  saddr4 (chain_out_at_hook global_hooks     Hpostrouting pkt_priv)
  <> saddr4 (chain_out_at_hook global_hooks_natbug Hpostrouting pkt_priv).
Proof.
  rewrite natbug_correct_fires, natbug_leaks. discriminate.
Qed.

(* The dual mutation — registering masquerade at the WRONG hook (Hinput) — also
   leaks: postrouting then has no registered chain, identical to the dropped-entry
   bug at the postrouting hook. *)
Definition global_hooks_wronghook : list hooked_chain :=
  [{| hc_hook := Hinput;   hc_prio := (0)%Z;   hc_env := global_chains; hc_base := global_inbound |};
   {| hc_hook := Hforward; hc_prio := (0)%Z;   hc_env := global_chains; hc_base := global_forward |};
   {| hc_hook := Hinput;   hc_prio := (100)%Z; hc_env := global_chains; hc_base := global_postrouting |}].

Lemma wronghook_no_postrouting_chain :
  select_hook global_hooks_wronghook Hpostrouting = [].
Proof.
  unfold select_hook, global_hooks_wronghook.
  cbn [filter hook_eqb sort_hc insert_hc map hc_hook]. reflexivity.
Qed.

Theorem wronghook_observable :
  saddr4 (chain_out_at_hook global_hooks         Hpostrouting pkt_priv)
  <> saddr4 (chain_out_at_hook global_hooks_wronghook Hpostrouting pkt_priv).
Proof.
  rewrite natbug_correct_fires.
  unfold chain_out_at_hook at 1. rewrite wronghook_no_postrouting_chain.
  cbn [chain_out_bases]. unfold wan_addr. vm_compute. discriminate.
Qed.

(* ================================================================== *)
(** ** The NF_NAT_MANIP "no usable WAN address" NF_DROP, at the hook.

    THE GAP (medium / missing-flow): the semantics faithfully models
    nf_nat_masquerade.c:54-58 — when masquerade must take the exit interface's
    address but that address is EMPTY ([e_ifaddr ... = []]), [nat_drops] fires and
    [eval_rules_trace] returns [(Some Drop, dsl_step r p)] — the packet is DROPPED
    *before* the source is spliced.  But NO Router-level theorem pinned this flow:
    [postrouting_hook_masquerades] requires [wan <> []] (EXCLUDES it) and
    [postrouting_hook_no_leak] requires a non-private/non-ppp0 packet (SAYS NOTHING
    about a private source out ppp0).  A private 192.168.0.0/16 source egressing ppp0
    on a fresh original-direction flow with no usable exit address sits in the scope
    of NEITHER theorem: the model drops it (no real leak), but without this section
    the property set would never assert the Drop verdict OR the no-leak — a mutation
    flipping this NF_DROP to a silent accept-and-leave-unrewritten (leaking the
    internal 192.168.x.y un-NATted to the WAN) would satisfy every other NAT theorem
    verbatim.

    THIS SECTION: (i) a VERDICT-bearing hook companion [eval_chain_trace_at_hook] to
    the data-plane [chain_out_at_hook] (so the verdict, not just [saddr4], is lifted
    through the parser's registration), and (ii) the third-case theorem
    [postrouting_hook_noaddr_drops] — at the parser-registered postrouting hook the
    verdict is Drop AND the source slot is left UNCHANGED (no leak) — plus a complete
    TRICHOTOMY iff [postrouting_hook_verdict_trichotomy] partitioning the postrouting
    hook verdict (Drop iff private ∧ ppp0 ∧ orig-fresh ∧ no-usable-address), making the
    NF_DROP path load-bearing.  A mutation making [nat_iface_addr_absent] return false
    flips this verdict to Accept and is observable. *)

(* ------------------------------------------------------------------ *)
(** *** A VERDICT-bearing data-plane hook evaluator.

    [chain_out_bases]/[chain_out_at_hook] thread the PACKET through the hook; their
    verdict companions thread the VERDICT.  At a singleton hook (the postrouting case
    here) the hook verdict is exactly the base chain's trace verdict. *)
Fixpoint eval_trace_bases (h : hook_id)
    (bases : list (list (String.string * chain) * chain)) (p : packet) : verdict :=
  match bases with
  | [] => Accept
  | (_, base) :: rest =>
      let v := fst (eval_chain_trace h base p) in
      let q := snd (eval_chain_trace h base p) in
      if base_continues v then eval_trace_bases h rest q else v
  end.

Definition eval_chain_trace_at_hook (rs : list hooked_chain) (h : hook_id) (p : packet) : verdict :=
  eval_trace_bases h (select_hook rs h) p.

(* At a hook with EXACTLY ONE registered base chain whose trace verdict is Accept or
   Drop (the only two the policy-resolved postrouting chain returns — never Continue),
   the hook verdict is exactly that base chain's trace verdict (mirrors
   [chain_out_at_hook_singleton]).  Accept continues to the empty tail, which returns
   Accept again; Drop is returned directly — both agree with [fst eval_chain_trace]. *)
Lemma eval_chain_trace_at_hook_singleton_ad : forall rs h cs b p,
  select_hook rs h = [(cs, b)] ->
  (fst (eval_chain_trace h b p) = Accept \/ fst (eval_chain_trace h b p) = Drop) ->
  eval_chain_trace_at_hook rs h p = fst (eval_chain_trace h b p).
Proof.
  intros rs h cs b p Hsel Had. unfold eval_chain_trace_at_hook. rewrite Hsel.
  cbn [eval_trace_bases]. destruct Had as [Ha|Hd]; rewrite ?Ha, ?Hd;
    cbn [base_continues]; [cbn [eval_trace_bases]|]; reflexivity.
Qed.

(* The postrouting chain's trace verdict is always Accept or Drop: it is either the
   NAT-core Drop or the chain's resolved verdict, which for the single-Accept-rule
   accept-policy chain is Accept. *)
Lemma postrouting_trace_accept_or_drop : forall p,
  fst (eval_chain_trace Hpostrouting global_postrouting p) = Accept
  \/ fst (eval_chain_trace Hpostrouting global_postrouting p) = Drop.
Proof.
  intro p. rewrite eval_chain_trace_verdict.
  destruct (trace_nat_drops Hpostrouting (c_rules global_postrouting) p); [right; reflexivity|].
  left. unfold eval_chain_mut. rewrite global_postrouting_rules.
  cbn [c_rules c_policy eval_rules_mut].
  destruct (rule_loadable masq_rule p && rule_applies masq_rule p);
    [assert (Ho : outcome masq_rule p = Some Accept) by reflexivity; rewrite Ho; reflexivity
    | reflexivity].
Qed.

(* The postrouting hook of the PARSER's registration: its verdict is exactly the
   trace verdict of [global_postrouting] under [Hpostrouting] — derived from
   [select_postrouting], not a hand-supplied hook. *)
Lemma eval_chain_trace_postrouting_hook : forall p,
  eval_chain_trace_at_hook global_hooks Hpostrouting p
    = fst (eval_chain_trace Hpostrouting global_postrouting p).
Proof.
  intro p. apply (eval_chain_trace_at_hook_singleton_ad global_hooks Hpostrouting
                    global_chains global_postrouting p).
  - apply select_postrouting.
  - apply postrouting_trace_accept_or_drop.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Chain-level NF_DROP: masquerade with no usable exit address DROPS and does
       NOT splice the source. *)

(* When both masq matches pass ([saddr_private] && [oif_ppp0]) the masq rule LOADS:
   both [match_loadable]s are supplied by the [eval_matchcond] conjuncts. *)
Lemma masq_rule_loadable_of_applies : forall p,
  saddr_private p = true -> oif_ppp0 p = true -> rule_loadable masq_rule p = true.
Proof.
  intros p Hpriv Hppp.
  unfold saddr_private, oif_ppp0, eval_matchcond in Hpriv, Hppp.
  apply Bool.andb_true_iff in Hpriv as [Hpl _].
  apply Bool.andb_true_iff in Hppp as [Hol _].
  unfold rule_loadable, masq_rule; cbn [r_body body_loadable_walk
    body_synproxy_stops existsb body_item_loadable body_thread body_has_notrack].
  cbn [match_loadable] in Hpl, Hol |- *. rewrite Hpl, Hol. reflexivity.
Qed.

(* [nat_iface_addr_absent] is TRUE for the masq rule exactly when the exit
   interface address is empty (family "ip" reads [e_ifaddr], so an empty
   [e_ifaddr ... ] makes [masq_saddr] empty). *)
Lemma masq_iface_absent_iff : forall p,
  nat_iface_addr_absent Hpostrouting masq_spec p
    = (match e_ifaddr (pkt_env p) (field_value FMetaOifname p) with [] => true | _ => false end).
Proof.
  intro p. unfold nat_iface_addr_absent, masq_spec; cbn [nat_kind].
  unfold nat_addrfamily_pkt, nat_addrfamily, masq_saddr; cbn [nat_family].
  reflexivity.
Qed.

(* The DUAL of [masq_no_drop]: when the exit interface has NO usable address (and the
   flow is fresh original-direction), the NAT core DROPS — [nat_drops] is true. *)
Lemma masq_drops_noaddr : forall p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  e_ifaddr (pkt_env p) (field_value FMetaOifname p) = [] ->
  nat_drops Hpostrouting masq_rule p = true.
Proof.
  intros p Horig Hnone Hempty. unfold nat_drops, masq_rule; cbn [r_nat].
  rewrite Hnone. rewrite Horig; cbn [andb].
  rewrite masq_iface_absent_iff, Hempty. reflexivity.
Qed.

(* THE CHAIN OUTPUT when the no-address NF_DROP fires: verdict Drop, packet UNCHANGED
   (the source is never spliced — [dsl_step] is the identity on the masq rule, and the
   drop branch returns [dsl_step r p] without [apply_nat]). *)
Theorem masq_noaddr_drop_output : forall p,
  saddr_private p = true ->
  oif_ppp0 p = true ->
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  e_ifaddr (pkt_env p) (field_value FMetaOifname p) = [] ->
  eval_chain_trace Hpostrouting global_postrouting p = (Drop, p).
Proof.
  intros p Hpriv Hppp Horig Hnone Hempty.
  unfold eval_chain_trace. rewrite global_postrouting_rules.
  cbn [c_rules eval_rules_trace].
  rewrite (masq_rule_loadable_of_applies p Hpriv Hppp).
  assert (Happ : rule_applies masq_rule p = true)
    by (rewrite masq_rule_applies_eq, Hpriv, Hppp; reflexivity).
  rewrite Happ. cbn [andb].
  assert (Ho : outcome masq_rule p = Some Accept) by reflexivity.
  rewrite Ho. cbn [terminal].
  rewrite masq_dsl_step_id.
  rewrite (masq_drops_noaddr p Horig Hnone Hempty). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** *** THE GAP CLOSED — hook-level NF_DROP + no-leak through the parser's
       registration. *)

(* A private 192.168.0.0/16 source egressing ppp0 on a fresh original-direction flow
   whose exit interface has NO usable address is DROPPED at the parser-registered
   postrouting hook AND its source slot is left UNCHANGED — the kernel-faithful
   NF_DROP, proven to NOT leak the internal source.  This is precisely the flow in the
   scope of neither [postrouting_hook_masquerades] nor [postrouting_hook_no_leak]. *)
Theorem postrouting_hook_noaddr_drops : forall p,
  saddr_private p = true ->
  oif_ppp0 p = true ->
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  e_ifaddr (pkt_env p) (field_value FMetaOifname p) = [] ->
  eval_chain_trace_at_hook global_hooks Hpostrouting p = Drop
  /\ saddr4 (chain_out_at_hook global_hooks Hpostrouting p) = saddr4 p.
Proof.
  intros p Hpriv Hppp Horig Hnone Hempty.
  pose proof (masq_noaddr_drop_output p Hpriv Hppp Horig Hnone Hempty) as Hout.
  split.
  - rewrite eval_chain_trace_postrouting_hook, Hout. reflexivity.
  - rewrite chain_out_postrouting_hook. unfold chain_out. rewrite Hout. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** *** A COMPLETE TRICHOTOMY for the postrouting hook verdict.

    The postrouting hook verdict is:
      - Drop   iff (private ∧ ppp0 ∧ orig-fresh ∧ no-usable-address)
      - Accept otherwise.
    (The postrouting chain's policy is `accept` and its single rule's stated verdict is
    Accept; the ONLY way the hook drops is the NAT-core NF_DROP.)  This makes the
    NF_DROP path LOAD-BEARING: a mutation removing it changes the verdict on the
    no-address flow from Drop to Accept, observably violating the [<->]. *)
Definition masq_noaddr_cond (p : packet) : bool :=
  saddr_private p && oif_ppp0 p
  && (match e_nat (pkt_env p) (pkt_flow p) with None => true | Some _ => false end)
  && pkt_ctdir_orig p
  && (match e_ifaddr (pkt_env p) (field_value FMetaOifname p) with [] => true | _ => false end).

(* [trace_nat_drops] for the postrouting chain reduces to exactly [masq_noaddr_cond]. *)
Lemma trace_nat_drops_postrouting : forall p,
  trace_nat_drops Hpostrouting (c_rules global_postrouting) p = masq_noaddr_cond p.
Proof.
  intro p. rewrite global_postrouting_rules. cbn [trace_nat_drops].
  unfold masq_noaddr_cond.
  destruct (rule_loadable masq_rule p && rule_applies masq_rule p) eqn:E.
  - (* the rule fires: trace_nat_drops = nat_drops on dsl_step (= identity) *)
    apply Bool.andb_true_iff in E as [Hload Happ].
    rewrite masq_rule_applies_eq in Happ.
    apply Bool.andb_true_iff in Happ as [Hpriv Hppp].
    assert (Ho : outcome masq_rule p = Some Accept) by reflexivity.
    rewrite Ho; cbn [terminal]. rewrite masq_dsl_step_id.
    unfold nat_drops, masq_rule; cbn [r_nat].
    rewrite Hpriv, Hppp; cbn [andb].
    destruct (e_nat (pkt_env p) (pkt_flow p)) eqn:En; [reflexivity|].
    destruct (pkt_ctdir_orig p) eqn:Eo; cbn [andb]; [|reflexivity].
    rewrite masq_iface_absent_iff. reflexivity.
  - (* the rule does not fire: no drop.  Then saddr_private && oif_ppp0 = false:
       if it were true the rule would both LOAD ([masq_rule_loadable_of_applies]) and
       APPLY (= saddr_private && oif_ppp0), contradicting [E]. *)
    assert (Hsp : saddr_private p && oif_ppp0 p = false).
    { destruct (saddr_private p) eqn:Hp; destruct (oif_ppp0 p) eqn:Ho;
        cbn [andb]; try reflexivity.
      rewrite (masq_rule_loadable_of_applies p Hp Ho) in E.
      rewrite masq_rule_applies_eq, Hp, Ho in E. cbn [andb] in E. discriminate E. }
    rewrite Hsp; cbn [andb]. reflexivity.
Qed.

(* The postrouting hook verdict is Drop iff the no-address masquerade condition
   holds; otherwise Accept. *)
Theorem postrouting_hook_verdict_trichotomy : forall p,
  eval_chain_trace_at_hook global_hooks Hpostrouting p
    = (if masq_noaddr_cond p then Drop else Accept).
Proof.
  intro p. rewrite eval_chain_trace_postrouting_hook.
  rewrite eval_chain_trace_verdict, trace_nat_drops_postrouting.
  destruct (masq_noaddr_cond p) eqn:E; [reflexivity|].
  (* no drop: the hook verdict is eval_chain_mut global_postrouting, which is Accept
     (policy accept; either the rule fires terminal-Accept or falls through to policy). *)
  unfold eval_chain_mut. rewrite global_postrouting_rules. cbn [c_rules c_policy eval_rules_mut].
  destruct (rule_loadable masq_rule p && rule_applies masq_rule p);
    [assert (Ho : outcome masq_rule p = Some Accept) by reflexivity; rewrite Ho; reflexivity
    | reflexivity].
Qed.

(* The trichotomy IS satisfiable on the Drop side: a witness whose exit interface has
   no usable address (private source 192.168.1.5 out ppp0, fresh flow, EMPTY WAN). *)
Definition env_noaddr : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0;
     e_ifaddrs := fun _ => [];          (* NO usable address on any interface *)
     e_ifaddrs6 := fun _ => []; e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

Definition pkt_priv_noaddr : packet :=
  {| pkt_env := env_noaddr;
     pkt_meta := fun k => if meta_eqb k MKoifname then if_ppp0 else [];
     pkt_ct := fun _ => []; pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := ip4_priv; pkt_th := [0;0;0;0;0;0;0;0]; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := true;
     pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false;
     pkt_ctdir_orig := true; pkt_ct_present := true |}.

Lemma pkt_priv_noaddr_private : saddr_private pkt_priv_noaddr = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pkt_priv_noaddr_oif : oif_ppp0 pkt_priv_noaddr = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pkt_priv_noaddr_ifaddr :
  e_ifaddr (pkt_env pkt_priv_noaddr) (field_value FMetaOifname pkt_priv_noaddr) = [].
Proof. vm_compute. reflexivity. Qed.

(* The witness DROPS at the postrouting hook and does NOT leak its private source. *)
Theorem witness_noaddr_drops :
  eval_chain_trace_at_hook global_hooks Hpostrouting pkt_priv_noaddr = Drop
  /\ saddr4 (chain_out_at_hook global_hooks Hpostrouting pkt_priv_noaddr) = [192;168;1;5].
Proof.
  pose proof (postrouting_hook_noaddr_drops pkt_priv_noaddr
                pkt_priv_noaddr_private pkt_priv_noaddr_oif eq_refl eq_refl
                pkt_priv_noaddr_ifaddr) as [Hv Hs].
  split; [exact Hv|]. rewrite Hs. vm_compute. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** *** MUTATION KILL: an [nat_iface_addr_absent] that NEVER reports absent (NF_DROP
       -> silent accept) flips the verdict from Drop to Accept on the witness and
       leaves the source 192.168.1.5 un-NATted — a leak — yet (before this file) broke
       no proven theorem.  We exhibit the mutated [nat_drops] and show the verdict
       differs, so [postrouting_hook_verdict_trichotomy] genuinely depends on the
       NF_DROP path. *)

(* The mutated trace verdict that DROPS the NF_DROP entirely (nat_drops ≡ false): it
   is just the control-plane [eval_chain_mut], which on the witness is Accept. *)
Definition mutated_postrouting_verdict (p : packet) : verdict :=
  eval_chain_mut global_postrouting p.

Lemma mutated_accepts_witness :
  mutated_postrouting_verdict pkt_priv_noaddr = Accept.
Proof. vm_compute. reflexivity. Qed.

(* The honest (NF_DROP-faithful) verdict DROPS the same witness — observably different
   from the mutation: the trichotomy's Drop case is load-bearing. *)
Theorem noaddr_drop_observable :
  eval_chain_trace_at_hook global_hooks Hpostrouting pkt_priv_noaddr
  <> mutated_postrouting_verdict pkt_priv_noaddr.
Proof.
  rewrite (proj1 witness_noaddr_drops), mutated_accepts_witness. discriminate.
Qed.
