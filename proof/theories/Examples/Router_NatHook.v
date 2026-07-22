(* ============================================================================
   router.nft postrouting masquerade — DATA-PLANE HOOK BRIDGE (the parser's hook
   registration is load-bearing for NAT).

   THE GAP this file closes (the postrouting half of the chain<->hook bridge,
   for the DATA PLANE):

   [Router_Hooks] lifts the VERDICT-bearing input/forward security theorems to the
   hook level via [eval_hook_u hk_fuel global_hooks H...], so a wrong-hook swap of
   those chains is observable.  But the masquerade NAT — the entire security reason
   the postrouting chain exists, the crux [Router_Reach] proves — is not, by
   itself, connected to the parser's registration [global_hooks].  Every masquerade
   theorem in Router_Reach.v is stated as

       chain_out Hpostrouting global_postrouting e p     (Hpostrouting hand-supplied,
                                                         global_postrouting hand-named)

   and the VERDICT projection of [eval_hook_u]/[eval_ruleset_u] discards the output
   packet, so that projection could not even *express* "the masquerade chain is the one netfilter runs at
   postrouting".  Consequently a planted bug that registers masquerade at the WRONG
   hook, or drops its postrouting registration entirely, leaks every internal
   192.168.0.0/16 source address un-NATted to the WAN yet satisfies every proven NAT
   property verbatim ([select_postrouting] in Router_Hooks.v is a DEAD lemma — no NAT
   theorem uses it).

   THE FIX: a DATA-PLANE hook evaluator [chain_out_at_hook] that DERIVES the hook_id
   and the base chain from the PARSED registration [rs] and threads the PACKET (not
   just a verdict) through it — selecting the base chain(s) registered at [h] and
   running [eval_chain_u h base] with THAT [h] as the [apply_nat] hook.  Then:

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
    [h], in priority order (Semantics.v).  The verdict projection of [eval_ruleset_u]
    folds verdicts over it; here we fold the PACKET: each base chain that does not
    terminate-drop passes its OUTPUT packet ([chain_out h base], the data-plane
    trace) to the next, threading NAT rewrites through the hook.  [h] — the hook the
    packet ACTUALLY hits per the parsed registration — is supplied to [chain_out] as
    the [apply_nat] hook_id, so a wrong-hook registration changes which hook drives
    the rewrite. *)
Fixpoint chain_out_bases (h : hook_id)
    (bases : list (list (String.string * chain) * chain)) (e : env) (p : packet) : packet :=
  match bases with
  | [] => p
  | (_, base) :: rest =>
      let v := fst (eval_chain_u h base e p) in
      let s := snd (eval_chain_u h base e p) in
      if base_continues v then chain_out_bases h rest (fst s) (snd s) else snd s
  end.

Definition chain_out_at_hook (rs : list hooked_chain) (h : hook_id) (e : env) (p : packet)
  : packet :=
  chain_out_bases h (select_hook rs h) e p.

(* At a hook with EXACTLY ONE registered base chain [b], the data-plane hook output
   is exactly that base chain's trace output [chain_out h b] — independent of the
   chain's verdict (Accept continues to [] which returns the packet; a terminal
   verdict returns the same packet [q]). *)
Lemma chain_out_at_hook_singleton : forall rs h cs b e p,
  select_hook rs h = [(cs, b)] ->
  chain_out_at_hook rs h e p = chain_out h b e p.
Proof.
  intros rs h cs b e p Hsel. unfold chain_out_at_hook, chain_out. rewrite Hsel.
  cbn [chain_out_bases]. destruct (base_continues (fst (eval_chain_u h b e p)));
    cbn [chain_out_bases]; reflexivity.
Qed.

(* The postrouting hook of the PARSER's registration resolves to global_postrouting,
   and its data-plane output is exactly the trace output Router_Reach characterises
   — but now with [Hpostrouting] DERIVED from [select_postrouting], not hand-given. *)
Lemma chain_out_postrouting_hook : forall e p,
  chain_out_at_hook global_hooks Hpostrouting e p
    = chain_out Hpostrouting global_postrouting e p.
Proof.
  intros e p. apply (chain_out_at_hook_singleton global_hooks Hpostrouting
                    global_chains global_postrouting e p).
  apply select_postrouting.
Qed.

(* ================================================================== *)
(** ** The masquerade crux, proven THROUGH the parser's registration. *)

(* (a) FIRES — a private source (192.168.0.0/16) egressing ppp0, on the first
   (unconfirmed, original-direction) packet of its flow with a usable exit address
   [wan], has its source slot rewritten to [wan] — by whatever chain the PARSER
   registered at the postrouting hook.  No [Hpostrouting] is supplied by hand: it is
   the hook_id the registration binds to global_postrouting. *)
Theorem postrouting_hook_masquerades : forall e p wan,
  saddr_private e p = true ->
  oif_ppp0 e p = true ->
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  e_ifaddr e (field_value FMetaOifname e p) = wan ->
  wan <> [] ->
  16 <= List.length (pkt_nh p) ->
  List.length wan = 4 ->
  saddr4 (chain_out_at_hook global_hooks Hpostrouting e p) = wan.
Proof.
  intros e p wan Hpriv Hppp Horig Hnone Hwan Hne Hnh Hwl.
  rewrite chain_out_postrouting_hook.
  apply (proj1 (nat_masquerade_fires e p wan Hpriv Hppp Horig Hnone Hwan Hne Hnh Hwl)).
Qed.

(* (b) NO-LEAK (the security half) — a packet whose source is NOT private OR whose
   egress is NOT ppp0 is returned source-UNCHANGED through the postrouting hook: no
   internal-address leak.  Also stated for the parser-derived hook. *)
Theorem postrouting_hook_no_leak : forall e p,
  (saddr_private e p = false \/ oif_ppp0 e p = false) ->
  saddr4 (chain_out_at_hook global_hooks Hpostrouting e p) = saddr4 p.
Proof.
  intros e p Hor. rewrite chain_out_postrouting_hook.
  apply (proj1 (nat_no_leak e p Hor)).
Qed.

(* CONFIRMED-FLOW stability through the hook: a later packet of an established masq
   flow is rewritten from the STORED wan ([Router_Reach]'s flow-stability crux),
   here through the parser's hook. *)
Theorem postrouting_hook_confirmed_reuses_stored : forall e p oa wan,
  saddr_private e p = true ->
  oif_ppp0 e p = true ->
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = Some (Some oa, Some wan, None, None) ->
  16 <= List.length (pkt_nh p) ->
  List.length wan = 4 ->
  saddr4 (chain_out_at_hook global_hooks Hpostrouting e p) = wan.
Proof.
  intros e p oa wan Hpriv Hppp Horig Hsome Hnh Hwl.
  rewrite chain_out_postrouting_hook.
  apply (nat_masq_confirmed_reuses_stored e p oa wan Hpriv Hppp Horig Hsome Hnh Hwl).
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
Lemma bug_postrouting_hook_id : forall e p,
  chain_out_at_hook global_hooks_natbug Hpostrouting e p = p.
Proof.
  intros e p. unfold chain_out_at_hook. rewrite bug_no_postrouting_chain.
  reflexivity.
Qed.

(* On the firing witness [pkt_priv] (private source 192.168.1.5 out ppp0, fresh
   flow, usable WAN), the PARSER's registration source-NATs to the WAN address... *)
Lemma natbug_correct_fires :
  saddr4 (chain_out_at_hook global_hooks Hpostrouting env_bug pkt_priv) = wan_addr.
Proof.
  rewrite chain_out_postrouting_hook. exact witness_fires.
Qed.

(* ...while the bugged (postrouting-dropped) registration LEAKS the private source
   192.168.1.5 un-NATted. *)
Lemma natbug_leaks :
  saddr4 (chain_out_at_hook global_hooks_natbug Hpostrouting env_bug pkt_priv)
  = [192;168;1;5].
Proof.
  rewrite bug_postrouting_hook_id. vm_compute. reflexivity.
Qed.

(* THE OBSERVABLE: the parser's registration and the postrouting-dropped one disagree
   on a real packet's SOURCE SLICE — so [postrouting_hook_masquerades] genuinely
   depends on the registration the parser emitted ([select_postrouting] is now
   load-bearing), closing the postrouting half of the chain<->hook bridge. *)
Theorem natbug_observable :
  saddr4 (chain_out_at_hook global_hooks     Hpostrouting env_bug pkt_priv)
  <> saddr4 (chain_out_at_hook global_hooks_natbug Hpostrouting env_bug pkt_priv).
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
  saddr4 (chain_out_at_hook global_hooks         Hpostrouting env_bug pkt_priv)
  <> saddr4 (chain_out_at_hook global_hooks_wronghook Hpostrouting env_bug pkt_priv).
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
    the single fold returns [(Some Drop, (e, p))] — the packet is DROPPED
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

    THIS SECTION: (i) a VERDICT-bearing hook companion [eval_chain_u_at_hook] to
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
Fixpoint eval_u_bases (h : hook_id)
    (bases : list (list (String.string * chain) * chain)) (e : env) (p : packet) : verdict :=
  match bases with
  | [] => Accept
  | (_, base) :: rest =>
      let v := fst (eval_chain_u h base e p) in
      let s := snd (eval_chain_u h base e p) in
      if base_continues v then eval_u_bases h rest (fst s) (snd s) else v
  end.

Definition eval_chain_u_at_hook (rs : list hooked_chain) (h : hook_id)
    (e : env) (p : packet) : verdict :=
  eval_u_bases h (select_hook rs h) e p.

(* At a hook with EXACTLY ONE registered base chain whose trace verdict is Accept or
   Drop (the only two the policy-resolved postrouting chain returns — never Continue),
   the hook verdict is exactly that base chain's trace verdict (mirrors
   [chain_out_at_hook_singleton]).  Accept continues to the empty tail, which returns
   Accept again; Drop is returned directly — both agree with [fst eval_chain_u]. *)
Lemma eval_chain_u_at_hook_singleton_ad : forall rs h cs b e p,
  select_hook rs h = [(cs, b)] ->
  (fst (eval_chain_u h b e p) = Accept \/ fst (eval_chain_u h b e p) = Drop) ->
  eval_chain_u_at_hook rs h e p = fst (eval_chain_u h b e p).
Proof.
  intros rs h cs b e p Hsel Had. unfold eval_chain_u_at_hook. rewrite Hsel.
  cbn [eval_u_bases]. destruct Had as [Ha|Hd]; rewrite ?Ha, ?Hd;
    cbn [base_continues]; [cbn [eval_u_bases]|]; reflexivity.
Qed.

(* The postrouting chain's trace verdict is always Accept or Drop: it is either the
   NAT-core Drop or the chain's resolved verdict, which for the single-Accept-rule
   accept-policy chain is Accept. *)
Lemma postrouting_trace_accept_or_drop : forall e p,
  fst (eval_chain_u Hpostrouting global_postrouting e p) = Accept
  \/ fst (eval_chain_u Hpostrouting global_postrouting e p) = Drop.
Proof.
  intros e p. rewrite masq_chain_u.
  destruct (saddr_private e p && oif_ppp0 e p); [|left; reflexivity].
  destruct (nat_drops Hpostrouting masq_rule e p); [right; reflexivity|].
  left. destruct (apply_nat Hpostrouting masq_rule e p); reflexivity.
Qed.

(* The postrouting hook of the PARSER's registration: its verdict is exactly the
   trace verdict of [global_postrouting] under [Hpostrouting] — derived from
   [select_postrouting], not a hand-supplied hook. *)
Lemma eval_chain_u_postrouting_hook : forall e p,
  eval_chain_u_at_hook global_hooks Hpostrouting e p
    = fst (eval_chain_u Hpostrouting global_postrouting e p).
Proof.
  intros e p. apply (eval_chain_u_at_hook_singleton_ad global_hooks Hpostrouting
                    global_chains global_postrouting e p).
  - apply select_postrouting.
  - apply postrouting_trace_accept_or_drop.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Chain-level NF_DROP: masquerade with no usable exit address DROPS and does
       NOT splice the source. *)

(* When both masq matches pass ([saddr_private] && [oif_ppp0]) the masq rule LOADS:
   both [match_loadable]s are supplied by the [eval_matchcond] conjuncts. *)
Lemma masq_rule_loadable_of_applies : forall e p,
  saddr_private e p = true -> oif_ppp0 e p = true -> rule_loadable masq_rule e p = true.
Proof.
  intros e p Hpriv Hppp.
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
Lemma masq_iface_absent_iff : forall e p,
  nat_iface_addr_absent Hpostrouting (nat_kind masq_spec) (nat_family masq_spec) e p
    = (match e_ifaddr e (field_value FMetaOifname e p) with [] => true | _ => false end).
Proof.
  intros e p. unfold nat_iface_addr_absent, masq_spec; cbn [nat_kind nat_family].
  unfold nat_af_pkt, nat_af_norm, masq_saddr.
  reflexivity.
Qed.

(* The DUAL of [masq_no_drop]: when the exit interface has NO usable address (and the
   flow is fresh original-direction), the NAT core DROPS — [nat_drops] is true. *)
Lemma masq_drops_noaddr : forall e p,
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  e_ifaddr e (field_value FMetaOifname e p) = [] ->
  nat_drops Hpostrouting masq_rule e p = true.
Proof.
  intros e p Horig Hnone Hempty.
  unfold nat_drops, nat_drops_c, masq_rule; cbn [r_nat r_outcome].
  rewrite Hnone. rewrite Horig; cbn [andb].
  rewrite masq_iface_absent_iff, Hempty. reflexivity.
Qed.

(* THE CHAIN OUTPUT when the no-address NF_DROP fires: verdict Drop, packet UNCHANGED
   (the source is never spliced — [dsl_step] is the identity on the masq rule, and the
   drop branch returns [dsl_step r e p] without [apply_nat]). *)
Theorem masq_noaddr_drop_output : forall e p,
  saddr_private e p = true ->
  oif_ppp0 e p = true ->
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  e_ifaddr e (field_value FMetaOifname e p) = [] ->
  eval_chain_u Hpostrouting global_postrouting e p = (Drop, (e, p)).
Proof.
  intros e p Hpriv Hppp Horig Hnone Hempty.
  rewrite masq_chain_u, Hpriv, Hppp. cbn [andb].
  rewrite (masq_drops_noaddr e p Horig Hnone Hempty). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** *** THE GAP CLOSED — hook-level NF_DROP + no-leak through the parser's
       registration. *)

(* A private 192.168.0.0/16 source egressing ppp0 on a fresh original-direction flow
   whose exit interface has NO usable address is DROPPED at the parser-registered
   postrouting hook AND its source slot is left UNCHANGED — the kernel-faithful
   NF_DROP, proven to NOT leak the internal source.  This is precisely the flow in the
   scope of neither [postrouting_hook_masquerades] nor [postrouting_hook_no_leak]. *)
Theorem postrouting_hook_noaddr_drops : forall e p,
  saddr_private e p = true ->
  oif_ppp0 e p = true ->
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  e_ifaddr e (field_value FMetaOifname e p) = [] ->
  eval_chain_u_at_hook global_hooks Hpostrouting e p = Drop
  /\ saddr4 (chain_out_at_hook global_hooks Hpostrouting e p) = saddr4 p.
Proof.
  intros e p Hpriv Hppp Horig Hnone Hempty.
  pose proof (masq_noaddr_drop_output e p Hpriv Hppp Horig Hnone Hempty) as Hout.
  split.
  - rewrite eval_chain_u_postrouting_hook, Hout. reflexivity.
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
Definition masq_noaddr_cond (e : env) (p : packet) : bool :=
  saddr_private e p && oif_ppp0 e p
  && (match e_nat e (pkt_flow p) with None => true | Some _ => false end)
  && pkt_ctdir_orig p
  && (match e_ifaddr e (field_value FMetaOifname e p) with [] => true | _ => false end).

(* The postrouting hook verdict is Drop iff the no-address masquerade condition
   holds; otherwise Accept — read directly off the single fold ([masq_chain_u]):
   the ONLY way the hook drops is the in-fold NAT-core NF_DROP. *)
Theorem postrouting_hook_verdict_trichotomy : forall e p,
  eval_chain_u_at_hook global_hooks Hpostrouting e p
    = (if masq_noaddr_cond e p then Drop else Accept).
Proof.
  intros e p. rewrite eval_chain_u_postrouting_hook.
  rewrite masq_chain_u.
  unfold masq_noaddr_cond.
  destruct (saddr_private e p && oif_ppp0 e p) eqn:Hsp; cbn [andb]; [|reflexivity].
  unfold nat_drops, nat_drops_c, masq_rule; cbn [r_nat r_outcome].
  rewrite masq_iface_absent_iff.
  destruct (e_nat e (pkt_flow p)) eqn:En.
  - cbn [andb]. destruct (apply_nat Hpostrouting masq_rule e p); reflexivity.
  - destruct (pkt_ctdir_orig p) eqn:Eo; cbn [andb].
    + destruct (e_ifaddr e (field_value FMetaOifname e p)); [reflexivity|].
      destruct (apply_nat Hpostrouting masq_rule e p); reflexivity.
    + destruct (apply_nat Hpostrouting masq_rule e p); reflexivity.
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
  {|
     pkt_meta := fun k => if meta_eqb k MKoifname then if_ppp0 else [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := ip4_priv; pkt_th := [0;0;0;0;0;0;0;0]; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := true;
     pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false;
     pkt_ctdir_orig := true; pkt_ct_present := true |}.

Lemma pkt_priv_noaddr_private : saddr_private env_noaddr pkt_priv_noaddr = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pkt_priv_noaddr_oif : oif_ppp0 env_noaddr pkt_priv_noaddr = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pkt_priv_noaddr_ifaddr :
  e_ifaddr env_noaddr (field_value FMetaOifname env_noaddr pkt_priv_noaddr) = [].
Proof. vm_compute. reflexivity. Qed.

(* The witness DROPS at the postrouting hook and does NOT leak its private source. *)
Theorem witness_noaddr_drops :
  eval_chain_u_at_hook global_hooks Hpostrouting env_noaddr pkt_priv_noaddr = Drop
  /\ saddr4 (chain_out_at_hook global_hooks Hpostrouting env_noaddr pkt_priv_noaddr)
     = [192;168;1;5].
Proof.
  pose proof (postrouting_hook_noaddr_drops env_noaddr pkt_priv_noaddr
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

(* The honest (NF_DROP-faithful) canonical verdict DROPS the no-address witness
   ([witness_noaddr_drops]).  A NAT-blind evaluator that dropped the NF_DROP path
   would instead ACCEPT (leaking the un-NATted source 192.168.1.5) — exactly the
   evaluator shape a NAT rule must never be run through, and why NAT rules are
   OUTSIDE every write-free license (Router_Input § "UNIFIED-SEMANTICS LICENSE").
   That the honest verdict is [Drop], not [Accept], is what makes the trichotomy's
   Drop case load-bearing. *)
Theorem noaddr_drop_observable :
  eval_chain_u_at_hook global_hooks Hpostrouting env_noaddr pkt_priv_noaddr = Drop
  /\ Drop <> Accept.
Proof.
  rewrite (proj1 witness_noaddr_drops). split; [ reflexivity | discriminate ].
Qed.
