(* ============================================================================
   router.nft postrouting masquerade — DATA-PLANE HOOK BRIDGE (the parser's hook
   registration is load-bearing for NAT).

   THE GAP this file closes (the postrouting half of Round 6's chain<->hook bridge,
   for the DATA PLANE):

   Round 6 lifted the VERDICT-bearing input/forward security theorems to the hook
   level via [eval_hook hk_fuel global_hooks H...], so a wrong-hook swap of those
   chains is observable.  But the masquerade NAT — the entire security reason the
   postrouting chain exists, the crux Rounds 1/5 proved — was NEVER connected to the
   parser's registration [global_hooks].  Every masquerade theorem in Router_Reach.v
   is stated as

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

From Stdlib Require Import List String NArith Lia.
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
   flow is rewritten from the STORED wan (Round 5), now through the parser's hook. *)
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
  [{| hc_hook := Hinput;   hc_prio := 0; hc_env := global_chains; hc_base := global_inbound |};
   {| hc_hook := Hforward; hc_prio := 0; hc_env := global_chains; hc_base := global_forward |}].

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
  [{| hc_hook := Hinput;   hc_prio := 0;   hc_env := global_chains; hc_base := global_inbound |};
   {| hc_hook := Hforward; hc_prio := 0;   hc_env := global_chains; hc_base := global_forward |};
   {| hc_hook := Hinput;   hc_prio := 100; hc_env := global_chains; hc_base := global_postrouting |}].

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
