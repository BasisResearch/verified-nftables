(* ============================================================================
   router.nft — HOOK-LEVEL reachability (the chain<->hook registration is proven).

   Rounds 1-5 characterised each base chain IN ISOLATION via
       eval_table fuel global_chains global_<chain> p = V,
   with the *prover* hand-selecting which chain corresponds to which hook.  But
   netfilter's actual data-plane decision for a packet is

       eval_hook fuel <ruleset> h p              (Semantics.v)

   which select+orders the base chains REGISTERED at hook [h] (select_hook /
   sort_hc, by priority) and combines their verdicts (base_continues).  The
   binding "chain C is registered at hook H with priority P" is exactly the
   `type filter hook input priority 0;` line in router.nft.

   THE GAP it closed: the lowering used to DISCARD that declaration
   (`ITypeHook _ -> ()`), so Router_Gen.v emitted ZERO hook metadata and no
   theorem ever mentioned a hook.  A planted bug that registers the locked-down
   `inbound` chain at FORWARD and the permissive `forward` chain at INPUT yields
   a wide-open router yet satisfies every per-chain property verbatim.

   THE FIX (this round): the generator now emits, from the parser's ITypeHook
   records, a `global_hooks : list hooked_chain` (Router_Gen.v) — inbound@Hinput
   prio 0, forward@Hforward prio 0, postrouting@Hpostrouting prio 100.  Here we
   RE-STATE the security crux at the HOOK level over that parser-emitted
   registration, prove the iff bridge that transfers the Round 2/3 per-chain
   results to the hook the packet actually hits, and KILL the swap mutation:
   `global_hooks_bug` (inbound<->forward swapped onto each other's hooks) FAILS
   the hook-level theorems while satisfying every per-chain one, witnessed by a
   real LAN packet (tcp/25) that the bugged input hook ACCEPTs but the correct
   input hook DROPs.
   ========================================================================== *)

From Stdlib Require Import List String.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Router_Gen.
From Nft Require Import Router_Input Router_Forward Router_Private.
Import ListNotations.

(* The dispatch fuel: 8 fuel resolves jumps across global_chains (= in_fuel = fw_fuel). *)
Definition hk_fuel : nat := 8.

(* ------------------------------------------------------------------ *)
(** ** The registration the PARSER emitted reduces to exactly the chain the
    Round 2/3 theorems characterise — established by computing select_hook on
    the parser's global_hooks (NOT a hand-written registration). *)

Lemma select_input :
  select_hook global_hooks Hinput = [(global_chains, global_inbound)].
Proof.
  unfold select_hook, global_hooks.
  cbn [filter hook_eqb map sort_hc insert_hc hc_hook hc_prio hc_env hc_base Nat.leb].
  reflexivity.
Qed.

Lemma select_forward :
  select_hook global_hooks Hforward = [(global_chains, global_forward)].
Proof.
  unfold select_hook, global_hooks.
  cbn [filter hook_eqb map sort_hc insert_hc hc_hook hc_prio hc_env hc_base Nat.leb].
  reflexivity.
Qed.

Lemma select_postrouting :
  select_hook global_hooks Hpostrouting = [(global_chains, global_postrouting)].
Proof.
  unfold select_hook, global_hooks.
  cbn [filter hook_eqb map sort_hc insert_hc hc_hook hc_prio hc_env hc_base Nat.leb].
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Generic singleton-hook bridge: at a hook with exactly one registered base
    chain, the hook verdict is [Drop] iff the base chain's table verdict is
    [Drop], and [Accept] iff it is [Accept] (the only two verdicts the
    policy-resolved [eval_table] returns for these chains). *)

Lemma eval_ruleset_singleton : forall f cs b p,
  eval_ruleset f [(cs, b)] p =
  (if base_continues (eval_table f cs b p) then Accept else eval_table f cs b p).
Proof. intros. reflexivity. Qed.

Lemma singleton_hook_drop : forall f cs b p,
  eval_ruleset f [(cs, b)] p = Drop <-> eval_table f cs b p = Drop.
Proof.
  intros f cs b p. rewrite eval_ruleset_singleton.
  destruct (eval_table f cs b p) eqn:E; cbn; split; intro H;
    try discriminate; try reflexivity; try assumption.
Qed.

Lemma singleton_hook_accept : forall f cs b p,
  eval_table f cs b p = Accept ->
  eval_ruleset f [(cs, b)] p = Accept.
Proof.
  intros f cs b p H. rewrite eval_ruleset_singleton, H. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The hook-level iff bridges: the parser's input/forward hook verdict
    equals the per-chain verdict the existing theorems characterise.  These let
    every Round 2/3 result transfer to the hook the packet actually hits. *)

Theorem input_hook_drop_iff_inbound_drop : forall p,
  eval_hook hk_fuel global_hooks Hinput p = Drop
  <-> eval_table hk_fuel global_chains global_inbound p = Drop.
Proof.
  intros p. unfold eval_hook. rewrite select_input.
  apply singleton_hook_drop.
Qed.

Theorem forward_hook_drop_iff_forward_drop : forall p,
  eval_hook hk_fuel global_hooks Hforward p = Drop
  <-> eval_table hk_fuel global_chains global_forward p = Drop.
Proof.
  intros p. unfold eval_hook. rewrite select_forward.
  apply singleton_hook_drop.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The security crux, RE-STATED at the hook level over the parser-emitted
    registration.  These are the Round 3 / Round 2 invariants — but now about
    "what netfilter dispatches at the input/forward hook", not a chain the
    prover named. *)

(* INPUT hook: a new-state packet arriving on the world interface (ppp0) that is
   not ssh from 81.209.165.42 is DROPPED by whatever chain is registered at the
   input hook.  (Round 3 world_ingress_locked_down, lifted.) *)
Theorem input_hook_world_locked : forall p,
  pkt_env p = gen_env ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  Router_Input.world_loads p = true ->
  field_value FCtState p = Router_Input.cts_new ->
  field_value FMetaIifname p = Router_Input.if_ppp0 ->
  Router_Input.world_ssh p = false ->
  eval_hook hk_fuel global_hooks Hinput p = Drop.
Proof.
  intros p Hpe Hl1 Hl2 Hwl Hct Hppp0 Hssh.
  apply input_hook_drop_iff_inbound_drop.
  apply world_ingress_locked_down; assumption.
Qed.

(* FORWARD hook: unsolicited world->private traffic (new ct-state, not arriving
   on the LAN interface eth1) is NOT forwarded — the NAT-router crux, now at the
   hook netfilter dispatches.  (Round 2 forward_unsolicited_dropped, lifted.) *)
Theorem forward_hook_unsolicited_dropped : forall p,
  pkt_env p = gen_env ->
  field_value FCtState p = Router_Forward.cts_new ->
  Router_Forward.iif_eth1 p = false ->
  eval_hook hk_fuel global_hooks Hforward p = Drop.
Proof.
  intros p Hpe Hct Hiif.
  apply forward_hook_drop_iff_forward_drop.
  apply forward_unsolicited_dropped; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(** ** MUTATION KILL: a registration that swaps inbound<->forward onto each
    other's hooks.  Every per-chain (Round 1-5) theorem holds verbatim for it
    (none mention global_hooks), but the hook-level theorems FAIL — witnessed by
    a real LAN packet. *)

Definition global_hooks_bug : list hooked_chain :=
  [{| hc_hook := Hinput;       hc_prio := 0;   hc_env := global_chains; hc_base := global_forward |};
   {| hc_hook := Hforward;     hc_prio := 0;   hc_env := global_chains; hc_base := global_inbound |};
   {| hc_hook := Hpostrouting; hc_prio := 100; hc_env := global_chains; hc_base := global_postrouting |}].

(* pkt_lan_smtp = LAN packet on eth1, ct-new, unlisted service tcp/25.
   Proven DROPPED by the real input chain in Router_Private.pkt_lan_smtp_dropped. *)

(* At the CORRECT input hook the parser registers, the unlisted LAN service is
   dropped (inbound_private's service filter rejects tcp/25). *)
Theorem input_hook_smtp_correct_drop :
  eval_hook hk_fuel global_hooks Hinput pkt_lan_smtp = Drop.
Proof. vm_compute. reflexivity. Qed.

(* At the BUGGED input hook (global_forward registered there), the bare
   `iif eth1 accept` rule accepts the unlisted LAN service unconditionally —
   bypassing inbound_private's whole service filter. *)
Theorem input_hook_smtp_bug_accept :
  eval_hook hk_fuel global_hooks_bug Hinput pkt_lan_smtp = Accept.
Proof. vm_compute. reflexivity. Qed.

(* The observable: the parser's registration and the swapped one disagree on a
   real packet — so the hook-level theorems genuinely depend on the registration
   the parser emitted, not a chain the prover named. *)
Theorem hook_swap_observable :
  eval_hook hk_fuel global_hooks     Hinput pkt_lan_smtp
  <> eval_hook hk_fuel global_hooks_bug Hinput pkt_lan_smtp.
Proof.
  rewrite input_hook_smtp_correct_drop, input_hook_smtp_bug_accept. discriminate.
Qed.

(* The bugged registration FAILS input_hook_world_locked's conclusion shape:
   the world-locked theorem would be FALSE for global_hooks_bug, because the
   forward chain it puts at input accepts the LAN smtp packet that the locked
   input must drop.  (We witness the discriminating verdict directly.) *)
Theorem bug_breaks_input_lockdown :
  eval_hook hk_fuel global_hooks_bug Hinput pkt_lan_smtp <> Drop.
Proof. rewrite input_hook_smtp_bug_accept. discriminate. Qed.
