(* ============================================================================
   router.nft — HOOK-LEVEL reachability (the chain<->hook registration is proven).

   The per-chain files (Router_Input / Router_Forward / Router_Private /
   Router_Reach) characterise each base chain IN ISOLATION via
       eval_table fuel global_chains global_<chain> p = V,
   with the *prover* hand-selecting which chain corresponds to which hook.  But
   netfilter's actual data-plane decision for a packet is

       eval_hook fuel <ruleset> h p              (Semantics.v)

   which select+orders the base chains REGISTERED at hook [h] (select_hook /
   sort_hc, by priority) and combines their verdicts (base_continues).  The
   binding "chain C is registered at hook H with priority P" is exactly the
   `type filter hook input priority 0;` line in router.nft.

   Per-chain properties alone cannot see the registration: a planted bug that
   registers the locked-down `inbound` chain at FORWARD and the permissive
   `forward` chain at INPUT yields a wide-open router yet satisfies every
   per-chain property verbatim.

   THIS FILE: the generator emits, from the parser's ITypeHook records, a
   `global_hooks : list hooked_chain` (Router_Gen.v) — inbound@Hinput prio 0,
   forward@Hforward prio 0, postrouting@Hpostrouting prio 100.  Here we RE-STATE
   the security crux at the HOOK level over that parser-emitted registration,
   prove the iff bridge that transfers the per-chain results
   ([forward_unsolicited_dropped], [world_ingress_locked_down]) to the hook the
   packet actually hits, and KILL the swap mutation: `global_hooks_bug`
   (inbound<->forward swapped onto each other's hooks) FAILS the hook-level
   theorems while satisfying every per-chain one, witnessed by a real LAN packet
   (tcp/25) that the bugged input hook ACCEPTs but the correct input hook DROPs.

   M4 NOTE — the hook-level theorems below that combine [e = gen_env] with
   [cts_new] inherit the per-chain VACUITY
   ([Router_Realistic.ctstate_under_genenv_never_new]); the registration
   bridges ([*_hook_drop_iff_*], no env hypothesis) and the mutation kill are
   unaffected.  The de-vacuized hook-level forms are
   [Router_Realistic.input_hook_world_locked_real] /
   [forward_hook_unsolicited_dropped_real] (+ their witnessed instances).
   ========================================================================== *)

From Stdlib Require Import List String ZArith.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Router_Gen.
From Nft Require Import Router_Input Router_Forward Router_Private.
Import ListNotations.

(* The dispatch fuel: 8 fuel resolves jumps across global_chains (= in_fuel = fw_fuel). *)
Definition hk_fuel : nat := 8.

(* ------------------------------------------------------------------ *)
(** ** The registration the PARSER emitted reduces to exactly the chain the
    per-chain theorems (Router_Input / Router_Forward) characterise — established
    by computing select_hook on the parser's global_hooks (NOT a hand-written
    registration). *)

Lemma select_input :
  select_hook global_hooks Hinput = [(global_chains, global_inbound)].
Proof.
  unfold select_hook, global_hooks.
  cbn [filter hook_eqb map sort_hc insert_hc hc_hook hc_prio hc_env hc_base Z.leb].
  reflexivity.
Qed.

Lemma select_forward :
  select_hook global_hooks Hforward = [(global_chains, global_forward)].
Proof.
  unfold select_hook, global_hooks.
  cbn [filter hook_eqb map sort_hc insert_hc hc_hook hc_prio hc_env hc_base Z.leb].
  reflexivity.
Qed.

Lemma select_postrouting :
  select_hook global_hooks Hpostrouting = [(global_chains, global_postrouting)].
Proof.
  unfold select_hook, global_hooks.
  cbn [filter hook_eqb map sort_hc insert_hc hc_hook hc_prio hc_env hc_base Z.leb].
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Generic singleton-hook bridge: at a hook with exactly one registered base
    chain, the hook verdict is [Drop] iff the base chain's table verdict is
    [Drop], and [Accept] iff it is [Accept] (the only two verdicts the
    policy-resolved [eval_table] returns for these chains). *)

Lemma eval_ruleset_singleton : forall f cs b e p,
  eval_ruleset f [(cs, b)] e p =
  (if base_continues (eval_table f cs b e p) then Accept else eval_table f cs b e p).
Proof.
  intros. rewrite eval_ruleset_cons. cbv zeta.
  destruct (base_continues (eval_table f cs b e p)); reflexivity.
Qed.

Lemma singleton_hook_drop : forall f cs b e p,
  eval_ruleset f [(cs, b)] e p = Drop <-> eval_table f cs b e p = Drop.
Proof.
  intros f cs b e p. rewrite eval_ruleset_singleton.
  destruct (eval_table f cs b e p) eqn:E; cbn; split; intro H;
    try discriminate; try reflexivity; try assumption.
Qed.

Lemma singleton_hook_accept : forall f cs b e p,
  eval_table f cs b e p = Accept ->
  eval_ruleset f [(cs, b)] e p = Accept.
Proof.
  intros f cs b e p H. rewrite eval_ruleset_singleton, H. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The hook-level iff bridges: the parser's input/forward hook verdict
    equals the per-chain verdict the existing theorems characterise.  These let
    every per-chain result transfer to the hook the packet actually hits. *)

Theorem input_hook_drop_iff_inbound_drop : forall e p,
  eval_hook hk_fuel global_hooks Hinput e p = Drop
  <-> eval_table hk_fuel global_chains global_inbound e p = Drop.
Proof.
  intros e p. unfold eval_hook. rewrite select_input.
  apply singleton_hook_drop.
Qed.

Theorem forward_hook_drop_iff_forward_drop : forall e p,
  eval_hook hk_fuel global_hooks Hforward e p = Drop
  <-> eval_table hk_fuel global_chains global_forward e p = Drop.
Proof.
  intros e p. unfold eval_hook. rewrite select_forward.
  apply singleton_hook_drop.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The security crux, RE-STATED at the hook level over the parser-emitted
    registration.  These are [world_ingress_locked_down] and
    [forward_unsolicited_dropped] — but about "what netfilter dispatches at the
    input/forward hook", not a chain the prover named. *)

(* INPUT hook: a new-state packet arriving on the world interface (ppp0) that is
   not ssh from 81.209.165.42 is DROPPED by whatever chain is registered at the
   input hook.  ([Router_Input.world_ingress_locked_down], lifted.) *)
Theorem input_hook_world_locked : forall e p,
  e = gen_env ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  Router_Input.world_loads p = true ->
  field_value FCtState e p = Router_Input.cts_new ->
  field_value FMetaIifname e p = Router_Input.if_ppp0 ->
  Router_Input.world_ssh e p = false ->
  eval_hook hk_fuel global_hooks Hinput e p = Drop.
Proof.
  intros e p Hpe Hl1 Hl2 Hwl Hct Hppp0 Hssh.
  apply input_hook_drop_iff_inbound_drop.
  apply world_ingress_locked_down; assumption.
Qed.

(* FORWARD hook: unsolicited world->private traffic (new ct-state, not arriving
   on the LAN interface eth1) is NOT forwarded — the NAT-router crux, now at the
   hook netfilter dispatches.  ([Router_Forward.forward_unsolicited_dropped], lifted.) *)
Theorem forward_hook_unsolicited_dropped : forall e p,
  e = gen_env ->
  field_value FCtState e p = Router_Forward.cts_new ->
  Router_Forward.iif_eth1 e p = false ->
  eval_hook hk_fuel global_hooks Hforward e p = Drop.
Proof.
  intros e p Hpe Hct Hiif.
  apply forward_hook_drop_iff_forward_drop.
  apply forward_unsolicited_dropped; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(** ** MUTATION KILL: a registration that swaps inbound<->forward onto each
    other's hooks.  Every per-chain theorem holds verbatim for it
    (none mention global_hooks), but the hook-level theorems FAIL — witnessed by
    a real LAN packet. *)

Definition global_hooks_bug : list hooked_chain :=
  [{| hc_hook := Hinput;       hc_prio := (0)%Z;   hc_env := global_chains; hc_base := global_forward |};
   {| hc_hook := Hforward;     hc_prio := (0)%Z;   hc_env := global_chains; hc_base := global_inbound |};
   {| hc_hook := Hpostrouting; hc_prio := (100)%Z; hc_env := global_chains; hc_base := global_postrouting |}].

(* pkt_lan_smtp = LAN packet on eth1, ct-new, unlisted service tcp/25.
   Proven DROPPED by the real input chain in Router_Private.pkt_lan_smtp_dropped. *)

(* At the CORRECT input hook the parser registers, the unlisted LAN service is
   dropped (inbound_private's service filter rejects tcp/25). *)
Theorem input_hook_smtp_correct_drop :
  eval_hook hk_fuel global_hooks Hinput env_lan pkt_lan_smtp = Drop.
Proof. vm_compute. reflexivity. Qed.

(* At the BUGGED input hook (global_forward registered there), the bare
   `iif eth1 accept` rule accepts the unlisted LAN service unconditionally —
   bypassing inbound_private's whole service filter. *)
Theorem input_hook_smtp_bug_accept :
  eval_hook hk_fuel global_hooks_bug Hinput env_lan pkt_lan_smtp = Accept.
Proof. vm_compute. reflexivity. Qed.

(* The observable: the parser's registration and the swapped one disagree on a
   real packet — so the hook-level theorems genuinely depend on the registration
   the parser emitted, not a chain the prover named. *)
Theorem hook_swap_observable :
  eval_hook hk_fuel global_hooks     Hinput env_lan pkt_lan_smtp
  <> eval_hook hk_fuel global_hooks_bug Hinput env_lan pkt_lan_smtp.
Proof.
  rewrite input_hook_smtp_correct_drop, input_hook_smtp_bug_accept. discriminate.
Qed.

(* The bugged registration FAILS input_hook_world_locked's conclusion shape:
   the world-locked theorem would be FALSE for global_hooks_bug, because the
   forward chain it puts at input accepts the LAN smtp packet that the locked
   input must drop.  (We witness the discriminating verdict directly.) *)
Theorem bug_breaks_input_lockdown :
  eval_hook hk_fuel global_hooks_bug Hinput env_lan pkt_lan_smtp <> Drop.
Proof. rewrite input_hook_smtp_bug_accept. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(** ** UNIFIED-SEMANTICS LICENSE (Semantics.v § "Projection 1b").

    The registration dispatches to the `global` chain env, which carries the
    ONE limiter rule ([Router_Private.r_icmp]) — not write-free, but
    LIMITER-TOLERANT — and, since M3, the postrouting MASQUERADE, whose NAT
    data plane (packet rewrite + [e_nat] store + possible NF_DROP) lives
    inside the fold and is OUTSIDE every pure-strand license (see
    [Router_Input] § "UNIFIED-SEMANTICS LICENSE").  The filter hooks are
    licensed over the NAT-free registration [global_tol_hooks] (their bases
    and jump env restricted to [Router_Input.global_tol_chains]); the
    postrouting hook is stated over the unified semantics ONLY
    ([postrouting_hook_masquerades] below; data-plane characterisation in
    Router_Reach / Router_NatHook; compiler axis in
    [Correct.compile_hook_u_correct]). *)

Definition global_tol_hooks : list hooked_chain :=
  map (fun hc => {| hc_hook := hc_hook hc; hc_prio := hc_prio hc;
                    hc_env := global_tol_chains; hc_base := hc_base hc |})
      (filter (fun hc => forallb rule_natfree (c_rules (hc_base hc))) global_hooks).

Lemma select_input_tol :
  select_hook global_tol_hooks Hinput = [(global_tol_chains, global_inbound)].
Proof. vm_compute. reflexivity. Qed.
Lemma select_forward_tol :
  select_hook global_tol_hooks Hforward = [(global_tol_chains, global_forward)].
Proof. vm_compute. reflexivity. Qed.
(* the masquerade hook has NO NAT-free registration: it is unified-only *)
Lemma select_postrouting_tol :
  select_hook global_tol_hooks Hpostrouting = [].
Proof. vm_compute. reflexivity. Qed.

Theorem input_hook_licensed : forall fuel e p,
  eval_hook fuel global_tol_hooks Hinput e p
  = fst (eval_hook_u Hinput fuel global_tol_hooks e p).
Proof.
  intros fuel e p. symmetry.
  apply (eval_hook_u_limiter_tolerant_1 Hinput fuel global_tol_hooks
           global_tol_chains global_inbound);
    [exact select_input_tol | vm_compute; reflexivity
     | exact global_chains_limiter_tol].
Qed.

Theorem forward_hook_licensed : forall fuel e p,
  eval_hook fuel global_tol_hooks Hforward e p
  = fst (eval_hook_u Hforward fuel global_tol_hooks e p).
Proof.
  intros fuel e p. symmetry.
  apply (eval_hook_u_limiter_tolerant_1 Hforward fuel global_tol_hooks
           global_tol_chains global_forward);
    [exact select_forward_tol | vm_compute; reflexivity
     | exact global_chains_limiter_tol].
Qed.

(* The masquerade hook is stated on the unified semantics: the write-free
   projection cannot see the NAT drop / packet rewrite, so the masquerade hook
   is characterised here on [eval_hook_u], with the data-plane facts in
   Router_Reach. *)
Theorem postrouting_hook_unified : forall fuel e p,
  eval_hook_u Hpostrouting (S fuel) global_hooks e p
  = match eval_table_u Hpostrouting (S fuel) global_chains global_postrouting e p with
    | (v, s) => if base_continues v then (Accept, s) else (v, s)
    end.
Proof.
  intros fuel e p. unfold eval_hook_u. rewrite select_postrouting.
  rewrite eval_ruleset_u_cons.
  destruct (eval_table_u Hpostrouting (S fuel) global_chains global_postrouting e p)
    as [v [e' p']].
  destruct (base_continues v); reflexivity.
Qed.

(** The mutation-kill registration (inbound<->forward swapped) is licensed
    too — over its NAT-free restriction, like the parser's. *)
Definition global_tol_hooks_bug : list hooked_chain :=
  map (fun hc => {| hc_hook := hc_hook hc; hc_prio := hc_prio hc;
                    hc_env := global_tol_chains; hc_base := hc_base hc |})
      (filter (fun hc => forallb rule_natfree (c_rules (hc_base hc))) global_hooks_bug).

Lemma select_input_bug :
  select_hook global_tol_hooks_bug Hinput = [(global_tol_chains, global_forward)].
Proof. vm_compute. reflexivity. Qed.

Theorem input_hook_bug_licensed : forall fuel e p,
  eval_hook fuel global_tol_hooks_bug Hinput e p
  = fst (eval_hook_u Hinput fuel global_tol_hooks_bug e p).
Proof.
  intros fuel e p. symmetry.
  apply (eval_hook_u_limiter_tolerant_1 Hinput fuel global_tol_hooks_bug
           global_tol_chains global_forward);
    [exact select_input_bug | vm_compute; reflexivity
     | exact global_chains_limiter_tol].
Qed.
