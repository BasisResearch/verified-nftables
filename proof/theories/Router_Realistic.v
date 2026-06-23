(** * router.nft new-connection security theorems, RE-STATED over a REALISTIC
      conntrack environment (the vacuity fix).

    The Round 2/3/4/6 "new-connection" theorems — [forward_unsolicited_dropped],
    [world_ingress_locked_down], [inbound_eth1_accept_iff], the hook lifts, etc. —
    each combine TWO jointly-UNSATISFIABLE hypotheses:

        pkt_env p = gen_env        AND        field_value FCtState p = cts_new.

    [field_value FCtState p] reduces (Syntax.v) to [do_load (LCt CKstate) p], whose
    only outcomes are: [pkt_untracked p] -> [0;0;0;64]; else [pkt_ct_present p] ->
    [e_ct (pkt_env p) (pkt_flow p) CKstate]; else -> [0;0;0;1].  Under
    [pkt_env p = gen_env], [gen_env] pins [e_ct = fun _ _ => []], so the present
    branch is [[]] and the only reachable ct-state values are [[0;0;0;64]], [[]],
    or [[0;0;0;1]].  [cts_new = [0;0;0;8]] is UNREACHABLE under [gen_env]: the two
    hypotheses are contradictory, so EVERY such theorem certifies ZERO real packets.
    (Worse: under those hypotheses BOTH Drop and Accept are provable, so a wide-open
    ruleset bug survives them all — see [ctstate_under_genenv_never_new] below for the
    axiom-free contradiction.)

    THE FIX (this file).  A vmap/set lookup only reads [e_vmap (pkt_env p) name] /
    [e_set ...]; it does NOT need the WHOLE env to equal [gen_env].  So we relax
    [pkt_env p = gen_env] to exactly what the lookups use — the [e_vmap] CONTENTS —
    while letting [e_ct] carry a real (NEW) value.  The witness envs the prior rounds
    used ([env_fwd], [env_in]) already set [e_vmap := e_vmap gen_env], so they meet
    the relaxed hypothesis AND carry [cts_new] through [e_ct]: the theorems below are
    therefore proven NON-VACUOUS on the SAME hypotheses they are stated with (the
    [*_witness_*] lemmas discharge every hypothesis on the concrete packet).

    What is re-stated here (all axiom-free, all about the PARSER's [global_*] chains):
      - [ctstate_under_genenv_never_new] : the contradiction itself, proven.
      - [forward_unsolicited_dropped_real] : unsolicited world->LAN never forwarded,
        over the realistic env — NON-VACUOUS (witness [pkt_world] meets the hyps).
      - [forward_accept_iff_real] : the exact forward characterisation, realistic.
      - [world_ingress_locked_down_real] : world-ingress lockdown, realistic + witness.
      - [inbound_world_ssh_accept_real] : the one allowed world flow, realistic + witness. *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Router_Gen.
From Nft Require Router_Forward Router_Input Router_Private Router_Hooks.
Import ListNotations.
Open Scope string_scope.

(* ============================================================ *)
(** ** 0. The vacuity is REAL: under [pkt_env p = gen_env] the ct-state can never be
       [cts_new].  Hence the old hypotheses are contradictory (axiom-free). *)

Lemma ctstate_under_genenv_never_new : forall p,
  pkt_env p = gen_env ->
  field_value FCtState p <> Router_Input.cts_new.
Proof.
  intros p Hpe.
  unfold field_value, do_load. cbn [field_load].
  unfold Router_Input.cts_new. rewrite Hpe.
  destruct (pkt_untracked p); cbn; [ discriminate | ].
  destruct (pkt_ct_present p); cbn;
    [ unfold gen_env, env_with_sets, base_env; cbn | ]; discriminate.
Qed.

(* ============================================================ *)
(** ** 1. Relaxed FORWARD unfold: parametrised by the [__map3] CONTENTS, not the
       whole env.  This is exactly [Router_Forward.forward_eval_unfold] with
       [pkt_env p = gen_env] replaced by [e_vmap (pkt_env p) "__map3" = map3]. *)

Import Router_Forward.

(* The vmap contents the parser emitted, exposed as an env-relative fact (the
   realistic envs set [e_vmap := e_vmap gen_env], so they satisfy this). *)
Lemma e_vmap_map3_gen : e_vmap gen_env "__map3" = map3.
Proof. reflexivity. Qed.

Lemma forward_eval_unfold_real : forall p,
  e_vmap (pkt_env p) "__map3" = map3 ->
  eval_table fw_fuel global_chains global_forward p =
    (if data_eqb cts_established (field_value FCtState p) then Accept
     else if data_eqb cts_related (field_value FCtState p) then Accept
     else if data_eqb cts_invalid (field_value FCtState p) then Drop
     else if iif_eth1 p then Accept else Drop).
Proof.
  intros p Hvm.
  unfold eval_table, fw_fuel, global_forward, global_chains.
  cbn [c_rules c_policy].
  rewrite Router_Forward.erj_cons.
  unfold rule_loadable, rule_applies, outcome, outcome_core;
    cbn -[eval_rules_j assoc_verdict pkt_env field_value iif_eth1].
  (* The ct vmap key is [field_value FCtState p]; the lookup table is
     [e_vmap (pkt_env p) "__map3"], which the hypothesis pins to [map3]. *)
  rewrite Hvm.
  rewrite assoc_map3_eq.
  destruct (data_eqb cts_established (field_value FCtState p)) eqn:He;
    [ cbn -[eval_rules_j]; reflexivity | ].
  destruct (data_eqb cts_related (field_value FCtState p)) eqn:Hr;
    [ cbn -[eval_rules_j]; reflexivity | ].
  destruct (data_eqb cts_invalid (field_value FCtState p)) eqn:Hi;
    [ cbn -[eval_rules_j]; reflexivity | ].
  cbn -[eval_rules_j data_eqb field_value eval_matchcond_body iif_eth1].
  rewrite Router_Forward.erj_cons.
  change {| r_body := [BMatch (MEq FMetaIifname
              [101;116;104;49;0;0;0;0;0;0;0;0;0;0;0;0])];
            r_verdict := Accept; r_vmap := None; r_nat := None;
            r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}
    with r2_fwd.
  rewrite r2_loadable, r2_applies, r2_outcome. cbn [andb].
  destruct (iif_eth1 p) eqn:Heq;
    cbn -[eval_rules_j iif_eth1]; rewrite ?Router_Forward.erj_nil; reflexivity.
Qed.

(** The realistic, NON-VACUOUS forward characterisation: the forward chain accepts
    iff one of the three faithful accept paths holds.  Stated over the relaxed env
    hypothesis (only the [__map3] contents), so a real NEW packet satisfies it. *)
Theorem forward_accept_iff_real : forall p,
  e_vmap (pkt_env p) "__map3" = map3 ->
  ( eval_table fw_fuel global_chains global_forward p = Accept
    <->
    ( field_value FCtState p = cts_established
      \/ field_value FCtState p = cts_related
      \/ ( field_value FCtState p <> cts_invalid
           /\ iif_eth1 p = true ) ) ).
Proof.
  intros p Hvm. rewrite (forward_eval_unfold_real p Hvm).
  destruct (data_eqb cts_established (field_value FCtState p)) eqn:Hest.
  { apply data_eqb_true_iff in Hest. split; [ intros _ | reflexivity ]. auto. }
  destruct (data_eqb cts_related (field_value FCtState p)) eqn:Hrel.
  { apply data_eqb_true_iff in Hrel. split; [ intros _ | reflexivity ]. auto. }
  destruct (data_eqb cts_invalid (field_value FCtState p)) eqn:Hinv.
  { apply data_eqb_true_iff in Hinv. split.
    - discriminate.
    - intros [He | [He | [Hni _]]].
      + rewrite <- He in Hest; rewrite data_eqb_refl in Hest; discriminate.
      + rewrite <- He in Hrel; rewrite data_eqb_refl in Hrel; discriminate.
      + exfalso; apply Hni; rewrite <- Hinv; reflexivity. }
  split.
  - intro Hacc.
    destruct (iif_eth1 p) eqn:Heq; [ | discriminate Hacc ].
    right; right; split; [ | reflexivity ].
    intro Hc. rewrite <- Hc in Hinv. rewrite data_eqb_refl in Hinv; discriminate.
  - intros [He | [He | [_ Heq]]].
    + rewrite <- He in Hest; rewrite data_eqb_refl in Hest; discriminate.
    + rewrite <- He in Hrel; rewrite data_eqb_refl in Hrel; discriminate.
    + rewrite Heq. reflexivity.
Qed.

(** THE CRUX, realistic: a NEW (unsolicited) packet whose ingress is NOT eth1 is
    DROPPED — world(ppp0)->LAN is never forwarded — over a realistic conntrack env. *)
Theorem forward_unsolicited_dropped_real : forall p,
  e_vmap (pkt_env p) "__map3" = map3 ->
  field_value FCtState p = cts_new ->
  iif_eth1 p = false ->
  eval_table fw_fuel global_chains global_forward p = Drop.
Proof.
  intros p Hvm Hct Hiif.
  rewrite (forward_eval_unfold_real p Hvm), Hct, Hiif. vm_compute. reflexivity.
Qed.

(** NON-VACUITY: the prior round's concrete witness [pkt_world] (NEW on ppp0)
    satisfies EVERY hypothesis of [forward_unsolicited_dropped_real] — including the
    relaxed env hypothesis — so the theorem constrains a REAL packet. *)
Lemma pkt_world_vmap3 : e_vmap (pkt_env pkt_world) "__map3" = map3.
Proof. reflexivity. Qed.

Theorem forward_unsolicited_dropped_witnessed :
  eval_table fw_fuel global_chains global_forward pkt_world = Drop.
Proof.
  apply (forward_unsolicited_dropped_real pkt_world
           pkt_world_vmap3 pkt_world_ct pkt_world_iif).
Qed.

(* ============================================================ *)
(** ** 2. Relaxed INPUT unfold: parametrised by the [__map1] (ct-state) and [__map2]
       (iifname) CONTENTS, not the whole env.  This is exactly
       [Router_Input.inbound_eval_unfold] with [pkt_env p = gen_env] replaced by the
       two vmap-content equalities, so a real NEW packet on ppp0 satisfies it. *)

Import Router_Input.

Lemma inbound_eval_unfold_real : forall p,
  e_vmap (pkt_env p) "__map1" = map1 ->
  e_vmap (pkt_env p) "__map2" = map2 ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  eval_table in_fuel global_chains global_inbound p =
    (if data_eqb cts_established (ct_key p) then Accept
     else if data_eqb cts_related (ct_key p) then Accept
     else if data_eqb cts_invalid (ct_key p) then Drop
     else
       if data_eqb if_lo (iif_key p) then Accept
       else if data_eqb if_ppp0 (iif_key p) then (if world_ssh p then Accept else Drop)
       else if data_eqb if_eth1 (iif_key p)
            then match eval_rules_j 6 global_chains (c_rules global_inbound_private) p with
                 | Some v => v | None => Drop end
            else Drop).
Proof.
  intros p Hvm1 Hvm2 Hct Hiif Hwl.
  unfold eval_table, in_fuel. rewrite c_rules_inbound.
  (* rule 1: ct vmap *)
  rewrite Router_Input.erj_cons.
  rewrite (r_ct_loadable p Hct), r_ct_applies. cbn [andb].
  rewrite r_ct_outcome.
  rewrite Hvm1. rewrite assoc_map1_eq.
  unfold ct_key.
  destruct (data_eqb cts_established (field_value FCtState p)) eqn:He; [ reflexivity | ].
  destruct (data_eqb cts_related (field_value FCtState p)) eqn:Hr; [ reflexivity | ].
  destruct (data_eqb cts_invalid (field_value FCtState p)) eqn:Hi; [ reflexivity | ].
  (* ct vmap MISS: fall through to rule 2 (iif vmap) *)
  rewrite Router_Input.erj_cons.
  rewrite (r_iif_loadable p Hiif), r_iif_applies. cbn [andb].
  rewrite r_iif_outcome.
  rewrite Hvm2. rewrite assoc_map2_eq.
  unfold iif_key.
  destruct (data_eqb if_lo (field_value FMetaIifname p)) eqn:Hlo; [ reflexivity | ].
  destruct (data_eqb if_ppp0 (field_value FMetaIifname p)) eqn:Hppp0.
  { rewrite lookup_world.
    replace (eval_rules_j 6 global_chains (c_rules global_inbound_world) p)
      with (if world_ssh p then Some Accept else None)
      by (symmetry; apply (inbound_world_eval 5 p Hwl)).
    destruct (world_ssh p); rewrite ?Router_Input.erj_empty; reflexivity. }
  destruct (data_eqb if_eth1 (field_value FMetaIifname p)) eqn:Heth1.
  { rewrite lookup_private.
    destruct (eval_rules_j 6 global_chains (c_rules global_inbound_private) p) eqn:Hpriv;
      [ reflexivity | rewrite ?Router_Input.erj_empty; reflexivity ]. }
  rewrite ?Router_Input.erj_empty. reflexivity.
Qed.

(** THE CRUX, realistic + non-vacuous: a NEW packet on ppp0 (the world) that is NOT
    exactly ssh (tcp/22) from 81.209.165.42 is DROPPED.  Stated over the relaxed env
    hypothesis (only the [__map1]/[__map2] contents), so a real NEW packet — with a
    conntrack entry that reads NEW — satisfies every hypothesis. *)
Theorem world_ingress_locked_down_real : forall p,
  e_vmap (pkt_env p) "__map1" = map1 ->
  e_vmap (pkt_env p) "__map2" = map2 ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_ppp0 ->
  world_ssh p = false ->
  eval_table in_fuel global_chains global_inbound p = Drop.
Proof.
  intros p Hvm1 Hvm2 Hct Hiif Hwl Hcts Hppp0 Hssh.
  rewrite (inbound_eval_unfold_real p Hvm1 Hvm2 Hct Hiif Hwl).
  unfold ct_key, iif_key. rewrite Hcts, Hppp0.
  rewrite new_neq_estab, new_neq_rel, new_neq_inv, lo_neq_ppp0.
  rewrite data_eqb_refl, Hssh. reflexivity.
Qed.

(** The single allowed world flow IS accepted (lockdown non-vacuous), realistic env. *)
Theorem inbound_world_ssh_accept_real : forall p,
  e_vmap (pkt_env p) "__map1" = map1 ->
  e_vmap (pkt_env p) "__map2" = map2 ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_ppp0 ->
  world_ssh p = true ->
  eval_table in_fuel global_chains global_inbound p = Accept.
Proof.
  intros p Hvm1 Hvm2 Hct Hiif Hwl Hcts Hppp0 Hssh.
  rewrite (inbound_eval_unfold_real p Hvm1 Hvm2 Hct Hiif Hwl).
  unfold ct_key, iif_key. rewrite Hcts, Hppp0.
  rewrite new_neq_estab, new_neq_rel, new_neq_inv, lo_neq_ppp0.
  rewrite data_eqb_refl, Hssh. reflexivity.
Qed.

(** NON-VACUITY for the input crux.  The prior round's witnesses [pkt_world_ssh]
    (allowed) and [pkt_world_bad] (wrong source) use [env_in], whose [e_vmap] IS
    [e_vmap gen_env], so they satisfy the relaxed [__map1]/[__map2] hypotheses AND
    carry [cts_new] through [e_ct].  Hence they meet EVERY hypothesis of the realistic
    theorems jointly — the vacuity is gone. *)
Lemma pkt_world_ssh_vmaps :
  e_vmap (pkt_env pkt_world_ssh) "__map1" = map1
  /\ e_vmap (pkt_env pkt_world_ssh) "__map2" = map2.
Proof. split; reflexivity. Qed.

Lemma pkt_world_bad_vmaps :
  e_vmap (pkt_env pkt_world_bad) "__map1" = map1
  /\ e_vmap (pkt_env pkt_world_bad) "__map2" = map2.
Proof. split; reflexivity. Qed.

(* The wrong-source world packet IS dropped, derived through the REALISTIC theorem on
   its own (satisfied) hypotheses — not vacuously. *)
Theorem world_locked_down_witnessed :
  eval_table in_fuel global_chains global_inbound pkt_world_bad = Drop.
Proof.
  destruct pkt_world_bad_vmaps as [Hv1 Hv2].
  destruct pkt_world_bad_facts as (Hct & Hiif & Hwl & Hcts & Hppp0 & Hssh).
  apply (world_ingress_locked_down_real pkt_world_bad Hv1 Hv2 Hct Hiif Hwl Hcts Hppp0 Hssh).
Qed.

(* The allowed ssh-from-81.209.165.42 packet IS accepted, through the realistic
   theorem on its own satisfied hypotheses. *)
Theorem world_ssh_accept_witnessed :
  eval_table in_fuel global_chains global_inbound pkt_world_ssh = Accept.
Proof.
  destruct pkt_world_ssh_vmaps as [Hv1 Hv2].
  destruct pkt_world_ssh_loads as (Hct & Hiif & Hwl & Hcts & Hppp0 & Hssh).
  apply (inbound_world_ssh_accept_real pkt_world_ssh Hv1 Hv2 Hct Hiif Hwl Hcts Hppp0 Hssh).
Qed.

(* ============================================================ *)
(** ** 2b. Relaxed PRIVATE (eth1->inbound_private) characterisation.  Round 4's
       [inbound_eth1_accept_iff] was ALSO vacuous (same [pkt_env = gen_env] +
       [cts_new]).  The private sub-chain's lookups read only [e_vmap "__map0"] (the
       concat-service vmap) and [e_limit] (the icmp rate limit, kept ABSTRACT in
       [icmp_ok]); they do NOT need the whole env.  We relax to the [__map0]/[__map1]/
       [__map2] contents and lift to a realistic, non-vacuous iff. *)

Import Router_Private.

Lemma inbound_private_eval_real : forall n p,
  e_vmap (pkt_env p) "__map0" = map0 ->
  icmp_loads p = true ->
  svc_loads p = true ->
  eval_rules_j (S (S n)) global_chains (c_rules global_inbound_private) p =
    (if icmp_ok p then Some Accept else svc_hit p).
Proof.
  intros n p Hvm Hil Hsl.
  rewrite c_rules_private.
  rewrite Router_Input.erj_cons.
  rewrite (r_icmp_loadable p Hil), (r_icmp_applies p Hil). cbn [andb].
  destruct (icmp_ok p) eqn:Hok.
  { rewrite r_icmp_outcome. reflexivity. }
  rewrite Router_Input.erj_cons.
  rewrite (r_svc_loadable p Hsl), r_svc_applies. cbn [andb].
  rewrite r_svc_outcome.
  rewrite Hvm.
  unfold svc_hit, svc_key.
  destruct (assoc_verdict
              (List.concat (map (fun f => field_value f p) [FIp4Protocol; FThDport]))
              map0) eqn:Hhit.
  { assert (Hv : v = Accept) by (apply (svc_hit_accept p); unfold svc_hit, svc_key; exact Hhit).
    subst v. reflexivity. }
  rewrite Router_Input.erj_empty. reflexivity.
Qed.

Lemma inbound_eth1_eval_real : forall p,
  e_vmap (pkt_env p) "__map0" = map0 ->
  e_vmap (pkt_env p) "__map1" = map1 ->
  e_vmap (pkt_env p) "__map2" = map2 ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  icmp_loads p = true ->
  svc_loads p = true ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = Router_Input.if_eth1 ->
  eval_table in_fuel global_chains global_inbound p =
    (if icmp_ok p then Accept
     else match svc_hit p with Some v => v | None => Drop end).
Proof.
  intros p Hvm0 Hvm1 Hvm2 Hct Hiif Hwl Hil Hsl Hcts Heth1.
  rewrite (inbound_eval_unfold_real p Hvm1 Hvm2 Hct Hiif Hwl).
  unfold ct_key, iif_key. rewrite Hcts, Heth1.
  rewrite new_neq_estab, new_neq_rel, new_neq_inv.
  change (data_eqb if_lo Router_Input.if_eth1) with false.
  change (data_eqb if_ppp0 Router_Input.if_eth1) with false.
  rewrite data_eqb_refl.
  change 6 with (S (S 4)).
  rewrite (inbound_private_eval_real 4 p Hvm0 Hil Hsl).
  destruct (icmp_ok p); [ reflexivity | ].
  destruct (svc_hit p) as [v|]; reflexivity.
Qed.

(** THE LAN-INGRESS CRUX, realistic + non-vacuous (mirrors [inbound_eth1_accept_iff]):
    a NEW packet ingressing on eth1 is ACCEPTED iff it is a rate-limited icmp echo OR
    one of the four listed services (ssh / dns-tcp / dns-udp / dhcp).  Over a realistic
    conntrack env, so a real LAN packet satisfies it. *)
Theorem inbound_eth1_accept_iff_real : forall p,
  e_vmap (pkt_env p) "__map0" = map0 ->
  e_vmap (pkt_env p) "__map1" = map1 ->
  e_vmap (pkt_env p) "__map2" = map2 ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  icmp_loads p = true ->
  svc_loads p = true ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = Router_Input.if_eth1 ->
  ( eval_table in_fuel global_chains global_inbound p = Accept <->
    ( icmp_ok p = true \/
      ( svc_key p = [6;0;22] \/ svc_key p = [17;0;53]
        \/ svc_key p = [6;0;53] \/ svc_key p = [17;0;67] ) ) ).
Proof.
  intros p Hvm0 Hvm1 Hvm2 Hct Hiif Hwl Hil Hsl Hcts Heth1.
  rewrite (inbound_eth1_eval_real p Hvm0 Hvm1 Hvm2 Hct Hiif Hwl Hil Hsl Hcts Heth1).
  split.
  - intro H. destruct (icmp_ok p) eqn:Hok; [ now left | ].
    right. apply svc_hit_iff.
    destruct (svc_hit p) as [v|] eqn:Hh.
    + apply svc_hit_accept in Hh as Hv. now subst v.
    + discriminate H.
  - intro H. destruct H as [Hok | Hsvc].
    + rewrite Hok. reflexivity.
    + destruct (icmp_ok p); [ reflexivity | ].
      apply svc_hit_iff in Hsvc. rewrite Hsvc. reflexivity.
Qed.

(** NON-VACUITY for the LAN crux.  The prior round's witnesses [pkt_lan_dns]
    (a listed service: udp/53) and [pkt_lan_smtp] (an unlisted service) use [env_lan],
    whose [e_vmap] IS [e_vmap gen_env]; they meet the relaxed [__map0]/[__map1]/[__map2]
    hypotheses and carry [cts_new]/[e_limit] through the env. *)
Lemma pkt_lan_dns_vmaps :
  e_vmap (pkt_env pkt_lan_dns) "__map0" = map0
  /\ e_vmap (pkt_env pkt_lan_dns) "__map1" = map1
  /\ e_vmap (pkt_env pkt_lan_dns) "__map2" = map2.
Proof. repeat split; reflexivity. Qed.

Theorem pkt_lan_dns_accepted_real :
  eval_table in_fuel global_chains global_inbound pkt_lan_dns = Accept.
Proof.
  destruct pkt_lan_dns_vmaps as (Hv0 & Hv1 & Hv2).
  destruct pkt_lan_dns_facts as (Hct & Hiif & Hwl & Hil & Hsl & Hcts & Heth1 & Hsvc).
  apply (inbound_eth1_accept_iff_real pkt_lan_dns
           Hv0 Hv1 Hv2 Hct Hiif Hwl Hil Hsl Hcts Heth1).
  right. right. left. exact Hsvc.
Qed.

(* ============================================================ *)
(** ** 3. HOOK-LEVEL lifts, realistic.  Round 6's [input_hook_world_locked] and
       [forward_hook_unsolicited_dropped] were ALSO vacuous (same [pkt_env = gen_env]
       + [cts_new]).  The registration bridges [input_hook_drop_iff_inbound_drop] /
       [forward_hook_drop_iff_forward_drop] are NON-vacuous (no env hypothesis), so
       we lift the realistic CHAIN theorems through them to realistic HOOK theorems
       — what netfilter actually dispatches at each hook, on REAL packets. *)

Import Router_Hooks.

(* [hk_fuel] = [in_fuel] = [fw_fuel] = 8, so the bridge connects to our chain
   theorems directly. *)
Lemma hk_in_fuel : hk_fuel = in_fuel. Proof. reflexivity. Qed.
Lemma hk_fw_fuel : hk_fuel = fw_fuel. Proof. reflexivity. Qed.

(* INPUT hook, realistic: a NEW packet on ppp0 that is not ssh-from-the-allowed-host
   is DROPPED by whatever chain netfilter registers at the input hook. *)
Theorem input_hook_world_locked_real : forall p,
  e_vmap (pkt_env p) "__map1" = map1 ->
  e_vmap (pkt_env p) "__map2" = map2 ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  Router_Input.world_loads p = true ->
  field_value FCtState p = Router_Input.cts_new ->
  field_value FMetaIifname p = Router_Input.if_ppp0 ->
  Router_Input.world_ssh p = false ->
  eval_hook hk_fuel global_hooks Hinput p = Drop.
Proof.
  intros p Hv1 Hv2 Hl1 Hl2 Hwl Hct Hppp0 Hssh.
  apply input_hook_drop_iff_inbound_drop.
  apply (world_ingress_locked_down_real p Hv1 Hv2 Hl1 Hl2 Hwl Hct Hppp0 Hssh).
Qed.

(* FORWARD hook, realistic: unsolicited world->LAN (NEW, not eth1) is NOT forwarded
   by whatever chain netfilter registers at the forward hook. *)
Theorem forward_hook_unsolicited_dropped_real : forall p,
  e_vmap (pkt_env p) "__map3" = map3 ->
  field_value FCtState p = Router_Forward.cts_new ->
  Router_Forward.iif_eth1 p = false ->
  eval_hook hk_fuel global_hooks Hforward p = Drop.
Proof.
  intros p Hvm Hct Hiif.
  apply forward_hook_drop_iff_forward_drop.
  apply (forward_unsolicited_dropped_real p Hvm Hct Hiif).
Qed.

(* NON-VACUITY at the hook level: the concrete witnesses meet the hook theorems'
   relaxed hypotheses, so netfilter's dispatch DROPS them for real. *)
Theorem input_hook_world_locked_witnessed :
  eval_hook hk_fuel global_hooks Hinput pkt_world_bad = Drop.
Proof.
  destruct pkt_world_bad_vmaps as [Hv1 Hv2].
  destruct pkt_world_bad_facts as (Hct & Hiif & Hwl & Hcts & Hppp0 & Hssh).
  apply (input_hook_world_locked_real pkt_world_bad Hv1 Hv2 Hct Hiif Hwl Hcts Hppp0 Hssh).
Qed.

Theorem forward_hook_unsolicited_dropped_witnessed :
  eval_hook hk_fuel global_hooks Hforward pkt_world = Drop.
Proof.
  apply (forward_hook_unsolicited_dropped_real pkt_world
           pkt_world_vmap3 pkt_world_ct pkt_world_iif).
Qed.
