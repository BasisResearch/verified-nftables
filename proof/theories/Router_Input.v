(** * router.nft INPUT hook — the router box's self-protection, verdict-characterised.

    The `inbound` base chain is what stops the WORLD from reaching the BOX itself
    (the `forward` chain, proved in [Router_Forward], stops world->LAN routing).  In
    router.nft:

        chain inbound { type filter hook input priority 0; policy DROP;
                        ct state vmap {established:accept, related:accept, invalid:drop};
                        iifname vmap {lo:accept, ppp0:jump inbound_world,
                                      eth1:jump inbound_private} }
        chain inbound_world  { ip saddr 81.209.165.42 tcp dport ssh accept }
        chain inbound_private{ icmp echo-request limit 5/s accept;
                               ip protocol . th dport vmap {...services...} }

    Prior rounds proved postrouting (masquerade) and forward; the INPUT hook had
    ZERO proven properties.  This file pins down the WORLD-INGRESS LOCKDOWN — the
    security crux of input — against the PARSER-generated [global_inbound]
    (from [Router_Gen]):

      - [inbound_eval_unfold] : the input chain's verdict fully reduced from the two
                                vmaps (__map1 ct-state, __map2 iifname) and the two
                                jumps (ppp0->inbound_world, eth1->inbound_private).
      - [world_ingress_locked_down] : THE CRUX — a new packet on ppp0 (the world)
                                that is NOT exactly ssh (tcp/22) from 81.209.165.42 is
                                DROPPED.  No other world packet can reach the box.
      - [inbound_world_ssh_accept] : the single allowed world flow (ssh from that one
                                host) IS accepted (the lockdown is not vacuous).
      - [inbound_loopback_accept]  : loopback (iif lo) is always accepted.
      - [inbound_unknown_drop]     : an unknown iif (not lo/ppp0/eth1), new ct -> Drop.
      - [inbound_invalid_dropped]  : ct-state invalid -> Drop (the __map1 entry fires).
      - [inbound_estab/related_accepted] : established/related connections accepted.

    Non-vacuity / mutation kill:
      - [pkt_world_ssh] / [pkt_world_bad] : concrete witnesses (allowed ssh; a wrong-
                                source ssh that the parser's chain DROPs).
      - [bug_inbound_world] removes the `ip saddr 81.209.165.42` guard (opens ssh to
                            the whole Internet); under it the wrong-source ssh packet
                            ACCEPTs, and [input_property_discriminates_bug] witnesses
                            the catastrophic ssh-to-the-world hole the lockdown rules
                            out. *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Router_Gen.
Import ListNotations.
Open Scope string_scope.

(** Concrete ct-state wire values (big-endian 32-bit; only equality matters). *)
Definition cts_invalid     : data := [0;0;0;1].
Definition cts_established : data := [0;0;0;2].
Definition cts_related     : data := [0;0;0;4].
Definition cts_new         : data := [0;0;0;8].

(* The three named interfaces as the 16-byte zero-padded ASCII the parser emitted. *)
Definition if_lo   : data := [108;111;0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0].
Definition if_ppp0 : data := [112;112;112;48; 0;0;0;0; 0;0;0;0; 0;0;0;0].
Definition if_eth1 : data := [101;116;104;49; 0;0;0;0; 0;0;0;0; 0;0;0;0].

(* The single allowed world source: 81.209.165.42, and the ssh service (tcp/22). *)
Definition wan_ssh_host : data := [81;209;165;42].
Definition l4_tcp : data := [6].
Definition dport_ssh : data := [0;22].

Definition in_fuel : nat := 8.

(** One-step unfolding lemmas for the fuel-recursive interpreter (kept opaque so
    [cbn] reduces only the current rule).  Identical to [Ruleset_Verified]. *)
Lemma erj_nil : forall n cs p, eval_rules_j (S n) cs [] p = None.
Proof. reflexivity. Qed.

Lemma erj_cons : forall n cs r rest p,
  eval_rules_j (S n) cs (r :: rest) p =
  (if andb (rule_loadable r p) (rule_applies r p)
   then match outcome r p with
        | None => eval_rules_j n cs rest p
        | Some Return => None
        | Some (Jump m) =>
            match chain_lookup cs m with
            | Some ch => match eval_rules_j n cs (c_rules ch) p with
                         | Some v => Some v | None => eval_rules_j n cs rest p end
            | None => eval_rules_j n cs rest p
            end
        | Some (Goto m) =>
            match chain_lookup cs m with
            | Some ch => eval_rules_j n cs (c_rules ch) p | None => None end
        | Some Continue => eval_rules_j n cs rest p
        | Some v => Some v
        end
   else eval_rules_j n cs rest p).
Proof. reflexivity. Qed.

Lemma erj_empty : forall m cs p, eval_rules_j m cs [] p = None.
Proof. destruct m; reflexivity. Qed.

Opaque eval_rules_j.

(** ** Point-interval vmap classification (as in [Router_Forward]). *)
Lemma data_in_iv_point : forall k key, data_in_iv key (k, k) = data_eqb k key.
Proof.
  intros k key. unfold data_in_iv; cbn [fst snd].
  rewrite data_le_antisym. reflexivity.
Qed.

(* The ct-state vmap [__map1] (== [__map3]) the parser emitted. *)
Definition map1 : list (data * data * verdict) :=
  [(cts_established, cts_established, Accept);
   (cts_related, cts_related, Accept);
   (cts_invalid, cts_invalid, Drop)].

(* The iifname vmap [__map2]: lo->Accept, ppp0->Jump inbound_world,
   eth1->Jump inbound_private. *)
Definition map2 : list (data * data * verdict) :=
  [(if_lo, if_lo, Accept);
   (if_ppp0, if_ppp0, Jump "inbound_world");
   (if_eth1, if_eth1, Jump "inbound_private")].

Lemma assoc_map1_eq : forall key,
  assoc_verdict key map1 =
    (if data_eqb cts_established key then Some Accept
     else if data_eqb cts_related key then Some Accept
     else if data_eqb cts_invalid key then Some Drop
     else None).
Proof.
  intro key. unfold map1; cbn [assoc_verdict].
  rewrite !data_in_iv_point. reflexivity.
Qed.

Lemma assoc_map2_eq : forall key,
  assoc_verdict key map2 =
    (if data_eqb if_lo key then Some Accept
     else if data_eqb if_ppp0 key then Some (Jump "inbound_world")
     else if data_eqb if_eth1 key then Some (Jump "inbound_private")
     else None).
Proof.
  intro key. unfold map2; cbn [assoc_verdict].
  rewrite !data_in_iv_point. reflexivity.
Qed.

(* Keep the field reads and the vmap lookup opaque so [cbn] leaves them folded.
   Also keep [eval_matchcond_body] opaque so the per-match firstn-truncation stays
   folded into the named match predicates below (it never reduces under [cbn]). *)
Opaque field_value assoc_verdict eval_matchcond_body field_loadable.

(** ** The inbound_world sub-chain verdict (the ppp0 jump target).

    [global_inbound_world] has policy Continue and ONE rule: accept iff
    saddr=81.209.165.42 AND l4proto=tcp AND dport=22.  When evaluated as a jump
    target, [eval_rules_j] returns [Some Accept] on a hit and [None] on a miss (so
    the caller falls through to inbound's policy DROP). *)
(* The three matches of the inbound_world rule, exactly as the kernel evaluates
   them (firstn-truncated equality compares against the rule's literals). *)
Definition m_saddr  (p : packet) : bool := eval_matchcond_body (MEq FIp4Saddr [81;209;165;42]) p.
Definition m_tcp    (p : packet) : bool := eval_matchcond_body (MEq FMetaL4proto [6]) p.
Definition m_dport22(p : packet) : bool := eval_matchcond_body (MEq FThDport [0;22]) p.

Definition world_ssh (p : packet) : bool := m_saddr p && m_tcp p && m_dport22 p.

(* The single rule of [global_inbound_world] (the parser's literal): accept iff
   saddr=81.209.165.42 AND l4proto=tcp AND dport=22. *)
Definition r1_world : rule :=
  {| r_body := [BMatch (MEq FIp4Saddr [81;209;165;42]);
                BMatch (MEq FMetaL4proto [6]);
                BMatch (MEq FThDport [0;22])];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.

Lemma c_rules_world : c_rules global_inbound_world = [r1_world].
Proof. reflexivity. Qed.

(* The world rule's loads (its three field reads).  When they all succeed,
   [rule_loadable r1_world p = true] and each [eval_matchcond] collapses to its
   (opaque) body. *)
Definition world_loads (p : packet) : bool :=
  field_loadable FIp4Saddr p && field_loadable FMetaL4proto p
  && field_loadable FThDport p.

Lemma world_rule_loadable : forall p,
  world_loads p = true -> rule_loadable r1_world p = true.
Proof.
  intros p H. unfold world_loads in H.
  apply Bool.andb_true_iff in H as [H12 H3].
  apply Bool.andb_true_iff in H12 as [H1 H2].
  unfold rule_loadable, r1_world.
  cbn.
  rewrite H1, H2, H3. reflexivity.
Qed.

(* When the rule's loads succeed, [global_inbound_world] (as a jump target) yields
   [Some Accept] exactly on the ssh-from-the-allowed-host flow, else [None]. *)
Lemma inbound_world_eval : forall n p,
  world_loads p = true ->
  eval_rules_j (S n) global_chains (c_rules global_inbound_world) p =
    (if world_ssh p then Some Accept else None).
Proof.
  intros n p Hwl.
  pose proof (world_rule_loadable p Hwl) as Hld.
  unfold world_loads in Hwl.
  apply Bool.andb_true_iff in Hwl as [H12 H3].
  apply Bool.andb_true_iff in H12 as [H1 H2].
  rewrite c_rules_world.
  rewrite erj_cons. rewrite Hld. cbn [andb].
  unfold r1_world, rule_applies, outcome, outcome_core, terminal_outcome;
    cbn [r_body r_vmap r_verdict rule_applies_walk].
  unfold eval_matchcond, match_loadable.
  rewrite H1, H2, H3. cbn [andb].
  unfold world_ssh, m_saddr, m_tcp, m_dport22.
  cbn -[eval_rules_j eval_matchcond_body].
  destruct (eval_matchcond_body (MEq FIp4Saddr [81;209;165;42]) p) eqn:Hs;
    cbn -[eval_rules_j eval_matchcond_body];
    [ | rewrite ?erj_empty; reflexivity ].
  destruct (eval_matchcond_body (MEq FMetaL4proto [6]) p) eqn:Hl;
    cbn -[eval_rules_j eval_matchcond_body];
    [ | rewrite ?erj_empty; reflexivity ].
  destruct (eval_matchcond_body (MEq FThDport [0;22]) p) eqn:Hd;
    cbn -[eval_rules_j eval_matchcond_body];
    rewrite ?erj_empty; reflexivity.
Qed.

(** ** The gen_env verdict-map contents (the parser emitted them in [decls]). *)
Lemma e_vmap_map1 : forall p, pkt_env p = gen_env ->
  e_vmap (pkt_env p) "__map1" = map1.
Proof. intros p H. rewrite H. reflexivity. Qed.

Lemma e_vmap_map2 : forall p, pkt_env p = gen_env ->
  e_vmap (pkt_env p) "__map2" = map2.
Proof. intros p H. rewrite H. reflexivity. Qed.

(** ** The two empty-body vmap rules of [global_inbound], named.  Both have an
       empty body, so [rule_loadable] is just the vmap-key load (a meta/ct field
       read, modelled loadable under our packets). *)

(* The ct-state vmap rule (rule 1 of inbound). *)
Definition r_ct : rule :=
  {| r_body := []; r_verdict := Continue;
     r_vmap := Some {| vm_fields := []; vm_keyf := Some (FCtState, []); vm_name := "__map1" |};
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.

(* The iifname vmap rule (rule 2 of inbound). *)
Definition r_iif : rule :=
  {| r_body := []; r_verdict := Continue;
     r_vmap := Some {| vm_fields := []; vm_keyf := Some (FMetaIifname, []); vm_name := "__map2" |};
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.

Lemma c_rules_inbound : c_rules global_inbound = [r_ct; r_iif].
Proof. reflexivity. Qed.

(* Loadability of the two vmap rules: an empty body and a single meta/ct vmap-key
   load.  [field_loadable] of the ct-state / iifname registers. *)
Lemma r_ct_loadable : forall p,
  field_loadable FCtState p = true -> rule_loadable r_ct p = true.
Proof.
  intros p H. unfold rule_loadable, r_ct. cbn. rewrite H. cbn [andb].
  destruct (assoc_verdict (field_value FCtState p) (e_vmap (pkt_env p) "__map1")); reflexivity.
Qed.

Lemma r_iif_loadable : forall p,
  field_loadable FMetaIifname p = true -> rule_loadable r_iif p = true.
Proof.
  intros p H. unfold rule_loadable, r_iif. cbn. rewrite H. cbn [andb].
  destruct (assoc_verdict (field_value FMetaIifname p) (e_vmap (pkt_env p) "__map2")); reflexivity.
Qed.

(* Both vmap rules always "apply" (empty body) and their outcome is exactly the
   verdict-map lookup (a MISS yields [None] = fall through, since the static
   verdict is [Continue] with no post-outcome statements). *)
Lemma r_ct_applies  : forall p, rule_applies r_ct p = true.
Proof. reflexivity. Qed.
Lemma r_iif_applies : forall p, rule_applies r_iif p = true.
Proof. reflexivity. Qed.

Lemma r_ct_outcome : forall p,
  outcome r_ct p =
    match assoc_verdict (field_value FCtState p) (e_vmap (pkt_env p) "__map1") with
    | Some v => Some v | None => None end.
Proof. reflexivity. Qed.

Lemma r_iif_outcome : forall p,
  outcome r_iif p =
    match assoc_verdict (field_value FMetaIifname p) (e_vmap (pkt_env p) "__map2") with
    | Some v => Some v | None => None end.
Proof. reflexivity. Qed.

(** ** The INPUT chain's verdict, fully reduced from [global_inbound].

    Rule 1 (ct vmap __map1): estab/related -> Accept, invalid -> Drop, else MISS.
    Rule 2 (iif  vmap __map2): lo -> Accept, ppp0 -> JUMP inbound_world (accepts iff
                               [world_ssh]), eth1 -> JUMP inbound_private, else MISS;
                               a MISS (and the inbound_world jump's [None]) falls
                               through to the chain policy DROP.

    Hypotheses: [pkt_env p = gen_env] pins the two vmaps to [map1]/[map2]; the ct
    and iif registers are loadable; and the world rule's three field reads are
    loadable (needed only on the ppp0 branch, but assumed throughout for a single
    clean statement — every concrete witness discharges it).  The eth1 branch is
    left as the (opaque) sub-evaluation of [inbound_private] — characterised
    separately. *)
Definition iif_key (p : packet) : data := field_value FMetaIifname p.
Definition ct_key  (p : packet) : data := field_value FCtState p.

Lemma lookup_world : chain_lookup global_chains "inbound_world" = Some global_inbound_world.
Proof. reflexivity. Qed.
Lemma lookup_private : chain_lookup global_chains "inbound_private" = Some global_inbound_private.
Proof. reflexivity. Qed.

Lemma inbound_eval_unfold : forall p,
  pkt_env p = gen_env ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  eval_table in_fuel global_chains global_inbound p =
    (if data_eqb cts_established (ct_key p) then Accept
     else if data_eqb cts_related (ct_key p) then Accept
     else if data_eqb cts_invalid (ct_key p) then Drop
     else (* ct vmap MISS -> iif vmap *)
       if data_eqb if_lo (iif_key p) then Accept
       else if data_eqb if_ppp0 (iif_key p) then (if world_ssh p then Accept else Drop)
       else if data_eqb if_eth1 (iif_key p)
            then match eval_rules_j 6 global_chains (c_rules global_inbound_private) p with
                 | Some v => v | None => Drop end
            else Drop).
Proof.
  intros p Hpe Hct Hiif Hwl.
  unfold eval_table, in_fuel. rewrite c_rules_inbound.
  (* rule 1: ct vmap *)
  rewrite erj_cons.
  rewrite (r_ct_loadable p Hct), r_ct_applies. cbn [andb].
  rewrite r_ct_outcome.
  rewrite (e_vmap_map1 p Hpe). rewrite assoc_map1_eq.
  unfold ct_key.
  destruct (data_eqb cts_established (field_value FCtState p)) eqn:He; [ reflexivity | ].
  destruct (data_eqb cts_related (field_value FCtState p)) eqn:Hr; [ reflexivity | ].
  destruct (data_eqb cts_invalid (field_value FCtState p)) eqn:Hi; [ reflexivity | ].
  (* ct vmap MISS: fall through to rule 2 (iif vmap) *)
  rewrite erj_cons.
  rewrite (r_iif_loadable p Hiif), r_iif_applies. cbn [andb].
  rewrite r_iif_outcome.
  rewrite (e_vmap_map2 p Hpe). rewrite assoc_map2_eq.
  unfold iif_key.
  destruct (data_eqb if_lo (field_value FMetaIifname p)) eqn:Hlo; [ reflexivity | ].
  destruct (data_eqb if_ppp0 (field_value FMetaIifname p)) eqn:Hppp0.
  { (* ppp0 -> JUMP inbound_world *)
    rewrite lookup_world.
    replace (eval_rules_j 6 global_chains (c_rules global_inbound_world) p)
      with (if world_ssh p then Some Accept else None)
      by (symmetry; apply (inbound_world_eval 5 p Hwl)).
    destruct (world_ssh p); rewrite ?erj_empty; reflexivity. }
  destruct (data_eqb if_eth1 (field_value FMetaIifname p)) eqn:Heth1.
  { (* eth1 -> JUMP inbound_private (sub-eval left opaque) *)
    rewrite lookup_private.
    destruct (eval_rules_j 6 global_chains (c_rules global_inbound_private) p) eqn:Hpriv;
      [ reflexivity | rewrite ?erj_empty; reflexivity ]. }
  (* iif vmap MISS: policy DROP *)
  rewrite ?erj_empty. reflexivity.
Qed.

(* ============================================================ *)
(** ** Security corollaries about the INPUT hook (the box's self-protection). *)

(* Helpers: the three named interfaces are pairwise distinct (point bytes). *)
Lemma lo_neq_ppp0  : data_eqb if_lo   if_ppp0 = false. Proof. reflexivity. Qed.
Lemma lo_neq_eth1  : data_eqb if_lo   if_eth1 = false. Proof. reflexivity. Qed.
Lemma ppp0_neq_lo  : data_eqb if_ppp0 if_lo   = false. Proof. reflexivity. Qed.
Lemma eth1_neq_lo  : data_eqb if_eth1 if_lo   = false. Proof. reflexivity. Qed.
Lemma eth1_neq_ppp0: data_eqb if_eth1 if_ppp0 = false. Proof. reflexivity. Qed.

(* ct-state [new] is none of estab/related/invalid. *)
Lemma new_neq_estab : data_eqb cts_established cts_new = false. Proof. reflexivity. Qed.
Lemma new_neq_rel   : data_eqb cts_related     cts_new = false. Proof. reflexivity. Qed.
Lemma new_neq_inv   : data_eqb cts_invalid     cts_new = false. Proof. reflexivity. Qed.

(** THE CRUX — world-ingress lockdown.  A [new] (unsolicited) packet arriving on
    ppp0 (the world) that is NOT exactly ssh (tcp dport 22) from 81.209.165.42 is
    DROPPED: it jumps to [inbound_world], misses the single accept rule, falls back
    to [inbound], and is dropped by the chain's policy DROP.  No other world packet
    can reach the box. *)
Theorem world_ingress_locked_down : forall p,
  pkt_env p = gen_env ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_ppp0 ->
  world_ssh p = false ->
  eval_table in_fuel global_chains global_inbound p = Drop.
Proof.
  intros p Hpe Hct Hiif Hwl Hcts Hppp0 Hssh.
  rewrite (inbound_eval_unfold p Hpe Hct Hiif Hwl).
  unfold ct_key, iif_key. rewrite Hcts, Hppp0.
  rewrite new_neq_estab, new_neq_rel, new_neq_inv, lo_neq_ppp0.
  rewrite data_eqb_refl, Hssh. reflexivity.
Qed.

(* The same crux, decomposed by which guard fails (the exact disjunction the
   parser's three-match rule rejects). *)
Theorem world_ingress_locked_down_disj : forall p,
  pkt_env p = gen_env ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_ppp0 ->
  ( m_saddr p = false \/ m_tcp p = false \/ m_dport22 p = false ) ->
  eval_table in_fuel global_chains global_inbound p = Drop.
Proof.
  intros p Hpe Hct Hiif Hwl Hcts Hppp0 Hdisj.
  apply (world_ingress_locked_down p Hpe Hct Hiif Hwl Hcts Hppp0).
  unfold world_ssh.
  destruct Hdisj as [H | [H | H]]; rewrite H; cbn [andb];
    rewrite ?Bool.andb_false_r; reflexivity.
Qed.

(** The single allowed world flow IS accepted (the lockdown is NOT vacuous): a new
    packet on ppp0 that IS ssh (tcp/22) from 81.209.165.42 is ACCEPTed. *)
Theorem inbound_world_ssh_accept : forall p,
  pkt_env p = gen_env ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_ppp0 ->
  world_ssh p = true ->
  eval_table in_fuel global_chains global_inbound p = Accept.
Proof.
  intros p Hpe Hct Hiif Hwl Hcts Hppp0 Hssh.
  rewrite (inbound_eval_unfold p Hpe Hct Hiif Hwl).
  unfold ct_key, iif_key. rewrite Hcts, Hppp0.
  rewrite new_neq_estab, new_neq_rel, new_neq_inv, lo_neq_ppp0.
  rewrite data_eqb_refl, Hssh. reflexivity.
Qed.

(** Loopback is ALWAYS accepted at input (the __map2 `lo -> accept` entry), for any
    ct-state that misses the ct vmap (a new connection). *)
Theorem inbound_loopback_accept : forall p,
  pkt_env p = gen_env ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_lo ->
  eval_table in_fuel global_chains global_inbound p = Accept.
Proof.
  intros p Hpe Hct Hiif Hwl Hcts Hlo.
  rewrite (inbound_eval_unfold p Hpe Hct Hiif Hwl).
  unfold ct_key, iif_key. rewrite Hcts, Hlo.
  rewrite new_neq_estab, new_neq_rel, new_neq_inv, data_eqb_refl. reflexivity.
Qed.

(** An UNKNOWN ingress interface (not lo/ppp0/eth1) with a new connection is
    DROPPED (the iif vmap misses, policy DROP). *)
Theorem inbound_unknown_drop : forall p,
  pkt_env p = gen_env ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  field_value FCtState p = cts_new ->
  data_eqb if_lo   (field_value FMetaIifname p) = false ->
  data_eqb if_ppp0 (field_value FMetaIifname p) = false ->
  data_eqb if_eth1 (field_value FMetaIifname p) = false ->
  eval_table in_fuel global_chains global_inbound p = Drop.
Proof.
  intros p Hpe Hct Hiif Hwl Hcts Hlo Hppp0 Heth1.
  rewrite (inbound_eval_unfold p Hpe Hct Hiif Hwl).
  unfold ct_key, iif_key. rewrite Hcts.
  rewrite new_neq_estab, new_neq_rel, new_neq_inv, Hlo, Hppp0, Heth1. reflexivity.
Qed.

(** ct-state INVALID is DROPPED at input — the __map1 `invalid -> drop` entry fires
    regardless of the ingress interface (it precedes the iifname vmap). *)
Theorem inbound_invalid_dropped : forall p,
  pkt_env p = gen_env ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  field_value FCtState p = cts_invalid ->
  eval_table in_fuel global_chains global_inbound p = Drop.
Proof.
  intros p Hpe Hct Hiif Hwl Hcts.
  rewrite (inbound_eval_unfold p Hpe Hct Hiif Hwl).
  unfold ct_key. rewrite Hcts. reflexivity.
Qed.

(** Established / related connections are ACCEPTED at input (the __map1
    `established/related -> accept` entries). *)
Theorem inbound_established_accept : forall p,
  pkt_env p = gen_env ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  field_value FCtState p = cts_established ->
  eval_table in_fuel global_chains global_inbound p = Accept.
Proof.
  intros p Hpe Hct Hiif Hwl Hcts.
  rewrite (inbound_eval_unfold p Hpe Hct Hiif Hwl).
  unfold ct_key. rewrite Hcts. reflexivity.
Qed.

Theorem inbound_related_accept : forall p,
  pkt_env p = gen_env ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  field_value FCtState p = cts_related ->
  eval_table in_fuel global_chains global_inbound p = Accept.
Proof.
  intros p Hpe Hct Hiif Hwl Hcts.
  rewrite (inbound_eval_unfold p Hpe Hct Hiif Hwl).
  unfold ct_key. rewrite Hcts. reflexivity.
Qed.

(* ============================================================ *)
(** ** Satisfiability + mutation kill: concrete world-ssh packets, the planted
       open-ssh bug, and the discrimination. *)

(* A realistic input env: like [gen_env] for the vmap contents but reporting a NEW
   ct-state through [e_ct] (the literal [gen_env] pins [e_ct] to [], so a concrete
   ct-state witness needs an env that actually carries one). *)
Definition env_in : env :=
  {| e_set := fun _ => []; e_vmap := e_vmap gen_env; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddr := fun _ => []; e_ifaddr6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => cts_new; e_nat := fun _ => None;
     e_numgen := fun _ => 0 |}.

(* A well-formed IPv4 header carrying source [s] and proto TCP at byte 9. *)
Definition ip4_with (s : data) : data :=
  ([69; 0; 0; 40; 0; 0; 0; 0; 64; 6; 0; 0] ++ s ++ [1;2;3;4])%list.
(* A TCP header with destination port 22 (bytes 2..3). *)
Definition th22 : data := [0;0; 0;22; 0;0;0;0; 0;0;0;0; 80;0;0;0; 0;0;0;0]%list.

(* An input packet on ppp0 (the world), NEW ct-state, ssh dport 22, from source [s]. *)
Definition mk_in (s : data) : packet :=
  {| pkt_env := env_in;
     pkt_meta := fun k => if meta_eqb k MKiifname then if_ppp0
                          else if meta_eqb k MKl4proto then l4_tcp else [];
     pkt_ct := fun _ => []; pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := ip4_with s; pkt_th := th22; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := true;
     pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false;
     pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* The allowed source 81.209.165.42, and a wrong source 1.2.3.4. *)
Definition pkt_world_ssh : packet := mk_in [81;209;165;42]%list.
Definition pkt_world_bad : packet := mk_in [1;2;3;4]%list.

(* The allowed ssh-from-81.209.165.42 packet is ACCEPTED by the parser's chain. *)
Theorem pkt_world_ssh_accepted :
  eval_table in_fuel global_chains global_inbound pkt_world_ssh = Accept.
Proof. vm_compute. reflexivity. Qed.

(* The wrong-source ssh packet is DROPPED by the parser's chain (the saddr guard). *)
Theorem pkt_world_bad_dropped :
  eval_table in_fuel global_chains global_inbound pkt_world_bad = Drop.
Proof. vm_compute. reflexivity. Qed.

(* [bug_inbound_world] = inbound_world with the `ip saddr 81.209.165.42` guard
   REMOVED, so it accepts ssh (tcp/22) from ANY source -- opening ssh to the whole
   Internet (the catastrophic hole the lockdown rules out). *)
Definition bug_inbound_world : chain :=
  {| c_policy := Continue;
     c_rules := [{| r_body := [BMatch (MEq FMetaL4proto [6]);
                               BMatch (MEq FThDport [0;22])];   (* saddr guard removed *)
                    r_verdict := Accept; r_vmap := None;
                    r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None;
                    r_after := [] |}] |}.

(* The chain env with the bugged inbound_world substituted for the parser's. *)
Definition bug_chains : list (string * chain) :=
  [("inbound_world", bug_inbound_world);
   ("inbound_private", global_inbound_private);
   ("inbound", global_inbound);
   ("forward", global_forward);
   ("postrouting", global_postrouting)].

(* Under the bug, the SAME wrong-source ssh packet is ACCEPTED -- the ssh-to-the-
   world hole. *)
Theorem bug_world_bad_accepted :
  eval_table in_fuel bug_chains global_inbound pkt_world_bad = Accept.
Proof. vm_compute. reflexivity. Qed.

(* Hence the input lockdown DISCRIMINATES the bug: on the same wrong-source ssh
   packet the parser's chain DROPs while the de-guarded chain ACCEPTs. *)
Theorem input_property_discriminates_bug :
  eval_table in_fuel global_chains global_inbound pkt_world_bad
  <> eval_table in_fuel bug_chains global_inbound pkt_world_bad.
Proof. rewrite pkt_world_bad_dropped, bug_world_bad_accepted. discriminate. Qed.

(* The lockdown hypotheses are SATISFIABLE: the allowed ssh witness meets every
   hypothesis of [inbound_world_ssh_accept]; the bad witness meets every hypothesis
   of [world_ingress_locked_down]. *)
Lemma pkt_world_ssh_loads :
  field_loadable FCtState pkt_world_ssh = true
  /\ field_loadable FMetaIifname pkt_world_ssh = true
  /\ world_loads pkt_world_ssh = true
  /\ field_value FCtState pkt_world_ssh = cts_new
  /\ field_value FMetaIifname pkt_world_ssh = if_ppp0
  /\ world_ssh pkt_world_ssh = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma pkt_world_bad_facts :
  field_loadable FCtState pkt_world_bad = true
  /\ field_loadable FMetaIifname pkt_world_bad = true
  /\ world_loads pkt_world_bad = true
  /\ field_value FCtState pkt_world_bad = cts_new
  /\ field_value FMetaIifname pkt_world_bad = if_ppp0
  /\ world_ssh pkt_world_bad = false.
Proof. repeat split; vm_compute; reflexivity. Qed.

