(** * router.nft FORWARD chain — the NAT-router security crux, verdict-characterised.

    The whole security reason a NAT router is safe is that its `forward` base chain
    DROPS unsolicited world->private traffic.  In router.nft:

        chain forward { type filter hook forward priority 0; policy DROP;
                        ct state vmap {established:accept, related:accept, invalid:drop};
                        iifname eth1 accept }

    The postrouting masquerade theorems ([Router_Reach]) are data-plane source-NAT
    properties only; without this file the forward chain — where the actual
    forwarding decision is made — would have no proven properties, so a packet
    arriving on ppp0 (the world) in ct-state `new`, destined for the LAN, would
    have an entirely UNDETERMINED fate, and a planted bug that removes the
    `iifname eth1` guard (open forwarding) would survive every masquerade property.

    This file pins the forward chain's verdict down COMPLETELY, against the
    PARSER-generated [global_forward] (from [Router_Gen]), as an exact characterisation:

      - [forward_accept_iff]  : the chain ACCEPTS iff the packet is ct established/related
                                OR (not invalid and) ingresses on eth1 (the LAN).
      - [forward_drop_iff]    : the chain DROPS iff it does not accept (the only two
                                reachable verdicts — there is no Continue/Jump leak).
      - [forward_unsolicited_dropped] : the security corollary — a `new` (not estab/
                                related) packet whose ingress is NOT eth1 is DROPPED, so
                                unsolicited world(ppp0)->private is NEVER forwarded.
      - [forward_invalid_dropped] : the ct-state `invalid->drop` vmap entry fires (a DROP
                                distinct from the policy drop), even on eth1.

    Non-vacuity / mutation kill:
      - [forward_eth1_accepts]  : a new-state packet on eth1 IS accepted (the accept path
                                  is real), so [forward_unsolicited_dropped]'s contrapositive
                                  is satisfiable.
      - [bug_forward] removes the eth1 guard (accepts every iif); under it the SAME
                      unsolicited ppp0 packet ACCEPTS, and [bug_breaks_unsolicited_drop]
                      witnesses the catastrophic open-forwarding leak that
                      [forward_unsolicited_dropped] rules out.

    M4 NOTE — the symbolic theorems below that combine [e = gen_env] with
    [field_value FCtState e p = cts_new] are VACUOUS (the pin empties the
    conntrack table, so NEW is unreadable —
    [Router_Realistic.ctstate_under_genenv_never_new]).  The de-vacuized
    forms, with the env relaxed to the [__map3] contents the chain's one
    lookup reads (recipe: proof/CONFIG_PROOFS.md § "Pin only what the lookups
    read"), are [Router_Realistic.forward_unsolicited_dropped_real] /
    [forward_accept_iff_real]; cite those. *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Router_Gen Nftval Eval_Fw.
Import ListNotations.
Open Scope string_scope.

(** Concrete ct-state wire values (only equality matters; big-endian 32-bit).
    Routed through the central typed nft constructors + [encode] (as
    [Example_Ruleset]/[Nftval] do) so the byte literals cannot drift from the
    central conntrack-state encoding; [Eval compute] reduces each to the very
    literal the [cbn]-based proofs match against. *)
Definition cts_invalid     : data := Eval compute in encode ct_invalid.      (* [0;0;0;1] *)
Definition cts_established : data := Eval compute in encode ct_established.   (* [0;0;0;2] *)
Definition cts_related     : data := Eval compute in encode ct_related.      (* [0;0;0;4] *)
Definition cts_new         : data := Eval compute in encode ct_new.          (* [0;0;0;8] *)

(* The LAN ingress interface "eth1" as the 16-byte zero-padded ASCII the parser
   emitted in the `iifname eth1 accept` rule. *)
Definition if_eth1 : data :=
  [101;116;104;49; 0;0;0;0; 0;0;0;0; 0;0;0;0].
(* The WAN ingress interface "ppp0" (the world side). *)
Definition if_ppp0 : data :=
  [112;112;112;48; 0;0;0;0; 0;0;0;0; 0;0;0;0].

Definition fw_fuel : nat := 8.

(* The `iifname eth1` match the parser emitted, exactly as the kernel evaluates it:
   the [MEq FMetaIifname if_eth1] condition (an exact compare of the iif register
   against the 16-byte "eth1"). *)
Definition iif_eth1 (e : env) (p : packet) : bool :=
  eval_matchcond_body (MEq FMetaIifname if_eth1) e p.

(* The ct-state verdict map [__map3] the parser emitted (point-interval entries). *)
Definition map3 : list (data * data * verdict) :=
  [(cts_established, cts_established, Accept);
   (cts_related, cts_related, Accept);
   (cts_invalid, cts_invalid, Drop)].

(** The one-step unfolding lemmas [erj_nil]/[erj_cons] for the fuel-recursive
    interpreter (and [Global Opaque eval_rules_j], so [cbn] reduces only the
    current rule) come from [Eval_Fw] — the single shared source of truth. *)

(** ** A clean classification of the ct-state vmap [__map3].

    Each entry is a POINT interval [(k,k,v)], so [data_in_iv key (k,k)] reduces to
    [data_eqb k key] (by [data_le_antisym]).  Hence the whole lookup is a cascade of
    byte-equality tests — no concrete-byte case analysis on the key is needed. *)

(* [data_in_iv_point] — a point interval's membership test IS byte equality —
   comes from [Eval_Fw] (shared with [Router_Input]). *)

(* The vmap lookup expressed as a cascade of equality tests against the keys: the
   ONLY possible results are [Some Accept] (estab/related), [Some Drop] (invalid),
   or [None] (miss) — there is no [Continue]/[Jump] verdict, so the fall-through
   structure of the chain is fully determined. *)
Lemma assoc_map3_eq : forall key,
  assoc_verdict key map3 =
    (if data_eqb cts_established key then Some Accept
     else if data_eqb cts_related key then Some Accept
     else if data_eqb cts_invalid key then Some Drop
     else None).
Proof.
  intro key. unfold map3; cbn [assoc_verdict].
  rewrite !data_in_iv_point. reflexivity.
Qed.

(** ** Concrete vmap lookups (non-vacuity: the entries are real). *)

Lemma assoc_estab  : assoc_verdict cts_established map3 = Some Accept.
Proof. vm_compute. reflexivity. Qed.
Lemma assoc_related : assoc_verdict cts_related map3 = Some Accept.
Proof. vm_compute. reflexivity. Qed.
Lemma assoc_invalid : assoc_verdict cts_invalid map3 = Some Drop.
Proof. vm_compute. reflexivity. Qed.
Lemma assoc_new    : assoc_verdict cts_new map3 = None.
Proof. vm_compute. reflexivity. Qed.

(* Keep the field reads and the vmap lookup opaque so [cbn] leaves
   [assoc_verdict (field_value FCtState e p) map3] folded instead of expanding it. *)
Opaque field_value assoc_verdict.

(** ** The forward chain's two rules, as a clean verdict over the ct-state and iif.

    Rule 1 is the ct-state vmap [__map3]; rule 2 is `MEq FMetaIifname eth1 -> Accept`.
    Under [e = gen_env] the vmap lookups are concrete:
      estab/related -> Accept, invalid -> Drop, anything else -> MISS (fall through).
    The vmap rule body is empty (no payload load), the iifname rule loads a meta
    register (always loadable), so [rule_loadable] is [true] throughout. *)

(* Rule 2 of the forward chain: `iifname eth1 accept` (the parser's literal). *)
Definition r2_fwd : rule :=
  {| r_body := [BMatch (MEq FMetaIifname if_eth1)];
     r_outcome := OVerdict Accept; r_after := [] |}.

(* Its load always succeeds (a meta iifname read never BREAKs). *)
Lemma r2_loadable : forall e p, rule_loadable r2_fwd e p = true.
Proof. intros e p. reflexivity. Qed.

(* It applies exactly when the iifname is eth1. *)
Lemma r2_applies : forall e p, rule_applies r2_fwd e p = iif_eth1 e p.
Proof.
  intros e p. unfold rule_applies, r2_fwd; cbn [r_body rule_applies_walk].
  unfold eval_matchcond, iif_eth1.
  rewrite Bool.andb_true_r.
  (* [match_loadable (MEq FMetaIifname _) p = field_loadable FMetaIifname p = true]. *)
  reflexivity.
Qed.

(* When it applies, its outcome is the terminal Accept (no vmap, static verdict). *)
Lemma r2_outcome : forall e p, outcome r2_fwd e p = Some Accept.
Proof. intros e p. reflexivity. Qed.

(* The forward chain's verdict, fully symbolically reduced from [global_forward]:
   stepping rule 1 (ct vmap) then rule 2 (iifname) then policy DROP.  Since the ct
   vmap [__map3] can only yield Accept/Drop/MISS (no Continue/Jump — see
   [assoc_map3_eq]), the verdict is a closed cascade of byte-equality tests with NO
   undetermined branch. *)
Lemma forward_eval_unfold : forall e p,
  e = gen_env ->
  eval_table fw_fuel global_chains global_forward e p =
    (if data_eqb cts_established (field_value FCtState e p) then Accept
     else if data_eqb cts_related (field_value FCtState e p) then Accept
     else if data_eqb cts_invalid (field_value FCtState e p) then Drop
     else if iif_eth1 e p then Accept else Drop).
Proof.
  intros e p Hpe.
  unfold eval_table, fw_fuel, global_forward, global_chains.
  cbn [c_rules c_policy].
  rewrite erj_cons.
  (* rule 1: ct-state vmap.  rule_loadable: empty body, vmap key meta-load = ok. *)
  unfold rule_loadable, rule_applies, outcome, outcome_core;
    cbn -[eval_rules_j assoc_verdict field_value iif_eth1].
  (* the ct vmap key is [field_value FCtState e p] (vm_keyf = Some (FCtState, []), no
     transforms), and the lookup table under [e = gen_env] is exactly [map3]. *)
  replace (e_vmap e "__map3") with map3 by (rewrite Hpe; reflexivity).
  rewrite assoc_map3_eq.
  destruct (data_eqb cts_established (field_value FCtState e p)) eqn:He;
    [ cbn -[eval_rules_j]; reflexivity | ].
  destruct (data_eqb cts_related (field_value FCtState e p)) eqn:Hr;
    [ cbn -[eval_rules_j]; reflexivity | ].
  destruct (data_eqb cts_invalid (field_value FCtState e p)) eqn:Hi;
    [ cbn -[eval_rules_j]; reflexivity | ].
  (* vmap MISS: fall through to rule 2 (iifname eth1). *)
  cbn -[eval_rules_j data_eqb field_value eval_matchcond_body iif_eth1].
  rewrite erj_cons.
  (* fold the parser's literal rule into [r2_fwd] (the iifname literal IS [if_eth1]),
     then use its [loadable]/[applies]/[outcome] lemmas — no [firstn] unrolling. *)
  change {| r_body := [BMatch (MEq FMetaIifname
              [101;116;104;49;0;0;0;0;0;0;0;0;0;0;0;0])];
     r_outcome := OVerdict Accept; r_after := [] |}
    with r2_fwd.
  rewrite r2_loadable, r2_applies, r2_outcome. cbn [andb].
  destruct (iif_eth1 e p) eqn:Heq;
    cbn -[eval_rules_j iif_eth1]; rewrite ?erj_nil; reflexivity.
Qed.

(** ** The security corollaries. *)

(* THE CRUX: a `new` (unsolicited, not estab/related) packet whose ingress is NOT
   eth1 (the LAN) is DROPPED — so world(ppp0)->private is never forwarded. *)
Theorem forward_unsolicited_dropped : forall e p,
  e = gen_env ->
  field_value FCtState e p = cts_new ->
  iif_eth1 e p = false ->
  eval_table fw_fuel global_chains global_forward e p = Drop.
Proof.
  intros e p Hpe Hct Hiif.
  rewrite (forward_eval_unfold e p Hpe), Hct, Hiif. vm_compute. reflexivity.
Qed.

(* The same crux phrased directly on ppp0 (the world interface): a new packet
   arriving on ppp0 is dropped. *)
Theorem forward_ppp0_dropped : forall e p,
  e = gen_env ->
  field_value FCtState e p = cts_new ->
  field_value FMetaIifname e p = if_ppp0 ->
  eval_table fw_fuel global_chains global_forward e p = Drop.
Proof.
  intros e p Hpe Hct Hiif.
  apply forward_unsolicited_dropped; auto.
  unfold iif_eth1, eval_matchcond_body. rewrite Hiif. vm_compute. reflexivity.
Qed.

(* The ct-state `invalid -> drop` vmap entry FIRES — an invalid packet is dropped
   at forward even if it ingresses on eth1 (the LAN), because the vmap terminal
   Drop precedes the eth1 accept rule. *)
Theorem forward_invalid_dropped : forall e p,
  e = gen_env ->
  field_value FCtState e p = cts_invalid ->
  eval_table fw_fuel global_chains global_forward e p = Drop.
Proof.
  intros e p Hpe Hct.
  rewrite (forward_eval_unfold e p Hpe), Hct. vm_compute. reflexivity.
Qed.

(** ** The accept paths (non-vacuity of the drop properties' contrapositive). *)

(* Established connections are forwarded (the vmap `established -> accept`). *)
Theorem forward_established_accepted : forall e p,
  e = gen_env ->
  field_value FCtState e p = cts_established ->
  eval_table fw_fuel global_chains global_forward e p = Accept.
Proof.
  intros e p Hpe Hct.
  rewrite (forward_eval_unfold e p Hpe), Hct. vm_compute. reflexivity.
Qed.

(* Related connections are forwarded (the vmap `related -> accept`). *)
Theorem forward_related_accepted : forall e p,
  e = gen_env ->
  field_value FCtState e p = cts_related ->
  eval_table fw_fuel global_chains global_forward e p = Accept.
Proof.
  intros e p Hpe Hct.
  rewrite (forward_eval_unfold e p Hpe), Hct. vm_compute. reflexivity.
Qed.

(* A new connection ingressing on the LAN (eth1) IS forwarded (the `iifname eth1
   accept` rule fires after the vmap misses) — the accept path is REAL, so
   [forward_unsolicited_dropped]'s "not eth1" hypothesis is the only thing standing
   between this packet and a DROP. *)
Theorem forward_eth1_accepted : forall e p,
  e = gen_env ->
  field_value FCtState e p = cts_new ->
  field_value FMetaIifname e p = if_eth1 ->
  eval_table fw_fuel global_chains global_forward e p = Accept.
Proof.
  intros e p Hpe Hct Hiif.
  rewrite (forward_eval_unfold e p Hpe), Hct.
  unfold iif_eth1, eval_matchcond_body. rewrite Hiif.
  vm_compute. reflexivity.
Qed.

(** ** The EXACT characterisation: the forward chain accepts iff one of the three
       faithful accept paths holds; otherwise it drops (no third verdict). *)

Theorem forward_accept_iff : forall e p,
  e = gen_env ->
  ( eval_table fw_fuel global_chains global_forward e p = Accept
    <->
    ( field_value FCtState e p = cts_established
      \/ field_value FCtState e p = cts_related
      \/ ( field_value FCtState e p <> cts_invalid
           /\ iif_eth1 e p = true ) ) ).
Proof.
  intros e p Hpe. rewrite (forward_eval_unfold e p Hpe).
  destruct (data_eqb cts_established (field_value FCtState e p)) eqn:Hest.
  { (* established *)
    apply data_eqb_true_iff in Hest. split; [ intros _ | reflexivity ]. auto. }
  destruct (data_eqb cts_related (field_value FCtState e p)) eqn:Hrel.
  { (* related *)
    apply data_eqb_true_iff in Hrel. split; [ intros _ | reflexivity ]. auto. }
  destruct (data_eqb cts_invalid (field_value FCtState e p)) eqn:Hinv.
  { (* invalid: chain DROPs (never Accept), and the invalid disjunct is excluded *)
    apply data_eqb_true_iff in Hinv. split.
    - discriminate.
    - intros [He | [He | [Hni _]]].
      + rewrite <- He in Hest; rewrite data_eqb_refl in Hest; discriminate.
      + rewrite <- He in Hrel; rewrite data_eqb_refl in Hrel; discriminate.
      + exfalso; apply Hni; rewrite <- Hinv; reflexivity. }
  (* ct-state not in {estab,related,invalid}: MISS -> verdict is the iif test *)
  split.
  - (* Accept here iff iif=eth1 *)
    intro Hacc.
    destruct (iif_eth1 e p) eqn:Heq; [ | discriminate Hacc ].
    right; right; split; [ | reflexivity ].
    intro Hc. rewrite <- Hc in Hinv. rewrite data_eqb_refl in Hinv; discriminate.
  - intros [He | [He | [_ Heq]]].
    + rewrite <- He in Hest; rewrite data_eqb_refl in Hest; discriminate.
    + rewrite <- He in Hrel; rewrite data_eqb_refl in Hrel; discriminate.
    + rewrite Heq. reflexivity.
Qed.

(* ============================================================ *)
(** ** Satisfiability + mutation kill: a concrete unsolicited world packet, the
       planted open-forwarding bug, and the discrimination. *)

(* A custom env that reports an [established]/[new] ct-state through [e_ct] (the
   literal [gen_env] pins [e_ct] to the empty value, so a concrete ct-state witness
   needs an env that actually carries one — this is the realistic conntrack env). *)
Definition env_fwd : env :=
  {| e_set := fun _ => []; e_vmap := e_vmap gen_env; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => cts_new; e_nat := fun _ => None;
     e_numgen := fun _ => 0 |}.

(* An unsolicited packet: NEW ct-state, ingress on ppp0 (the world). *)
Definition pkt_world : packet :=
  {|
     pkt_meta := fun k => if meta_eqb k MKiifname then if_ppp0 else [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := true;
     pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false;
     pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* The witness is genuinely NEW-state on ppp0 (the security hyps are satisfiable). *)
Lemma pkt_world_ct  : field_value FCtState env_fwd pkt_world = cts_new.
Proof. vm_compute. reflexivity. Qed.
Lemma pkt_world_iif : iif_eth1 env_fwd pkt_world = false.
Proof. vm_compute. reflexivity. Qed.

(* The CORRECT forward chain DROPS this unsolicited world packet. *)
Theorem pkt_world_dropped :
  eval_table fw_fuel global_chains global_forward env_fwd pkt_world = Drop.
Proof. vm_compute. reflexivity. Qed.

(* [bug_forward] = the forward chain with the `iifname eth1` GUARD REMOVED, so rule 2
   accepts EVERY ingress interface (an open-forwarding hole: it forwards traffic from
   any interface once the ct vmap misses). *)
Definition bug_forward : chain :=
  {| c_policy := Drop;
     c_rules :=
       [{| r_body := [];
     r_outcome := OVmap {| vm_fields := []; vm_keyf := Some (FCtState, []);
                             vm_name := "__map3" |}; r_after := [] |};
        {| r_body := [];
     r_outcome := OVerdict Accept; r_after := [] |}] |}.

(* Under the bug, the SAME unsolicited world packet is ACCEPTED — the catastrophic
   open-forwarding leak that [forward_unsolicited_dropped] / [pkt_world_dropped] rule
   out: the Internet would reach internal hosts. *)
Theorem bug_world_accepted :
  eval_table fw_fuel global_chains bug_forward env_fwd pkt_world = Accept.
Proof. vm_compute. reflexivity. Qed.

(* Hence the forward verdict property DISCRIMINATES the bug: on the same world packet
   the parser's chain DROPs while the de-guarded chain ACCEPTs — the discrimination a
   forward property had to make, and which the prior postrouting-only set could not. *)
Theorem forward_property_discriminates_bug :
  eval_table fw_fuel global_chains global_forward env_fwd pkt_world
  <> eval_table fw_fuel global_chains bug_forward env_fwd pkt_world.
Proof. rewrite pkt_world_dropped, bug_world_accepted. discriminate. Qed.

(* ============================================================ *)
(** ** UNIFIED-SEMANTICS LICENSE (Semantics.v § "Projection 1b").

    The `global` chain env is not write-free (`inbound_private`'s
    `limit rate 5/second` is an env write), but it IS limiter-tolerant
    ([Semantics.chains_limiter_tol]), so every [eval_table] statement in
    this file is the proven VERDICT projection of the unified
    effect-threading semantics ([Semantics.eval_table_u_limiter_tolerant])
    at every fuel, env and packet — see the license header in
    [Router_Input] § "UNIFIED-SEMANTICS LICENSE". *)

Theorem forward_licensed : forall fuel e p,
  eval_table fuel global_chains global_forward e p
  = fst (eval_table_u fuel global_chains global_forward e p).
Proof.
  intros fuel e p. symmetry.
  apply eval_table_u_limiter_tolerant; vm_compute; reflexivity.
Qed.

(** The mutation-kill base chain is licensed under the same chain env. *)
Theorem bug_forward_licensed : forall fuel e p,
  eval_table fuel global_chains bug_forward e p
  = fst (eval_table_u fuel global_chains bug_forward e p).
Proof.
  intros fuel e p. symmetry.
  apply eval_table_u_limiter_tolerant; vm_compute; reflexivity.
Qed.
