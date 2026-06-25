(** * router.nft PRIVATE-ingress (eth1 -> inbound_private) — fully characterised.

    The INPUT hook ([Router_Input]) proved the WORLD (ppp0), LOOPBACK (lo) and
    ct-state (estab/related/invalid) branches, but deliberately left the eth1 branch
    of [global_inbound] as an OPAQUE sub-evaluation of [global_inbound_private]
    ([inbound_eval_unfold] line ~317 keeps it as
       [match eval_rules_j 6 global_chains (c_rules global_inbound_private) p with ...]).
    So the entire LAN-ingress path — packets from internal hosts to the box itself
    (the router's DNS resolver, DHCP, ssh management, rate-limited ping) — had an
    UNDETERMINED fate, and the two genuinely-new constructs of router.nft (the
    concatenated-key verdict map [__map0] and the [limit 5/second] statement) had no
    reachability property at all.  In particular a planted bug widening [__map0] to a
    catch-all (LAN-open) survived the entire prior property set.

    In router.nft:

        chain inbound_private {
          icmp echo-request limit 5/second accept;             (* rule 1 *)
          ip protocol . th dport vmap {tcp.22:accept,           (* rule 2: concat vmap *)
                                       udp.53:accept,
                                       tcp.53:accept,
                                       udp.67:accept} }

    This file pins it down against the PARSER-generated [global_inbound_private] /
    [global_inbound] (from [Router_Gen]):

      - [inbound_private_eval] : the private sub-chain's [eval_rules_j] result fully
            reduced — [Some Accept] iff the packet is icmp-echo AND under the rate
            limit, OR its [ip protocol . th dport] concat key is one of the four
            listed services; else [None] (fall through to inbound's policy DROP).
      - [inbound_eth1_accept_iff] : THE CRUX (mirrors [forward_accept_iff]) — for an
            eth1, new-conn packet, [eval_table … global_inbound = Accept] IFF
            (icmp-echo under limit) OR (proto.port in the four services).
      - [inbound_eth1_unlisted_dropped] : the SECURITY half — an eth1 packet that is
            neither icmp-echo nor a listed service is DROPPED.  The box exposes
            EXACTLY ssh/dns(tcp+udp)/dhcp + rate-limited ping to the LAN, nothing else.
      - [inbound_icmp_ratelimited_dropped] : even icmp-echo is dropped once the rate
            limit is EXHAUSTED (the [limit 5/second] construct genuinely gates).
      - Non-vacuity witnesses (dns/dhcp/ssh accept; smtp drop) + the mutation kill
        [priv_property_discriminates_bug] (the catch-all [__map0] bug the prior
        property set could not see). *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Router_Gen Router_Input Eval_Fw.
Import ListNotations.
Open Scope string_scope.

(** ** The icmp / limit rule (rule 1 of inbound_private), named. *)
Definition icmp_spec : limit_spec :=
  {| ls_rate := 5; ls_unit := 0; ls_burst := 5; ls_bytes := false; ls_flags := 0 |}.

Definition r_icmp : rule :=
  {| r_body := [BMatch (MEq FMetaL4proto [1]);
                BMatch (MEq FIcmpType [8]);
                BMatch (MLimit icmp_spec)];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.

(** The concat-key vmap rule (rule 2 of inbound_private), named. *)
Definition r_svc : rule :=
  {| r_body := []; r_verdict := Continue;
     r_vmap := Some {| vm_fields := [FIp4Protocol; FThDport]; vm_keyf := None;
                       vm_name := "__map0" |};
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.

Lemma c_rules_private : c_rules global_inbound_private = [r_icmp; r_svc].
Proof. reflexivity. Qed.

(** The four listed services exactly as the parser emitted them in [__map0]
    ([proto; dportHi; dportLo]): ssh (tcp/22), dns (udp/53), dns (tcp/53),
    dhcp (udp/67). *)
Definition map0 : list (data * data * verdict) :=
  [([6;0;22],  [6;0;22],  Accept);
   ([17;0;53], [17;0;53], Accept);
   ([6;0;53],  [6;0;53],  Accept);
   ([17;0;67], [17;0;67], Accept)].

Lemma e_vmap_map0 : forall p, pkt_env p = gen_env ->
  e_vmap (pkt_env p) "__map0" = map0.
Proof. intros p H. rewrite H. reflexivity. Qed.

(** The named matches of the icmp rule (kept folded, like [Router_Input]'s
    [m_saddr]/etc., so [cbn] never unfolds the firstn-truncation). *)
Definition m_icmpproto (p : packet) : bool := eval_matchcond_body (MEq FMetaL4proto [1]) p.
Definition m_icmpecho  (p : packet) : bool := eval_matchcond_body (MEq FIcmpType [8]) p.

(** The rate-limit test for the parser's [limit 5/second] match, kept as the match
    body (so it stays folded under [cbn]/[Opaque eval_matchcond_body]).  Since
    [icmp_spec]'s invert bit (bit 0 of [ls_flags = 0]) is clear, this is exactly the
    non-inverted "under / not exceeded" test [lim_under] (see [icmp_under_lim]). *)
Definition icmp_under (p : packet) : bool := eval_matchcond_body (MLimit icmp_spec) p.

Lemma icmp_under_lim : forall p, icmp_under p = lim_under p icmp_spec.
Proof. reflexivity. Qed.

(** [icmp_ok]: the icmp rule fires (accepts) iff it is an icmp echo-request AND the
    rate limit is not yet exhausted. *)
Definition icmp_ok (p : packet) : bool := m_icmpproto p && m_icmpecho p && icmp_under p.

(** The concat-vmap key the parser builds for rule 2: [ip protocol] ++ [th dport]. *)
Definition svc_key (p : packet) : data :=
  List.concat (map (fun f => field_value f p) [FIp4Protocol; FThDport]).

(** [svc_hit]: the concat key resolves in [__map0] (one of the four services). *)
Definition svc_hit (p : packet) : option verdict := assoc_verdict (svc_key p) map0.

(** ** Loadability of the two private rules. *)

Definition icmp_loads (p : packet) : bool :=
  field_loadable FMetaL4proto p && field_loadable FIcmpType p.

(* The vmap-key load for the concat rule (its two payload fields). *)
Definition svc_loads (p : packet) : bool :=
  field_loadable FIp4Protocol p && field_loadable FThDport p.

Opaque field_value assoc_verdict eval_matchcond_body field_loadable.

Lemma r_icmp_loadable : forall p,
  icmp_loads p = true -> rule_loadable r_icmp p = true.
Proof.
  intros p H. unfold icmp_loads in H.
  apply Bool.andb_true_iff in H as [H1 H2].
  unfold rule_loadable, r_icmp. cbn.
  rewrite H1, H2. reflexivity.
Qed.

Lemma r_svc_loadable : forall p,
  svc_loads p = true -> rule_loadable r_svc p = true.
Proof.
  intros p H. unfold svc_loads in H.
  apply Bool.andb_true_iff in H as [H1 H2].
  unfold rule_loadable, r_svc. cbn.
  rewrite H1, H2. cbn [andb].
  destruct (assoc_verdict _ (e_vmap (pkt_env p) "__map0")); reflexivity.
Qed.

(** The icmp rule applies (when its loads succeed) iff icmp-echo under the limit. *)
Lemma r_icmp_applies : forall p,
  icmp_loads p = true -> rule_applies r_icmp p = icmp_ok p.
Proof.
  intros p H. unfold icmp_loads in H.
  apply Bool.andb_true_iff in H as [H1 H2].
  unfold rule_applies, r_icmp, icmp_ok; cbn [r_body rule_applies_walk].
  unfold eval_matchcond, match_loadable.
  (* match_loadable for MLimit is [true]; for MEq it is [field_loadable]. *)
  rewrite H1, H2. cbn [andb].
  unfold m_icmpproto, m_icmpecho, icmp_under.
  generalize (eval_matchcond_body (MEq FMetaL4proto [1]) p) as b1;
  generalize (eval_matchcond_body (MEq FIcmpType [8]) p) as b2;
  generalize (eval_matchcond_body (MLimit icmp_spec) p) as b3;
  intros b3 b2 b1. now destruct b1, b2, b3.
Qed.

(* When the icmp rule applies its outcome is the terminal Accept. *)
Lemma r_icmp_outcome : forall p, outcome r_icmp p = Some Accept.
Proof. reflexivity. Qed.

Lemma r_svc_applies : forall p, rule_applies r_svc p = true.
Proof. reflexivity. Qed.

(* The concat rule's outcome: a vmap HIT gives the service verdict, a MISS falls
   through ([Continue] terminal = [None]). *)
Lemma r_svc_outcome : forall p,
  outcome r_svc p =
    match assoc_verdict (svc_key p) (e_vmap (pkt_env p) "__map0") with
    | Some v => Some v | None => None end.
Proof. reflexivity. Qed.

(* Every entry of [__map0] maps to Accept, so a HIT is necessarily [Some Accept]. *)
Lemma svc_hit_accept : forall p v, svc_hit p = Some v -> v = Accept.
Proof.
  intro p. unfold svc_hit, map0. set (k := svc_key p). cbn [assoc_verdict].
  rewrite !data_in_iv_point.
  destruct (data_eqb [6;0;22] k); [ intros v H; now inversion H | ].
  destruct (data_eqb [17;0;53] k); [ intros v H; now inversion H | ].
  destruct (data_eqb [6;0;53] k); [ intros v H; now inversion H | ].
  destruct (data_eqb [17;0;67] k); [ intros v H; now inversion H | ].
  discriminate.
Qed.

(** ** The PRIVATE sub-chain's [eval_rules_j] result, fully reduced.

    Rule 1 (icmp + limit): accept iff icmp-echo AND under rate.
    Rule 2 (concat vmap __map0): a HIT gives the service verdict (Accept), a MISS
    falls through (Continue) -> [None].
    Since [icmp_ok = true] makes rule 1 ACCEPT (terminal), and otherwise we fall to
    the vmap, the sub-chain returns [Some Accept] iff [icmp_ok] OR a service hit,
    else [None] (back to inbound's policy DROP). *)
Lemma inbound_private_eval : forall n p,
  pkt_env p = gen_env ->
  icmp_loads p = true ->
  svc_loads p = true ->
  eval_rules_j (S (S n)) global_chains (c_rules global_inbound_private) p =
    (if icmp_ok p then Some Accept
     else svc_hit p).
Proof.
  intros n p Hpe Hil Hsl.
  rewrite c_rules_private.
  (* rule 1 *)
  rewrite erj_cons.
  rewrite (r_icmp_loadable p Hil), (r_icmp_applies p Hil). cbn [andb].
  destruct (icmp_ok p) eqn:Hok.
  { rewrite r_icmp_outcome. reflexivity. }
  (* icmp rule does not fire: fall through to rule 2 (the concat vmap) *)
  rewrite erj_cons.
  rewrite (r_svc_loadable p Hsl), r_svc_applies. cbn [andb].
  rewrite r_svc_outcome.
  rewrite (e_vmap_map0 p Hpe).
  unfold svc_hit, svc_key.
  destruct (assoc_verdict
              (List.concat (map (fun f => field_value f p) [FIp4Protocol; FThDport]))
              map0) eqn:Hhit.
  { (* vmap HIT: a service verdict — necessarily Accept (every [__map0] entry is
       Accept), so it is terminal -> [Some Accept]. *)
    assert (Hv : v = Accept) by (apply (svc_hit_accept p); unfold svc_hit, svc_key; exact Hhit).
    subst v. reflexivity. }
  (* vmap MISS: rule 2 outcome [None] -> fall through to the empty tail. *)
  rewrite erj_empty. reflexivity.
Qed.

(** ** The eth1 branch of [global_inbound], characterised.

    Plugging [inbound_private_eval] into [inbound_eval_unfold]'s opaque eth1 slot
    gives the exact verdict for a LAN packet (eth1, new conn). *)
Lemma inbound_eth1_eval : forall p,
  pkt_env p = gen_env ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  icmp_loads p = true ->
  svc_loads p = true ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_eth1 ->
  eval_table in_fuel global_chains global_inbound p =
    (if icmp_ok p then Accept
     else match svc_hit p with Some v => v | None => Drop end).
Proof.
  intros p Hpe Hct Hiif Hwl Hil Hsl Hcts Heth1.
  rewrite (inbound_eval_unfold p Hpe Hct Hiif Hwl).
  unfold ct_key, iif_key. rewrite Hcts, Heth1.
  rewrite new_neq_estab, new_neq_rel, new_neq_inv.
  (* if_lo =? if_eth1 and if_ppp0 =? if_eth1 are false; the eth1 guard is refl-true *)
  change (data_eqb if_lo if_eth1) with false.
  change (data_eqb if_ppp0 if_eth1) with false.
  rewrite data_eqb_refl.
  (* the opaque eth1 sub-eval -> [inbound_private_eval] (fuel 6 = S (S 4)) *)
  change 6 with (S (S 4)).
  rewrite (inbound_private_eval 4 p Hpe Hil Hsl).
  destruct (icmp_ok p); [ reflexivity | ].
  destruct (svc_hit p) as [v|]; reflexivity.
Qed.

(* ============================================================ *)
(** ** THE CRUX — the eth1 (LAN-ingress) accept characterisation. *)

(** A clean classification of the four listed services by the concat key. *)
Lemma svc_hit_iff : forall p,
  (svc_hit p = Some Accept) <->
  ( svc_key p = [6;0;22] \/ svc_key p = [17;0;53]
    \/ svc_key p = [6;0;53] \/ svc_key p = [17;0;67] ).
Proof.
  intro p.
  assert (Hexp : svc_hit p =
    (if data_eqb [6;0;22]  (svc_key p) then Some Accept
     else if data_eqb [17;0;53] (svc_key p) then Some Accept
     else if data_eqb [6;0;53]  (svc_key p) then Some Accept
     else if data_eqb [17;0;67] (svc_key p) then Some Accept
     else None)).
  { unfold svc_hit, map0. cbn [assoc_verdict]. now rewrite !data_in_iv_point. }
  rewrite Hexp. split.
  - intro H.
    destruct (data_eqb [6;0;22] (svc_key p)) eqn:E1.
    { left. apply data_eqb_true_iff in E1. now rewrite E1. }
    destruct (data_eqb [17;0;53] (svc_key p)) eqn:E2.
    { right; left. apply data_eqb_true_iff in E2. now rewrite E2. }
    destruct (data_eqb [6;0;53] (svc_key p)) eqn:E3.
    { right; right; left. apply data_eqb_true_iff in E3. now rewrite E3. }
    destruct (data_eqb [17;0;67] (svc_key p)) eqn:E4.
    { right; right; right. apply data_eqb_true_iff in E4. now rewrite E4. }
    discriminate H.
  - intro H. destruct H as [H|[H|[H|H]]]; rewrite H;
      rewrite ?data_eqb_refl;
      [ reflexivity
      | change (data_eqb [6;0;22] [17;0;53]) with false; reflexivity
      | change (data_eqb [6;0;22] [6;0;53]) with false;
        change (data_eqb [17;0;53] [6;0;53]) with false; reflexivity
      | change (data_eqb [6;0;22] [17;0;67]) with false;
        change (data_eqb [17;0;53] [17;0;67]) with false;
        change (data_eqb [6;0;53] [17;0;67]) with false; reflexivity ].
Qed.

(** THE CRUX (mirrors [forward_accept_iff]): for a NEW-connection packet ingressing
    on eth1 (the LAN), the INPUT hook ACCEPTs IFF the packet is an icmp echo-request
    within the rate limit, OR its [ip protocol . th dport] is one of the four listed
    services (ssh / dns(tcp) / dns(udp) / dhcp).  Nothing else from the LAN reaches
    the box. *)
Theorem inbound_eth1_accept_iff : forall p,
  pkt_env p = gen_env ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  icmp_loads p = true ->
  svc_loads p = true ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_eth1 ->
  ( eval_table in_fuel global_chains global_inbound p = Accept <->
    ( icmp_ok p = true \/
      ( svc_key p = [6;0;22] \/ svc_key p = [17;0;53]
        \/ svc_key p = [6;0;53] \/ svc_key p = [17;0;67] ) ) ).
Proof.
  intros p Hpe Hct Hiif Hwl Hil Hsl Hcts Heth1.
  rewrite (inbound_eth1_eval p Hpe Hct Hiif Hwl Hil Hsl Hcts Heth1).
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

(** The SECURITY half: an eth1 packet that is NEITHER icmp-echo (under limit) NOR a
    listed service is DROPPED.  This is the LAN-exposure invariant — the box offers
    EXACTLY ssh/dns/dhcp + rate-limited ping to internal hosts, and nothing else. *)
Theorem inbound_eth1_unlisted_dropped : forall p,
  pkt_env p = gen_env ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  icmp_loads p = true ->
  svc_loads p = true ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_eth1 ->
  icmp_ok p = false ->
  ( svc_key p <> [6;0;22] /\ svc_key p <> [17;0;53]
    /\ svc_key p <> [6;0;53] /\ svc_key p <> [17;0;67] ) ->
  eval_table in_fuel global_chains global_inbound p = Drop.
Proof.
  intros p Hpe Hct Hiif Hwl Hil Hsl Hcts Heth1 Hicmp Hsvc.
  rewrite (inbound_eth1_eval p Hpe Hct Hiif Hwl Hil Hsl Hcts Heth1).
  rewrite Hicmp.
  destruct (svc_hit p) as [v|] eqn:Hh; [ | reflexivity ].
  exfalso. apply svc_hit_accept in Hh as Hv. subst v.
  apply svc_hit_iff in Hh.
  destruct Hsvc as [H1 [H2 [H3 H4]]].
  destruct Hh as [H|[H|[H|H]]]; congruence.
Qed.

(** The rate-limit construct GENUINELY gates: an icmp echo-request whose rate is
    EXHAUSTED ([icmp_under = false]) and that is not a listed service is DROPPED. *)
Theorem inbound_icmp_ratelimited_dropped : forall p,
  pkt_env p = gen_env ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  icmp_loads p = true ->
  svc_loads p = true ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_eth1 ->
  icmp_under p = false ->
  ( svc_key p <> [6;0;22] /\ svc_key p <> [17;0;53]
    /\ svc_key p <> [6;0;53] /\ svc_key p <> [17;0;67] ) ->
  eval_table in_fuel global_chains global_inbound p = Drop.
Proof.
  intros p Hpe Hct Hiif Hwl Hil Hsl Hcts Heth1 Hover Hsvc.
  apply (inbound_eth1_unlisted_dropped p Hpe Hct Hiif Hwl Hil Hsl Hcts Heth1); [ | exact Hsvc ].
  unfold icmp_ok. rewrite Hover. now rewrite Bool.andb_false_r.
Qed.

(** The four listed services ARE accepted (the iff is not vacuous on the accept side). *)
Theorem inbound_eth1_service_accept : forall p,
  pkt_env p = gen_env ->
  field_loadable FCtState p = true ->
  field_loadable FMetaIifname p = true ->
  world_loads p = true ->
  icmp_loads p = true ->
  svc_loads p = true ->
  field_value FCtState p = cts_new ->
  field_value FMetaIifname p = if_eth1 ->
  ( svc_key p = [6;0;22] \/ svc_key p = [17;0;53]
    \/ svc_key p = [6;0;53] \/ svc_key p = [17;0;67] ) ->
  eval_table in_fuel global_chains global_inbound p = Accept.
Proof.
  intros p Hpe Hct Hiif Hwl Hil Hsl Hcts Heth1 Hsvc.
  apply (inbound_eth1_accept_iff p Hpe Hct Hiif Hwl Hil Hsl Hcts Heth1).
  now right.
Qed.

(* ============================================================ *)
(** ** Satisfiability witnesses + mutation kill. *)

(* A realistic LAN-ingress env: gen_env's vmap contents, e_ct reports NEW, and the
   rate-limit bucket starts FULL (e_limit = a large stored level, so icmp passes). *)
Definition env_lan : env :=
  {| e_set := fun _ => []; e_vmap := e_vmap gen_env; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 100;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => cts_new; e_nat := fun _ => None;
     e_numgen := fun _ => 0 |}.

(* An IPv4 header with proto byte [pr] at byte 9 (and a dummy source/dest). *)
Definition ip4_proto (pr : nat) : data :=
  ([69; 0; 0; 40; 0; 0; 0; 0; 64; pr; 0; 0] ++ [10;0;0;5] ++ [10;0;0;1])%list.
(* A transport header with destination port [d] (bytes 2..3). *)
Definition th_dport (d : nat) : data :=
  [0;0; Nat.div d 256; Nat.modulo d 256; 0;0;0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0]%list.
(* An ICMP header with type [t] at byte 0. *)
Definition icmp_th (t : nat) : data :=
  [t; 0; 0;0; 0;0;0;0]%list.

(* A LAN packet on eth1, NEW ct, ip proto [pr], transport carrying [th]. *)
Definition mk_lan (pr : nat) (th : data) : packet :=
  {| pkt_env := env_lan;
     pkt_meta := fun k => if meta_eqb k MKiifname then if_eth1
                          else if meta_eqb k MKl4proto then [pr] else [];
     pkt_ct := fun _ => []; pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := ip4_proto pr; pkt_th := th; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := true;
     pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false;
     pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* dns over udp (proto 17, dport 53): a listed service -> ACCEPT. *)
Definition pkt_lan_dns  : packet := mk_lan 17 (th_dport 53).
(* dhcp (proto 17, dport 67): a listed service -> ACCEPT. *)
Definition pkt_lan_dhcp : packet := mk_lan 17 (th_dport 67).
(* ssh over tcp (proto 6, dport 22): a listed service -> ACCEPT. *)
Definition pkt_lan_ssh  : packet := mk_lan 6 (th_dport 22).
(* icmp echo-request (proto 1, type 8) -> ACCEPT (under the full-bucket limit). *)
Definition pkt_lan_ping : packet := mk_lan 1 (icmp_th 8).
(* smtp over tcp (proto 6, dport 25): UNLISTED, not icmp -> DROP. *)
Definition pkt_lan_smtp : packet := mk_lan 6 (th_dport 25).

Theorem pkt_lan_dns_accepted :
  eval_table in_fuel global_chains global_inbound pkt_lan_dns = Accept.
Proof. vm_compute. reflexivity. Qed.

Theorem pkt_lan_dhcp_accepted :
  eval_table in_fuel global_chains global_inbound pkt_lan_dhcp = Accept.
Proof. vm_compute. reflexivity. Qed.

Theorem pkt_lan_ssh_accepted :
  eval_table in_fuel global_chains global_inbound pkt_lan_ssh = Accept.
Proof. vm_compute. reflexivity. Qed.

Theorem pkt_lan_ping_accepted :
  eval_table in_fuel global_chains global_inbound pkt_lan_ping = Accept.
Proof. vm_compute. reflexivity. Qed.

(* The UNLISTED smtp packet is DROPPED by the parser's chain (the security crux). *)
Theorem pkt_lan_smtp_dropped :
  eval_table in_fuel global_chains global_inbound pkt_lan_smtp = Drop.
Proof. vm_compute. reflexivity. Qed.

(* [bug_inbound_private] = inbound_private with rule 2's concat-vmap WIDENED to an
   unconditional static accept ([r_body := []; r_verdict := Accept]) — modelling
   [__map0] opened to a catch-all (the proto.port guard dropped).  This is the
   catastrophic LAN-OPEN bug: every LAN packet to the box is now accepted. *)
Definition bug_inbound_private : chain :=
  {| c_policy := Continue;
     c_rules := [r_icmp;
                 {| r_body := []; r_verdict := Accept; r_vmap := None;
                    r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None;
                    r_after := [] |}] |}.

(* The chain env with ONLY inbound_private swapped (global_inbound itself unchanged,
   so every prior Router_Input theorem still holds verbatim). *)
Definition bug_priv_chains : list (string * chain) :=
  [("inbound_world", global_inbound_world);
   ("inbound_private", bug_inbound_private);
   ("inbound", global_inbound);
   ("forward", global_forward);
   ("postrouting", global_postrouting)].

(* Under the bug, the SAME unlisted smtp packet is ACCEPTED — the LAN-open hole. *)
Theorem bug_lan_smtp_accepted :
  eval_table in_fuel bug_priv_chains global_inbound pkt_lan_smtp = Accept.
Proof. vm_compute. reflexivity. Qed.

(* Hence the private characterisation DISCRIMINATES the catch-all bug that the
   prior (Router_Input) property set could not see: on the same unlisted LAN packet
   the parser's chain DROPs while the widened chain ACCEPTs. *)
Theorem priv_property_discriminates_bug :
  eval_table in_fuel global_chains global_inbound pkt_lan_smtp
  <> eval_table in_fuel bug_priv_chains global_inbound pkt_lan_smtp.
Proof. rewrite pkt_lan_smtp_dropped, bug_lan_smtp_accepted. discriminate. Qed.

(* The accept-side hypotheses are SATISFIABLE: the dns witness meets every
   hypothesis of [inbound_eth1_service_accept]. *)
Lemma pkt_lan_dns_facts :
  field_loadable FCtState pkt_lan_dns = true /\
  field_loadable FMetaIifname pkt_lan_dns = true /\
  world_loads pkt_lan_dns = true /\
  icmp_loads pkt_lan_dns = true /\
  svc_loads pkt_lan_dns = true /\
  field_value FCtState pkt_lan_dns = cts_new /\
  field_value FMetaIifname pkt_lan_dns = if_eth1 /\
  svc_key pkt_lan_dns = [17;0;53].
Proof. repeat split; try (vm_compute; reflexivity). Qed.

(* The drop-side hypotheses are SATISFIABLE: the smtp witness meets every
   hypothesis of [inbound_eth1_unlisted_dropped]. *)
Lemma pkt_lan_smtp_facts :
  field_loadable FCtState pkt_lan_smtp = true /\
  field_loadable FMetaIifname pkt_lan_smtp = true /\
  world_loads pkt_lan_smtp = true /\
  icmp_loads pkt_lan_smtp = true /\
  svc_loads pkt_lan_smtp = true /\
  field_value FCtState pkt_lan_smtp = cts_new /\
  field_value FMetaIifname pkt_lan_smtp = if_eth1 /\
  icmp_ok pkt_lan_smtp = false /\
  svc_key pkt_lan_smtp = [6;0;25].
Proof. repeat split; try (vm_compute; reflexivity). Qed.
