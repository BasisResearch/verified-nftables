(** * router.nft postrouting masquerade — DATA-PLANE source-NAT characterisation

    The security crux of a NAT router is its postrouting `masquerade` rule:

        chain postrouting { type nat hook postrouting priority 100; policy accept;
                            ip saddr 192.168.0.0/16 oifname ppp0 masquerade }

    A *verdict-only* property about [global_postrouting] is VACUOUS: masquerade is a
    terminal-Accept whose only effect lives in the PACKET component of the trace
    evaluator ([apply_nat] / [masq_saddr] / [store_nat_mapping], surfaced through
    [eval_chain_trace] / [chain_out]); the chain's policy is `accept`, so a verdict
    property pins down NOTHING about the source rewrite — it holds identically whether
    masquerade fires correctly, never fires, or is mutated to source-NAT every packet.

    This file states the property where it actually lives: the source-ADDRESS slice
    of the packet the chain emits, as a TWO-DIRECTIONAL pair about the PARSER-generated
    chain [global_postrouting] (from [Router_Gen]):

      (a) FIRES — a private source (192.168.0.0/16) egressing ppp0, on the first
          (unconfirmed, original-direction) packet of its flow with a usable exit
          address [wan], has its IPv4 source slot REWRITTEN to [wan], and the flow's
          NAT mapping is STORED ([nat_masquerade_fires]).

      (b) NO-FIRE (the security half) — a packet whose source is NOT in 192.168.0.0/16
          OR whose oifname is NOT ppp0 is returned BYTE-FOR-BYTE UNCHANGED: no source
          rewrite, no internal-address leak, no mapping stored
          ([nat_masquerade_does_not_fire]).

    Half (b) is what KILLS the planted NAT-leak bug ([bug_postrouting], which drops the
    `ip saddr 192.168.0.0/16` guard so it masquerades EVERY source out ppp0): under the
    bug a non-private source out ppp0 IS rewritten, so (b) is FALSE for it
    ([bug_breaks_no_fire]) — exactly the discrimination the verdict layer lacks. *)

From Stdlib Require Import List String NArith Lia.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Semantics Router_Gen.

Open Scope string_scope.
Local Open Scope bool_scope.

(* The IPv4 source-address slot the kernel masquerade rewrites: network-header
   bytes 12..15, exactly where [FIp4Saddr] reads. *)
Definition saddr4 (p : packet) : data := slice (pkt_nh p) 12 4.

(* The interface name "ppp0" as the 16-byte zero-padded ASCII the parser emits
   (matches the [MEq FMetaOifname ...] literal the parser put in the rule). *)
Definition if_ppp0 : data := [112; 112; 112; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].

(* The masquerade NAT spec the parser emitted for `masquerade` (family ip). *)
Definition masq_spec : nat_spec :=
  {| nat_imms := []; nat_field := None; nat_map := None; nat_src := None;
     nat_kind := "masq"; nat_family := "ip"; nat_amin := None; nat_amax := None;
     nat_pmin := None; nat_pmax := None; nat_flags := 0 |}.

(* The masquerade rule = the single rule of the generated postrouting chain,
   reproduced for unfolding; proved equal to the parser output below. *)
Definition masq_rule : rule :=
  {| r_body := [(BMatch (MMasked FIp4Saddr false [255; 255; 0; 0] [0; 0; 0; 0] [192; 168; 0; 0]));
                (BMatch (MEq FMetaOifname if_ppp0))];
     r_verdict := Accept; r_vmap := None; r_nat := Some masq_spec;
     r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.

(* The reproduced rule IS the parser's postrouting rule. *)
Lemma global_postrouting_rules : global_postrouting.(c_rules) = [masq_rule].
Proof. reflexivity. Qed.

(* The rule's body has no limiters / writes, so [dsl_step] is the identity: the
   body is two [BMatch]es, and [body_writes] over matches returns the input. *)
Lemma masq_dsl_step_id : forall p, dsl_step masq_rule p = p.
Proof.
  intro p. rewrite dsl_step_limit_free by reflexivity.
  unfold dsl_writes, masq_rule; cbn [r_body body_writes].
  destruct (eval_matchcond (MMasked FIp4Saddr false [255;255;0;0] [0;0;0;0] [192;168;0;0]) p);
    [destruct (eval_matchcond (MEq FMetaOifname if_ppp0) p)|]; reflexivity.
Qed.

(* The body-thread leaves the packet alone (no notrack in the body). *)
Lemma masq_body_thread_id : forall p, body_thread (r_body masq_rule) p = p.
Proof. reflexivity. Qed.

(* [set_saddr] preserves the env and the flow (it only ever splices header bytes /
   the L4 checksum slot — every component copy keeps [pkt_env] and [pkt_flow]). *)
Lemma set_l4_csum_addr_env : forall p old new,
  pkt_env (set_l4_csum_addr p old new) = pkt_env p
  /\ pkt_flow (set_l4_csum_addr p old new) = pkt_flow p.
Proof.
  intros p old new. unfold set_l4_csum_addr.
  destruct (l4_csum_slot (pkt_meta p MKl4proto)) as [[[coff clen] mand]|];
    [|split; reflexivity].
  destruct (pkt_have_l4 p && Nat.leb (coff + clen) (List.length (pkt_th p)));
    [|split; reflexivity].
  destruct (negb mand && N.eqb (data_to_N (slice (pkt_th p) coff clen)) 0);
    split; reflexivity.
Qed.

Lemma set_saddr_env : forall fam p v, pkt_env (set_saddr fam p v) = pkt_env p.
Proof.
  intros fam p v. unfold set_saddr. destruct (saddr_slot fam) as [off len].
  rewrite (proj1 (set_l4_csum_addr_env _ _ _)).
  destruct (String.eqb fam nat_fam_ip6); reflexivity.
Qed.
Lemma set_saddr_flow : forall fam p v, pkt_flow (set_saddr fam p v) = pkt_flow p.
Proof.
  intros fam p v. unfold set_saddr. destruct (saddr_slot fam) as [off len].
  rewrite (proj2 (set_l4_csum_addr_env _ _ _)).
  destruct (String.eqb fam nat_fam_ip6); reflexivity.
Qed.

(* ============================================================ *)
(** ** When the masquerade rule APPLIES (saddr in /16 AND oif = ppp0). *)

(* `ip saddr 192.168.0.0/16` masked-matches iff (saddr & 0xffff0000) = 192.168.0.0,
   i.e. the first two address bytes are 192.168. *)
Definition saddr_private (p : packet) : bool :=
  eval_matchcond (MMasked FIp4Saddr false [255;255;0;0] [0;0;0;0] [192;168;0;0]) p.

Definition oif_ppp0 (p : packet) : bool :=
  eval_matchcond (MEq FMetaOifname if_ppp0) p.

(* [rule_applies] for the masq rule = both matches pass. *)
Lemma masq_rule_applies_eq : forall p,
  rule_applies masq_rule p = saddr_private p && oif_ppp0 p.
Proof.
  intro p. unfold rule_applies, masq_rule, saddr_private, oif_ppp0; cbn [r_body].
  cbn [rule_applies_walk]. now rewrite Bool.andb_true_r.
Qed.

(* ------------------------------------------------------------ *)
(** *** Half (a): the masquerade FIRES — the source is rewritten to the exit
       interface address, and the mapping is stored. *)

(* On the first (unconfirmed, original-direction) packet of a flow, [apply_nat] of
   the masq rule source-rewrites to the exit-interface address [wan] and stores the
   tuple — the masquerade data-plane effect. *)
Lemma masq_apply : forall h p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  apply_nat h masq_rule p
    = store_nat_mapping
        (set_saddr "ip" p (e_ifaddr (pkt_env p) (field_value FMetaOifname p)))
        (Some (slice (pkt_nh p) 12 4),
         Some (e_ifaddr (pkt_env p) (field_value FMetaOifname p)), None, None).
Proof.
  intros h p Horig Hnone. unfold apply_nat, masq_rule, masq_spec.
  cbn -[set_saddr store_nat_mapping e_nat pkt_env pkt_flow e_ifaddr field_value
        slice pkt_nh masq_saddr nat_operand_addr apply_nat_tuple nat_orig_addr].
  rewrite Hnone.
  unfold apply_nat_tuple, nat_orig_addr, nat_is_src, nat_addrfamily_pkt, nat_addrfamily,
    nat_operand_addr, masq_saddr.
  cbn -[set_saddr store_nat_mapping e_ifaddr field_value slice pkt_nh]. rewrite ?Horig.
  reflexivity.
Qed.

(* The masquerade does NOT hit the NAT-core "no usable address" NF_DROP when the
   exit interface HAS an address (the masq_saddr is non-empty). *)
Lemma masq_no_drop : forall h p,
  e_ifaddr (pkt_env p) (field_value FMetaOifname p) <> [] ->
  nat_drops h masq_rule p = false.
Proof.
  intros h p Hwan. unfold nat_drops, masq_rule.
  destruct (e_nat (pkt_env p) (pkt_flow p)); [reflexivity|].
  unfold nat_iface_addr_absent, masq_spec; cbn [nat_kind r_nat].
  unfold nat_addrfamily_pkt, nat_addrfamily, masq_saddr; cbn -[e_ifaddr field_value].
  destruct (pkt_ctdir_orig p); [|reflexivity].
  cbn [andb]. destruct (e_ifaddr (pkt_env p) (field_value FMetaOifname p)) eqn:E;
    [exfalso; now apply Hwan | reflexivity].
Qed.

(* THE OUTPUT PACKET of the postrouting chain when masquerade fires. *)
Theorem nat_masquerade_fires_output : forall p wan,
  saddr_private p = true ->
  oif_ppp0 p = true ->
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  e_ifaddr (pkt_env p) (field_value FMetaOifname p) = wan ->
  wan <> [] ->
  eval_chain_trace Hpostrouting global_postrouting p
    = (Accept, store_nat_mapping (set_saddr "ip" p wan)
                 (Some (slice (pkt_nh p) 12 4), Some wan, None, None)).
Proof.
  intros p wan Hpriv Hppp Horig Hnone Hwan Hne.
  unfold eval_chain_trace. rewrite global_postrouting_rules. cbn [c_rules eval_rules_trace].
  assert (Hload : rule_loadable masq_rule p = true).
  { (* both matches load: the masked saddr load and the oifname meta load.  When the
       rule applies, [saddr_private]/[oif_ppp0] are true (each = load && body), which
       supply the loads; the end part is unconditionally loadable (NAT, vmap None). *)
    unfold saddr_private, oif_ppp0, eval_matchcond in Hpriv, Hppp.
    apply Bool.andb_true_iff in Hpriv as [Hpl _].
    apply Bool.andb_true_iff in Hppp as [Hol _].
    unfold rule_loadable, masq_rule; cbn [r_body body_loadable_walk
      body_synproxy_stops existsb body_item_loadable body_thread body_has_notrack].
    cbn [match_loadable] in Hpl, Hol |- *. rewrite Hpl, Hol. reflexivity. }
  assert (Happ : rule_applies masq_rule p = true)
    by (rewrite masq_rule_applies_eq, Hpriv, Hppp; reflexivity).
  rewrite Hload, Happ. cbn [andb].
  assert (Ho : outcome masq_rule p = Some Accept) by reflexivity.
  rewrite Ho. cbn [terminal].
  rewrite masq_dsl_step_id.
  rewrite (masq_no_drop Hpostrouting p) by (rewrite Hwan; exact Hne).
  rewrite (masq_apply Hpostrouting p Horig Hnone), Hwan. reflexivity.
Qed.

(* The IPv4 source slot of the emitted packet IS the exit-interface address — the
   internal source 192.168.x.y has been replaced by the WAN address. *)
Theorem nat_masquerade_fires : forall p wan,
  saddr_private p = true ->
  oif_ppp0 p = true ->
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  e_ifaddr (pkt_env p) (field_value FMetaOifname p) = wan ->
  wan <> [] ->
  16 <= List.length (pkt_nh p) ->
  List.length wan = 4 ->
  saddr4 (chain_out Hpostrouting global_postrouting p) = wan
  /\ e_nat (pkt_env (chain_out Hpostrouting global_postrouting p)) (pkt_flow p)
       = Some (Some (slice (pkt_nh p) 12 4), Some wan, None, None).
Proof.
  intros p wan Hpriv Hppp Horig Hnone Hwan Hne Hnh Hwl. unfold chain_out, saddr4.
  rewrite (nat_masquerade_fires_output p wan Hpriv Hppp Horig Hnone Hwan Hne).
  cbn [snd]. split.
  - (* source slot = wan, read back through store_nat_mapping (env-only) + set_saddr *)
    unfold store_nat_mapping at 1; cbn [pkt_nh].
    apply slice_set_saddr_ip4_same; assumption.
  - (* the stored mapping is recorded at this flow *)
    unfold store_nat_mapping at 1; cbn [pkt_env pkt_flow].
    rewrite set_saddr_env, set_saddr_flow.
    unfold env_nat_upd; cbn [e_nat]. now rewrite data_eqb_refl.
Qed.

(* ------------------------------------------------------------ *)
(** *** Half (b): the masquerade does NOT fire — packet returned UNCHANGED. *)

(* When the rule does NOT apply (saddr not in /16 OR oif <> ppp0), the postrouting
   chain returns the packet BYTE-FOR-BYTE UNCHANGED: no source rewrite, no leak. *)
Theorem nat_masquerade_does_not_fire : forall p,
  rule_applies masq_rule p = false ->
  chain_out Hpostrouting global_postrouting p = p.
Proof.
  intros p Happ. unfold chain_out, eval_chain_trace.
  rewrite global_postrouting_rules. cbn [c_rules eval_rules_trace].
  rewrite Happ, Bool.andb_false_r. cbn [snd]. apply masq_dsl_step_id.
Qed.

(* Phrased on the security HYPOTHESES: a packet whose source is NOT private OR whose
   oifname is NOT ppp0 has its source slot UNCHANGED and no mapping stored. *)
Theorem nat_no_leak : forall p,
  (saddr_private p = false \/ oif_ppp0 p = false) ->
  saddr4 (chain_out Hpostrouting global_postrouting p) = saddr4 p
  /\ pkt_env (chain_out Hpostrouting global_postrouting p) = pkt_env p.
Proof.
  intros p Hor.
  assert (Happ : rule_applies masq_rule p = false).
  { rewrite masq_rule_applies_eq. destruct Hor as [H|H]; rewrite H;
      [reflexivity | now rewrite Bool.andb_false_r]. }
  rewrite (nat_masquerade_does_not_fire p Happ). split; reflexivity.
Qed.

(* ============================================================ *)
(** ** The discrimination: a PLANTED NAT-leak bug survives the verdict but is
       caught by half (b). *)

(* [bug_postrouting] = the postrouting chain with the `ip saddr 192.168.0.0/16`
   guard REMOVED, so it masquerades EVERY source egressing ppp0 (a real
   internal-address leak: it source-NATs traffic it must not). *)
Definition bug_rule : rule :=
  {| r_body := [(BMatch (MEq FMetaOifname if_ppp0))];
     r_verdict := Accept; r_vmap := None; r_nat := Some masq_spec;
     r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.
Definition bug_postrouting : chain :=
  {| c_policy := Accept; c_rules := [bug_rule] |}.

Lemma bug_dsl_step_id : forall p, dsl_step bug_rule p = p.
Proof.
  intro p. rewrite dsl_step_limit_free by reflexivity.
  unfold dsl_writes, bug_rule; cbn [r_body body_writes].
  destruct (eval_matchcond (MEq FMetaOifname if_ppp0) p); reflexivity.
Qed.

Lemma bug_apply : forall h p,
  pkt_ctdir_orig p = true ->
  e_nat (pkt_env p) (pkt_flow p) = None ->
  apply_nat h bug_rule p
    = store_nat_mapping
        (set_saddr "ip" p (e_ifaddr (pkt_env p) (field_value FMetaOifname p)))
        (Some (slice (pkt_nh p) 12 4),
         Some (e_ifaddr (pkt_env p) (field_value FMetaOifname p)), None, None).
Proof.
  intros h p Horig Hnone. unfold apply_nat, bug_rule, masq_spec.
  cbn -[set_saddr store_nat_mapping e_nat pkt_env pkt_flow e_ifaddr field_value
        slice pkt_nh].
  rewrite Hnone.
  unfold apply_nat_tuple, nat_orig_addr, nat_is_src, nat_addrfamily_pkt, nat_addrfamily,
    nat_operand_addr, masq_saddr.
  cbn -[set_saddr store_nat_mapping e_ifaddr field_value slice pkt_nh]. rewrite ?Horig.
  reflexivity.
Qed.

(* The buggy chain rewrites the source of a packet egressing ppp0 EVEN WHEN the
   source is NOT private — half (b) is FALSE for it.  Witnessed on a concrete packet
   with a public source 8.8.8.8 out ppp0 and a usable WAN address 203.0.113.7. *)
Definition wan_addr : data := [203; 0; 113; 7].

(* A well-formed 20-byte IPv4 header, source 8.8.8.8 (NOT in 192.168.0.0/16). *)
Definition ip4_pub : data :=
  [ 69; 0; 0; 20; 0; 0; 0; 0; 64; 6; 0; 0;  (* ver/ihl..ttl/proto/csum *)
    8; 8; 8; 8;                              (* source 8.8.8.8 *)
    1; 2; 3; 4 ].                            (* destination *)

Definition env_bug : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0;
     e_ifaddr := fun n => if data_eqb n if_ppp0 then wan_addr else [];
     e_ifaddr6 := fun _ => []; e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

Definition pkt_pub : packet :=
  {| pkt_env := env_bug;
     pkt_meta := fun k => if meta_eqb k MKoifname then if_ppp0 else [];
     pkt_ct := fun _ => []; pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := ip4_pub; pkt_th := [0;0;0;0;0;0;0;0]; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := true;
     pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false;
     pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* The witness packet has a PUBLIC, non-private source: half (b)'s hypothesis holds. *)
Lemma pkt_pub_not_private : saddr_private pkt_pub = false.
Proof. vm_compute. reflexivity. Qed.

(* For the CORRECT chain, the source slot of the witness is UNCHANGED (8.8.8.8) —
   half (b) (and [nat_no_leak]) holds. *)
Theorem correct_keeps_public_source :
  saddr4 (chain_out Hpostrouting global_postrouting pkt_pub) = [8;8;8;8].
Proof.
  pose proof (nat_no_leak pkt_pub (or_introl pkt_pub_not_private)) as [Hkeep _].
  rewrite Hkeep. vm_compute. reflexivity.
Qed.

(* For the BUGGY chain, the SAME witness has its source REWRITTEN to the WAN address
   (the leak): half (b) is FALSE for [bug_postrouting]. *)
Theorem bug_breaks_no_fire :
  saddr4 (snd (eval_chain_trace Hpostrouting bug_postrouting pkt_pub)) = wan_addr.
Proof. vm_compute. reflexivity. Qed.

(* Hence the data-plane property DISCRIMINATES the bug: the correct chain leaves the
   public source [8;8;8;8], the buggy chain leaks it as the WAN address — the two
   chains are observably different on the SOURCE SLICE, the discrimination a
   verdict-only property (both chains accept) cannot make. *)
Theorem property_discriminates_bug :
  saddr4 (chain_out Hpostrouting global_postrouting pkt_pub)
  <> saddr4 (snd (eval_chain_trace Hpostrouting bug_postrouting pkt_pub)).
Proof.
  rewrite correct_keeps_public_source, bug_breaks_no_fire. discriminate.
Qed.

(* ============================================================ *)
(** ** Satisfiability: half (a)'s hypotheses are not vacuous — a witness that
       FIRES (private source 192.168.1.5 out ppp0 -> rewritten to WAN). *)

Definition ip4_priv : data :=
  [ 69; 0; 0; 20; 0; 0; 0; 0; 64; 6; 0; 0;
    192; 168; 1; 5;                          (* source 192.168.1.5 (in /16) *)
    1; 2; 3; 4 ].

Definition pkt_priv : packet :=
  {| pkt_env := env_bug;
     pkt_meta := fun k => if meta_eqb k MKoifname then if_ppp0 else [];
     pkt_ct := fun _ => []; pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := ip4_priv; pkt_th := [0;0;0;0;0;0;0;0]; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := true;
     pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false;
     pkt_ctdir_orig := true; pkt_ct_present := true |}.

Lemma pkt_priv_private : saddr_private pkt_priv = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pkt_priv_oif : oif_ppp0 pkt_priv = true.
Proof. vm_compute. reflexivity. Qed.

(* The firing witness: the private source 192.168.1.5 IS rewritten to the WAN
   address — half (a) is satisfiable (and the source actually changes). *)
Theorem witness_fires :
  saddr4 (chain_out Hpostrouting global_postrouting pkt_priv) = wan_addr.
Proof. vm_compute. reflexivity. Qed.
