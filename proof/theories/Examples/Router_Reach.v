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
From Nft Require Import Bytes Packet Verdict Bytecode Syntax Semantics Router_Gen.

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
  {| nat_addr_imm := None; nat_field := None; nat_map := None; nat_src := None;
     nat_kind := NKmasq; nat_family := NFip4; nat_extra := NXnone; nat_flags := 0 |}.

(* The masquerade rule = the single rule of the generated postrouting chain,
   reproduced for unfolding; proved equal to the parser output below. *)
Definition masq_rule : rule :=
  {| r_body := [(BMatch (MEq (FPayload PNetwork 12 2) [192; 168]));
                (BMatch (MEq FMetaOifname if_ppp0))];
     r_outcome := ONat masq_spec; r_after := [] |}.

(* The reproduced rule IS the parser's postrouting rule. *)
Lemma global_postrouting_rules : global_postrouting.(c_rules) = [masq_rule].
Proof. reflexivity. Qed.

(* The rule's body has no limiters / writes, so [dsl_step] is the identity: the
   body is two [BMatch]es, and [body_writes] over matches returns the input. *)
Lemma masq_dsl_step_id : forall e p, dsl_step masq_rule e p = (e, p).
Proof.
  intros e p. rewrite dsl_step_limit_free by reflexivity.
  unfold dsl_writes, body_writes, masq_rule; cbn [r_body body_step].
  destruct (eval_matchcond (MEq (FPayload PNetwork 12 2) [192;168]) e p);
    [destruct (eval_matchcond (MEq FMetaOifname if_ppp0) e p)|]; reflexivity.
Qed.

(* The body-thread leaves the packet alone (no notrack in the body). *)
Lemma masq_body_thread_id : forall p, body_thread (r_body masq_rule) p = p.
Proof. reflexivity. Qed.

(* [set_saddr] preserves the flow key (it only ever splices header bytes /
   the L4 checksum slot — every component copy keeps [pkt_flow]; the shared env
   is a separate argument the packet rewrite cannot touch at all). *)
Lemma set_l4_csum_addr_flow : forall p old new,
  pkt_flow (set_l4_csum_addr p old new) = pkt_flow p.
Proof.
  intros p old new. unfold set_l4_csum_addr.
  destruct (l4_csum_slot (pkt_meta p MKl4proto)) as [[[coff clen] mand]|];
    [|reflexivity].
  destruct (pkt_have_l4 p && Nat.leb (coff + clen) (List.length (pkt_th p)));
    [|reflexivity].
  destruct (negb mand && N.eqb (data_to_N (slice (pkt_th p) coff clen)) 0);
    reflexivity.
Qed.

Lemma set_saddr_flow : forall fam p v, pkt_flow (set_saddr fam p v) = pkt_flow p.
Proof.
  intros fam p v. unfold set_saddr. destruct (saddr_slot fam) as [off len].
  rewrite set_l4_csum_addr_flow.
  destruct (nataf_eqb fam nat_fam_ip6); reflexivity.
Qed.

(* ============================================================ *)
(** ** When the masquerade rule APPLIES (saddr in /16 AND oif = ppp0). *)

(* `ip saddr 192.168.0.0/16` lowers to a byte-aligned PREFIX compare (the first
   two address bytes equal 192.168) — a 2-byte payload read at network offset 12. *)
Definition saddr_private (e : env) (p : packet) : bool :=
  eval_matchcond (MEq (FPayload PNetwork 12 2) [192;168]) e p.

Definition oif_ppp0 (e : env) (p : packet) : bool :=
  eval_matchcond (MEq FMetaOifname if_ppp0) e p.

(* [rule_applies] for the masq rule = both matches pass. *)
Lemma masq_rule_applies_eq : forall e p,
  rule_applies masq_rule e p = saddr_private e p && oif_ppp0 e p.
Proof.
  intros e p. unfold rule_applies, masq_rule, saddr_private, oif_ppp0; cbn [r_body].
  cbn [rule_applies_walk]. now rewrite Bool.andb_true_r.
Qed.

(* ------------------------------------------------------------ *)
(** *** Half (a): the masquerade FIRES — the source is rewritten to the exit
       interface address, and the mapping is stored. *)

(* On the first (unconfirmed, original-direction) packet of a flow, [apply_nat] of
   the masq rule source-rewrites to the exit-interface address [wan] and stores the
   tuple — the masquerade data-plane effect. *)
Lemma masq_apply : forall h e p,
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  apply_nat h masq_rule e p
    = (store_nat_mapping e p
         (Some (slice (pkt_nh p) 12 4),
          Some (e_ifaddr e (field_value FMetaOifname e p)), None, None),
       set_saddr nat_fam_ip4 p (e_ifaddr e (field_value FMetaOifname e p))).
Proof.
  intros h e p Horig Hnone. unfold apply_nat, masq_rule, masq_spec.
  cbn -[set_saddr store_nat_mapping e_nat pkt_flow e_ifaddr field_value
        slice pkt_nh masq_saddr nat_operand_addr apply_nat_tuple nat_orig_addr].
  rewrite Hnone.
  unfold apply_nat_tuple, nat_orig_addr, nat_is_src, nat_addrfamily_pkt, nat_addrfamily,
    nat_operand_addr, masq_saddr.
  cbn -[set_saddr store_nat_mapping e_ifaddr field_value slice pkt_nh]. rewrite ?Horig.
  reflexivity.
Qed.

(* The masquerade does NOT hit the NAT-core "no usable address" NF_DROP when the
   exit interface HAS an address (the masq_saddr is non-empty). *)
Lemma masq_no_drop : forall h e p,
  e_ifaddr e (field_value FMetaOifname e p) <> [] ->
  nat_drops h masq_rule e p = false.
Proof.
  intros h e p Hwan. unfold nat_drops, masq_rule.
  destruct (e_nat e (pkt_flow p)); [reflexivity|].
  unfold nat_iface_addr_absent, masq_spec; cbn [nat_kind r_nat r_outcome].
  unfold nat_addrfamily_pkt, nat_addrfamily, masq_saddr; cbn -[e_ifaddr field_value].
  destruct (pkt_ctdir_orig p); [|reflexivity].
  cbn [andb]. destruct (e_ifaddr e (field_value FMetaOifname e p)) eqn:E;
    [exfalso; now apply Hwan | reflexivity].
Qed.

(* THE OUTPUT PACKET of the postrouting chain when masquerade fires. *)
Theorem nat_masquerade_fires_output : forall e p wan,
  saddr_private e p = true ->
  oif_ppp0 e p = true ->
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  e_ifaddr e (field_value FMetaOifname e p) = wan ->
  wan <> [] ->
  eval_chain_trace Hpostrouting global_postrouting e p
    = (Accept, (store_nat_mapping e p
                  (Some (slice (pkt_nh p) 12 4), Some wan, None, None),
                set_saddr nat_fam_ip4 p wan)).
Proof.
  intros e p wan Hpriv Hppp Horig Hnone Hwan Hne.
  unfold eval_chain_trace. rewrite global_postrouting_rules. cbn [c_rules eval_rules_trace].
  assert (Hload : rule_loadable masq_rule e p = true).
  { (* both matches load: the masked saddr load and the oifname meta load.  When the
       rule applies, [saddr_private]/[oif_ppp0] are true (each = load && body), which
       supply the loads; the end part is unconditionally loadable (NAT, vmap None). *)
    unfold saddr_private, oif_ppp0, eval_matchcond in Hpriv, Hppp.
    apply Bool.andb_true_iff in Hpriv as [Hpl _].
    apply Bool.andb_true_iff in Hppp as [Hol _].
    unfold rule_loadable, masq_rule; cbn [r_body body_loadable_walk
      body_synproxy_stops existsb body_item_loadable body_thread body_has_notrack].
    cbn [match_loadable] in Hpl, Hol |- *. rewrite Hpl, Hol. reflexivity. }
  assert (Happ : rule_applies masq_rule e p = true)
    by (rewrite masq_rule_applies_eq, Hpriv, Hppp; reflexivity).
  assert (Ho : outcome masq_rule e p = Some Accept) by reflexivity.
  assert (Hd : dsl_rule_step masq_rule e p = (Some Accept, (e, p))).
  { unfold dsl_rule_step. rewrite rule_step_mutfree by reflexivity.
    rewrite Hload, Happ. cbn [andb]. rewrite Ho. reflexivity. }
  rewrite Hd. cbn [terminal].
  rewrite (masq_no_drop Hpostrouting e p) by (rewrite Hwan; exact Hne).
  rewrite (masq_apply Hpostrouting e p Horig Hnone), Hwan. reflexivity.
Qed.

(* The IPv4 source slot of the emitted packet IS the exit-interface address — the
   internal source 192.168.x.y has been replaced by the WAN address. *)
Theorem nat_masquerade_fires : forall e p wan,
  saddr_private e p = true ->
  oif_ppp0 e p = true ->
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  e_ifaddr e (field_value FMetaOifname e p) = wan ->
  wan <> [] ->
  16 <= List.length (pkt_nh p) ->
  List.length wan = 4 ->
  saddr4 (chain_out Hpostrouting global_postrouting e p) = wan
  /\ e_nat (chain_out_env Hpostrouting global_postrouting e p) (pkt_flow p)
       = Some (Some (slice (pkt_nh p) 12 4), Some wan, None, None).
Proof.
  intros e p wan Hpriv Hppp Horig Hnone Hwan Hne Hnh Hwl.
  unfold chain_out, chain_out_env, saddr4.
  rewrite (nat_masquerade_fires_output e p wan Hpriv Hppp Horig Hnone Hwan Hne).
  cbn [fst snd]. split.
  - (* source slot = wan through set_saddr (the env write cannot touch the bytes) *)
    apply slice_set_saddr_ip4_same; assumption.
  - (* the stored mapping is recorded at this flow *)
    unfold store_nat_mapping, env_nat_upd; cbn [with_e_nat e_nat].
    now rewrite data_eqb_refl.
Qed.

(** Axiom-freedom guard (build-time; mirrors Fib_Local.v): prints "Closed under
    the global context". *)
Print Assumptions nat_masquerade_fires.

(* ------------------------------------------------------------ *)
(** *** Half (b): the masquerade does NOT fire — packet returned UNCHANGED. *)

(* When the rule does NOT apply (saddr not in /16 OR oif <> ppp0), the postrouting
   chain returns the packet BYTE-FOR-BYTE UNCHANGED: no source rewrite, no leak. *)
Theorem nat_masquerade_does_not_fire : forall e p,
  rule_applies masq_rule e p = false ->
  chain_out Hpostrouting global_postrouting e p = p
  /\ chain_out_env Hpostrouting global_postrouting e p = e.
Proof.
  intros e p Happ. unfold chain_out, chain_out_env, eval_chain_trace.
  rewrite global_postrouting_rules. cbn [c_rules eval_rules_trace].
  assert (Hd : dsl_rule_step masq_rule e p = (None, (e, p))).
  { unfold dsl_rule_step. rewrite rule_step_mutfree by reflexivity.
    rewrite Happ, Bool.andb_false_r. reflexivity. }
  rewrite Hd. split; reflexivity.
Qed.

(* Phrased on the security HYPOTHESES: a packet whose source is NOT private OR whose
   oifname is NOT ppp0 has its source slot UNCHANGED and no mapping stored. *)
Theorem nat_no_leak : forall e p,
  (saddr_private e p = false \/ oif_ppp0 e p = false) ->
  saddr4 (chain_out Hpostrouting global_postrouting e p) = saddr4 p
  /\ chain_out_env Hpostrouting global_postrouting e p = e.
Proof.
  intros e p Hor.
  assert (Happ : rule_applies masq_rule e p = false).
  { rewrite masq_rule_applies_eq. destruct Hor as [H|H]; rewrite H;
      [reflexivity | now rewrite Bool.andb_false_r]. }
  destruct (nat_masquerade_does_not_fire e p Happ) as [Hp He].
  rewrite Hp, He. split; reflexivity.
Qed.

(* ============================================================ *)
(** ** The discrimination: a PLANTED NAT-leak bug survives the verdict but is
       caught by half (b). *)

(* [bug_postrouting] = the postrouting chain with the `ip saddr 192.168.0.0/16`
   guard REMOVED, so it masquerades EVERY source egressing ppp0 (a real
   internal-address leak: it source-NATs traffic it must not). *)
Definition bug_rule : rule :=
  {| r_body := [(BMatch (MEq FMetaOifname if_ppp0))];
     r_outcome := ONat masq_spec; r_after := [] |}.
Definition bug_postrouting : chain :=
  {| c_policy := Accept; c_rules := [bug_rule] |}.

Lemma bug_dsl_step_id : forall e p, dsl_step bug_rule e p = (e, p).
Proof.
  intros e p. rewrite dsl_step_limit_free by reflexivity.
  unfold dsl_writes, body_writes, bug_rule; cbn [r_body body_step].
  destruct (eval_matchcond (MEq FMetaOifname if_ppp0) e p); reflexivity.
Qed.

Lemma bug_apply : forall h e p,
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = None ->
  apply_nat h bug_rule e p
    = (store_nat_mapping e p
         (Some (slice (pkt_nh p) 12 4),
          Some (e_ifaddr e (field_value FMetaOifname e p)), None, None),
       set_saddr nat_fam_ip4 p (e_ifaddr e (field_value FMetaOifname e p))).
Proof.
  intros h e p Horig Hnone. unfold apply_nat, bug_rule, masq_spec.
  cbn -[set_saddr store_nat_mapping e_nat pkt_flow e_ifaddr field_value
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
     e_ifaddrs := fun n => ifaddrs_of (if data_eqb n if_ppp0 then wan_addr else []);
     e_ifaddrs6 := fun _ => []; e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

Definition pkt_pub : packet :=
  {|
     pkt_meta := fun k => if meta_eqb k MKoifname then if_ppp0 else [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := ip4_pub; pkt_th := [0;0;0;0;0;0;0;0]; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := true;
     pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false;
     pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* The witness packet has a PUBLIC, non-private source: half (b)'s hypothesis holds. *)
Lemma pkt_pub_not_private : saddr_private env_bug pkt_pub = false.
Proof. vm_compute. reflexivity. Qed.

(* For the CORRECT chain, the source slot of the witness is UNCHANGED (8.8.8.8) —
   half (b) (and [nat_no_leak]) holds. *)
Theorem correct_keeps_public_source :
  saddr4 (chain_out Hpostrouting global_postrouting env_bug pkt_pub) = [8;8;8;8].
Proof.
  pose proof (nat_no_leak env_bug pkt_pub (or_introl pkt_pub_not_private)) as [Hkeep _].
  rewrite Hkeep. vm_compute. reflexivity.
Qed.

(* For the BUGGY chain, the SAME witness has its source REWRITTEN to the WAN address
   (the leak): half (b) is FALSE for [bug_postrouting]. *)
Theorem bug_breaks_no_fire :
  saddr4 (snd (snd (eval_chain_trace Hpostrouting bug_postrouting env_bug pkt_pub))) = wan_addr.
Proof. vm_compute. reflexivity. Qed.

(* Hence the data-plane property DISCRIMINATES the bug: the correct chain leaves the
   public source [8;8;8;8], the buggy chain leaks it as the WAN address — the two
   chains are observably different on the SOURCE SLICE, the discrimination a
   verdict-only property (both chains accept) cannot make. *)
Theorem property_discriminates_bug :
  saddr4 (chain_out Hpostrouting global_postrouting env_bug pkt_pub)
  <> saddr4 (snd (snd (eval_chain_trace Hpostrouting bug_postrouting env_bug pkt_pub))).
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

Lemma pkt_priv_private : saddr_private env_bug pkt_priv = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pkt_priv_oif : oif_ppp0 env_bug pkt_priv = true.
Proof. vm_compute. reflexivity. Qed.

(* The firing witness: the private source 192.168.1.5 IS rewritten to the WAN
   address — half (a) is satisfiable (and the source actually changes). *)
Theorem witness_fires :
  saddr4 (chain_out Hpostrouting global_postrouting env_bug pkt_priv) = wan_addr.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(** ** CONFIRMED-FLOW masquerade: stored-tuple REUSE (NAT-flow stability).

    Every theorem above pins [e_nat (pkt_flow p) = None] — the FIRST (unconfirmed,
    original-direction) packet of a flow, where the kernel COMPUTES the tuple from
    the rule operand (the exit-interface address) and STORES it.  But a real
    masquerading router translates EVERY LATER packet of the same flow too, and the
    security-critical invariant is that those packets are rewritten from the STORED
    tuple — never recomputed from the current operand.  The model's [apply_nat]
    (Semantics.v:2563) has exactly this second branch: when [e_nat (pkt_flow p) =
    Some m] it applies [m] VERBATIM via [apply_nat_tuple], deliberately not re-reading
    the operand (and [nat_drops] returns [false] unconditionally on a confirmed flow,
    so the no-usable-address NF_DROP never fires either).

    The theorems below characterise that branch on the PARSER's [global_postrouting]:

      (1) [nat_masq_confirmed_reuses_stored] — an ORIGINAL-direction packet of an
          ESTABLISHED masq flow ([e_nat = Some (Some oa, Some wan, None, None)]) has
          its source slot rewritten to the STORED [wan], INDEPENDENT of the current
          exit-interface address ([e_ifaddr]) and of the packet's own private source.
          This is NAT-flow STABILITY: the translation chosen on packet 1 is reused
          for the life of the flow.

      (2) [confirmed_property_discriminates_bug] — a planted bug whose confirmed
          branch RECOMPUTES from the current operand (the exit interface's address)
          instead of reusing [m] is caught: on a flow whose CURRENT exit address
          differs from the STORED [wan], the correct chain emits the stored [wan]
          while the bug emits the recomputed (different) address.

      (3) [nat_masq_confirmed_reply_unnat] — the REPLY-direction ([pkt_ctdir_orig =
          false]) un-NAT branch: a confirmed source-NAT flow restores the reply's
          DESTINATION slot to the stored ORIGINAL address [oa] (and, the masq tuple
          carrying no port, leaves the source slot untouched). *)

(* The exit-interface address slot daddr-side helper: the dest slice for reply. *)
Definition daddr4 (p : packet) : data := slice (pkt_nh p) 16 4.

(* On a CONFIRMED original-direction flow [apply_nat] reuses the stored tuple [m]
   verbatim: for the masq tuple shape (Some oa, Some wan, None, None) the result is
   exactly [set_saddr nat_fam_ip4 p wan] — no operand re-read, no env touched. *)
Lemma masq_apply_confirmed_orig : forall h e p oa wan,
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = Some (Some oa, Some wan, None, None) ->
  apply_nat h masq_rule e p = (e, set_saddr nat_fam_ip4 p wan).
Proof.
  intros h e p oa wan Horig Hsome. unfold apply_nat, masq_rule, masq_spec.
  cbn -[set_saddr e_nat pkt_flow apply_nat_tuple].
  rewrite Hsome.
  unfold apply_nat_tuple, nat_is_src, nat_addrfamily_pkt, nat_addrfamily.
  cbn -[set_saddr]. rewrite Horig. cbn [apply_nat_port_val]. reflexivity.
Qed.

(* nat_drops is FALSE on a confirmed flow (the stored tuple is reused, no recompute,
   no no-usable-address NF_DROP). *)
Lemma masq_no_drop_confirmed : forall h e p m,
  e_nat e (pkt_flow p) = Some m ->
  nat_drops h masq_rule e p = false.
Proof.
  intros h e p m Hsome. unfold nat_drops, masq_rule; cbn [r_nat r_outcome].
  rewrite Hsome. reflexivity.
Qed.

(* THE OUTPUT PACKET of the parser's postrouting chain on a confirmed orig-direction
   masq flow: source rewritten to the STORED wan, env/flow untouched. *)
Theorem nat_masq_confirmed_output : forall e p oa wan,
  saddr_private e p = true ->
  oif_ppp0 e p = true ->
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = Some (Some oa, Some wan, None, None) ->
  chain_out Hpostrouting global_postrouting e p = set_saddr nat_fam_ip4 p wan.
Proof.
  intros e p oa wan Hpriv Hppp Horig Hsome.
  unfold chain_out, eval_chain_trace.
  rewrite global_postrouting_rules. cbn [c_rules eval_rules_trace].
  assert (Hload : rule_loadable masq_rule e p = true).
  { unfold saddr_private, oif_ppp0, eval_matchcond in Hpriv, Hppp.
    apply Bool.andb_true_iff in Hpriv as [Hpl _].
    apply Bool.andb_true_iff in Hppp as [Hol _].
    unfold rule_loadable, masq_rule; cbn [r_body body_loadable_walk
      body_synproxy_stops existsb body_item_loadable body_thread body_has_notrack].
    cbn [match_loadable] in Hpl, Hol |- *. rewrite Hpl, Hol. reflexivity. }
  assert (Happ : rule_applies masq_rule e p = true)
    by (rewrite masq_rule_applies_eq, Hpriv, Hppp; reflexivity).
  assert (Ho : outcome masq_rule e p = Some Accept) by reflexivity.
  assert (Hd : dsl_rule_step masq_rule e p = (Some Accept, (e, p))).
  { unfold dsl_rule_step. rewrite rule_step_mutfree by reflexivity.
    rewrite Hload, Happ. cbn [andb]. rewrite Ho. reflexivity. }
  rewrite Hd. cbn [terminal].
  rewrite (masq_no_drop_confirmed Hpostrouting e p _ Hsome).
  rewrite (masq_apply_confirmed_orig Hpostrouting e p oa wan Horig Hsome).
  reflexivity.
Qed.

(* (1) NAT-flow STABILITY: the source slot equals the STORED wan — independent of the
   current exit-interface address [e_ifaddr] and of the packet's own private source.
   [wan] is taken straight from the conntrack mapping [m], never from [e_ifaddr]. *)
Theorem nat_masq_confirmed_reuses_stored : forall e p oa wan,
  saddr_private e p = true ->
  oif_ppp0 e p = true ->
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = Some (Some oa, Some wan, None, None) ->
  16 <= List.length (pkt_nh p) ->
  List.length wan = 4 ->
  saddr4 (chain_out Hpostrouting global_postrouting e p) = wan.
Proof.
  intros e p oa wan Hpriv Hppp Horig Hsome Hnh Hwl. unfold saddr4.
  rewrite (nat_masq_confirmed_output e p oa wan Hpriv Hppp Horig Hsome).
  apply slice_set_saddr_ip4_same; assumption.
Qed.

(* ------------------------------------------------------------ *)
(** *** (2) Mutation kill: a confirmed branch that RECOMPUTES from the current
       operand (the exit interface address) instead of reusing the stored tuple. *)

(* [bug_apply_recompute]: the confirmed branch is replaced by a recompute of the
   masq source from the CURRENT exit interface ([e_ifaddr]).  This is the planted
   infidelity — it breaks NAT-flow stability whenever the exit address has changed
   (interface re-addressed mid-flow), or whenever the stored wan was chosen on a
   different operand. *)
Definition bug_apply_recompute (h : hook_id) (r : rule) (e : env) (p : packet) : packet :=
  match r_nat r with
  | Some _ =>
      if pkt_ctdir_orig p
      then set_saddr nat_fam_ip4 p (e_ifaddr e (field_value FMetaOifname e p))
      else p
  | None => p
  end.

(* On a confirmed flow whose CURRENT exit address differs from the stored wan, the
   correct [apply_nat] yields the STORED wan while the bug yields the RECOMPUTED
   exit address — they disagree on the source slot. *)
Theorem confirmed_apply_discriminates_bug : forall h e p oa wan,
  pkt_ctdir_orig p = true ->
  e_nat e (pkt_flow p) = Some (Some oa, Some wan, None, None) ->
  16 <= List.length (pkt_nh p) ->
  List.length wan = 4 ->
  List.length (e_ifaddr e (field_value FMetaOifname e p)) = 4 ->
  e_ifaddr e (field_value FMetaOifname e p) <> wan ->
  saddr4 (snd (apply_nat h masq_rule e p)) <> saddr4 (bug_apply_recompute h masq_rule e p).
Proof.
  intros h e p oa wan Horig Hsome Hnh Hwl Hifl Hdiff.
  unfold saddr4.
  rewrite (masq_apply_confirmed_orig h e p oa wan Horig Hsome). cbn [snd].
  unfold bug_apply_recompute, masq_rule; cbn [r_nat r_outcome]. rewrite Horig.
  change "ip"%string with nat_fam_ip4.
  rewrite (slice_set_saddr_ip4_same p wan Hnh Hwl).
  rewrite (slice_set_saddr_ip4_same p _ Hnh Hifl).
  intro Heq. apply Hdiff. symmetry. exact Heq.
Qed.

(* ------------------------------------------------------------ *)
(** *** (3) Reply-direction un-NAT: a confirmed source-NAT flow restores the reply's
       DESTINATION to the stored ORIGINAL address [oa] (source untouched: no port). *)

(* On a confirmed REPLY-direction packet [apply_nat] applies the INVERSE manip: the
   source NAT un-rewrites the reply's DESTINATION slot back to the stored [oa]. *)
Lemma masq_apply_confirmed_reply : forall h e p oa wan,
  pkt_ctdir_orig p = false ->
  e_nat e (pkt_flow p) = Some (Some oa, Some wan, None, None) ->
  apply_nat h masq_rule e p = (e, set_daddr nat_fam_ip4 p oa).
Proof.
  intros h e p oa wan Hrep Hsome. unfold apply_nat, masq_rule, masq_spec.
  cbn -[set_daddr e_nat pkt_flow apply_nat_tuple].
  rewrite Hsome.
  unfold apply_nat_tuple, nat_is_src, nat_addrfamily_pkt, nat_addrfamily.
  cbn -[set_daddr]. rewrite Hrep. reflexivity.
Qed.

(* THE OUTPUT PACKET on a confirmed reply: dest restored to stored [oa]. *)
Theorem nat_masq_confirmed_reply_output : forall e p oa wan,
  saddr_private e p = true ->
  oif_ppp0 e p = true ->
  pkt_ctdir_orig p = false ->
  e_nat e (pkt_flow p) = Some (Some oa, Some wan, None, None) ->
  chain_out Hpostrouting global_postrouting e p = set_daddr nat_fam_ip4 p oa.
Proof.
  intros e p oa wan Hpriv Hppp Hrep Hsome.
  unfold chain_out, eval_chain_trace.
  rewrite global_postrouting_rules. cbn [c_rules eval_rules_trace].
  assert (Hload : rule_loadable masq_rule e p = true).
  { unfold saddr_private, oif_ppp0, eval_matchcond in Hpriv, Hppp.
    apply Bool.andb_true_iff in Hpriv as [Hpl _].
    apply Bool.andb_true_iff in Hppp as [Hol _].
    unfold rule_loadable, masq_rule; cbn [r_body body_loadable_walk
      body_synproxy_stops existsb body_item_loadable body_thread body_has_notrack].
    cbn [match_loadable] in Hpl, Hol |- *. rewrite Hpl, Hol. reflexivity. }
  assert (Happ : rule_applies masq_rule e p = true)
    by (rewrite masq_rule_applies_eq, Hpriv, Hppp; reflexivity).
  assert (Ho : outcome masq_rule e p = Some Accept) by reflexivity.
  assert (Hd : dsl_rule_step masq_rule e p = (Some Accept, (e, p))).
  { unfold dsl_rule_step. rewrite rule_step_mutfree by reflexivity.
    rewrite Hload, Happ. cbn [andb]. rewrite Ho. reflexivity. }
  rewrite Hd. cbn [terminal].
  rewrite (masq_no_drop_confirmed Hpostrouting e p _ Hsome).
  rewrite (masq_apply_confirmed_reply Hpostrouting e p oa wan Hrep Hsome).
  reflexivity.
Qed.

(* The reply's DESTINATION slot equals the stored ORIGINAL (pre-NAT) address [oa] —
   the un-NAT that lets the established connection's replies reach the LAN host. *)
Theorem nat_masq_confirmed_reply_unnat : forall e p oa wan,
  saddr_private e p = true ->
  oif_ppp0 e p = true ->
  pkt_ctdir_orig p = false ->
  e_nat e (pkt_flow p) = Some (Some oa, Some wan, None, None) ->
  20 <= List.length (pkt_nh p) ->
  List.length oa = 4 ->
  daddr4 (chain_out Hpostrouting global_postrouting e p) = oa.
Proof.
  intros e p oa wan Hpriv Hppp Hrep Hsome Hnh Hol. unfold daddr4.
  rewrite (nat_masq_confirmed_reply_output e p oa wan Hpriv Hppp Hrep Hsome).
  apply slice_set_daddr_ip4_same; assumption.
Qed.

(* ------------------------------------------------------------ *)
(** *** Satisfiability witnesses (non-vacuity of the confirmed-flow hypotheses). *)

(* A stored mapping whose WAN address (203.0.113.7) is the connection's frozen tuple,
   while the CURRENT exit interface carries a DIFFERENT address (198.51.100.9) —
   exactly the "interface re-addressed mid-flow" scenario the stability invariant
   protects.  flowkey = [7;7] arbitrary. *)
Definition flowkey : data := [7; 7].
Definition stored_wan : data := [203; 0; 113; 7].
Definition orig_priv : data := [192; 168; 9; 9].
Definition current_exit : data := [198; 51; 100; 9].

Definition env_confirmed : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0;
     e_ifaddrs := fun n => ifaddrs_of (if data_eqb n if_ppp0 then current_exit else []);
     e_ifaddrs6 := fun _ => []; e_connlimit := fun _ => [];
     e_ct := fun _ _ => [];
     e_nat := fun k => if data_eqb k flowkey
                       then Some (Some orig_priv, Some stored_wan, None, None)
                       else None;
     e_numgen := fun _ => 0 |}.

(* A confirmed ORIGINAL-direction packet of that flow: private source out ppp0. *)
Definition pkt_orig_confirmed : packet :=
  {|
     pkt_meta := fun k => if meta_eqb k MKoifname then if_ppp0 else [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := ip4_priv; pkt_th := [0;0;0;0;0;0;0;0]; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := true;
     pkt_fragoff := 0; pkt_flow := flowkey; pkt_untracked := false;
     pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* The confirmed-flow hypotheses are satisfiable: private source, oif ppp0, orig dir,
   established mapping at the flow. *)
Lemma pkt_orig_confirmed_private : saddr_private env_confirmed pkt_orig_confirmed = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pkt_orig_confirmed_oif : oif_ppp0 env_confirmed pkt_orig_confirmed = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pkt_orig_confirmed_enat :
  e_nat env_confirmed (pkt_flow pkt_orig_confirmed)
    = Some (Some orig_priv, Some stored_wan, None, None).
Proof. vm_compute. reflexivity. Qed.

(* End-to-end: the parser's chain rewrites the source to the STORED wan (203.0.113.7),
   NOT to the current exit address (198.51.100.9) — proven by the abstract theorem and
   independently confirmed by direct evaluation. *)
Theorem witness_confirmed_reuses_stored :
  saddr4 (chain_out Hpostrouting global_postrouting env_confirmed pkt_orig_confirmed)
  = stored_wan.
Proof.
  apply (nat_masq_confirmed_reuses_stored env_confirmed pkt_orig_confirmed orig_priv stored_wan
           pkt_orig_confirmed_private pkt_orig_confirmed_oif eq_refl
           pkt_orig_confirmed_enat); vm_compute; lia.
Qed.

(* The same witness, the bug RECOMPUTES from the current exit address — observably
   different (stored 203.0.113.7 vs recomputed 198.51.100.9). *)
Theorem witness_confirmed_bug :
  saddr4 (bug_apply_recompute Hpostrouting masq_rule env_confirmed pkt_orig_confirmed)
  = current_exit.
Proof. vm_compute. reflexivity. Qed.

Theorem confirmed_property_discriminates_bug :
  saddr4 (snd (apply_nat Hpostrouting masq_rule env_confirmed pkt_orig_confirmed))
  <> saddr4 (bug_apply_recompute Hpostrouting masq_rule env_confirmed pkt_orig_confirmed).
Proof.
  apply (confirmed_apply_discriminates_bug Hpostrouting env_confirmed pkt_orig_confirmed
           orig_priv stored_wan eq_refl pkt_orig_confirmed_enat);
    vm_compute; (lia || discriminate).
Qed.

(* Reply-direction witness: a confirmed REPLY packet of the same flow (its dest is the
   peer/WAN; un-NAT restores the dest to the stored original private addr). *)
(* For the chain-level reply witness the masq rule must still APPLY (the model only
   runs [apply_nat] at a rule's terminal verdict), so this reply packet carries a
   private source + oif ppp0.  (In the kernel the reply un-NAT is driven by conntrack
   independent of rule matching; the rule-gated model needs the match to hold.  The
   abstract lemma [masq_apply_confirmed_reply] is the rule-independent statement of
   the inverse branch.) *)
Definition ip4_reply : data :=
  [ 69; 0; 0; 20; 0; 0; 0; 0; 64; 6; 0; 0;
    192; 168; 9; 9;                          (* source private (so the rule applies) *)
    203; 0; 113; 7 ].                        (* dest pre-unnat (the stored WAN) *)

Definition pkt_reply_confirmed : packet :=
  {|
     pkt_meta := fun k => if meta_eqb k MKoifname then if_ppp0 else [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := ip4_reply; pkt_th := [0;0;0;0;0;0;0;0]; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := true;
     pkt_fragoff := 0; pkt_flow := flowkey; pkt_untracked := false;
     pkt_ctdir_orig := false; pkt_ct_present := true |}.

Lemma pkt_reply_confirmed_private : saddr_private env_confirmed pkt_reply_confirmed = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pkt_reply_confirmed_oif : oif_ppp0 env_confirmed pkt_reply_confirmed = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pkt_reply_confirmed_enat :
  e_nat env_confirmed (pkt_flow pkt_reply_confirmed)
    = Some (Some orig_priv, Some stored_wan, None, None).
Proof. vm_compute. reflexivity. Qed.

(* End-to-end reply un-NAT: the dest slot is restored to the stored original
   private address (192.168.9.9). *)
Theorem witness_confirmed_reply_unnat :
  daddr4 (chain_out Hpostrouting global_postrouting env_confirmed pkt_reply_confirmed)
  = orig_priv.
Proof.
  apply (nat_masq_confirmed_reply_unnat env_confirmed pkt_reply_confirmed orig_priv stored_wan
           pkt_reply_confirmed_private pkt_reply_confirmed_oif eq_refl
           pkt_reply_confirmed_enat); vm_compute; lia.
Qed.
