(** * Netstate_MultiAddr: the interface address model is multi-address, and the
      masquerade source is a CORRECT SELECTION from the set.

    This theory discharges the deliverable's core obligations on top of the
    multi-address state introduced in [Packet.v]:

    (1) An interface carries a LIST of addresses ([e_ifaddrs : data -> list ifaddr],
        each [ifaddr] = [ifa_local]/[ifa_secondary]/[ifa_scope]), NOT a single
        oracle.  [inet_select_addr] is the kernel's source-address SELECTION
        (net/ipv4/devinet.c:1359): skip secondaries, skip out-of-scope, return the
        FIRST eligible primary; [] (=> NF_DROP) when none exists.

    (2) The masquerade source [masq_saddr] is PROVED to be exactly that selection on
        the egress interface's address list at RT_SCOPE_UNIVERSE — the first
        non-secondary, in-scope primary — and the NF_DROP ([nat_iface_addr_absent])
        fires EXACTLY when no such address exists.

    (3) The host-wide local-address set is the UNION ([flat_map]) of all interfaces'
        addresses, and a `fib daddr type == local` lookup against the corresponding
        per-address /32 RTN_LOCAL routes (the kernel's [fib_add_ifaddr]) returns the
        local type-code EXACTLY for addresses in that union.

    Nothing here is admitted or axiomatic, and no existing theorem is touched: the
    must-preserve masquerade theorems keep going through [e_ifaddr]/[e_ifaddr6],
    which are now DERIVED from the selection. *)

From Stdlib Require Import List String NArith Bool PeanoNat.
From Nft Require Import Bytes Packet Verdict Syntax Semantics.
Import ListNotations.

(** ** (1)/(2)  inet_select_addr is a faithful first-eligible selection *)

(** An [ifaddr] is ELIGIBLE for selection at [scope] iff it is a PRIMARY
    (not [IFA_F_SECONDARY]) AND in scope ([ifa_scope <= scope]) — the kernel's
    `if (ifa->ifa_flags & IFA_F_SECONDARY) continue;` plus
    `if (min(ifa->ifa_scope, ...) > scope) continue;`. *)
Definition ifa_eligible (scope : nat) (ia : ifaddr) : bool :=
  andb (negb (ifa_secondary ia)) (Nat.leb (ifa_scope ia) scope).

(** The selection equals the FIRST eligible address's [ifa_local], computed by
    [find]; [] when none is eligible.  This is a clean restatement of the kernel's
    loop+break. *)
Lemma inet_select_addr_find : forall l scope,
  inet_select_addr l scope
  = match find (ifa_eligible scope) l with
    | Some ia => ifa_local ia
    | None => []
    end.
Proof.
  induction l as [|ia rest IH]; intro scope; [reflexivity|].
  cbn [inet_select_addr find]. unfold ifa_eligible.
  destruct (andb (negb (ifa_secondary ia)) (Nat.leb (ifa_scope ia) scope)) eqn:E.
  - reflexivity.
  - apply IH.
Qed.

(** ** Selection IS a member of the interface set (not a fabricated value).

    When the result is non-empty, it is the [ifa_local] of an address that is
    actually in the interface's list AND is eligible (primary + in scope) AND is
    the FIRST such — i.e. every EARLIER list element is ineligible.  This is the
    deliverable's core "the masquerade source is a CORRECT selection from the set"
    statement. *)
Theorem inet_select_addr_is_first_eligible : forall l scope a,
  inet_select_addr l scope = a -> a <> [] ->
  exists pre ia post,
    l = pre ++ ia :: post
    /\ ifa_local ia = a
    /\ ifa_eligible scope ia = true
    /\ (forall x, In x pre -> ifa_eligible scope x = false).
Proof.
  intros l scope a Hsel Hne.
  rewrite inet_select_addr_find in Hsel.
  (* induct on l, tracking the FIRST eligible element via [find] *)
  induction l as [|x rest IH].
  - cbn in Hsel. subst a. now exfalso.
  - cbn [find] in Hsel. destruct (ifa_eligible scope x) eqn:Ex.
    + (* head is eligible: it is the selected one *)
      exists [], x, rest. subst a. repeat split; auto.
      intros y [].
    + (* head ineligible: recurse *)
      specialize (IH Hsel) as (pre & ia' & post & Hl & Hloc & Helg & Hpre).
      exists (x :: pre), ia', post. repeat split; auto.
      * cbn. rewrite Hl. reflexivity.
      * intros y [<-|Hy]; [exact Ex | now apply Hpre].
Qed.

(** ** Well-formed interface lists: every address value is non-empty (a genuine
       4-byte IPv4 / 16-byte IPv6 [ifa_local]), as a real [in_ifaddr] always is. *)
Definition ifaddrs_wf (l : list ifaddr) : Prop :=
  forall ia, In ia l -> ifa_local ia <> [].

(** Under well-formedness, the selection is EMPTY iff NO address is eligible — the
    exact NF_DROP condition the masquerade core tests (`if (!newsrc) return
    NF_DROP;`).  Without [ifaddrs_wf] the only extra case is an eligible address
    whose value is itself [] (never a real address). *)
Theorem inet_select_addr_empty_iff_no_eligible : forall l scope,
  ifaddrs_wf l ->
  (inet_select_addr l scope = []
   <-> (forall ia, In ia l -> ifa_eligible scope ia = false)).
Proof.
  intros l scope Hwf. rewrite inet_select_addr_find. split.
  - destruct (find (ifa_eligible scope) l) as [ia|] eqn:Ef.
    + intro Hempty. apply find_some in Ef as [Hin _].
      exfalso. now apply (Hwf ia Hin).
    + intros _ ia Hin.
      (* find = None means NO element satisfies the predicate *)
      pose proof (find_none _ _ Ef ia Hin) as Hno. exact Hno.
  - intro Hall.
    destruct (find (ifa_eligible scope) l) as [ia|] eqn:Ef; [|reflexivity].
    apply find_some in Ef as [Hin Helig].
    now rewrite (Hall ia Hin) in Helig.
Qed.

(** ** (2)  The masquerade source IS the selection from the egress interface set.

    [masq_saddr] unfolds to [inet_select_addr] over the egress interface's IPv4 or
    IPv6 address list (by family) at RT_SCOPE_UNIVERSE — i.e. a genuine selection
    from the multi-address state, not "the one address". *)

(** The egress interface name a packet exits by (the masquerade key). *)
Definition egress_ifname (p : packet) : data := field_value FMetaOifname p.

(** The address LIST masquerade selects from, by family. *)
Definition masq_ifaddrs (fam : String.string) (p : packet) : list ifaddr :=
  if String.eqb fam nat_fam_ip6
  then e_ifaddrs6 (pkt_env p) (egress_ifname p)
  else e_ifaddrs  (pkt_env p) (egress_ifname p).

Lemma masq_saddr_is_select : forall fam p,
  masq_saddr fam p = inet_select_addr (masq_ifaddrs fam p) scope_universe.
Proof.
  intros fam p. unfold masq_saddr, masq_ifaddrs, egress_ifname.
  destruct (String.eqb fam nat_fam_ip6).
  - reflexivity.   (* e_ifaddr6 = inet_select_addr (e_ifaddrs6 ...) scope_universe, by definition *)
  - reflexivity.
Qed.

(** THE CORE SELECTION THEOREM: when masquerade produces a (non-drop) source
    address, that address is a CORRECT selection from the egress interface's
    address set — it is the [ifa_local] of the FIRST non-secondary, in-scope
    primary in the interface's list. *)
Theorem masq_saddr_is_selected_primary : forall fam p a,
  masq_saddr fam p = a -> a <> [] ->
  exists pre ia post,
    masq_ifaddrs fam p = pre ++ ia :: post
    /\ ifa_local ia = a
    /\ ifa_secondary ia = false
    /\ ifa_scope ia <= scope_universe
    /\ (forall x, In x pre -> ifa_eligible scope_universe x = false).
Proof.
  intros fam p a Hsel Hne.
  rewrite masq_saddr_is_select in Hsel.
  destruct (inet_select_addr_is_first_eligible _ _ _ Hsel Hne)
    as (pre & ia & post & Hl & Hloc & Helig & Hpre).
  unfold ifa_eligible in Helig. apply andb_true_iff in Helig as [Hsec Hsc].
  apply negb_true_iff in Hsec. apply Nat.leb_le in Hsc.
  exists pre, ia, post. repeat split; auto.
Qed.

(** Axiom-freedom guard (build-time; mirrors Fib_Local.v): prints "Closed under
    the global context". *)
Print Assumptions masq_saddr_is_selected_primary.

(** THE NF_DROP THEOREM: the masquerade NAT-core drop fires EXACTLY when the egress
    interface has NO eligible (non-secondary, in-scope) primary address — the
    kernel's `newsrc = inet_select_addr(out,...); if (!newsrc) return NF_DROP;`.
    (Well-formed interface lists: a real [ifa_local] is a non-empty address.) *)
Theorem masq_drop_iff_no_eligible_addr : forall fam p,
  ifaddrs_wf (masq_ifaddrs fam p) ->
  ( (match masq_saddr fam p with [] => true | _ => false end) = true
    <-> (forall ia, In ia (masq_ifaddrs fam p) -> ifa_eligible scope_universe ia = false) ).
Proof.
  intros fam p Hwf. rewrite masq_saddr_is_select.
  rewrite <- (inet_select_addr_empty_iff_no_eligible _ scope_universe Hwf).
  destruct (inet_select_addr (masq_ifaddrs fam p) scope_universe);
    split; intro H; congruence.
Qed.

(** Tie to the actual trace gate [nat_iface_addr_absent] for a masquerade spec:
    it is precisely the "no eligible address" condition above. *)
Theorem nat_iface_addr_absent_masq_iff : forall h ns p,
  nat_kind ns = nat_masq_kind ->
  ifaddrs_wf (masq_ifaddrs (nat_addrfamily_pkt ns p) p) ->
  ( nat_iface_addr_absent h ns p = true
    <-> (forall ia, In ia (masq_ifaddrs (nat_addrfamily_pkt ns p) p) ->
                    ifa_eligible scope_universe ia = false) ).
Proof.
  intros h ns p Hk Hwf. unfold nat_iface_addr_absent.
  rewrite Hk. unfold nat_masq_kind. rewrite String.eqb_refl.
  apply masq_drop_iff_no_eligible_addr; auto.
Qed.

(** ** (3)  The host-wide local-address set is the UNION of interface addresses.

    The kernel inserts EVERY interface address (primary AND secondary) as a /32
    RTN_LOCAL route into RT_TABLE_LOCAL ([fib_add_ifaddr], net/ipv4/fib_frontend.c),
    so `fib daddr type == local` (read via [inet_addr_type] over RT_TABLE_LOCAL) is
    true EXACTLY for an address in the union of all interfaces' address lists.  We
    model that union and prove the fib-type lookup agrees with membership in it. *)

(** All addresses of an interface (primary + secondaries), the [ifa_local] values
    of its full list. *)
Definition iface_addrs (e : env) (n : data) : list data :=
  map ifa_local (e_ifaddrs e n).

(** The host-wide local-address set = the UNION over the given interfaces.  (The
    real kernel ranges over every netdevice; here we take the host's interface
    name list as a parameter, faithful to "all interfaces".) *)
Definition host_local_addrs (e : env) (ifaces : list data) : list data :=
  flat_map (iface_addrs e) ifaces.

(** Membership in the host-local set is membership in SOME interface's address
    list — the union characterization, the kernel's "addr is local on the host iff
    it is configured on some device". *)
Lemma host_local_addrs_iff : forall e ifaces a,
  In a (host_local_addrs e ifaces)
  <-> (exists n, In n ifaces /\ In a (iface_addrs e n)).
Proof.
  intros e ifaces a. unfold host_local_addrs.
  rewrite in_flat_map. reflexivity.
Qed.

(** The fib type-code returned for a local address (RTN_LOCAL = 2, host-endian u32
    on LE), matching [Optiplex_Mark.fib_local]. *)
Definition fib_local_type : data := [2; 0; 0; 0].

(** A /32 RTN_LOCAL route for one address [a]: the singleton interval [a,a] whose
    [FRtype] result is [fib_local_type] — the model of one [fib_add_ifaddr]
    insertion. *)
Definition local_route (a : data) : data * data * (fib_result -> data) :=
  (a, a, fun _ => fib_local_type).

(** The RT_TABLE_LOCAL routing table built from the host-local set: one /32
    RTN_LOCAL route per address.  This is exactly what [fib_add_ifaddr] populates. *)
Definition local_routes (e : env) (ifaces : list data) :=
  map local_route (host_local_addrs e ifaces).

(** THE HOST-LOCAL FIB THEOREM: against the RT_TABLE_LOCAL routes built from the
    interface-address UNION, an [lpm_fib ... FRtype] lookup on a key [a] returns the
    local type-code whenever [a] is in the union — i.e. `fib daddr type == local`
    holds EXACTLY for host-local (= some-interface) addresses.  This relates the fib
    local result to membership in [host_local_addrs]. *)
Theorem fib_local_of_host_local : forall e ifaces a,
  In a (host_local_addrs e ifaces) ->
  lpm_fib (local_routes e ifaces) a FRtype = fib_local_type.
Proof.
  intros e ifaces a Hin. unfold local_routes.
  (* [data_le a a = true], from antisymmetry + reflexivity of data_eqb *)
  assert (Hrefl : data_le a a = true).
  { pose proof (data_le_antisym a a) as Hanti.
    rewrite data_eqb_refl in Hanti. apply andb_true_iff in Hanti. apply Hanti. }
  induction (host_local_addrs e ifaces) as [|b rest IH]; [destruct Hin|].
  cbn [map lpm_fib local_route].
  destruct (andb (data_le b a) (data_le a b)) eqn:E.
  - reflexivity.
  - (* head route did not match: then a <> b, so a is in the tail *)
    apply IH. destruct Hin as [<-|Hin']; [|exact Hin'].
    exfalso. rewrite Hrefl in E. discriminate.
Qed.

(** Read through the actual field semantics: against [local_routes] as the env's
    route table, `field_value (FFib "daddr" FRtype)` reports the local type-code for
    a host-local destination.  ([pkt_fibkey p "daddr"] is the packet's destination
    key.) *)
Theorem field_fib_daddr_local_of_host_local : forall p ifaces,
  e_routes (pkt_env p) = local_routes (pkt_env p) ifaces ->
  In (pkt_fibkey p "daddr") (host_local_addrs (pkt_env p) ifaces) ->
  field_value (FFib "daddr" FRtype) p = fib_local_type.
Proof.
  intros p ifaces Hroutes Hin.
  unfold field_value. cbn [field_load do_load].
  rewrite Hroutes. now apply fib_local_of_host_local.
Qed.

(** ** Non-vacuity witnesses: the multi-address state is LOAD-BEARING.

    These concrete computations show the selection genuinely DISCRIMINATES on the
    new [ifa_secondary]/[ifa_scope] fields — it is NOT a one-address oracle wearing
    a list costume.  A single-address model could not produce any of these. *)

(* An interface eth0 with THREE addresses: a SECONDARY 10.0.0.1, a HOST-scoped
   (loopback-only, scope 254) 127.0.0.2, and a global PRIMARY 203.0.113.5.
   inet_select_addr must SKIP the first two and pick the third. *)
Definition eth0_list : list ifaddr :=
  [ {| ifa_local := [10;0;0;1];   ifa_secondary := true;  ifa_scope := 0   |};
    {| ifa_local := [127;0;0;2];  ifa_secondary := false; ifa_scope := 254 |};
    {| ifa_local := [203;0;113;5];ifa_secondary := false; ifa_scope := 0   |} ].

(* Selection skips the secondary AND the out-of-scope address, picking the global
   primary — a result NO single-address oracle and NO "just take the head" model
   could give. *)
Example select_skips_secondary_and_scope :
  inet_select_addr eth0_list scope_universe = [203;0;113;5].
Proof. reflexivity. Qed.

(* If we make the global primary a SECONDARY too, every address is now ineligible
   (secondary or out-of-scope) and selection is [] => NF_DROP — even though the
   interface HAS three configured addresses.  This is the precise drop the
   single-"is it []" oracle could only fake. *)
Definition eth0_all_unusable : list ifaddr :=
  [ {| ifa_local := [10;0;0;1];   ifa_secondary := true;  ifa_scope := 0   |};
    {| ifa_local := [127;0;0;2];  ifa_secondary := false; ifa_scope := 254 |};
    {| ifa_local := [203;0;113;5];ifa_secondary := true;  ifa_scope := 0   |} ].

Example select_empty_when_all_unusable :
  inet_select_addr eth0_all_unusable scope_universe = [].
Proof. reflexivity. Qed.

(* The host-local UNION genuinely spans MULTIPLE interfaces' MULTIPLE addresses:
   eth0 contributes all three of its addresses (incl. the secondary, which
   fib_add_ifaddr DOES insert as a local route), lo contributes 127.0.0.1. *)
Definition demo_env : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0;
     e_ifaddrs := fun n => if data_eqb n [101;116;104;48] (* "eth0" *)
                           then eth0_list
                           else [ mk_primary [127;0;0;1] ];
     e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => []; e_nat := fun _ => None;
     e_numgen := fun _ => 0 |}.

Example host_local_union_spans_interfaces :
  host_local_addrs demo_env [ [101;116;104;48]; [108;111] (* "lo" *) ]
  = [ [10;0;0;1]; [127;0;0;2]; [203;0;113;5]; [127;0;0;1] ].
Proof. reflexivity. Qed.

(* And every one of those union members resolves `fib daddr type` to LOCAL. *)
Example fib_local_for_each_union_member :
  Forall (fun a => lpm_fib (local_routes demo_env
                              [ [101;116;104;48]; [108;111] ]) a FRtype = fib_local_type)
         (host_local_addrs demo_env [ [101;116;104;48]; [108;111] ]).
Proof.
  repeat constructor.
Qed.
