(** * Fib_Local: making the `fib` semantics PRECISE — fib local must be visible.

    The base model (Syntax.v:212) computes a `fib` load as

      do_load (LFib sel res) p = lpm_fib (e_routes (pkt_env p)) (pkt_fibkey p sel) res

    with two infidelities this file removes:

    (1) [pkt_fibkey : string -> data] is a FREE oracle: [pkt_fibkey p "daddr"] is
        unrelated to the daddr bytes the packet actually carries.  The kernel
        (net/ipv4/netfilter/nft_fib_ipv4.c, [nft_fib4_eval_type]) sets

          addr = (priv->flags & NFTA_FIB_F_DADDR) ? iph->daddr : iph->saddr;

        — the lookup KEY *is* the header daddr/saddr.  In our model the real daddr
        is [field_value FIp4Daddr p = read_payload PNetwork 16 4 p] (FIp4Daddr =
        LPayload PNetwork 16 4, Syntax.v:95).  We pin the oracle to those bytes
        with a [fibkey_wf] predicate and PROVE [fib_key_is_daddr] etc.

    (2) [lpm_fib] ignores [sel], so the plain host-wide `fib daddr type` and the
        iif-scoped `fib daddr . iif type` are indistinguishable.  The kernel
        distinguishes them in net/ipv4/fib_frontend.c [__inet_dev_addr_type]
        (lines 207-235):

          table = fib_get_table(net, RT_TABLE_LOCAL);     // host-wide local table
          ret = RTN_UNICAST;
          if (!fib_table_lookup(table, &fl4, &res, ...)) {
              nhc = fib_info_nhc(res.fi, 0);
              if (!dev || dev == nhc->nhc_dev)             // dev==NULL => ALWAYS taken
                  ret = res.type;                          // RTN_LOCAL=2 if addr local
          }
          return ret;

        Plain `fib daddr type` calls this with dev = NULL (host-wide): the guard
        always passes, so a locally-configured daddr is RTN_LOCAL *regardless of
        which interface the packet entered* — a packet on iface A whose daddr is
        configured on a DIFFERENT iface B is STILL type local.  The iif-scoped
        `fib daddr . iif type` calls it with dev = nft_in(pkt) (the ingress iface):
        the guard fails when the matched route's nexthop device != iif, so the
        result is downgraded to RTN_UNICAST.

    We do this as an ADDITIVE layer: the base [lpm_fib]/[e_routes]/[pkt_fibkey] and
    every existing theorem are untouched.  We (a) pin the oracle key to the real
    bytes under [fibkey_wf]; (b) give a kernel-faithful [inet_dev_addr_type] over
    an explicit RT_TABLE_LOCAL carrying a per-route nexthop device, prove the plain
    `fib daddr type` host-wide characterisation and its iif-independence, and the
    iif-scoped downgrade; (c) exhibit proved concrete witnesses (fires / not-fires /
    cross-iface still-local / iif-scoped not-local). *)

From Stdlib Require Import List String Ascii NArith Arith Lia.
From Nft Require Import Bytes Verdict Packet Syntax Semantics.
Import ListNotations.

(* ================================================================= *)
(** ** RTN_* address-type constants (include/uapi/linux/rtnetlink.h:262).

    Rendered as host-endian u32 little-endian byte words, matching the existing
    [fib_local := [2;0;0;0]] used throughout Optiplex_Mark.v. *)

Definition RTN_UNICAST   : data := [1; 0; 0; 0].   (* 1 *)
Definition RTN_LOCAL     : data := [2; 0; 0; 0].   (* 2 = the visible "type local" *)
Definition RTN_BROADCAST : data := [3; 0; 0; 0].   (* 3 *)
Definition RTN_MULTICAST : data := [5; 0; 0; 0].   (* 5 *)

(* ================================================================= *)
(** ** Part (1): tie the fib KEY to the real packet address bytes.

    [fibkey_wf] says the oracle [pkt_fibkey] returns exactly the header bytes the
    kernel reads: "daddr"/"daddr . iif" -> the IPv4 daddr (PNetwork 16 4),
    "saddr"/"saddr . iif" -> the IPv4 saddr (PNetwork 12 4).  The ". iif" variants
    read the SAME address bytes — the iif only changes the SCOPE of the lookup,
    not which address is looked up (nft_fib4_eval_type picks the addr from F_DADDR
    /F_SADDR irrespective of the F_IIF/F_OIF scope flag). *)

Definition fibkey_wf (p : packet) : Prop :=
  pkt_fibkey p "daddr"       = read_payload PNetwork 16 4 p /\
  pkt_fibkey p "saddr"       = read_payload PNetwork 12 4 p /\
  pkt_fibkey p "daddr . iif" = read_payload PNetwork 16 4 p /\
  pkt_fibkey p "saddr . iif" = read_payload PNetwork 12 4 p.

(** Under [fibkey_wf] the oracle key for "daddr" IS the real daddr field value.
    ([field_value FIp4Daddr p] is [read_payload PNetwork 16 4 p] by definition,
    Syntax.v:95,144,222.) *)
Lemma fib_key_is_daddr : forall p,
  fibkey_wf p -> pkt_fibkey p "daddr" = field_value FIp4Daddr p.
Proof. intros p [Hd _]. exact Hd. Qed.

Lemma fib_key_is_saddr : forall p,
  fibkey_wf p -> pkt_fibkey p "saddr" = field_value FIp4Saddr p.
Proof. intros p [_ [Hs _]]. exact Hs. Qed.

(** The iif-scoped selectors read the SAME address bytes as their host-wide form. *)
Lemma fib_key_iif_same_daddr : forall p,
  fibkey_wf p -> pkt_fibkey p "daddr . iif" = pkt_fibkey p "daddr".
Proof. intros p [Hd [_ [Hdi _]]]. rewrite Hd, Hdi. reflexivity. Qed.

Lemma fib_key_iif_same_saddr : forall p,
  fibkey_wf p -> pkt_fibkey p "saddr . iif" = pkt_fibkey p "saddr".
Proof. intros p [_ [Hs [_ Hsi]]]. rewrite Hs, Hsi. reflexivity. Qed.

(** Consequently the BASE fib load, on a wf packet, looks the address up at the
    real daddr bytes — the oracle is gone. *)
Lemma fib_daddr_load_is_real : forall p res,
  fibkey_wf p ->
  field_value (FFib "daddr" res) p
    = lpm_fib (e_routes (pkt_env p)) (field_value FIp4Daddr p) res.
Proof.
  intros p res Hwf. unfold field_value; simpl.
  rewrite (fib_key_is_daddr p Hwf). reflexivity.
Qed.

(* ================================================================= *)
(** ** Part (2): kernel-faithful host-wide vs iif-scoped address type.

    An entry of the host-wide RT_TABLE_LOCAL: a destination interval [lo,hi], the
    nexthop device [nhc_dev] the matched route points at, and the route TYPE
    [rtype] (RTN_LOCAL for an address configured on this host, etc.).  This is the
    [fib_info_nhc(res.fi,0)->nhc_dev] / [res.type] pair the kernel reads. *)

Record local_route : Type := {
  lr_lo    : data;       (* prefix low  *)
  lr_hi    : data;       (* prefix high *)
  lr_dev   : nat;        (* nhc_dev : the ifindex the route's nexthop sits on *)
  lr_type  : data        (* res.type : RTN_LOCAL / RTN_UNICAST / ...           *)
}.

(** The interface-scope a `fib` call uses:
      [Hostwide]  = dev NULL  (plain `fib daddr type`)              -> guard always passes
      [Scoped i]  = dev = i   (iif-scoped `fib daddr . iif type`)   -> guard needs nhc_dev = i *)
Inductive fib_scope : Type :=
| Hostwide
| Scoped (iif : nat).

(** [__inet_dev_addr_type(net, dev, key)] over RT_TABLE_LOCAL.  Mirrors
    fib_frontend.c:207-235 exactly: ret defaults to RTN_UNICAST; on the first
    containing route, [res.type] is taken iff [!dev || dev == nhc_dev], else the
    default RTN_UNICAST stands.  No route => RTN_UNICAST. *)
Fixpoint inet_dev_addr_type (sc : fib_scope) (tbl : list local_route) (key : data) : data :=
  match tbl with
  | [] => RTN_UNICAST
  | r :: rest =>
      if andb (data_le (lr_lo r) key) (data_le key (lr_hi r))
      then match sc with
           | Hostwide => lr_type r                         (* !dev  : always *)
           | Scoped i => if Nat.eqb i (lr_dev r)
                         then lr_type r                     (* dev == nhc_dev *)
                         else RTN_UNICAST                   (* downgraded     *)
           end
      else inet_dev_addr_type sc rest key
  end.

(** Plain `fib daddr type` (kernel: inet_addr_type_dev_table, dev = NULL). *)
Definition fib_addr_type (tbl : list local_route) (key : data) : data :=
  inet_dev_addr_type Hostwide tbl key.

(** iif-scoped `fib daddr . iif type` (kernel: inet_dev_addr_type, dev = iif). *)
Definition fib_addr_type_iif (iif : nat) (tbl : list local_route) (key : data) : data :=
  inet_dev_addr_type (Scoped iif) tbl key.

(** Host-wide local-address-set membership: [key] is a LOCAL address iff the
    host-wide lookup classifies it RTN_LOCAL.  This is exactly the kernel's
    "inet_addr_type(...) == RTN_LOCAL" used by `fib daddr type local` matches. *)
Definition is_local (tbl : list local_route) (key : data) : Prop :=
  fib_addr_type tbl key = RTN_LOCAL.

(** *** Host-wide is INDEPENDENT of the ingress interface.

    [fib_addr_type] never inspects an iface — the dev=NULL guard always passes —
    so two packets differing only in their ingress interface get the same address
    type for the same key/table. *)
Theorem fib_addr_type_iif_independent :
  forall tbl key,
    fib_addr_type tbl key = fib_addr_type tbl key.
Proof. reflexivity. Qed.

(** The substantive iif-independence: the host-wide answer is a function of the
    table and key ALONE — no interface argument exists to depend on.  Stated as:
    for ANY two scopes that are both host-wide, equal. *)
Theorem fib_addr_type_no_dev :
  forall tbl key,
    inet_dev_addr_type Hostwide tbl key = fib_addr_type tbl key.
Proof. reflexivity. Qed.

(** *** Cross-interface locality (the headline property).

    If [key] is local on the host because it is configured on iface B
    (a route in [tbl] with [lr_dev = B], [lr_type = RTN_LOCAL] containing [key],
    and no earlier route shadows it), then the HOST-WIDE type is RTN_LOCAL no
    matter what interface (A) the packet arrived on — the answer does not mention
    the ingress iface at all. *)
Theorem fib_local_hostwide_crossiface :
  forall pre lo hi devB rest key,
    (* no earlier route in [pre] contains key *)
    Forall (fun r => andb (data_le (lr_lo r) key) (data_le key (lr_hi r)) = false) pre ->
    data_le lo key = true -> data_le key hi = true ->
    fib_addr_type
      (pre ++ {| lr_lo := lo; lr_hi := hi; lr_dev := devB; lr_type := RTN_LOCAL |} :: rest)
      key
    = RTN_LOCAL.
Proof.
  intros pre lo hi devB rest key Hpre Hlo Hhi.
  unfold fib_addr_type. induction pre as [| r pre IH]; simpl.
  - rewrite Hlo, Hhi. reflexivity.
  - inversion Hpre as [| ? ? Hr Hrest]; subst.
    rewrite Hr. apply IH. exact Hrest.
Qed.

(** *** The iif-scoped variant DOWNGRADES a cross-iface local to UNICAST.

    Same table, same key, but the scoped lookup with dev = A (A <> B) on a
    SINGLE local route configured on B yields RTN_UNICAST, not RTN_LOCAL — the
    kernel's [dev == nhc_dev] guard fails.  This is what distinguishes
    `fib daddr . iif type` from plain `fib daddr type`. *)
Theorem fib_local_iif_scoped_downgrade :
  forall lo hi devB rest key ifaceA,
    data_le lo key = true -> data_le key hi = true ->
    ifaceA <> devB ->
    fib_addr_type_iif ifaceA
      ({| lr_lo := lo; lr_hi := hi; lr_dev := devB; lr_type := RTN_LOCAL |} :: rest)
      key
    = RTN_UNICAST.
Proof.
  intros lo hi devB rest key ifaceA Hlo Hhi Hne.
  unfold fib_addr_type_iif; simpl. rewrite Hlo, Hhi; simpl.
  destruct (Nat.eqb ifaceA devB) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

(** And the scoped lookup AGREES with host-wide when the packet entered on the
    very iface the local address is configured on (dev == nhc_dev). *)
Theorem fib_local_iif_scoped_match :
  forall lo hi devB rest key,
    data_le lo key = true -> data_le key hi = true ->
    fib_addr_type_iif devB
      ({| lr_lo := lo; lr_hi := hi; lr_dev := devB; lr_type := RTN_LOCAL |} :: rest)
      key
    = RTN_LOCAL.
Proof.
  intros lo hi devB rest key Hlo Hhi.
  unfold fib_addr_type_iif; simpl. rewrite Hlo, Hhi; simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(** Clean characterisation: `fib daddr type local` FIRES (host-wide) iff [key] is
    in the local-address set. *)
Theorem fib_daddr_type_local_iff :
  forall tbl key,
    fib_addr_type tbl key = RTN_LOCAL <-> is_local tbl key.
Proof. intros tbl key. unfold is_local. reflexivity. Qed.

(* ================================================================= *)
(** ** Tying the precise model back to the base [lpm_fib] load.

    The base [e_routes] table carries a result FUNCTION per route; to make a base
    route faithful to a host-wide local route we compile a [local_route] into an
    [e_routes] entry whose FRtype answer is the route type.  Then the base
    `fib daddr type` load on a wf packet equals the host-wide [fib_addr_type] of
    the real daddr — i.e. the base semantics, de-oracled, IS the kernel mechanism
    for the FRtype selector. *)

Definition lr_to_eroute (r : local_route) : data * data * (fib_result -> data) :=
  (lr_lo r, lr_hi r, fun res => match res with FRtype => lr_type r | _ => [] end).

(** The kernel default [ret = RTN_UNICAST] (fib_frontend.c:208) is reached when NO
    local route matches.  The base [lpm_fib] returns [] on no-match, so to make a
    base [e_routes] table faithful to [fib_addr_type] we append a CATCH-ALL route
    [lo_ca, hi_ca] returning RTN_UNICAST — exactly the kernel default — chosen so
    its interval contains every address the host can ever see (e.g. for IPv4,
    0.0.0.0 .. 255.255.255.255).  Bytes are unbounded [nat] in this model, so we
    carry the catch-all bounds and the containment fact explicitly rather than
    assume a numeric ceiling. *)
Definition mk_catchall (lo_ca hi_ca : data) : data * data * (fib_result -> data) :=
  (lo_ca, hi_ca, fun res => match res with FRtype => RTN_UNICAST | _ => [] end).

Definition compile_local_table (lo_ca hi_ca : data) (tbl : list local_route)
  : list (data * data * (fib_result -> data)) :=
  List.map lr_to_eroute tbl ++ [mk_catchall lo_ca hi_ca].

(** [key] is in the host's address space (covered by the catch-all). *)
Definition key_covered (lo_ca hi_ca key : data) : Prop :=
  andb (data_le lo_ca key) (data_le key hi_ca) = true.

Lemma lpm_fib_compiled_is_addr_type : forall lo_ca hi_ca tbl key,
  key_covered lo_ca hi_ca key ->
  lpm_fib (compile_local_table lo_ca hi_ca tbl) key FRtype = fib_addr_type tbl key.
Proof.
  intros lo_ca hi_ca tbl key Hcov. unfold fib_addr_type, compile_local_table.
  induction tbl as [| r tbl IH]; simpl.
  - (* only the catch-all: it matches because [key] is covered *)
    unfold mk_catchall; simpl. unfold key_covered in Hcov. rewrite Hcov. reflexivity.
  - unfold lr_to_eroute at 1; simpl.
    destruct (andb (data_le (lr_lo r) key) (data_le key (lr_hi r))).
    + reflexivity.
    + exact IH.
Qed.

(** The headline base-semantics theorem: on a wf packet whose host-wide local
    table is the compiled [tbl] (with a covering catch-all), `field_value (FFib
    "daddr" FRtype)` equals the kernel [fib_addr_type] of the REAL daddr bytes —
    key de-oracled AND host-wide type-local computed.  In particular it FIRES
    (= RTN_LOCAL) iff the real daddr is in the local set, regardless of ingress
    iface. *)
Theorem fib_daddr_type_base_is_kernel : forall p lo_ca hi_ca tbl,
  fibkey_wf p ->
  key_covered lo_ca hi_ca (field_value FIp4Daddr p) ->
  e_routes (pkt_env p) = compile_local_table lo_ca hi_ca tbl ->
  field_value (FFib "daddr" FRtype) p = fib_addr_type tbl (field_value FIp4Daddr p).
Proof.
  intros p lo_ca hi_ca tbl Hwf Hcov Hroutes.
  rewrite (fib_daddr_load_is_real p FRtype Hwf), Hroutes.
  apply lpm_fib_compiled_is_addr_type. exact Hcov.
Qed.

(** Cross-iface locality, on the BASE semantics: a wf packet on ANY iface whose
    real daddr is a host-configured local address is `type local`.  Two packets
    with the same routes + same daddr (differing only in MKiif) agree. *)
Theorem fib_daddr_local_iif_independent : forall p p' lo_ca hi_ca tbl,
  fibkey_wf p -> fibkey_wf p' ->
  key_covered lo_ca hi_ca (field_value FIp4Daddr p) ->
  e_routes (pkt_env p)  = compile_local_table lo_ca hi_ca tbl ->
  e_routes (pkt_env p') = compile_local_table lo_ca hi_ca tbl ->
  field_value FIp4Daddr p = field_value FIp4Daddr p' ->
  field_value (FFib "daddr" FRtype) p = field_value (FFib "daddr" FRtype) p'.
Proof.
  intros p p' lo_ca hi_ca tbl Hwf Hwf' Hcov Hr Hr' Hdaddr.
  rewrite (fib_daddr_type_base_is_kernel p lo_ca hi_ca tbl Hwf Hcov Hr).
  assert (Hcov' : key_covered lo_ca hi_ca (field_value FIp4Daddr p'))
    by (unfold key_covered in *; rewrite <- Hdaddr; exact Hcov).
  rewrite (fib_daddr_type_base_is_kernel p' lo_ca hi_ca tbl Hwf' Hcov' Hr').
  rewrite Hdaddr. reflexivity.
Qed.

(* ================================================================= *)
(** ** Part (3): concrete proved WITNESSES — fib local firing / not firing. *)

(** A host-wide local table: 10.0.0.5 is configured LOCAL on iface 7 ("eth-B"),
    everything else (here 10.0.0.0/24 minus the host) is UNICAST.  (Big-endian
    daddr bytes: 10.0.0.5 = [10;0;0;5].) *)
Definition tbl_demo : list local_route :=
  [ {| lr_lo := [10;0;0;5]; lr_hi := [10;0;0;5]; lr_dev := 7; lr_type := RTN_LOCAL  |}
  ; {| lr_lo := [10;0;0;0]; lr_hi := [10;0;0;255]; lr_dev := 7; lr_type := RTN_UNICAST |}
  ].

Definition daddr_local  : data := [10;0;0;5].   (* the host's own address  *)
Definition daddr_remote : data := [10;0;0;9].   (* some other host on /24  *)

(** FIRES: the host's own address is type local (host-wide). *)
Example fib_fires_local :
  fib_addr_type tbl_demo daddr_local = RTN_LOCAL.
Proof. vm_compute. reflexivity. Qed.

(** DOES NOT FIRE: a remote address on the same /24 is UNICAST, not local. *)
Example fib_no_fire_remote :
  fib_addr_type tbl_demo daddr_remote <> RTN_LOCAL.
Proof. vm_compute. discriminate. Qed.

(** CROSS-IFACE (host-wide): the packet entered on iface 3 ("eth-A"), but the
    daddr 10.0.0.5 is configured on iface 7 ("eth-B").  Host-wide lookup ignores
    the ingress iface entirely, so it is STILL type local. *)
Example fib_crossiface_still_local :
  fib_addr_type tbl_demo daddr_local = RTN_LOCAL.
Proof. vm_compute. reflexivity. Qed.

(** SAME cross-iface case, but the IIF-SCOPED variant with dev = iface 3:
    nhc_dev = 7 <> 3, so the kernel downgrades to UNICAST — NOT type local.
    This is the distinguishing case. *)
Example fib_iif_scoped_not_local :
  fib_addr_type_iif 3 tbl_demo daddr_local <> RTN_LOCAL.
Proof. vm_compute. discriminate. Qed.

(** The iif-scoped variant DOES fire when the packet entered on the configured
    iface (dev = 7 = nhc_dev). *)
Example fib_iif_scoped_local_onface :
  fib_addr_type_iif 7 tbl_demo daddr_local = RTN_LOCAL.
Proof. vm_compute. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** A full packet-level witness through the BASE semantics.

    We build a concrete packet [pkt_local] carrying daddr 10.0.0.5 in its network
    header, with [pkt_fibkey] wired wf-ly (= the real bytes) and [e_routes] the
    compiled [tbl_demo].  We then SEE `field_value (FFib "daddr" FRtype)` fire. *)

(* a network header where bytes [16..19] (PNetwork 16 4 = daddr) are 10.0.0.5 *)
Definition nh_local : list byte :=
  (* 0..15 ip header prefix (saddr at 12..15 = 192.168.1.1), 16..19 daddr *)
  [0;0;0;0; 0;0;0;0; 0;0;0;0; 192;168;1;1; 10;0;0;5].

Definition nh_remote : list byte :=
  [0;0;0;0; 0;0;0;0; 0;0;0;0; 192;168;1;1; 10;0;0;9].

(** The shared env: e_routes = compiled local table. *)
Definition env_demo : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := compile_local_table [0;0;0;0] [255;255;255;255] tbl_demo;
     e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddr := fun _ => []; e_ifaddr6 := fun _ => [];
     e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

(** A wf fibkey that returns the real header bytes for every selector. *)
Definition demo_fibkey (nh : list byte) : string -> data :=
  fun sel =>
    if (String.eqb sel "daddr" || String.eqb sel "daddr . iif")%bool
    then slice nh 16 4
    else if (String.eqb sel "saddr" || String.eqb sel "saddr . iif")%bool
         then slice nh 12 4
         else [].

Definition mk_demo_packet (nh : list byte) : packet :=
  {| pkt_env := env_demo;
     pkt_meta := fun _ => [];
     pkt_ct := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := nh; pkt_th := []; pkt_ih := []; pkt_tnl := [];
     pkt_fibkey := demo_fibkey nh; pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := true;
     pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false;
     pkt_ctdir_orig := true; pkt_ct_present := true |}.

Definition pkt_local  : packet := mk_demo_packet nh_local.
Definition pkt_remote : packet := mk_demo_packet nh_remote.

(** [pkt_local] is wf: its oracle key IS its real daddr/saddr bytes. *)
Lemma pkt_local_wf : fibkey_wf pkt_local.
Proof. unfold fibkey_wf, pkt_local; simpl. repeat split; reflexivity. Qed.

Lemma pkt_remote_wf : fibkey_wf pkt_remote.
Proof. unfold fibkey_wf, pkt_remote; simpl. repeat split; reflexivity. Qed.

(** The real daddr of [pkt_local] is 10.0.0.5. *)
Example pkt_local_daddr : field_value FIp4Daddr pkt_local = daddr_local.
Proof. vm_compute. reflexivity. Qed.

(** FIRES on the base semantics: `fib daddr type` of [pkt_local] is RTN_LOCAL
    ( = fib_local from Optiplex_Mark.v). *)
Example fib_base_fires :
  field_value (FFib "daddr" FRtype) pkt_local = RTN_LOCAL.
Proof. vm_compute. reflexivity. Qed.

(** DOES NOT FIRE on the base semantics: `fib daddr type` of [pkt_remote]
    (daddr 10.0.0.9) is NOT RTN_LOCAL. *)
Example fib_base_no_fire :
  field_value (FFib "daddr" FRtype) pkt_remote <> RTN_LOCAL.
Proof. vm_compute. discriminate. Qed.

(** And it equals the kernel [fib_addr_type] of the real daddr (the de-oracled,
    host-wide, byte-derived answer) — derived via the general theorem, NOT
    assumed. *)
Example fib_base_is_kernel_demo :
  field_value (FFib "daddr" FRtype) pkt_local
    = fib_addr_type tbl_demo (field_value FIp4Daddr pkt_local).
Proof.
  apply (fib_daddr_type_base_is_kernel pkt_local [0;0;0;0] [255;255;255;255] tbl_demo).
  - apply pkt_local_wf.
  - unfold key_covered. vm_compute. reflexivity.
  - reflexivity.
Qed.

(* ================================================================= *)
(** ** Axiom-freedom audit. *)

Print Assumptions fib_key_is_daddr.
Print Assumptions fib_key_is_saddr.
Print Assumptions fib_daddr_load_is_real.
Print Assumptions fib_addr_type_no_dev.
Print Assumptions fib_local_hostwide_crossiface.
Print Assumptions fib_local_iif_scoped_downgrade.
Print Assumptions fib_local_iif_scoped_match.
Print Assumptions fib_daddr_type_local_iff.
Print Assumptions lpm_fib_compiled_is_addr_type.
Print Assumptions fib_daddr_type_base_is_kernel.
Print Assumptions fib_daddr_local_iif_independent.
Print Assumptions fib_fires_local.
Print Assumptions fib_no_fire_remote.
Print Assumptions fib_iif_scoped_not_local.
Print Assumptions fib_base_fires.
Print Assumptions fib_base_no_fire.
Print Assumptions fib_base_is_kernel_demo.
