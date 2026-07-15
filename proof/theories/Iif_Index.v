(* Regression for the iif/oif numeric-index lowering.

   `iif`/`oif` read the numeric interface INDEX (LMeta MKiif/MKoif, Syntax.v),
   which the kernel compares against the load-time-resolved 4-byte host-endian
   ifindex (meta.c ifindex_type: BYTEORDER_HOST_ENDIAN, size 4 bytes; golden
   bytecode tests/py/any/meta.t.payload: `meta iif "lo"` => cmp 0x00000001).
   The parser lowers `iif`/`oif` with kind KIfindex, encoding the RHS as the
   4-byte little-endian (host-endian on x86) index — NOT the ASCII name bytes
   (which are correct only for `iifname`/`oifname`).

   This file pins the lowering on the REAL parser output: Optiplex_Gen's
   filter_input carries `iif lo` lowered to `MEq FMetaIif [1;0;0;0]` (loopback
   index 1, little-endian), and that matchcond correctly matches a packet that
   genuinely arrived on lo (MKiif = [1;0;0;0]) and rejects the impossible
   ASCII-meta packet (which an ASCII-name lowering of `iif` would match). *)

From Stdlib Require Import List Bool.
From Nft Require Import Bytes Packet Verdict Syntax Semantics Optiplex_Gen.
Import ListNotations.

Definition e0 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => []; e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

(* Build a packet whose numeric iif metadata is [idx]. *)
Definition pkt_iif (idx : data) : packet :=
  {| pkt_env := e0;
     pkt_meta := fun k => match k with MKiif => idx | _ => [] end;
     pkt_ct := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := []; pkt_tnl := [];
     pkt_fibkey := fun _ => []; pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := false; pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* The matchcond the parser now produces for `iif lo`: the 4-byte little-endian
   loopback index (1), NOT the ASCII "lo" = [108;111]. *)
Definition m_iif_lo : matchcond := MEq FMetaIif [1;0;0;0].

(* The parser actually emits this: it is the second rule's body in the
   generated filter_input chain (optiplex.nft line 30: `iif lo accept`).
   This ties the regression to the REAL parser output, not a hand copy. *)
Example parser_lowers_iif_lo_to_index :
  exists v after,
    nth 1 (c_rules filter_input)
      {| r_body := []; r_verdict := Drop; r_vmap := None; r_nat := None;
         r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}
    = {| r_body := [BMatch m_iif_lo]; r_verdict := v; r_vmap := None;
         r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None;
         r_after := after |}.
Proof. eexists; eexists; reflexivity. Qed.

(* A packet that genuinely arrived on lo (numeric iif index 1) MATCHES `iif lo`.
   The refuted ASCII alternative (MEq FMetaIif [108;111]) makes this FALSE. *)
Theorem iif_lo_matches_real_lo_packet :
  eval_matchcond m_iif_lo (pkt_iif [1;0;0;0]) = true.
Proof. vm_compute. reflexivity. Qed.

(* A packet on a different interface (index 2) does NOT match. *)
Theorem iif_lo_misses_other_iface :
  eval_matchcond m_iif_lo (pkt_iif [2;0;0;0]) = false.
Proof. vm_compute. reflexivity. Qed.

(* The impossible ASCII-meta packet (iif = ASCII "lo") does not match:
   the model compares against the numeric index, not the name string. *)
Theorem iif_lo_rejects_ascii_meta :
  eval_matchcond m_iif_lo (pkt_iif [108;111]) = false.
Proof. vm_compute. reflexivity. Qed.
