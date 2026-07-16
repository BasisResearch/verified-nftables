(* Regression for the single-positive `ct state X` bitmask lowering.

   ct_state has .basetype = bitmask_type (nftables src/ct.c:54).  The relational
   evaluator (src/evaluate.c:2792-2797) rewrites an OP_IMPLICIT relational over a
   TYPE_BITMASK basetype to OP_EQ for EVERY bitmask type EXCEPT TYPE_CT_STATE
   (`rel->right->dtype->type != TYPE_CT_STATE`).  So a single positive
   `ct state established` does NOT compile to exact equality; it stays an
   implicit bitmask test, emitted (golden tests/py/any/ct.t.payload:35-40) as

     [ ct load state => reg 1 ]
     [ bitwise reg 1 = ( reg 1 & 0x00000002 ) ^ 0x00000000 ]
     [ cmp neq reg 1 0x00000000 ]

   i.e. it matches iff (state & 2) != 0, NOT state == 2.

   The parser lowers a single positive `ct state X` to
     MMasked FCtState CNe X [0;0;0;0] [0;0;0;0]
   which Semantics.v evaluates as
     eval_cmp CNe (data_bitops state X 0) 0 = (state & X) != 0,
   exactly matching the golden bytecode.

   Consequence proven below: a packet whose ct-state register has the
   established bit set together with another bit (state = 2|64 = 66) is ACCEPTED
   by the bitmask form (real nft: 66 & 2 = 2 != 0) but REJECTED by the refuted
   exact-equality (MEq) alternative (66 <> 2). *)

From Stdlib Require Import List Bool.
From Nft Require Import Bytes Packet Verdict Bytecode Syntax Semantics.
Import ListNotations.

(* The conntrack-state value is read from the SHARED, flow-keyed table [e_ct]
   at the packet's flow (here the empty flow []), NOT a per-packet oracle: this
   env records ct state [st] for the flow []. *)
Definition e0_st (st : data) : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => []; e_connlimit := fun _ => [];
     e_ct := fun _ k => match k with CKstate => st | _ => [] end;
     e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

(* A packet whose conntrack-state register is [st] (stored in the flow table). *)
Definition pkt_ctstate (st : data) : packet :=
  {| pkt_meta := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := []; pkt_tnl := [];
     pkt_fibkey := fun _ => []; pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := false; pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* The matchcond the parser emits for a single positive `ct state established`. *)
Definition m_estab : matchcond :=
  MMasked FCtState CNe [0;0;0;2] [0;0;0;0] [0;0;0;0].

(* The refuted exact-equality lowering, for contrast. *)
Definition m_estab_refuted : matchcond := MEq FCtState [0;0;0;2].

(* The bitmask form matches a pure established state (= 2). *)
Theorem estab_matches_pure :
  eval_matchcond m_estab (e0_st [0;0;0;2]) (pkt_ctstate [0;0;0;2]) = true.
Proof. vm_compute. reflexivity. Qed.

(* The KEY case: established | untracked (= 2|64 = 66) has the established bit
   set.  Real nft ACCEPTS it (66 & 2 = 2 != 0); the new lowering matches it. *)
Theorem estab_matches_established_plus_other :
  eval_matchcond m_estab (e0_st [0;0;0;66]) (pkt_ctstate [0;0;0;66]) = true.
Proof. vm_compute. reflexivity. Qed.

(* A state without the established bit (= new = 8) does NOT match. *)
Theorem estab_misses_without_bit :
  eval_matchcond m_estab (e0_st [0;0;0;8]) (pkt_ctstate [0;0;0;8]) = false.
Proof. vm_compute. reflexivity. Qed.

(* The exact-equality (MEq) alternative WRONGLY rejects the established|other
   packet: a strict under-approximation that loses every multi-bit state. *)
Theorem refuted_meq_rejects :
  eval_matchcond m_estab_refuted (e0_st [0;0;0;66]) (pkt_ctstate [0;0;0;66]) = false.
Proof. vm_compute. reflexivity. Qed.

(* The two lowerings genuinely DIFFER on that packet — the bitmask form is
   observably load-bearing exactly there. *)
Theorem refuted_alternative_diverges :
  eval_matchcond m_estab (e0_st [0;0;0;66]) (pkt_ctstate [0;0;0;66])
    <> eval_matchcond m_estab_refuted (e0_st [0;0;0;66]) (pkt_ctstate [0;0;0;66]).
Proof. vm_compute. discriminate. Qed.

(** Axiom-freedom prints (INFORMATIONAL: they go to the build log but cannot
    fail the build).  The build-FAILING check is `make axioms`, whose
    AXIOM_GATE_THEOREMS list carries all five theorems of this file — the
    README's "ct-state" axiom-free claim is gated there. *)
Print Assumptions estab_matches_pure.
Print Assumptions estab_matches_established_plus_other.
Print Assumptions estab_misses_without_bit.
Print Assumptions refuted_meq_rejects.
Print Assumptions refuted_alternative_diverges.
