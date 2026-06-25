(* Regression for the single-positive `tcp flags X` bitmask fix.

   tcp_flag_type has .basetype = &bitmask_type (nftables src/proto.c:583-591).
   The relational evaluator (src/evaluate.c:2792-2797) only rewrites an
   OP_IMPLICIT relational over a TYPE_BITMASK basetype to OP_EQ for *non-set*
   bitmask types, and the golden bytecode shows a bare `tcp flags X` stays an
   implicit bitmask test, emitted (golden tests/py/inet/tcp.t.payload:331-337)
   for `tcp flags cwr` as

     [ payload load 1b @ transport header + 13 => reg 1 ]
     [ bitwise reg 1 = ( reg 1 & 0x80 ) ^ 0x00 ]
     [ cmp neq reg 1 0x00 ]

   i.e. it matches iff (flags & X) != 0, NOT flags == X.  Only the EXPLICIT
   `tcp flags == X` is exact equality (tcp.t.payload:346-351 `cmp eq reg 1 0x02`).

   The four written operators differ (tests/py/inet/tcp.t:69-74):
     implicit `tcp flags X`    -> (flags & X) != 0   MMasked neg:=true
     bang     `tcp flags ! X`  -> (flags & X) == 0   MMasked neg:=false  (& X == 0)
     explicit `tcp flags == X` -> flags == X         MEq
     explicit `tcp flags != X` -> flags != X         MNeq               (cmp neq)

   The parser now lowers a single positive `tcp flags X` to
     MMasked FTcpFlags (neg:=true) [X] [0] [0]
   which Semantics.v evaluates as
     eval_cmp CNe (data_bitops flags [X] [0]) [0] = (flags & X) != 0,
   exactly matching the golden bytecode.

   Consequence proven below: a SYN|ACK packet (flags = 0x12 = syn|ack) is
   ACCEPTED by the bitmask form for `tcp flags syn` (real nft: 0x12 & 0x02 = 2
   != 0) but was REJECTED by the old exact-equality (MEq) encoding
   (0x12 <> 0x02). *)

From Stdlib Require Import List Bool.
From Nft Require Import Bytes Packet Verdict Syntax Semantics.
Import ListNotations.

Definition e0 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => []; e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

(* A TCP packet whose flags byte (transport header + 13) is [fl].
   FTcpFlags = LPayload PTransport 13 1 reads pkt_th at offset 13, length 1. *)
Definition pkt_tcpflags (fl : nat) : packet :=
  {| pkt_env := e0; pkt_meta := fun _ => []; pkt_ct := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := [];
     pkt_th := [0;0;0;0;0;0;0;0;0;0;0;0;0;fl];
     pkt_ih := []; pkt_tnl := [];
     pkt_fibkey := fun _ => []; pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := true; pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* fin=0x01 syn=0x02 rst=0x04 psh=0x08 ack=0x10 urg=0x20 ecn=0x40 cwr=0x80 *)

(* The matchcond the parser now emits for a single positive `tcp flags syn`. *)
Definition m_syn : matchcond := MMasked FTcpFlags true [2] [0] [0].
(* The old (only buildable / wrong) exact-equality encoding, for contrast. *)
Definition m_syn_old : matchcond := MEq FTcpFlags [2].
(* `tcp flags ! syn` (BANG): (flags & syn) == 0. *)
Definition m_not_syn : matchcond := MMasked FTcpFlags false [2] [0] [0].
(* `tcp flags == syn` (explicit EQ): exact equality. *)
Definition m_syn_eq : matchcond := MEq FTcpFlags [2].
(* `tcp flags != cwr` (explicit NE): plain cmp neq. *)
Definition m_ne_cwr : matchcond := MNeq FTcpFlags [128].

(* The bitmask form matches a pure SYN packet (flags = 0x02). *)
Theorem syn_matches_pure_syn :
  eval_matchcond m_syn (pkt_tcpflags 2) = true.
Proof. vm_compute. reflexivity. Qed.

(* THE KEY case: a SYN|ACK packet (flags = 0x12 = 18) has the SYN bit set.
   Real nft ACCEPTS it for `tcp flags syn` (0x12 & 0x02 = 2 != 0); the new
   lowering matches it. *)
Theorem syn_matches_synack :
  eval_matchcond m_syn (pkt_tcpflags 18) = true.
Proof. vm_compute. reflexivity. Qed.

(* A packet without the SYN bit (flags = 0x10 = ACK only) does NOT match. *)
Theorem syn_misses_ack_only :
  eval_matchcond m_syn (pkt_tcpflags 16) = false.
Proof. vm_compute. reflexivity. Qed.

(* The old MEq encoding WRONGLY rejected the SYN|ACK packet: a strict
   under-approximation that rejects every multi-flag packet. *)
Theorem old_meq_wrongly_rejects_synack :
  eval_matchcond m_syn_old (pkt_tcpflags 18) = false.
Proof. vm_compute. reflexivity. Qed.

(* So the new and old lowerings genuinely DIFFER on the SYN|ACK packet — the
   fix changes observable behaviour exactly where the bug was. *)
Theorem fix_changes_behaviour :
  eval_matchcond m_syn     (pkt_tcpflags 18)
    <> eval_matchcond m_syn_old (pkt_tcpflags 18).
Proof. vm_compute. discriminate. Qed.

(* The BANG form `tcp flags ! syn` = (flags & syn) == 0 is the complement of the
   implicit form: it REJECTS SYN|ACK (the SYN bit is set) and ACCEPTS ACK-only. *)
Theorem not_syn_rejects_synack :
  eval_matchcond m_not_syn (pkt_tcpflags 18) = false.
Proof. vm_compute. reflexivity. Qed.
Theorem not_syn_accepts_ack_only :
  eval_matchcond m_not_syn (pkt_tcpflags 16) = true.
Proof. vm_compute. reflexivity. Qed.

(* The EXPLICIT `tcp flags == syn` is genuine exact equality: it REJECTS SYN|ACK
   (0x12 <> 0x02) but ACCEPTS a pure SYN (0x02 == 0x02).  This is the only form
   that is equality, and it differs from the implicit/bitmask form on SYN|ACK. *)
Theorem eq_syn_rejects_synack :
  eval_matchcond m_syn_eq (pkt_tcpflags 18) = false.
Proof. vm_compute. reflexivity. Qed.
Theorem eq_syn_accepts_pure_syn :
  eval_matchcond m_syn_eq (pkt_tcpflags 2) = true.
Proof. vm_compute. reflexivity. Qed.
Theorem implicit_and_explicit_differ :
  eval_matchcond m_syn (pkt_tcpflags 18)
    <> eval_matchcond m_syn_eq (pkt_tcpflags 18).
Proof. vm_compute. discriminate. Qed.

(* The explicit `tcp flags != cwr` is a plain cmp neq (NOT a bitmask test): it
   matches any flags value other than exactly 0x80. *)
Theorem ne_cwr_matches_non_cwr :
  eval_matchcond m_ne_cwr (pkt_tcpflags 2) = true.
Proof. vm_compute. reflexivity. Qed.
Theorem ne_cwr_misses_exact_cwr :
  eval_matchcond m_ne_cwr (pkt_tcpflags 128) = false.
Proof. vm_compute. reflexivity. Qed.
