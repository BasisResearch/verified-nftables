(** * Regression: a short / absent transport header must NOT match a negated
    transport condition (no silent truncation).

    Linux nft (net/netfilter/nft_payload.c, nft_payload_eval) BREAKs the rule
    (NFT_BREAK -> the rule does not match, the packet falls through to the next
    rule / the chain policy) when a TRANSPORT-base payload load runs off the end
    of the header, or the packet has no L4 header, or it is an IP fragment.

    A model that instead SILENTLY TRUNCATED such a read to a short/empty byte
    string would make a *negated* transport match (`tcp dport != 22`) spuriously
    SUCCEED on a fragment / short / no-L4 packet (truncated [] != [0;22] = true),
    and a chain [tcp dport != 22 -> Drop] would DROP such a packet — both FALSE
    of real nftables (the kernel breaks; the packet reaches the policy).

    These theorems pin the NFT_BREAK behaviour and refute the truncating
    alternative:
      - [neq_dport_short_no_match]: the negated dport match is [false] on a packet
        with no usable transport header (the load breaks), regardless of negation;
      - [chain_dropneq_short_accepts]: a chain whose only rule is
        `tcp dport != 22 -> Drop` ACCEPTS (the policy) such a packet rather than
        dropping it.
    Both are about a packet [bad_pkt] with [pkt_have_l4 = false] (and an empty
    transport header), so the transport read [read_payload_ok PTransport 2 2]
    is [false] = the kernel's NFT_BREAK. *)

From Stdlib Require Import List NArith Bool.
From Nft Require Import Bytes Verdict Packet Syntax Semantics Compile Correct.
Import ListNotations.

(** A minimal packet with NO usable transport header: [pkt_have_l4 = false] and an
    empty [pkt_th].  Every oracle/field is a trivial default; only the transport
    loadability matters here. *)
Definition empty_env : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_limit := fun _ => 0; e_quota := fun _ => 0; e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

Definition bad_pkt : packet :=
  {|
     pkt_meta := fun _ => []; pkt_sock := fun _ => [];
     pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := []; pkt_tnl := [];
     pkt_fibkey := fun _ => []; pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => [];
     pkt_have_l2 := true; pkt_have_l4 := false;     (* NFT_PKTINFO_L4PROTO not set -> transport read BREAKs *)
     pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := true |}.

(** The transport read fails (the kernel would NFT_BREAK). *)
Lemma bad_pkt_th_breaks : read_payload_ok PTransport 2 2 bad_pkt = false.
Proof. reflexivity. Qed.

(** *** The fix, at the single-match level: a negated transport match does NOT
    apply when its load breaks — it is [false], NOT spuriously [true]. *)
Theorem neq_dport_short_no_match :
  eval_matchcond (MNeq FThDport [0; 22]) empty_env bad_pkt = false.
Proof. reflexivity. Qed.

(** For contrast: the *non-negated* equality match is also [false] (the rule does
    not match either way — the break is independent of the comparison). *)
Theorem eq_dport_short_no_match :
  eval_matchcond (MEq FThDport [0; 22]) empty_env bad_pkt = false.
Proof. reflexivity. Qed.

(** *** The fix, at the chain level: a chain whose only rule is
    `tcp dport != 22 -> Drop` ACCEPTS (the policy) a no-L4 packet — it does NOT
    drop it.  This DIRECTLY refutes the previously-provable incorrect property
    [eval_chain [tcp dport != 22 -> Drop] frag_pkt = Drop]. *)
Definition dropneq_chain : chain :=
  {| c_policy := Accept;
     c_rules := [ {| r_body := [BMatch (MNeq FThDport [0; 22])];
                     r_verdict := Drop; r_vmap := None; r_nat := None;
                     r_tproxy := None; r_fwd := None; r_queue := None;
                     r_after := [] |} ] |}.

Theorem chain_dropneq_short_accepts :
  eval_chain dropneq_chain empty_env bad_pkt = Accept.
Proof. reflexivity. Qed.

(** And the OLD incorrect verdict ([Drop]) is now disprovable — the chain does not
    drop. *)
Theorem chain_dropneq_short_not_drop :
  eval_chain dropneq_chain empty_env bad_pkt <> Drop.
Proof. discriminate. Qed.

(** The compiled bytecode agrees (via [compile_chain_correct]): the installed
    netlink program also ACCEPTS the no-L4 packet — the VM's [IPayloadLoad] breaks
    exactly as the kernel does. *)
Theorem chain_dropneq_short_accepts_bytecode :
  run_chain (compile_chain dropneq_chain) (c_policy dropneq_chain) empty_env bad_pkt = Accept.
Proof. rewrite compile_chain_correct. apply chain_dropneq_short_accepts. Qed.

(** A first-fragment-style packet (L4 present but [pkt_fragoff <> 0]) likewise
    breaks a transport read: a non-first fragment carries no usable transport
    header. *)
Definition frag_pkt : packet :=
  {|
     pkt_meta := fun _ => []; pkt_sock := fun _ => [];
     pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := [9; 9; 9; 9]; pkt_ih := []; pkt_tnl := [];
     pkt_fibkey := fun _ => []; pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => [];
     pkt_have_l2 := true; pkt_have_l4 := true;
     pkt_fragoff := 8; pkt_flow := []; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := true |}.   (* a non-first fragment *)

Theorem neq_dport_frag_no_match :
  eval_matchcond (MNeq FThDport [0; 22]) empty_env frag_pkt = false.
Proof. reflexivity. Qed.

Theorem chain_dropneq_frag_accepts :
  eval_chain dropneq_chain empty_env frag_pkt = Accept.
Proof. reflexivity. Qed.
