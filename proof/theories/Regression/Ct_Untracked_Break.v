(** A conntrack key read on a packet with NO conntrack entry BREAKs the rule
    (kernel-faithful), for EVERY key except `ct state`.

    ── Kernel truth (net/netfilter/nft_ct.c) ──────────────────────────────────────
        ct = nf_ct_get(pkt->skb, &ctinfo);            // NULL for an untracked/INVALID skb
        switch (priv->key) {
        case NFT_CT_STATE: ...; *dest = state; return; // :68-76 the ONLY key that
                                                       //   yields a value when ct==NULL
        default: break;
        }
        if (ct == NULL) goto err;                      // :81-82 EVERY other key
        ... case NFT_CT_DIRECTION/STATUS/MARK/EXPIRATION/ID ...
      err:
        regs->verdict.code = NFT_BREAK;                // :220-221 rule does NOT match
    For an untracked packet `nf_ct_get` returns NULL with ctinfo == IP_CT_UNTRACKED
    (nft_notrack_eval: nf_ct_set(skb, NULL, IP_CT_UNTRACKED)); for an INVALID packet
    NULL with ctinfo == 0.  Either way every non-state key BREAKs.

    ── Model ──────────────────────────────────────────────────────────────────────
    A per-packet [pkt_ct_present] flag records whether `nf_ct_get` returns non-NULL
    (an entry exists).  [load_ok (LCt CKstate) = true] (state is the lone always-
    readable key); [load_ok (LCt k<>CKstate) = pkt_ct_present p] — the non-state load
    BREAKs when there is no entry, exactly mirroring the kernel's NFT_BREAK.  The VM
    ([ICtLoad] in [run_rule]/[run_rule_step]) gates on the SAME [load_ok], so DSL and
    VM stay in lock-step (compile_chain_correct is axiom-free with this gate).
    [do_load (LCt CKstate)] returns NF_CT_STATE_INVALID_BIT ([0;0;0;1]) on a no-entry,
    non-untracked packet and NF_CT_STATE_UNTRACKED_BIT ([0;0;0;64]) on an untracked one,
    matching nft_ct.c:68-76.

    Regression gate: [ctmark_does_not_match_no_entry], [ctdir_does_not_match_no_entry],
    and [vm_ctmark_load_breaks_no_entry] lock in the no-entry BREAK; a model whose
    conntrack loads never break (a `ct mark 0x10 accept` matching a packet with no
    conntrack entry) makes them unprovable. *)

From Stdlib Require Import List Bool.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics.
Import ListNotations.

(** A packet with NO conntrack entry ([pkt_ct_present = false]): an untracked or
    INVALID skb.  Its conntrack table would report `ct mark 0x10`, but the kernel
    never reaches the mark read (it BREAKs at `if (ct == NULL)`). *)
Definition e_noentry : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => [];
     e_ct := fun _ k => match k with CKmark => [0;0;0;16] | _ => [] end;
     e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

Definition pkt_noentry : packet :=
  {| pkt_meta := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := []; pkt_tnl := [];
     pkt_fibkey := fun _ => []; pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := false;
     pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false; pkt_ctdir_orig := true;
     pkt_ct_present := false |}.

(** ── 1. The non-state ct keys BREAK on a no-entry packet (load_ok = false). *)
Theorem ct_mark_breaks_when_no_entry :
  load_ok (LCt CKmark) pkt_noentry = false.
Proof. reflexivity. Qed.

Theorem ct_direction_breaks_when_no_entry :
  load_ok (LCt CKdirection) pkt_noentry = false.
Proof. reflexivity. Qed.

Theorem ct_status_breaks_when_no_entry :
  load_ok (LCt CKstatus) pkt_noentry = false.
Proof. reflexivity. Qed.

Theorem ct_expiration_breaks_when_no_entry :
  load_ok (LCt CKexpiration) pkt_noentry = false.
Proof. reflexivity. Qed.

Theorem ct_id_breaks_when_no_entry :
  load_ok (LCt CKid) pkt_noentry = false.
Proof. reflexivity. Qed.

(** Generic: EVERY key but [CKstate] breaks on a no-entry packet. *)
Theorem ct_nonstate_breaks_when_no_entry :
  forall k, k <> CKstate -> load_ok (LCt k) pkt_noentry = false.
Proof. intros k Hk. destruct k; cbn; congruence. Qed.

(** ── 2. `ct state` is STILL readable on a no-entry packet (the lone exception). *)
Theorem ct_state_still_readable_when_no_entry :
  load_ok (LCt CKstate) pkt_noentry = true.
Proof. reflexivity. Qed.

(** And it reads NF_CT_STATE_INVALID_BIT (1<<0 = [0;0;0;1]) on an INVALID/no-entry,
    non-untracked packet — exactly nft_ct.c's `else state = NF_CT_STATE_INVALID_BIT`
    (nf_conntrack_common.h:37 NF_CT_STATE_INVALID_BIT = (1<<0)), agreeing with nft
    userspace's ct_state_tbl (src/ct.c: SYMBOL("invalid", NF_CT_STATE_INVALID_BIT))
    and the project parser (nft_lower.ml: "invalid",[0;0;0;1]). *)
Theorem ct_state_reads_invalid_when_no_entry :
  do_load (LCt CKstate) e_noentry pkt_noentry = [0;0;0;1].
Proof. reflexivity. Qed.

(** REGRESSION: a no-entry / non-untracked packet provably MATCHES
    `ct state invalid` — the state register [0;0;0;1] equals the immediate the parser
    emits for the keyword `invalid` ([0;0;0;1]).  The naive alternative (reading
    1<<5 = [0;0;0;32], a bit the kernel never assigns) would make this rule
    unmatchable and is refuted by this theorem. *)
Theorem ctstate_invalid_matches_no_entry :
  eval_matchcond (MEq FCtState [0;0;0;1]) e_noentry pkt_noentry = true.
Proof. reflexivity. Qed.

(** ── 3. The no-entry BREAK, at the match level.

    `ct mark 0x10 accept` does NOT match the no-entry packet: the match is gated by
    [match_loadable], which is [false] (the load BREAKs), so [eval_matchcond]
    returns [false] regardless of the conntrack table value — the rule falls through,
    exactly as the kernel does. *)
Definition m_ctmark : matchcond := MEq FCtMark [0;0;0;16].

Theorem ctmark_does_not_match_no_entry :
  eval_matchcond m_ctmark e_noentry pkt_noentry = false.
Proof. reflexivity. Qed.

Definition m_ctdir_orig : matchcond := MEq FCtDirection [0].

Theorem ctdir_does_not_match_no_entry :
  eval_matchcond m_ctdir_orig e_noentry pkt_noentry = false.
Proof. reflexivity. Qed.

(** The exact same `ct mark 0x10` packet, but WITH a conntrack entry
    ([pkt_ct_present = true]), DOES match — the rule is not vacuous; only the no-entry
    case breaks. *)
Definition pkt_withentry : packet :=
  {| pkt_meta := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := []; pkt_tnl := [];
     pkt_fibkey := fun _ => []; pkt_numgen := fun _ => []; pkt_osf := [];
     pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := false;
     pkt_fragoff := 0; pkt_flow := []; pkt_untracked := false; pkt_ctdir_orig := true;
     pkt_ct_present := true |}.

Theorem ctmark_matches_with_entry :
  eval_matchcond m_ctmark e_noentry pkt_withentry = true.
Proof. reflexivity. Qed.

(** ── 4. DSL/VM lock-step: the compiled `ct mark` load BREAKs the rule on the VM
    side too (run_rule = None), so the bytecode and the DSL agree on the no-entry
    packet (both fall through). *)
Theorem vm_ctmark_load_breaks_no_entry :
  forall dst rest rf,
    run_rule rf (ICtLoad CKmark dst :: rest) e_noentry pkt_noentry = None.
Proof. reflexivity. Qed.

Theorem vm_ctstate_load_proceeds_no_entry :
  forall dst rest rf,
    run_rule rf (ICtLoad CKstate dst :: rest) e_noentry pkt_noentry
    = run_rule (set_reg rf dst [0;0;0;1]) rest e_noentry pkt_noentry.
Proof. reflexivity. Qed.
