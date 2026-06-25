(** Round-3 fix (notrack -> ct state untracked), refined by the notrack-no-op round.

    ── Kernel truth ─────────────────────────────────────────────────────────────
    nft_notrack_eval (net/netfilter/nft_ct.c:860-874):
        ct = nf_ct_get(pkt->skb, &ctinfo);
        if (ct || ctinfo == IP_CT_UNTRACKED)   // entry present? => NO-OP, ignore
            return;
        nf_ct_set(skb, ct, IP_CT_UNTRACKED);   // sets ct UNTRACKED only when ct==NULL
    nft_ct_get_eval (nft_ct.c:67-77), the `ct state` reader:
        case NFT_CT_STATE:
            if (ct)                     state = NF_CT_STATE_BIT(ctinfo);
            else if (ctinfo == IP_CT_UNTRACKED)
                                        state = NF_CT_STATE_UNTRACKED_BIT;   // 1<<6 = 64
    => `notrack` latches IP_CT_UNTRACKED ONLY on a packet that has NO conntrack entry
       yet (ct == NULL).  On such a NO-ENTRY packet a SUBSEQUENT `ct state` read (in a
       LATER rule of the chain) returns NF_CT_STATE_UNTRACKED_BIT (= 64), so
       `notrack` (rule 1) ; `ct state untracked accept` (rule 2) ACCEPTS it.  On a
       packet that ALREADY has an entry the `notrack` is a NO-OP and the later
       `ct state` read returns the entry's REAL state.

    ── Model (fixed) ─────────────────────────────────────────────────────────────
    [SNotrack]/[INotrack] apply [set_untracked] in [body_writes]/[run_rule_writes].
    [set_untracked] mirrors the kernel guard: it is a NO-OP when [pkt_ct_present = true]
    and otherwise sets the per-packet-traversal flag [pkt_untracked := true].  The
    cross-rule threader [eval_rules_mut] carries [dsl_writes r1 p] (= [set_untracked p])
    into the NEXT rule, whose `ct state` match reads [do_load (LCt CKstate)] = [0;0;0;64]
    on a no-entry packet ([pkt_untracked] override) and the live entry state otherwise.
    The DSL and the VM apply the SAME [set_untracked], so [compile_chain_correct] stays
    axiom-free.

    Below: on a NO-ENTRY packet `notrack; ct state untracked accept` ACCEPTS (provable,
    and disprovable before the rule-walk fix); on an ENTRY-present packet `notrack` is a
    no-op and the chain DROPS (the notrack-no-op refinement). *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Packet Verdict Syntax Semantics.
Import ListNotations.

(* `ct state untracked`: the single-positive bitmask form the parser emits
   (cf. theories/Ct_State.v): (state & 64) != 0. *)
Definition untracked_bytes : data := [0;0;0;64].   (* NF_CT_STATE_UNTRACKED_BIT *)

Definition m_untracked : matchcond :=
  MMasked FCtState true untracked_bytes [0;0;0;0] [0;0;0;0].

(* Rule 1: bare `notrack` (Continue => falls through to rule 2, threading the
   set_untracked write). *)
Definition notrack_only : rule :=
  {| r_body := [ BStmt SNotrack ];
     r_verdict := Continue; r_vmap := None; r_nat := None; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.

(* Rule 2: `ct state untracked accept`. *)
Definition ctstate_rule : rule :=
  {| r_body := [ BMatch m_untracked ];
     r_verdict := Accept; r_vmap := None; r_nat := None; r_tproxy := None;
     r_fwd := None; r_queue := None; r_after := [] |}.

(* The two-rule chain, default policy Drop. *)
Definition notrack_chain : chain :=
  {| c_policy := Drop; c_rules := [ notrack_only; ctstate_rule ] |}.

Definition env0 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

(* A NO-ENTRY packet ([pkt_ct_present := false]): nf_ct_get returns NULL, the case
   where `notrack` HAS an effect.  The `notrack` in rule 1 latches it untracked
   before the `ct state untracked` match in rule 2 runs. *)
Definition pkt_noentry : packet :=
  {| pkt_env := env0; pkt_meta := fun _ => [];
     pkt_ct := fun k => match k with CKstate => [0;0;0;8] | _ => [] end;
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := false; pkt_fragoff := 0;
     pkt_flow := [7;7]; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := false |}.

(* The notrack write threads into rule 2: do_load (LCt CKstate) of the threaded
   no-entry packet returns the untracked constant. *)
Lemma untracked_after_notrack :
  do_load (LCt CKstate) (dsl_writes notrack_only pkt_noentry) = [0;0;0;64].
Proof. vm_compute. reflexivity. Qed.

(* Consequently the `ct state untracked` match in rule 2 SUCCEEDS on the threaded
   packet — the notrack had a real effect. *)
Lemma untracked_match_succeeds :
  eval_matchcond m_untracked (dsl_writes notrack_only pkt_noentry) = true.
Proof. vm_compute. reflexivity. Qed.

(* The threading evaluator ACCEPTS the no-entry packet — matching the kernel.  (The
   old rule-walk model DROPPED it: notrack was skipped and `ct state untracked` read
   the stale oracle.) *)
Theorem model_accepts_like_kernel :
  eval_chain_mut notrack_chain pkt_noentry = Accept.
Proof. vm_compute. reflexivity. Qed.

(* The kernel-guaranteed property — `notrack; ct state untracked accept` accepts
   every NO-ENTRY packet (ct == NULL at notrack time) — is PROVABLE in the model. *)
Theorem notrack_forces_untracked_accept :
  forall p : packet, pkt_ct_present p = false ->
    eval_chain_mut notrack_chain p = Accept.
Proof.
  intros p Hp.
  assert (Hu : pkt_untracked (set_untracked p) = true)
    by (unfold set_untracked; rewrite Hp; reflexivity).
  (* rule 2 sees the threaded packet [dsl_step notrack_only p], which (the body is just
     the notrack) is exactly [set_untracked p]; its `ct state untracked` match reads the
     UNTRACKED latch and applies. *)
  assert (Hstep : dsl_step notrack_only p = set_untracked p) by reflexivity.
  assert (Ha : rule_applies ctstate_rule (set_untracked p) = true).
  { unfold rule_applies. cbn [ctstate_rule r_body rule_applies_walk].
    unfold eval_matchcond, m_untracked. cbn [match_loadable].
    unfold field_loadable, field_load. cbn [load_ok].
    unfold eval_matchcond_body. cbn [field_value field_load do_load].
    rewrite Hu. reflexivity. }
  assert (Hout : outcome ctstate_rule (set_untracked p) = Some Accept) by reflexivity.
  unfold eval_chain_mut, notrack_chain. cbn [c_rules c_policy].
  unfold eval_rules_mut.
  replace (rule_loadable notrack_only p) with true by reflexivity.
  replace (rule_applies notrack_only p) with true by reflexivity.
  replace (outcome notrack_only p) with (@None verdict) by reflexivity.
  rewrite Hstep.
  replace (rule_loadable ctstate_rule (set_untracked p)) with true by reflexivity.
  rewrite Ha, Hout. reflexivity.
Qed.

(* KERNEL GUARD (the notrack-no-op refinement): on a packet that ALREADY has a
   conntrack ENTRY ([pkt_ct_present := true], here ESTABLISHED=2), `notrack` is a
   NO-OP.  The cross-rule `ct state untracked` match in rule 2 reads the entry's
   REAL state, does NOT match, and the chain falls through to its Drop policy —
   exactly nft_notrack_eval's `if (ct || ctinfo == IP_CT_UNTRACKED) return;`. *)
Definition pkt_estab_entry : packet :=
  {| pkt_env := {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
       e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
       e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
       e_connlimit := fun _ => [];
       e_ct := fun _ k => match k with CKstate => [0;0;0;2] | _ => [] end;
       e_nat := fun _ => None; e_numgen := fun _ => 0 |};
     pkt_meta := fun _ => [];
     pkt_ct := fun _ => [];
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := false; pkt_fragoff := 0;
     pkt_flow := []; pkt_untracked := false; pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* notrack does NOT latch untracked on the entry-present packet: the threaded
   `ct state` read returns the live ESTABLISHED value [0;0;0;2], not the UNTRACKED
   constant. *)
Lemma notrack_noop_on_entry :
  do_load (LCt CKstate) (dsl_writes notrack_only pkt_estab_entry) = [0;0;0;2].
Proof. vm_compute. reflexivity. Qed.

Theorem model_drops_entry_present_like_kernel :
  eval_chain_mut notrack_chain pkt_estab_entry = Drop.
Proof. vm_compute. reflexivity. Qed.
