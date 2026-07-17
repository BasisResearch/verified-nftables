(** * Intra-rule set-then-read — POSITIVE pins of the single-fold semantics.

    The kernel runs a rule's expressions ONCE, left to right, against the
    RUNNING state (nf_tables_core.c nft_rule_dp_for_each_expr): a `meta mark
    set 0x1` is visible to a `meta mark 0x1` comparison LATER IN THE SAME
    RULE, and a `add @s { key }` is visible to an `@s` lookup later in the
    same rule.  The single-fold semantics ([rule_step] / [run_rule_step])
    models exactly that walk, so both idioms now ACCEPT — on the DSL and on
    the compiled VM.

    These pins are the POSITIVE successors of the retired known-infidelity
    entry "intra-rule set-then-read" (the historical two-fold verdict/write
    split evaluated every match against the packet the rule ENTERED with, so
    the one-rule form dropped; the two-fold split is deleted, and with it the
    infidelity).  A future change that reintroduces an entry-packet verdict
    pass flips these theorems and must be caught here. *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Packet Verdict Bytecode Syntax Semantics Compile.
Import ListNotations.
Local Open Scope string_scope.

Definition base_meta : meta_key -> data := fun _ => [].

Definition mkpkt (meta : meta_key -> data) (flow : data) : packet :=
  {| pkt_meta := meta;
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := true;
     pkt_fragoff := 0; pkt_flow := flow; pkt_untracked := false;
     pkt_ctdir_orig := true; pkt_ct_present := true |}.

Definition env0 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => []; e_nat := fun _ => None;
     e_numgen := fun _ => 0 |}.

(* ------------------------------------------------------------------------ *)
(** ** (a) `meta mark set 0x1 meta mark 0x1 accept` — ONE rule, kernel ACCEPTS.

    nft_meta_set_eval writes skb->mark; the following nft_meta_get_eval /
    nft_cmp_eval of the SAME rule reads the updated mark. *)

Definition setread_rule : rule :=
  {| r_body := [ BStmt (SMetaSet MKmark (VImm [0;0;0;1]))
               ; BMatch (MEq FMetaMark [0;0;0;1]) ];
     r_outcome := OVerdict Accept; r_after := [] |}.
Definition setread_chain : chain := {| c_policy := Drop; c_rules := [setread_rule] |}.

Definition pkt_mark0 : packet := mkpkt base_meta [3;3].

(* The fold's walk sees the intra-rule write: the match reads the mark the
   preceding set statement just wrote. *)
Theorem setread_accepted : eval_chain_mut setread_chain env0 pkt_mark0 = Accept.
Proof. vm_compute. reflexivity. Qed.

(* The compiled VM agrees (both sides are kernel-faithful). *)
Theorem vm_setread_accepted :
  run_chain_mut (compile_chain setread_chain) Drop env0 pkt_mark0 = Accept.
Proof. vm_compute. reflexivity. Qed.

(* Non-vacuity: a rule whose comparison wants a DIFFERENT mark still drops —
   the walk reads the written value, not "anything". *)
Definition setread_wrong_rule : rule :=
  {| r_body := [ BStmt (SMetaSet MKmark (VImm [0;0;0;2]))
               ; BMatch (MEq FMetaMark [0;0;0;1]) ];
     r_outcome := OVerdict Accept; r_after := [] |}.
Definition setread_wrong_chain : chain :=
  {| c_policy := Drop; c_rules := [setread_wrong_rule] |}.

Theorem setread_wrong_dropped :
  eval_chain_mut setread_wrong_chain env0 pkt_mark0 = Drop.
Proof. vm_compute. reflexivity. Qed.
Theorem vm_setread_wrong_dropped :
  run_chain_mut (compile_chain setread_wrong_chain) Drop env0 pkt_mark0 = Drop.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(** ** (b) intra-rule DYNSET feedback: `add @learn { meta mark } @learn lookup`
    in ONE rule — the dynset's env write is visible to the lookup later in the
    same rule (nft_dynset_eval inserts into the set the subsequent
    nft_lookup_eval reads). *)

Definition pkt_mark9 : packet :=
  mkpkt (fun k => if meta_eqb k MKmark then [0;0;0;9] else []) [4;4].

Definition dynset_feedback_rule : rule :=
  {| r_body := [ BStmt (SDynset SOadd "learn" [FMetaMark] [])
               ; BMatch (MConcatSet [FMetaMark] false "learn") ];
     r_outcome := OVerdict Accept; r_after := [] |}.
Definition dynset_feedback_chain : chain :=
  {| c_policy := Drop; c_rules := [dynset_feedback_rule] |}.

Theorem dynset_feedback_accepted :
  eval_chain_mut dynset_feedback_chain env0 pkt_mark9 = Accept.
Proof. vm_compute. reflexivity. Qed.

Theorem vm_dynset_feedback_accepted :
  run_chain_mut (compile_chain dynset_feedback_chain) Drop env0 pkt_mark9 = Accept.
Proof. vm_compute. reflexivity. Qed.

(* Non-vacuity: WITHOUT the dynset add, the same lookup misses and the chain
   falls to its Drop policy — the accept above is the feedback loop, not a
   trivially-true lookup. *)
Definition lookup_only_rule : rule :=
  {| r_body := [ BMatch (MConcatSet [FMetaMark] false "learn") ];
     r_outcome := OVerdict Accept; r_after := [] |}.
Definition lookup_only_chain : chain :=
  {| c_policy := Drop; c_rules := [lookup_only_rule] |}.

Theorem lookup_only_dropped :
  eval_chain_mut lookup_only_chain env0 pkt_mark9 = Drop.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(** ** (c) statements after a failing match do NOT run — the walk stops at the
    break, KEEPING the writes made before it (kernel: NFT_BREAK ends the rule;
    earlier expressions already ran). *)

Definition break_keeps_rule : rule :=
  {| r_body := [ BStmt (SMetaSet MKmark (VImm [0;0;0;7]))   (* runs *)
               ; BMatch (MEq FMetaNfproto [9])              (* fails *)
               ; BStmt (SMetaSet MKmark (VImm [0;0;0;8])) ];(* never runs *)
     r_outcome := OVerdict Accept; r_after := [] |}.

Theorem break_keeps_earlier_write :
  pkt_meta (snd (snd (dsl_rule_step break_keeps_rule env0 pkt_mark0))) MKmark
  = [0;0;0;7].
Proof. vm_compute. reflexivity. Qed.

Theorem break_yields_no_verdict :
  fst (dsl_rule_step break_keeps_rule env0 pkt_mark0) = None.
Proof. vm_compute. reflexivity. Qed.

(* The VM step agrees on both components. *)
Theorem vm_break_agrees :
  vm_rule_step (compile_rule break_keeps_rule) env0 pkt_mark0
  = dsl_rule_step break_keeps_rule env0 pkt_mark0.
Proof. vm_compute. reflexivity. Qed.
