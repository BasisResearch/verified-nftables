(** * Effectful rules UNDER CONTROL FLOW — POSITIVE pins of the unified
      semantics (the U1 witness battery).

    The kernel threads ONE live (skb, state) through the whole traversal,
    regardless of which chain frame a rule sits in: nft_do_chain's jumpstack
    pushes/pops chain positions, never state (net/netfilter/nf_tables_core.c).
    So

      - a `meta mark set 0x1 meta mark 0x1 accept` rule ACCEPTS even when it
        is reached through a `jump`;
      - a mark set in the CALLER is visible to a match in the CALLEE;
      - a mark set in the CALLEE persists after the return and is visible to
        the CALLER's next rule;
      - a dynset `add @s {…}` in the callee is visible to an `@s` lookup
        after the return (the env is as global as the skb).

    The unified evaluators ([Semantics.eval_rules h]/[run_rules h]) model
    exactly this; these pins Compute-verify all four behaviours on the DSL
    AND on the compiled VM ([Correct.compile_table_correct] equates them
    wholesale, but the pins run both sides independently).

    They are the control-flow successors of [Setread_IntraRule.v] (the flat
    T1 pins): a future change that evaluates a jumped-to chain against the
    entry state — or drops a callee's writes on return — flips these theorems
    and must be caught here.

    This config sits on the OTHER side of the write-free projection's license:
    its [rule_writefree] license check is [false] (a `meta mark set` is a state
    write), so the write-free coincidence theorem does not apply and the unified
    evaluator is the only certified path for this ruleset — exactly why an
    effect-dropping projection would compute a different verdict class here (the
    entry-state match would miss). *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Packet Verdict Bytecode Syntax Semantics Compile
  Correct.
Import ListNotations.
Local Open Scope string_scope.

(* Pins below hold at EVERY netfilter hook [h] (no rule here carries a NAT
   terminal, so the hook is inert); the section generalizes each statement. *)
Section AtHook.
Context (h : hook_id).

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

Definition pkt_mark0 : packet := mkpkt base_meta [3;3].

(** A rule that only transfers control. *)
Definition jump_to (n : string) : rule :=
  {| r_body := []; r_outcome := OVerdict (Jump n); r_after := [] |}.

(* ------------------------------------------------------------------------ *)
(** ** (a) intra-rule set-then-read INSIDE a jumped-to chain.

    The flat-strand fix (Setread_IntraRule) now holds under control flow: the
    same one-rule idiom accepts when the rule lives in a user chain reached by
    `jump`. *)

Definition setread_rule : rule :=
  {| r_body := [ BStmt (SMetaSet MKmark (VImm [0;0;0;1]))
               ; BMatch (MEq FMetaMark [0;0;0;1]) ];
     r_outcome := OVerdict Accept; r_after := [] |}.

Definition sr_chain : chain := {| c_policy := Accept; c_rules := [setread_rule] |}.
Definition sr_cs : list (string * chain) := [("sr", sr_chain)].
Definition sr_base : chain := {| c_policy := Drop; c_rules := [jump_to "sr"] |}.

Theorem setread_under_jump_accepted :
  fst (eval_table h 10 sr_cs sr_base env0 pkt_mark0) = Accept.
Proof. vm_compute. reflexivity. Qed.

Theorem vm_setread_under_jump_accepted :
  fst (run_table h 10 (compile_env sr_cs) (compile_chain sr_base)
                   (c_policy sr_base) env0 pkt_mark0) = Accept.
Proof. vm_compute. reflexivity. Qed.

(* Non-vacuity: wanting a DIFFERENT mark still falls through to the base
   policy Drop — the callee's match reads the written value, not "anything". *)
Definition setread_wrong_rule : rule :=
  {| r_body := [ BStmt (SMetaSet MKmark (VImm [0;0;0;2]))
               ; BMatch (MEq FMetaMark [0;0;0;1]) ];
     r_outcome := OVerdict Accept; r_after := [] |}.
Definition srw_cs : list (string * chain) :=
  [("sr", {| c_policy := Accept; c_rules := [setread_wrong_rule] |})].

Theorem setread_wrong_under_jump_dropped :
  fst (eval_table h 10 srw_cs sr_base env0 pkt_mark0) = Drop.
Proof. vm_compute. reflexivity. Qed.
Theorem vm_setread_wrong_under_jump_dropped :
  fst (run_table h 10 (compile_env srw_cs) (compile_chain sr_base)
                   (c_policy sr_base) env0 pkt_mark0) = Drop.
Proof. vm_compute. reflexivity. Qed.

(** …and the write-free hook-independence argument is licensed on NEITHER
    config: its check [rule_writefree] is [false] on the effectful rule, so
    [Nft_Tactics.eval_rules_hookindep_writefree] correctly does not apply — an
    effect-dropping evaluation would read the callee's match against the ENTRY
    packet (verdict class Drop-by-policy instead of Accept), and the unified
    evaluator above is the only certified path for this config. *)
Example setread_rule_not_writefree : rule_writefree setread_rule = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(** ** (b) the CALLER's write is visible in the CALLEE.

    Rule 1 of the base chain sets the mark (no verdict); rule 2 jumps; the
    callee's match reads the caller's write. *)

Definition mark_set_rule : rule :=
  {| r_body := [ BStmt (SMetaSet MKmark (VImm [0;0;0;1])) ];
     r_outcome := ONone; r_after := [] |}.
Definition mark_chk_rule : rule :=
  {| r_body := [ BMatch (MEq FMetaMark [0;0;0;1]) ];
     r_outcome := OVerdict Accept; r_after := [] |}.

Definition caller_cs : list (string * chain) :=
  [("chk", {| c_policy := Accept; c_rules := [mark_chk_rule] |})].
Definition caller_base : chain :=
  {| c_policy := Drop; c_rules := [mark_set_rule; jump_to "chk"] |}.

Theorem caller_write_visible_in_callee :
  fst (eval_table h 10 caller_cs caller_base env0 pkt_mark0) = Accept.
Proof. vm_compute. reflexivity. Qed.
Theorem vm_caller_write_visible_in_callee :
  fst (run_table h 10 (compile_env caller_cs) (compile_chain caller_base)
                   (c_policy caller_base) env0 pkt_mark0) = Accept.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(** ** (c) the CALLEE's write persists after the return.

    The base jumps to a chain that only sets the mark (falling through, i.e.
    an implicit return); the base's NEXT rule reads it. *)

Definition setter_cs : list (string * chain) :=
  [("setter", {| c_policy := Accept; c_rules := [mark_set_rule] |})].
Definition retback_base : chain :=
  {| c_policy := Drop; c_rules := [jump_to "setter"; mark_chk_rule] |}.

Theorem callee_write_survives_return :
  fst (eval_table h 10 setter_cs retback_base env0 pkt_mark0) = Accept.
Proof. vm_compute. reflexivity. Qed.
Theorem vm_callee_write_survives_return :
  fst (run_table h 10 (compile_env setter_cs) (compile_chain retback_base)
                   (c_policy retback_base) env0 pkt_mark0) = Accept.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(** ** (d) ENV writes carry across the transfer too: a dynset `add` in the
    callee is visible to a lookup after the return. *)

Definition pkt_mark9 : packet :=
  mkpkt (fun k => if meta_eqb k MKmark then [0;0;0;9] else []) [4;4].

Definition dynset_add_rule : rule :=
  {| r_body := [ BStmt (SDynset SOadd "learn" [FMetaMark] []) ];
     r_outcome := ONone; r_after := [] |}.
Definition lookup_rule : rule :=
  {| r_body := [ BMatch (MConcatSet [FMetaMark] false "learn") ];
     r_outcome := OVerdict Accept; r_after := [] |}.

Definition learn_cs : list (string * chain) :=
  [("learn", {| c_policy := Accept; c_rules := [dynset_add_rule] |})].
Definition learn_base : chain :=
  {| c_policy := Drop; c_rules := [jump_to "learn"; lookup_rule] |}.

Theorem dynset_learned_under_jump :
  fst (eval_table h 10 learn_cs learn_base env0 pkt_mark9) = Accept.
Proof. vm_compute. reflexivity. Qed.
Theorem vm_dynset_learned_under_jump :
  fst (run_table h 10 (compile_env learn_cs) (compile_chain learn_base)
                   (c_policy learn_base) env0 pkt_mark9) = Accept.
Proof. vm_compute. reflexivity. Qed.

(* Non-vacuity: without the jump (empty callee), the same lookup misses and
   the base falls to its Drop policy. *)
Definition nolearn_cs : list (string * chain) :=
  [("learn", {| c_policy := Accept; c_rules := [] |})].
Theorem dynset_not_learned_drops :
  fst (eval_table h 10 nolearn_cs learn_base env0 pkt_mark9) = Drop.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(** ** (e) the learned env also LEAVES the traversal: cross-packet carry
    composes with the jump (the env component of [eval_table h] records the
    callee's dynset add). *)
Theorem dynset_env_left_by_jump :
  e_set (fst (snd (eval_table h 10 learn_cs learn_base env0 pkt_mark9))) "learn"
  = [([0;0;0;9], [0;0;0;9])].
Proof. vm_compute. reflexivity. Qed.

End AtHook.
