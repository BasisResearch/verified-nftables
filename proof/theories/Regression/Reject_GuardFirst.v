(** Corpus class Q: the reject-dependency guard lands at the RULE HEAD.

    nft's evaluator synthesises a `meta l4proto tcp` guard for `reject with
    tcp reset` (the kernel's nft_reject_eval sends the RST regardless of the
    packet's L4 protocol, net/netfilter/nft_reject.c) and — UNLIKE every other
    synthesised dependency, which sits next to the expression that needs it —
    list_add's it at the BEGINNING of the rule's statement list
    (src/evaluate.c stmt_reject_gen_dependency: "Unlike payload deps this adds
    the dependency at the beginning, i.e. log ... reject with tcp-reset turns
    into meta l4proto tcp log ... reject with tcp-reset.  Otherwise we'd log
    things that won't be rejected").

    Placement is NOT packet-neutral for a stateful body: with the guard LAST,
    a non-TCP packet runs every counter/log/mark-write in the body and only
    then BREAKs on the guard; with the guard FIRST it breaks immediately and
    the body effects never happen.  The kernel evaluates the emitted rule in
    instruction order (nft_do_chain), so the two emissions are OBSERVABLY
    different — the historical audit classification of class Q as "pure
    placement, packet-equal" was wrong, and the frontend now emits the guard
    at the rule head ([Lower.ensure_dep_head] / [Lower.rl_push_head]).

    Pins, DSL and VM:
    - [counter_guard_first]: the lowered `counter reject with tcp reset` body
      is guard-BEFORE-counter.  ([SCounter]/[ICounter] are verdict-neutral and
      carry no model state — the model has no per-rule hit count to observe —
      so the counter placement is pinned structurally, and the OBSERVABLE
      effect twin below uses the mark write, the model's stateful body item.
      The limiter bucket cannot serve as the witness either: its depletion is
      threaded by an unconditional whole-body sweep, the known infidelity
      pinned in Known_Infidelities.v [gate_limit_drained].)
    - [udp_guard_breaks_before_mark_write] / [vm_udp_*]: a NON-TCP packet
      leaves a `mark set 1 reject with tcp reset` rule with its mark
      UNTOUCHED (the guard breaks first) and no verdict.
    - [tcp_mark_written_and_rejected] / [vm_tcp_*]: a TCP packet takes the
      write and the Reject.
    - [guard_last_leaks_the_write]: the counterfactual — the PRE-FIX emission
      (guard last) writes the mark on the very same non-TCP packet, proving
      the two placements semantically differ (this is the regression trip
      wire: reverting the lowering to adjacent placement re-lowers
      [rule_mark] to [rule_mark_guard_last]'s body, whose behaviour
      [udp_guard_breaks_before_mark_write] forbids). *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics Compile
  Ast Lower.
Import ListNotations.
Local Open Scope string_scope.

Definition oracle0 : string -> option nat := fun _ => None.
Definition fs_init : fstate := mkFstate ls0 nil nil.
Definition dummy_rule : rule :=
  {| r_body := nil; r_outcome := ONone; r_after := nil |}.

Definition lower1 (cls : srule) : rule :=
  match lower_rule oracle0 20 "ip" [] cls fs_init with
  | LOk (r, _) => r
  | LErr _ => dummy_rule
  end.

(* ---------- structural pin: `counter reject with tcp reset` ---------- *)

Definition rule_counter : rule :=
  lower1 [CStmt (StCounter 0 0); CVerdict (SVreject "tcp reset")].

(** The synthesised guard PRECEDES the counter in the lowered body (nft's
    emission; a non-TCP packet breaks on the guard and never hits the
    counter). *)
Example counter_guard_first :
  rule_counter =
  {| r_body := [BMatch (MEq FMetaL4proto [6]); BStmt (SCounter 0 0)];
     r_outcome := OVerdict (Reject 1 0); r_after := nil |}.
Proof. vm_compute. reflexivity. Qed.

(* ---------- observable-effect pin: `mark set 1 reject with tcp reset` ---------- *)

Definition rule_mark : rule :=
  lower1 [CStmt (StMetaSet "mark" (SVNum 1)); CVerdict (SVreject "tcp reset")].

Example mark_guard_first :
  rule_mark =
  {| r_body := [BMatch (MEq FMetaL4proto [6]);
                BStmt (SMetaSet MKmark (VImm [1; 0; 0; 0]))];
     r_outcome := OVerdict (Reject 1 0); r_after := nil |}.
Proof. vm_compute. reflexivity. Qed.

Definition env0 : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => [];
     e_limit := fun _ => 0;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => []; e_nat := fun _ => None;
     e_numgen := fun _ => 0 |}.

(* A packet whose only populated oracle is the L4 protocol. *)
Definition mkpkt (l4 : data) : packet :=
  {| pkt_meta := fun k => match k with MKl4proto => l4 | _ => [] end;
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := []; pkt_th := []; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => [];
     pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := true;
     pkt_fragoff := 0;
     pkt_flow := [1; 1]; pkt_untracked := false; pkt_ctdir_orig := true;
     pkt_ct_present := true |}.

Definition p_udp : packet := mkpkt [17].
Definition p_tcp : packet := mkpkt [6].

(** DSL: the non-TCP packet BREAKs on the head guard — no verdict, and the
    body's mark write never ran. *)
Example udp_guard_breaks_before_mark_write :
  (let '(v, (_, p')) := dsl_rule_step rule_mark env0 p_udp in
   (v, pkt_meta p' MKmark))
  = (None, []).
Proof. vm_compute. reflexivity. Qed.

(** DSL: the TCP packet passes the guard, takes the write AND the Reject. *)
Example tcp_mark_written_and_rejected :
  (let '(v, (_, p')) := dsl_rule_step rule_mark env0 p_tcp in
   (v, pkt_meta p' MKmark))
  = (Some (Reject 1 0), [1; 0; 0; 0]).
Proof. vm_compute. reflexivity. Qed.

(* ---------- VM twins over the COMPILED rule ---------- *)

Definition prog_mark : rule_prog := Compile.compile_rule rule_mark.

Example vm_udp_guard_breaks_before_mark_write :
  (let '(v, (_, p')) := vm_rule_step prog_mark env0 p_udp in
   (v, pkt_meta p' MKmark))
  = (None, []).
Proof. vm_compute. reflexivity. Qed.

Example vm_tcp_mark_written_and_rejected :
  (let '(v, (_, p')) := vm_rule_step prog_mark env0 p_tcp in
   (v, pkt_meta p' MKmark))
  = (Some (Reject 1 0), [1; 0; 0; 0]).
Proof. vm_compute. reflexivity. Qed.

(* ---------- the counterfactual: guard-LAST is observably different ---------- *)

(** The pre-fix emission order (mark write first, guard adjacent to the
    reject).  On the SAME non-TCP packet the write happens before the guard
    breaks — so "pure placement, packet-equal" was false for stateful bodies,
    and this pin plus [udp_guard_breaks_before_mark_write] locks the head
    placement in. *)
Definition rule_mark_guard_last : rule :=
  {| r_body := [BStmt (SMetaSet MKmark (VImm [1; 0; 0; 0]));
                BMatch (MEq FMetaL4proto [6])];
     r_outcome := OVerdict (Reject 1 0); r_after := nil |}.

Example guard_last_leaks_the_write :
  (let '(v, (_, p')) := dsl_rule_step rule_mark_guard_last env0 p_udp in
   (v, pkt_meta p' MKmark))
  = (None, [1; 0; 0; 0]).
Proof. vm_compute. reflexivity. Qed.
