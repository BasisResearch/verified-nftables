(** * Cross-packet env carry UNDER hook dispatch and jumps — POSITIVE pins
      of the sequence semantics (the M4 witness battery).

    The kernel's state objects (dynamic sets, limiter token buckets, NAT
    mappings) live in the table, not in the packet: whatever a traversal
    writes there is what the NEXT packet's traversal reads, regardless of
    which base chain (priority) or user chain (jump) did the writing.  The
    model's sequence semantics is [seq_eval_env] over the unified per-packet
    hook run [eval_hook_env]: the between-packet env is DEFINITIONALLY the
    ruleset's own env-out — there is no external step function to instantiate
    with a wrong (or empty) model of the ruleset's learning.  Compiler
    theorem: [Correct.compile_seq_hook_correct].

    These pins Compute-verify the two flagship carries on the DSL AND on the
    compiled VM, each through CONTROL FLOW (a jump) and HOOK DISPATCH:

      - [seq_hook_limit_depletes]: a rate limiter inside a jumped-to chain
        gives IDENTICAL back-to-back packets DIFFERENT verdicts — packet 1
        consumes the bucket's only token (Accept), packet 2 finds it empty
        (policy Drop).  Depends on M2 (consumption inside the break-aware
        fold) and U1 (the write threads through the jump and back).

      - [seq_hook_dynset_learns]: a "block repeat offenders" pair of base
        chains at the SAME hook (priorities -100 / 0): the early base drops
        sources already in @seen, the late base learns the source in a
        jumped-to chain.  Packet 1 passes and is learned; the identical
        packet 2 is dropped by the EARLIER base — the learning crossed both
        a jump, a base-chain boundary, and a packet boundary.

    A regression that re-evaluates a later packet against the entry env —
    or reintroduces an external between-packet step — flips these theorems. *)

From Stdlib Require Import List String ZArith NArith.
From Nft Require Import Bytes Packet Verdict Bytecode Syntax Semantics Compile
  Correct.
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

(** A rule that only transfers control. *)
Definition jump_to (n : string) : rule :=
  {| r_body := []; r_outcome := OVerdict (Jump n); r_after := [] |}.

(* ------------------------------------------------------------------------ *)
(** ** (a) limiter depletion carries packet-to-packet, through a jump,
    under hook dispatch. *)

(* `limit rate 1/second burst 1` (packet-rate, no invert/over bit). *)
Definition lim1 : limit_spec :=
  {| ls_rate := 1; ls_unit := 0; ls_burst := 1; ls_bytes := false; ls_flags := 0 |}.

(* An env whose only limiter [lim1] starts with exactly 1 token. *)
Definition env_1token : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => []; e_limit := fun _ => 1;
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => []; e_nat := fun _ => None;
     e_numgen := fun _ => 0 |}.

Definition pkt0 : packet := mkpkt base_meta [1;1].

(* `limit rate 1/second burst 1 accept`, living in a USER chain the base
   jumps to; base policy DROP. *)
Definition lim_rule : rule :=
  {| r_body := [BMatch (MLimit lim1)];
     r_outcome := OVerdict Accept; r_after := [] |}.
Definition lim_cs : list (string * chain) :=
  [("ratelimit", {| c_policy := Accept; c_rules := [lim_rule] |})].
Definition lim_base : chain :=
  {| c_policy := Drop; c_rules := [jump_to "ratelimit"] |}.

Definition lim_rs (h : hook_id) : list hooked_chain :=
  [ {| hc_hook := h; hc_prio := 0%Z; hc_env := lim_cs; hc_base := lim_base |} ].

(** Two IDENTICAL packets, back to back: packet 1 takes the bucket's only
    token and is accepted; packet 2 — evaluated against the env packet 1
    LEFT, not the entry env — finds the bucket empty, the limit match fails
    inside the callee, the callee falls through, and the base's DROP policy
    applies.  Different verdicts for identical packets: the carry is real. *)
Theorem seq_hook_limit_depletes : forall h,
  seq_eval_env (eval_hook_env h 10 (lim_rs h)) env_1token [pkt0; pkt0]
  = [Accept; Drop].
Proof. intro h; destruct h; vm_compute; reflexivity. Qed.

(** VM twin: the compiled ruleset depletes the same bucket the same way. *)
Theorem vm_seq_hook_limit_depletes : forall h,
  seq_eval_env
    (run_ruleset_env h 10 (map compile_base (select_hook (lim_rs h) h)))
    env_1token [pkt0; pkt0]
  = [Accept; Drop].
Proof. intro h; destruct h; vm_compute; reflexivity. Qed.

(* The state pin behind the verdict flip: packet 1's hook run leaves the
   bucket empty (1 token consumed INSIDE the jumped-to chain). *)
Example limit_bucket_left_empty : forall h,
  e_limit (snd (eval_hook_env h 10 (lim_rs h) env_1token pkt0)) lim1 = 0.
Proof. intro h; destruct h; vm_compute; reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(** ** (b) dynset learning carries packet-to-packet ACROSS base chains at the
    same hook (multi-chain dispatch), the add itself under a jump. *)

Definition pkt9 : packet :=
  mkpkt (fun k => if meta_eqb k MKmark then [0;0;0;9] else []) [4;4].

(* Early base (priority -100): drop sources already seen; policy accept. *)
Definition seen_drop_rule : rule :=
  {| r_body := [ BMatch (MConcatSet [FMetaMark] false "seen") ];
     r_outcome := OVerdict Drop; r_after := [] |}.
Definition check_base : chain :=
  {| c_policy := Accept; c_rules := [seen_drop_rule] |}.

(* Late base (priority 0): jump to a chain that learns the source. *)
Definition learn_rule : rule :=
  {| r_body := [ BStmt (SDynset SOadd "seen" [FMetaMark] []) ];
     r_outcome := ONone; r_after := [] |}.
Definition learn_cs : list (string * chain) :=
  [("learn", {| c_policy := Accept; c_rules := [learn_rule] |})].
Definition learn_base : chain :=
  {| c_policy := Accept; c_rules := [jump_to "learn"] |}.

Definition learn_rs (h : hook_id) : list hooked_chain :=
  [ {| hc_hook := h; hc_prio := 0%Z;      hc_env := learn_cs; hc_base := learn_base |} ;
    {| hc_hook := h; hc_prio := (-100)%Z; hc_env := [];       hc_base := check_base |} ].

(** Packet 1: the check base has never seen the source (lookup misses,
    policy Accept continues to the next base), the learn base's callee adds
    it to @seen, the hook accepts.  The IDENTICAL packet 2 is dropped by the
    EARLIER base: the env written by packet 1 — in a jumped-to chain of the
    LATER base — is the env packet 2's first base reads. *)
Theorem seq_hook_dynset_learns : forall h,
  seq_eval_env (eval_hook_env h 10 (learn_rs h)) env0 [pkt9; pkt9]
  = [Accept; Drop].
Proof. intro h; destruct h; vm_compute; reflexivity. Qed.

(** VM twin. *)
Theorem vm_seq_hook_dynset_learns : forall h,
  seq_eval_env
    (run_ruleset_env h 10 (map compile_base (select_hook (learn_rs h) h)))
    env0 [pkt9; pkt9]
  = [Accept; Drop].
Proof. intro h; destruct h; vm_compute; reflexivity. Qed.

(* Non-vacuity: with the learning base REMOVED, the same two packets are both
   accepted — packet 2's drop above really is packet 1's learning. *)
Definition nolearn_rs (h : hook_id) : list hooked_chain :=
  [ {| hc_hook := h; hc_prio := (-100)%Z; hc_env := []; hc_base := check_base |} ].
Example no_learning_no_drop : forall h,
  seq_eval_env (eval_hook_env h 10 (nolearn_rs h)) env0 [pkt9; pkt9]
  = [Accept; Accept].
Proof. intro h; destruct h; vm_compute; reflexivity. Qed.
