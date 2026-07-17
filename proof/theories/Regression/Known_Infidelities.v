(** * KNOWN-INFIDELITY pins: the model's CONFIRMED divergences from the kernel.

    Every other file in Regression/ pins kernel-FAITHFUL behaviour.  This file is
    the opposite: each theorem below locks in a behaviour of the MODEL that is
    known to DIVERGE from linux-6.18.33, so that a future fidelity fix must
    consciously FLIP the pin (it becomes unprovable) and update the ledger —
    the divergence can neither be forgotten nor silently half-fixed.

    The authoritative ledger — kernel citation, code location, repro, why each
    is open rather than fixed — is proof/DEVELOPMENT.md § "Known model
    infidelities (open, confirmed)".  Repairing any of them is a SEMANTICS
    change and belongs to the adversarial-semantics-audit track
    (../adversarial.md), not to a documentation milestone; until then this file
    keeps the divergent behaviour checked instead of merely described.

    Two entries:
      (1) whole-body limiter sweep     — [gate_*] theorems below;
      (2) OVmapNat vmap-HIT trace NAT  — [vmaphit_*] theorems below.

    (The historical third entry — intra-rule set-then-read — is REPAIRED: the
    single-fold rule semantics runs every expression against the running
    state, so `meta mark set 0x1 meta mark 0x1 accept` now ACCEPTS on both
    sides.  Its positive successors live in Regression/Setread_IntraRule.v.) *)

From Stdlib Require Import List String NArith.
From Nft Require Import Bytes Packet Verdict Bytecode Syntax Semantics Compile.
Import ListNotations.
Local Open Scope string_scope.

(* A packet template: every oracle empty unless overridden. *)
Definition base_meta : meta_key -> data := fun _ => [].

Definition mkpkt (meta : meta_key -> data) (nh th flow : data) : packet :=
  {| pkt_meta := meta;
     pkt_sock := fun _ => []; pkt_eh := fun _ _ _ _ _ => [];
     pkt_lh := []; pkt_nh := nh; pkt_th := th; pkt_ih := [];
     pkt_tnl := []; pkt_fibkey := fun _ => []; pkt_numgen := fun _ => [];
     pkt_osf := []; pkt_tunnel := fun _ => []; pkt_symhash := fun _ _ => [];
     pkt_xfrm := fun _ _ _ => []; pkt_ctdir := fun _ _ => [];
     pkt_inner := fun _ _ _ _ => []; pkt_have_l2 := true; pkt_have_l4 := true;
     pkt_fragoff := 0; pkt_flow := flow; pkt_untracked := false;
     pkt_ctdir_orig := true; pkt_ct_present := true |}.

(* ------------------------------------------------------------------------ *)
(** ** (1) KNOWN INFIDELITY — the limiter sweep depletes buckets the kernel
    never evaluates.

    Kernel: a rule's expressions run left-to-right and a failing match sets
    NFT_BREAK, ending the rule (nf_tables_core.c nft_do_chain: the per-expr
    `regs.verdict.code != NFT_CONTINUE` break) — so in
    `meta mark 0x1 limit rate 1/second accept` a packet whose mark is NOT 0x1
    never reaches nft_limit_eval and consumes NO token.

    Model: [dsl_step] applies [limit_sweep_body] over the WHOLE rule body
    unconditionally (Semantics.v), and [vm_rule_step] mirrors it with
    [limit_sweep_prog] — so the bucket is drained even though the first match
    failed.  Both sides agree (the compiler theorems are honest); both diverge
    from the kernel.

    PINNED (model behaviour; a fidelity fix MUST flip [gate_limit_drained] /
    [vm_gate_limit_drained] to "= 1" and update the ledger): the failing-match
    rule still drains [e_limit] from 1 to 0 on BOTH the DSL and the VM side. *)

Definition lim1 : limit_spec :=
  {| ls_rate := 1; ls_unit := 0; ls_burst := 1; ls_bytes := false; ls_flags := 0 |}.

Definition env_lim : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => [];
     e_limit := fun _ => 1;                 (* exactly one token *)
     e_quota := fun _ => 0; e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => []; e_nat := fun _ => None;
     e_numgen := fun _ => 0 |}.

(* `meta mark 0x1 limit rate 1/second burst 1 accept` — the limiter sits AFTER
   the mark match. *)
Definition gate_rule : rule :=
  {| r_body := [ BMatch (MEq FMetaMark [0;0;0;1]) ; BMatch (MLimit lim1) ];
     r_outcome := OVerdict Accept; r_after := [] |}.
Definition gate_chain : chain := {| c_policy := Drop; c_rules := [gate_rule] |}.

(* A packet whose mark is NOT 0x1 (all-empty meta oracle). *)
Definition pkt_nomatch : packet := mkpkt base_meta [] [] [1;1].

(* The gating match FAILS — the kernel BREAKs here, before nft_limit_eval. *)
Lemma gate_match_fails :
  eval_matchcond (MEq FMetaMark [0;0;0;1]) env_lim pkt_nomatch = false.
Proof. vm_compute. reflexivity. Qed.

Definition gate_res : verdict * env := eval_chain_mut_env gate_chain env_lim pkt_nomatch.

(* The verdict is the policy (rule does not apply) — same as the kernel. *)
Lemma gate_verdict_policy : fst gate_res = Drop.
Proof. vm_compute. reflexivity. Qed.

(* THE DIVERGENCE: the model drains the bucket anyway (kernel leaves 1). *)
Theorem gate_limit_drained : e_limit (snd gate_res) lim1 = 0.
Proof. vm_compute. reflexivity. Qed.

(* The compiled VM agrees with the DSL (and hence also diverges from the kernel). *)
Definition vm_gate_res : verdict * env :=
  run_chain_mut_env (compile_chain gate_chain) Drop env_lim pkt_nomatch.

Theorem vm_gate_limit_drained : e_limit (snd vm_gate_res) lim1 = 0.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(** ** (2) KNOWN INFIDELITY — a vmap HIT on an [OVmapNat] rule still runs the
    trailing NAT in the trace evaluator.

    Kernel: `tcp dport vmap { ... } dnat to ...` runs its expressions in order;
    a vmap HIT writes a non-CONTINUE verdict register and the rule's remaining
    expressions — the trailing nft_nat — never evaluate (nf_tables_core.c
    nft_do_chain per-expr verdict break).  The repo's own verdict/loadability
    semantics agree ([Semantics.end_loadable]: "vmap HIT: terminal/r_after
    unreachable"; [run_rule]'s [IVmap] hit returns before the [INat]).

    Model ([eval_rules_trace], Semantics.v): on ANY terminal verdict of a rule
    it dispatches [nat_drops]/[apply_nat] on [r_nat r] — and [r_nat] projects
    the NAT out of [OVmapNat] whether the verdict came from the vmap HIT or the
    NAT terminal.  So a vmap HIT on an [OVmapNat] rule still (a) rewrites the
    packet and (b) STORES a flow-keyed [e_nat] mapping ([store_nat_mapping]) —
    a flow-visible side effect the kernel does not perform (later same-flow
    packets are translated by the stored tuple).

    PINNED (model behaviour; a fidelity fix MUST flip [vmaphit_daddr_rewritten]
    to "= [1;2;3;4]" and [vmaphit_stores_nat_mapping] to "= None", and update
    the ledger). *)

Definition vmnat_spec : nat_spec :=
  {| nat_addr_imm := Some [10;0;0;1]; nat_field := None; nat_map := None; nat_src := None;
     nat_kind := NKdnat; nat_family := NFip4;
     nat_extra := NXnone; nat_flags := 0 |}.

Definition vm_hit : vmap_spec :=
  {| vm_fields := [FMetaMark]; vm_keyf := None; vm_name := "vmnat" |}.

(* `meta mark vmap { 0x1 : accept } dnat to 10.0.0.1` *)
Definition vmaphit_rule : rule :=
  {| r_body := []; r_outcome := OVmapNat vm_hit vmnat_spec; r_after := [] |}.
Definition vmaphit_chain : chain := {| c_policy := Drop; c_rules := [vmaphit_rule] |}.

Definition env_vmap : env :=
  {| e_set := fun _ => [];
     e_vmap := fun n => if String.eqb n "vmnat"
                        then [([0;0;0;1], [0;0;0;1], Accept)] else [];
     e_map := fun _ => []; e_routes := []; e_rt := fun _ => [];
     e_limit := fun _ => 0; e_quota := fun _ => 0;
     e_ifaddrs := fun _ => []; e_ifaddrs6 := fun _ => [];
     e_connlimit := fun _ => []; e_ct := fun _ _ => []; e_nat := fun _ => None;
     e_numgen := fun _ => 0 |}.

(* A 20-byte IPv4 header, destination 1.2.3.4; the packet's mark HITS the vmap. *)
Definition ip4_hdr : data :=
  [ 69; 0; 0; 20 ; 0; 0; 0; 0 ; 64; 6 ; 0; 0 ; 10; 0; 0; 2 ; 1; 2; 3; 4 ].
Definition pkt_hit : packet :=
  mkpkt (fun k => if meta_eqb k MKmark then [0;0;0;1] else [])
        ip4_hdr [0;0;0;0;0;0;0;0] [7;7].

Definition vmaphit_res : option verdict * (env * packet) :=
  eval_rules_trace Hprerouting (c_rules vmaphit_chain) env_vmap pkt_hit.

(* The verdict IS the vmap-hit verdict (kernel and model agree on it). *)
Lemma vmaphit_verdict : fst vmaphit_res = Some Accept.
Proof. vm_compute. reflexivity. Qed.

(* THE DIVERGENCE (data plane): the destination was rewritten to the dnat
   target even though the vmap HIT — the kernel leaves it at [1;2;3;4]. *)
Theorem vmaphit_daddr_rewritten :
  field_value FIp4Daddr env_vmap (snd (snd vmaphit_res)) = [10;0;0;1].
Proof. vm_compute. reflexivity. Qed.

(* THE DIVERGENCE (flow state): a NAT mapping was STORED for the flow — the
   kernel's nf_nat_setup_info never ran, so no conntrack NAT tuple exists. *)
Theorem vmaphit_stores_nat_mapping :
  e_nat (fst (snd vmaphit_res)) [7;7]
  = Some (Some [1;2;3;4], Some [10;0;0;1], None, None).
Proof. vm_compute. reflexivity. Qed.
