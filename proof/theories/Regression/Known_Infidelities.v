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

    No open entries remain: every historical divergence below is REPAIRED and
    pinned POSITIVELY (kernel value), so a regression that re-introduces one
    flips a pin and fails the build.

    Entry (2) — the OVmapNat vmap-HIT and the trailing NAT: the NAT
    data-plane effect is evaluated INSIDE the single per-rule fold at the
    terminal the walk actually reached, so a vmap HIT stops the rule before
    the NAT (verdict provenance is the fold's structure); pinned by the
    [vmaphit_*] / [vm_vmaphit_*] theorems below.
    Entry (1) — the limiter position: the `limit`/`quota`/`connlimit`
    consumption is evaluated AT the limiter's own body/instruction position
    inside the break-aware fold, so a limiter after a failing match consumes
    nothing, exactly the kernel NFT_BREAK order; pinned by the [gate_*]
    theorems below.
    Entry (3) — intra-rule set-then-read: the single-fold rule semantics runs
    every expression against the running state, so
    `meta mark set 0x1 meta mark 0x1 accept` ACCEPTS on both sides; pinned in
    Regression/Setread_IntraRule.v.) *)

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
(** ** (1) REPAIRED — a limiter after a failing match consumes NOTHING.

    Kernel: a rule's expressions run left-to-right and a failing match sets
    NFT_BREAK, ending the rule (nf_tables_core.c nft_do_chain: the per-expr
    `regs.verdict.code != NFT_CONTINUE` break) — so in
    `meta mark 0x1 limit rate 1/second accept` a packet whose mark is NOT 0x1
    never reaches nft_limit_eval and consumes NO token.

    Model (repaired): the consumption is applied AT the limiter's body /
    instruction position inside the break-aware folds ([body_step]'s
    [match_consume] / [run_rule_step]'s [ILimit]), so the failing mark match
    BREAKs the rule before the limiter is ever evaluated and the bucket keeps
    its token — on BOTH the DSL and the VM side.  (The historical unconditional
    whole-body sweep drained it to 0; these pins FLIPPED from "= 0" when the
    consumption moved in-fold.)  The reached-limiter consumption itself —
    pass AND exhausted-branch token store — is pinned in
    Regression/Limit_SharedBucket.v. *)

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

Definition gate_res : verdict * env := eval_chain_flat_env Hprerouting gate_chain env_lim pkt_nomatch.

(* The verdict is the policy (rule does not apply) — same as the kernel. *)
Lemma gate_verdict_policy : fst gate_res = Drop.
Proof. vm_compute. reflexivity. Qed.

(* THE REPAIR: the bucket is NOT drained — the unreached limiter kept its
   token, exactly as the kernel leaves it. *)
Theorem gate_limit_undrained : e_limit (snd gate_res) lim1 = 1.
Proof. vm_compute. reflexivity. Qed.

(* The compiled VM agrees with the DSL (and with the kernel). *)
Definition vm_gate_res : verdict * env :=
  run_chain_flat_env Hprerouting (compile_chain gate_chain) Drop env_lim pkt_nomatch.

Theorem vm_gate_limit_undrained : e_limit (snd vm_gate_res) lim1 = 1.
Proof. vm_compute. reflexivity. Qed.

(* The positional counterpart — the SAME limiter placed BEFORE the failing
   match IS evaluated and consumes its token (the write surviving the later
   break) — is pinned in Regression/Limit_SharedBucket.v
   ([limit_before_failing_match_consumed] / [vm_limit_before_failing_match_consumed]). *)

(* ------------------------------------------------------------------------ *)
(** ** (2) REPAIRED — a vmap HIT on an [OVmapNat] rule does NOT run the
    trailing NAT.

    Kernel: `tcp dport vmap { ... } dnat to ...` runs its expressions in order;
    a vmap HIT writes a non-CONTINUE verdict register and the rule's remaining
    expressions — the trailing nft_nat — never evaluate (nf_tables_core.c
    nft_do_chain per-expr verdict break).

    Model: the NAT effect is applied INSIDE the per-rule fold
    ([terminal_step] / the VM's [INat] case), which is only reached when the
    vmap MISSES — the fold's structure IS the verdict provenance.  So a vmap
    HIT neither rewrites the packet nor stores a flow-keyed [e_nat] mapping,
    on BOTH sides (DSL fold and compiled bytecode). *)

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
  rule_step Hprerouting vmaphit_rule env_vmap pkt_hit.

(* The verdict IS the vmap-hit verdict (kernel and model agree on it). *)
Lemma vmaphit_verdict : fst vmaphit_res = Some Accept.
Proof. vm_compute. reflexivity. Qed.

(* POSITIVE (kernel value): on the vmap HIT the destination is NOT rewritten —
   it stays [1;2;3;4]; the trailing dnat never evaluated. *)
Theorem vmaphit_daddr_rewritten :
  field_value FIp4Daddr env_vmap (snd (snd vmaphit_res)) = [1;2;3;4].
Proof. vm_compute. reflexivity. Qed.

(* POSITIVE (kernel value): NO flow-keyed NAT mapping is stored on a vmap HIT —
   the kernel's nf_nat_setup_info never ran, and neither does the model's
   [apply_nat]/[store_nat_mapping]: e_nat stays None.
   = None *)
Theorem vmaphit_stores_nat_mapping :
  e_nat (fst (snd vmaphit_res)) [7;7] = None.
Proof. vm_compute. reflexivity. Qed.

(* The MISS side (provenance non-vacuity): a packet whose mark misses the vmap
   falls through to the NAT terminal, which rewrites AND stores the mapping —
   the effect is in the fold, not deleted. *)
Definition pkt_miss : packet :=
  mkpkt (fun k => if meta_eqb k MKmark then [0;0;0;2] else [])
        ip4_hdr [0;0;0;0;0;0;0;0] [7;7].
Definition vmapmiss_res : option verdict * (env * packet) :=
  rule_step Hprerouting vmaphit_rule env_vmap pkt_miss.
Theorem vmapmiss_daddr_rewritten :
  field_value FIp4Daddr env_vmap (snd (snd vmapmiss_res)) = [10;0;0;1].
Proof. vm_compute. reflexivity. Qed.
Theorem vmapmiss_stores_nat_mapping :
  e_nat (fst (snd vmapmiss_res)) [7;7]
  = Some (Some [1;2;3;4], Some [10;0;0;1], None, None).
Proof. vm_compute. reflexivity. Qed.

(* VM twins: the COMPILED rule behaves identically — the IVmap hit returns
   before the INat instruction; the miss reaches INat, which performs the
   data-plane effect from the register file. *)
Definition vm_vmaphit_res : option verdict * (env * packet) :=
  run_rule_step Hprerouting empty_rf (compile_rule vmaphit_rule) env_vmap pkt_hit.
Theorem vm_vmaphit_verdict : fst vm_vmaphit_res = Some Accept.
Proof. vm_compute. reflexivity. Qed.
Theorem vm_vmaphit_daddr_preserved :
  field_value FIp4Daddr env_vmap (snd (snd vm_vmaphit_res)) = [1;2;3;4].
Proof. vm_compute. reflexivity. Qed.
Theorem vm_vmaphit_no_mapping :
  e_nat (fst (snd vm_vmaphit_res)) [7;7] = None.
Proof. vm_compute. reflexivity. Qed.
Definition vm_vmapmiss_res : option verdict * (env * packet) :=
  run_rule_step Hprerouting empty_rf (compile_rule vmaphit_rule) env_vmap pkt_miss.
Theorem vm_vmapmiss_daddr_rewritten :
  field_value FIp4Daddr env_vmap (snd (snd vm_vmapmiss_res)) = [10;0;0;1].
Proof. vm_compute. reflexivity. Qed.
Theorem vm_vmapmiss_stores_mapping :
  e_nat (fst (snd vm_vmapmiss_res)) [7;7]
  = Some (Some [1;2;3;4], Some [10;0;0;1], None, None).
Proof. vm_compute. reflexivity. Qed.
