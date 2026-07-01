(** Fires-witness for the fixed-width-META value->set consolidation.  Three adjacent
    `meta mark <v> drop` rules collapse into ONE `meta mark { v1, v2, v3 } drop`
    lookup over a synthesised anonymous typed (TYPE_MARK/u32) set — exactly what
    `nft --optimize` emits for battery_cases/19_meta_mark_set.nft (confirmed against
    host nft v1.1.6 in a netns: EXIT=0, kernel-committed, semantics preserved). *)
From Stdlib Require Import List String.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Optimize Optimize_Merge Optimize_Table Optimize_Normalize
  Optimize_Uncond.

Local Open Scope nat_scope.

Definition empty_decls' : set_decls := {| sd_sets := []; sd_vmaps := []; sd_maps := [] |}.

(* meta mark 0x00000001 / 0x00000002 / 0x00000003 — u32, HOST byte order (4 bytes). *)
Definition m1 : data := [0;0;0;1].
Definition m2 : data := [0;0;0;2].
Definition m3 : data := [0;0;0;3].

(* a bare terminal-Drop shell shared by the three rules *)
Definition drp : rule :=
  {| r_body := []; r_verdict := Drop; r_vmap := None; r_nat := None;
     r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.

Definition metaset_input : list rule :=
  [ mk_head (MCmp FMetaMark CEq m1) [] drp
  ; mk_head (MCmp FMetaMark CEq m2) [] drp
  ; mk_head (MCmp FMetaMark CEq m3) [] drp ].

(* The recogniser now treats [meta mark] (LMeta MKmark) as fixed-width. *)
Example metamark_fixed_width : field_fixed_len FMetaMark = Some 4.
Proof. reflexivity. Qed.

Definition metaset_output :=
  optimize_rules_setsN (List.length metaset_input) 0 empty_decls' metaset_input.

Compute (List.length metaset_input).   (* 3 input rules *)
Compute metaset_output.

(* The pass FIRES: 3 point-cmp rules -> 1 set-lookup rule + a fresh anonymous set
   holding the three point (v,v) elements, with n' = 1 (one fresh setname minted). *)
Example metaset_fires :
  let '(n', d', rs') := metaset_output in
  rs' = [ mk_head (MConcatSet [FMetaMark] false (setname 0)) [] drp ]
  /\ sd_sets d' = [ (setname 0, [(m1, m1); (m2, m2); (m3, m3)]) ]
  /\ n' = 1.
Proof. cbv. repeat split. Qed.

(* And it fires in the SHIPPED optimizer [optimize_table_uncond] (the extracted term):
   the three-mark chain optimises to ONE rule + the anonymous mark set. *)
Definition metaset_chain : chain :=
  {| c_policy := Accept; c_rules := metaset_input |}.

Definition metaset_table_output := optimize_table_uncond metaset_chain.

Compute (let '(_, d, c) := metaset_table_output in
         (List.length (c_rules c), sd_sets d)).

Example metaset_table_fires :
  let '(_, d', c') := metaset_table_output in
  List.length (c_rules c') = 1 /\
  exists nm, sd_sets d' = [ (nm, [(m1, m1); (m2, m2); (m3, m3)]) ].
Proof. cbv. split; [reflexivity | eexists; reflexivity]. Qed.
