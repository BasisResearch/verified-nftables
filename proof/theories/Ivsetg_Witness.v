(** Fires-witness for the GUARDED interval / range set consolidation
    ([Optimize_Ivsetg]).  Two `tcp dport <lo>-<hi> accept` rules — each lowered to a
    l4proto-guarded range [MCmp meta_l4proto 6 ; MRange th_dport lo hi] — collapse
    into ONE guarded interval-set lookup, exactly what `nft --optimize` emits
    (`tcp dport { 20-30, 31-40 } accept`, ANONYMOUS|CONSTANT|INTERVAL set; confirmed
    against host nft v1.1.6 in a netns).

    ALSO witnesses the REPRESENTABILITY GATE: OVERLAPPING ranges (`20-30, 25-40`)
    are DECLINED (left as two rules) — our single-field fold is never an overlapping
    set (the rbtree backend would reject it; that is the `nft --optimize` defect). *)
From Stdlib Require Import List String.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Optimize Optimize_Merge Optimize_Setg Optimize_Ivsetg Optimize_Table
  Optimize_Normalize Optimize_Uncond.

Local Open Scope nat_scope.

Definition empty_decls' : set_decls := {| sd_sets := []; sd_vmaps := []; sd_maps := [] |}.

(* the shared l4proto guard `meta l4proto tcp` (proto 6) *)
Definition gtcp : matchcond := MCmp FMetaL4proto CEq [6].

(* tcp dport 20-30  and  31-40  (2-byte big-endian) *)
Definition plo1 : data := [0;20].  Definition phi1 : data := [0;30].
Definition plo2 : data := [0;31].  Definition phi2 : data := [0;40].
(* an OVERLAPPING second range 25-40 *)
Definition polap : data := [0;25].

Definition acc : rule :=
  {| r_body := []; r_verdict := Accept; r_vmap := None; r_nat := None;
     r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.

Definition ivsetg_input : list rule :=
  [ orig_ruleGr FThDport gtcp plo1 phi1 [] acc
  ; orig_ruleGr FThDport gtcp plo2 phi2 [] acc ].

Definition ivsetg_output :=
  optimize_rules_ivsetg (List.length ivsetg_input) 0 empty_decls' ivsetg_input.

Compute (List.length ivsetg_input).                          (* 2 input rules *)
Compute ivsetg_output.

(* FIRES: 2 guarded-range rules -> 1 guarded interval-set lookup (guard KEPT at head)
   + a fresh INTERVAL set holding both [lo,hi] pairs; n' = 1. *)
Example ivsetg_fires :
  let '(n', d', rs') := ivsetg_output in
  rs' = [ merged_ruleGs FThDport gtcp (setname 0) [] acc ]
  /\ sd_sets d' = [ (setname 0, [(plo1, phi1); (plo2, phi2)]) ]
  /\ n' = 1.
Proof. cbv. repeat split. Qed.

(* DECLINES on OVERLAP: 20-30 and 25-40 share points -> not pairwise disjoint ->
   the gate leaves BOTH rules unfolded (no set minted). *)
Definition ivsetg_overlap_input : list rule :=
  [ orig_ruleGr FThDport gtcp plo1 phi1 [] acc
  ; orig_ruleGr FThDport gtcp polap phi2 [] acc ].

Definition ivsetg_overlap_output :=
  optimize_rules_ivsetg (List.length ivsetg_overlap_input) 0 empty_decls' ivsetg_overlap_input.

Example ivsetg_declines_overlap :
  let '(n', d', rs') := ivsetg_overlap_output in
  rs' = ivsetg_overlap_input /\ sd_sets d' = [] /\ n' = 0.
Proof. cbv. repeat split. Qed.

(* And it fires in the SHIPPED optimizer [optimize_table_uncond] (the extracted term):
   the two-range guarded chain optimises to ONE rule + the interval set. *)
Definition ivsetg_chain : chain :=
  {| c_policy := Drop; c_rules := ivsetg_input |}.

Definition ivsetg_table_output := optimize_table_uncond ivsetg_chain.

Compute (let '(_, d, c) := ivsetg_table_output in
         (List.length (c_rules c), sd_sets d)).

Example ivsetg_table_fires :
  let '(_, d', c') := ivsetg_table_output in
  List.length (c_rules c') = 1 /\
  exists nm, sd_sets d' = [ (nm, [(plo1, phi1); (plo2, phi2)]) ].
Proof. cbv. split; [reflexivity | eexists; reflexivity]. Qed.
