(** Fires-witness for the interval / range set consolidation (Optimize_Ivset).  Two adjacent
    `ip saddr <lo>-<hi> accept` range rules collapse into ONE
    `ip saddr { lo1-hi1, lo2-hi2 } accept` lookup over a synthesised INTERVAL set —
    exactly what `nft --optimize` emits (set flags ANONYMOUS|CONSTANT|INTERVAL,
    stored as [lo,hi] element pairs; confirmed against host nft v1.1.6 in a netns). *)
From Stdlib Require Import List String.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Optimize Optimize_Merge Optimize_Ivset Optimize_Table Optimize_Normalize
  Optimize_Uncond.

Local Open Scope nat_scope.

Definition empty_decls' : set_decls := {| sd_sets := []; sd_vmaps := []; sd_maps := [] |}.

(* ip saddr 10.0.0.0-10.0.0.255  and  10.0.2.0-10.0.2.255 *)
Definition lo1 : data := [10;0;0;0].
Definition hi1 : data := [10;0;0;255].
Definition lo2 : data := [10;0;2;0].
Definition hi2 : data := [10;0;2;255].

(* a bare terminal-Accept shell (the end-fields the two range rules share) *)
Definition acc : rule :=
  {| r_body := [];
     r_outcome := OVerdict Accept; r_after := [] |}.

Definition ivset_input : list rule :=
  [ mk_head (MRange FIp4Saddr false lo1 hi1) [] acc
  ; mk_head (MRange FIp4Saddr false lo2 hi2) [] acc ].

Definition ivset_output :=
  optimize_rules_ivset (List.length ivset_input) 0 empty_decls' ivset_input.

Compute (List.length ivset_input).                            (* 2 input rules *)
Compute ivset_output.
Compute (let '(_, d, rs) := ivset_output in (List.length rs, sd_sets d)).

(* The pass FIRES: 2 range rules -> 1 interval-set lookup rule + a fresh INTERVAL
   set holding both [lo,hi] element pairs, with n' = 1 (one fresh setname minted). *)
Example ivset_fires :
  let '(n', d', rs') := ivset_output in
  rs' = [ mk_head (MConcatSet [FIp4Saddr] false (setname 0)) [] acc ]
  /\ sd_sets d' = [ (setname 0, [(lo1, hi1); (lo2, hi2)]) ]
  /\ n' = 1.
Proof. cbv. repeat split. Qed.

(* And it fires in the SHIPPED optimizer [optimize_table_uncond] (the extracted term):
   the two-range chain optimises to ONE rule + the interval set. *)
Definition ivset_chain : chain :=
  {| c_policy := Drop; c_rules := ivset_input |}.

Definition ivset_table_output := optimize_table_uncond ivset_chain.

Compute (let '(_, d, c) := ivset_table_output in
         (List.length (c_rules c), sd_sets d)).

Example ivset_table_fires :
  let '(_, d', c') := ivset_table_output in
  List.length (c_rules c') = 1 /\
  exists nm, sd_sets d' = [ (nm, [(lo1, hi1); (lo2, hi2)]) ].
Proof. cbv. split; [reflexivity | eexists; reflexivity]. Qed.
