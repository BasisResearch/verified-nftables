(** Fires-witness for the snat bare-map merge (Optimize_Snat): two adjacent
    `ip saddr <A>  snat to <T>` rules collapse into ONE bare
    `snat to ip saddr map { A:T1, B:T2 }` rule, synthesising a fresh data MAP. *)
From Stdlib Require Import List String.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Optimize Optimize_ValueSet Optimize_DataMap Optimize_Dnat Optimize_Snat.

Local Open Scope nat_scope.

Definition empty_decls : set_decls := {| sd_sets := []; sd_vmaps := []; sd_maps := [] |}.

(* source addresses 10.0.0.1 / 10.0.0.2, snat targets 192.168.1.1 / 192.168.1.2 *)
Definition A1 : data := [10;0;0;1].
Definition A2 : data := [10;0;0;2].
Definition T1 : data := [192;168;1;1].
Definition T2 : data := [192;168;1;2].

Definition snat_input : list rule :=
  [ orig_snat_rule FIp4Saddr A1 T1 ; orig_snat_rule FIp4Saddr A2 T2 ].

(* The pass fires: 2 rules -> 1 bare map rule, and a fresh data map is minted. *)
Definition snat_output := optimize_rules_snat 0 empty_decls snat_input.

Compute (List.length snat_input, snat_input).             (* 2 input rules *)
Compute snat_output.
(* extract just the rule count and the synthesised sd_maps: *)
Compute (let '(_, d, rs) := snat_output in (List.length rs, sd_maps d)).

(* Sanity: the merged rule is exactly the bare source-map rule over FIp4Saddr,
   and the synthesised map has both keys->targets. *)
Example snat_fires :
  let '(n', d', rs') := snat_output in
  rs' = [ mk_snat_rule FIp4Saddr (mapname 0) ]
  /\ sd_maps d' = [ (mapname 0, dmap2 A1 A2 T1 T2) ]
  /\ n' = 1.
Proof. cbv. repeat split. Qed.
