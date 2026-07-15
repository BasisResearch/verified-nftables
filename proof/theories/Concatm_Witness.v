(** Fires-witness for the guarded transport-key concat merge (Optimize_ConcatM): two adjacent
    `ip saddr <A>  tcp dport <P>  accept` rules — whose `tcp dport` selector carries
    its implicit `meta l4proto 6` guard BETWEEN the two selectors — collapse into ONE
    `ip saddr . tcp dport { A.P, B.Q } accept` lookup with the l4proto guard hoisted
    to the head, synthesising a fresh anonymous concat SET.  This is exactly what
    `nft --optimize` emits (guard first, saddr in reg 1, dport in the next reg slot,
    then the lookup). *)
From Stdlib Require Import List String.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Optimize Optimize_Merge Optimize_Concat Optimize_ConcatM.

Local Open Scope nat_scope.

Definition empty_decls : set_decls := {| sd_sets := []; sd_vmaps := []; sd_maps := [] |}.

(* ip saddr 1.1.1.1 / 2.2.2.2 ; tcp dport 22 (0x0016) / 80 (0x0050) *)
Definition A1 : data := [1;1;1;1].
Definition A2 : data := [2;2;2;2].
Definition P1 : data := [0;22].
Definition P2 : data := [0;80].
(* the shared l4proto==tcp(6) guard the frontend interposes for `tcp dport` *)
Definition gm : matchcond := MCmp FMetaL4proto CEq [6].

(* a bare terminal-Accept shell (the end-fields the two rules share) *)
Definition acc : rule :=
  {| r_body := []; r_verdict := Accept; r_vmap := None; r_nat := None;
     r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}.

Definition concatm_input : list rule :=
  [ orig_rule2g FIp4Saddr FThDport gm A1 P1 [] acc
  ; orig_rule2g FIp4Saddr FThDport gm A2 P2 [] acc ].

(* The pass fires: 2 rules -> 1 guarded concat-lookup rule + a fresh concat SET. *)
Definition concatm_output :=
  optimize_rules_concatM (List.length concatm_input) 0 empty_decls concatm_input.

Compute (List.length concatm_input).                       (* 2 input rules *)
Compute concatm_output.
Compute (let '(_, d, rs) := concatm_output in (List.length rs, sd_sets d)).

(* Sanity: the merged rule is exactly the guarded concat-lookup shell (l4proto guard
   at the head, MConcatSet over [FIp4Saddr; FThDport]), and the synthesised set holds
   both packed 2-field tuples.  n' = 1 (one fresh setname minted). *)
Example concatm_fires :
  let '(n', d', rs') := concatm_output in
  rs' = [ merged_rule2g FIp4Saddr FThDport gm (setname 0) [] acc ]
  /\ sd_sets d' = [ (setname 0, map pack_tuple [(A1, P1); (A2, P2)]) ]
  /\ n' = 1.
Proof. cbv. repeat split. Qed.
