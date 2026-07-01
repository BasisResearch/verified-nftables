(** Fires-witness for the guarded value+verdict -> VERDICT MAP merge (battery shape
    18): three adjacent `tcp dport <P> <verdict>` rules — whose `tcp dport` selector
    carries its implicit `meta l4proto 6` guard BEFORE it — with DIFFERING terminal
    verdicts collapse into ONE guarded verdict-map lookup

        tcp dport vmap { 22 : drop, 80 : accept, 443 : drop }

    synthesising a fresh anonymous `__vmap0`.  Exactly what `nft --optimize` emits
    (l4proto guard, then the tcp-dport payload load, then the `[ lookup dreg 0 ]`
    verdict-register map).  This shows [optimize_rules_vmapNg] fires NON-VACUOUSLY. *)
From Stdlib Require Import List String.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Optimize Optimize_Merge Optimize_Vmap Optimize_Vmapg.

Local Open Scope nat_scope.

Definition empty_decls : set_decls := {| sd_sets := []; sd_vmaps := []; sd_maps := [] |}.

(* tcp dport 22 (0x0016) / 80 (0x0050) / 443 (0x01BB) *)
Definition P1 : data := [0;22].
Definition P2 : data := [0;80].
Definition P3 : data := [1;187].
(* the shared l4proto==tcp(6) guard the frontend interposes for `tcp dport` *)
Definition gm : matchcond := MCmp FMetaL4proto CEq [6].

Definition vmapg_input : list rule :=
  [ orig_ruleGv FThDport gm P1 [] Drop
  ; orig_ruleGv FThDport gm P2 [] Accept
  ; orig_ruleGv FThDport gm P3 [] Drop ].

(* The pass fires: 3 rules -> 1 guarded vmap-lookup rule + a fresh __vmap0. *)
Definition vmapg_output :=
  optimize_rules_vmapNg (List.length vmapg_input) 0 empty_decls vmapg_input.

Compute (List.length vmapg_input).                       (* 3 input rules *)
Compute vmapg_output.
Compute (let '(_, d, rs) := vmapg_output in (List.length rs, sd_vmaps d)).

(* The merged rule is exactly the guarded vmap-lookup shell (l4proto guard at the
   head of the body, vmap key FThDport), and the synthesised map holds all three
   point (key,key,verdict) entries in first-match order.  n' = 1 (one fresh
   vmapname minted). *)
Example vmapg_fires :
  let '(n', d', rs') := vmapg_output in
  rs' = [ merged_ruleGv FThDport gm (vmapname 0) [] ]
  /\ sd_vmaps d' = [ (vmapname 0,
                      [ (P1, P1, Drop); (P2, P2, Accept); (P3, P3, Drop) ]) ]
  /\ n' = 1.
Proof. cbv. repeat split. Qed.
