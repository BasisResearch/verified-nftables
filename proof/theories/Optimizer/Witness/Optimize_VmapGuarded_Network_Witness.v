(** Fires-witness for the guarded value+verdict -> VERDICT MAP merge on the
    NETWORK-ADDRESS arm (Optimize_VmapGuarded.guard_okn): a run of adjacent
    `ip saddr <A> <verdict>` rules — whose `ip saddr` selector carries its implicit
    `meta nfproto 2` (NFPROTO_IPV4) guard BEFORE it in the `inet` family — with
    DIFFERING terminal verdicts collapses into ONE guarded verdict-map lookup

        ip saddr vmap { 1.2.3.4 : accept, 5.6.7.8 : drop, 9.10.11.12 : accept }

    synthesising a fresh anonymous `__vmap0`.  Exactly what `nft --optimize` emits
    (nfproto guard, then the ip-saddr payload load, then the `[ lookup dreg 0 ]`
    verdict-register map).  This shows [optimize_rules_vmapguarded] fires NON-VACUOUSLY on
    the nfproto-guarded network arm — the l4proto witness lives in
    [Optimize_VmapGuarded_Witness]. *)
From Stdlib Require Import List String.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Optimize Optimize_ValueSet Optimize_Vmap Optimize_VmapGuarded.

Local Open Scope nat_scope.

Definition empty_decls : set_decls := {| sd_sets := []; sd_vmaps := []; sd_maps := [] |}.

(* ip saddr 1.2.3.4 / 5.6.7.8 / 9.10.11.12 *)
Definition A1 : data := [1;2;3;4].
Definition A2 : data := [5;6;7;8].
Definition A3 : data := [9;10;11;12].
(* the shared nfproto==ipv4(2) guard the frontend interposes for `ip saddr` in inet *)
Definition gmn : matchcond := MCmp FMetaNfproto CEq [2].

Definition vmapgn_input : list rule :=
  [ orig_ruleGv FIp4Saddr gmn A1 [] Accept
  ; orig_ruleGv FIp4Saddr gmn A2 [] Drop
  ; orig_ruleGv FIp4Saddr gmn A3 [] Accept ].

(* The pass fires: 3 rules -> 1 guarded vmap-lookup rule + a fresh __vmap0. *)
Definition vmapgn_output :=
  optimize_rules_vmapguarded (List.length vmapgn_input) 0 empty_decls vmapgn_input.

Compute (List.length vmapgn_input).                       (* 3 input rules *)
Compute vmapgn_output.
Compute (let '(_, d, rs) := vmapgn_output in (List.length rs, sd_vmaps d)).

(* The merged rule is exactly the guarded vmap-lookup shell (nfproto guard at the
   head of the body, vmap key FIp4Saddr), and the synthesised map holds all three
   point (key,key,verdict) entries in first-match order.  n' = 1 (one fresh
   vmapname minted). *)
Example vmapgn_fires :
  let '(n', d', rs') := vmapgn_output in
  rs' = [ merged_ruleGv FIp4Saddr gmn (vmapname 0) [] ]
  /\ sd_vmaps d' = [ (vmapname 0,
                      [ (A1, A1, Accept); (A2, A2, Drop); (A3, A3, Accept) ]) ]
  /\ n' = 1.
Proof. cbv. repeat split. Qed.

(* And the nfproto guard actually satisfies the recogniser's whitelist. *)
Example guard_okn_fires : Optimize_VmapGuarded.guard_okn gmn = true.
Proof. reflexivity. Qed.

(* ip6 arm too: FIp6Daddr, nfproto==ipv6(10). *)
Definition B1 : data := [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;1].
Definition B2 : data := [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;2].
Definition gmn6 : matchcond := MCmp FMetaNfproto CEq [10].

Definition vmapgn6_input : list rule :=
  [ orig_ruleGv FIp6Daddr gmn6 B1 [] Drop
  ; orig_ruleGv FIp6Daddr gmn6 B2 [] Accept ].

Example vmapgn6_fires :
  let '(n', d', rs') :=
    optimize_rules_vmapguarded (List.length vmapgn6_input) 0 empty_decls vmapgn6_input in
  rs' = [ merged_ruleGv FIp6Daddr gmn6 (vmapname 0) [] ]
  /\ sd_vmaps d' = [ (vmapname 0, [ (B1, B1, Drop); (B2, B2, Accept) ]) ]
  /\ n' = 1.
Proof. cbv. repeat split. Qed.
