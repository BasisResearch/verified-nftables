(** Fires-witness for the L2 link-layer single-field value->set consolidation
    ([Optimize_Setg], L2 arm — [guard_okl2]).  Two `ether saddr <mac> accept` rules —
    each lowered by the frontend to an iiftype-guarded point match
    [MCmp FMetaIiftype CEq [0;1] ; MCmp FEtherSaddr CEq mac] (the `meta iiftype ==
    ARPHRD_ETHER (1)` dependency nft prepends before a link-layer address match in a
    non-inherently-ethernet family) — collapse into ONE guarded set lookup, exactly
    what `nft --optimize` emits (`ether saddr { 00:11:22:33:44:55, 00:11:22:33:44:66 }
    accept`; confirmed against host nft v1.1.6 in a netns, and kernel data-plane
    verdict-equivalent by an AF_PACKET frame probe).

    The 6-byte MAC field [FEtherSaddr] = [LPayload PLink 6 6] has [field_fixed_len =
    Some 6], so the merge is sound on the SAME fixed-width certificate as a transport
    port.  Distinct MAC literals are disjoint singletons => the synthesised single-field
    rbtree set is a VALID nftables object (no overlapping-interval defect). *)
From Stdlib Require Import List String.
Import ListNotations.
From Nft Require Import Bytes Packet Verdict Syntax Bytecode Semantics
  Compile Optimize Optimize_Merge Optimize_ConcatM Optimize_Setg Optimize_Table
  Optimize_Normalize Optimize_Uncond.

Local Open Scope nat_scope.

Definition empty_declsL2 : set_decls := {| sd_sets := []; sd_vmaps := []; sd_maps := [] |}.

(* the shared L2 guard `meta iiftype == ARPHRD_ETHER` (1, big-endian 2-byte) *)
Definition giift : matchcond := MCmp FMetaIiftype CEq [0;1].

(* [guard_okl2] admits the iiftype guard; [guard_ok] (the l4proto whitelist) does not. *)
Example giift_admitted : guard_okl2 giift = true /\ guard_ok giift = false.
Proof. split; reflexivity. Qed.

(* ether saddr 00:11:22:33:44:55  and  00:11:22:33:44:66  (6 verbatim bytes) *)
Definition mac1 : data := [0;17;34;51;68;85].    (* 00:11:22:33:44:55 *)
Definition mac2 : data := [0;17;34;51;68;102].   (* 00:11:22:33:44:66 *)

Definition accL2 : rule :=
  {| r_body := [];
     r_outcome := OVerdict Accept; r_after := [] |}.

Definition setl2_input : list rule :=
  [ orig_ruleGs FEtherSaddr giift mac1 [] accL2
  ; orig_ruleGs FEtherSaddr giift mac2 [] accL2 ].

Definition setl2_output :=
  optimize_rules_setg (List.length setl2_input) 0 empty_declsL2 setl2_input.

Compute (List.length setl2_input).   (* 2 input rules *)
Compute setl2_output.

(* FIRES: 2 iiftype-guarded ether-saddr rules -> 1 guarded set lookup (guard KEPT at
   head) + a fresh single-field set holding both discrete MACs; n' = 1. *)
Example setl2_fires :
  let '(n', d', rs') := setl2_output in
  rs' = [ merged_ruleGs FEtherSaddr giift (setname 0) [] accL2 ]
  /\ sd_sets d' = [ (setname 0, [(mac1, mac1); (mac2, mac2)]) ]
  /\ n' = 1.
Proof. cbv. repeat split. Qed.

(* And it fires in the SHIPPED optimizer [optimize_table_uncond] (the extracted term):
   the two ether-saddr rules optimise to ONE rule + the discrete-MAC set. *)
Definition setl2_chain : chain :=
  {| c_policy := Drop; c_rules := setl2_input |}.

Definition setl2_table_output := optimize_table_uncond setl2_chain.

Compute (let '(_, d, c) := setl2_table_output in
         (List.length (c_rules c), sd_sets d)).

Example setl2_table_fires :
  let '(_, d', c') := setl2_table_output in
  List.length (c_rules c') = 1 /\
  exists nm, sd_sets d' = [ (nm, [(mac1, mac1); (mac2, mac2)]) ].
Proof. cbv. split; [reflexivity | eexists; reflexivity]. Qed.
