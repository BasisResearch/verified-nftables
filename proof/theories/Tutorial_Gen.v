(* AUTO-GENERATED from ../../rulesets/tutorial.nft by nft2coq (extracted/nft_emit.ml). DO NOT EDIT.
   This is the parser's output as Coq terms: the chains and the set/map
   declarations their lookups read.  Properties proved about these terms
   are properties of the parsed ruleset (and, via compile_table_correct, of
   the installed bytecode). *)

From Stdlib Require Import List String ZArith.
From Nft Require Import Bytes Verdict Packet Syntax Semantics.
Import ListNotations.
Open Scope string_scope.

Definition decls : set_decls :=
  {| sd_sets := [];
   sd_vmaps := [];
   sd_maps := [] |}.

Definition base_env : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => [];
     e_ifaddrs := (fun _ => []); e_ifaddrs6 := (fun _ => []);
     e_limit := fun _ => 0; e_quota := fun _ => 0; e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

Definition gen_env : env := env_with_sets base_env decls.

(* ===== table ip tutorial ===== *)

Definition tutorial_input : chain :=
  {| c_policy := Accept;
   c_rules := [{| r_body := [(BMatch (MEq (FPayload PNetwork 12 3) [192; 168; 100]))];
     r_verdict := Drop; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}] |}.

Definition tutorial_chains : list (string * chain) :=
  [("input", tutorial_input)].

Definition tutorial_hooks : list hooked_chain :=
  [{| hc_hook := Hinput; hc_prio := (0)%Z; hc_env := tutorial_chains; hc_base := tutorial_input |}].

