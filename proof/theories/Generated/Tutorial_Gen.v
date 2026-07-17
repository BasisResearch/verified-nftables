(* AUTO-GENERATED from ../../rulesets/tutorial.nft by nft2coq (extracted/nft_emit.ml). DO NOT EDIT.
   This is the parser's SURFACE output as a Coq [sruleset]; the tables,
   chains, hooks and set/map declarations the proofs reason about are the
   VERIFIED lowering [Lower.lower_ruleset] applied to it (no hand-written
   bytes here).  A refused construct fails [tutorial_lowers_ok] (fail-loud). *)

From Stdlib Require Import List String ZArith.
From Nft Require Import Bytes Verdict Packet Bytecode Syntax Semantics Nftval Elab.
From Nft Require Import Surface.Ast Surface.Lower Gen_Support.
Import ListNotations.
Open Scope string_scope.

Definition tutorial_surface : sruleset :=
  [(TopTable {| st_family := "ip"; st_name := "tutorial";
      st_items := [(TChain {| sc_name := "input";
        sc_items := [(ITypeHook "filter" "input" false 0);
         (IPolicy SVaccept);
         (IRule [(CMatch {| sm_keys := [["ip"; "saddr"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVPrefix (sip4 192 168 100 0) 24)) |} |});
           (CVerdict SVdrop)])] |})] |})].

Definition ifindex_pins (s : string) : option nat :=
  if String.eqb s "lo" then Some 1%nat else None.

Example tutorial_lowers_ok : lower_ok ifindex_pins tutorial_surface = true.
Proof. vm_compute. reflexivity. Qed.

Definition tutorial_lowered : lowered_ruleset :=
  Eval vm_compute in lower_or_empty ifindex_pins tutorial_surface.

Definition decls : set_decls := Eval vm_compute in lr_set_decls tutorial_lowered.

Definition base_env : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => [];
     e_ifaddrs := (fun _ => []); e_ifaddrs6 := (fun _ => []);
     e_limit := fun _ => 0; e_quota := fun _ => 0; e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

Definition gen_env : env := env_with_sets base_env decls.

(* ===== table ip tutorial ===== *)

Definition tutorial_input : chain :=
  Eval vm_compute in lr_chain_of tutorial_lowered "tutorial" "input".

Definition tutorial_chains : list (string * chain) :=
  Eval vm_compute in lr_chains_of tutorial_lowered "tutorial".

Definition tutorial_hooks : list hooked_chain :=
  Eval vm_compute in lr_hooks_of tutorial_lowered "tutorial".

