(* AUTO-GENERATED from ../../rulesets/router.nft by nft2coq (extracted/nft_emit.ml). DO NOT EDIT.
   This is the parser's SURFACE output as a Coq [sruleset]; the tables,
   chains, hooks and set/map declarations the proofs reason about are the
   VERIFIED lowering [Lower.lower_ruleset] applied to it (no hand-written
   bytes here).  A refused construct fails [router_lowers_ok] (fail-loud). *)

From Stdlib Require Import List String ZArith.
From Nft Require Import Bytes Verdict Packet Bytecode Syntax Semantics Nftval.
From Nft Require Import Surface.Ast Surface.Lower Gen_Support.
Import ListNotations.
Open Scope string_scope.

Definition router_surface : sruleset :=
  [(TopDefine "DEV_PRIVATE" (SVSym "eth1"));

   (TopDefine "DEV_WORLD" (SVSym "ppp0"));

   (TopDefine "NET_PRIVATE" (SVPrefix (sip4 192 168 0 0) 16));

   (TopTable {| st_family := "ip"; st_name := "global";
      st_items := [(TChain {| sc_name := "inbound_world";
        sc_items := [(IRule [(CMatch {| sm_keys := [["ip"; "saddr"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (sip4 81 209 165 42)) |} |});
           (CMatch {| sm_keys := [["tcp"; "dport"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "ssh")) |} |});
           (CVerdict SVaccept)])] |});
      (TChain {| sc_name := "inbound_private";
        sc_items := [(IRule [(CMatch {| sm_keys := [["icmp"; "type"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "echo-request")) |} |});
           (CStmt (StLimit 5 "second" false 5 false));
           (CVerdict SVaccept)]);
         (IRule [(CVmap [["ip"; "protocol"]; ["th"; "dport"]] [((SVConcat [(SVSym "tcp"); (SVNum 22)]), SVaccept); ((SVConcat [(SVSym "udp"); (SVNum 53)]), SVaccept); ((SVConcat [(SVSym "tcp"); (SVNum 53)]), SVaccept); ((SVConcat [(SVSym "udp"); (SVNum 67)]), SVaccept)])])] |});
      (TChain {| sc_name := "inbound";
        sc_items := [(ITypeHook "filter" "input" false 0);
         (IPolicy SVdrop);
         (IRule [(CVmap [["ct"; "state"]] [((SVSym "established"), SVaccept); ((SVSym "related"), SVaccept); ((SVSym "invalid"), SVdrop)])]);
         (IRule [(CVmap [["iifname"]] [((SVSym "lo"), SVaccept); ((SVVar "DEV_WORLD"), (SVjump "inbound_world")); ((SVVar "DEV_PRIVATE"), (SVjump "inbound_private"))])])] |});
      (TChain {| sc_name := "forward";
        sc_items := [(ITypeHook "filter" "forward" false 0);
         (IPolicy SVdrop);
         (IRule [(CVmap [["ct"; "state"]] [((SVSym "established"), SVaccept); ((SVSym "related"), SVaccept); ((SVSym "invalid"), SVdrop)])]);
         (IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVVar "DEV_PRIVATE")) |} |});
           (CVerdict SVaccept)])] |});
      (TChain {| sc_name := "postrouting";
        sc_items := [(ITypeHook "nat" "postrouting" false 100);
         (IPolicy SVaccept);
         (IRule [(CMatch {| sm_keys := [["ip"; "saddr"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVVar "NET_PRIVATE")) |} |});
           (CMatch {| sm_keys := [["oifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVVar "DEV_WORLD")) |} |});
           (CStmt (StMasquerade []))])] |})] |})].

Definition ifindex_pins (s : string) : option nat :=
  if String.eqb s "lo" then Some 1%nat else None.

Example router_lowers_ok : lower_ok ifindex_pins router_surface = true.
Proof. vm_compute. reflexivity. Qed.

Definition router_lowered : lowered_ruleset :=
  Eval vm_compute in lower_or_empty ifindex_pins router_surface.

Definition decls : set_decls := Eval vm_compute in lr_set_decls router_lowered.

Definition base_env : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => [];
     e_ifaddrs := (fun _ => []); e_ifaddrs6 := (fun _ => []);
     e_limit := fun _ => 0; e_quota := fun _ => 0; e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

Definition gen_env : env := env_with_sets base_env decls.

(* ===== table ip global ===== *)

Definition global_inbound_world : chain :=
  Eval vm_compute in lr_chain_of router_lowered "global" "inbound_world".

Definition global_inbound_private : chain :=
  Eval vm_compute in lr_chain_of router_lowered "global" "inbound_private".

Definition global_inbound : chain :=
  Eval vm_compute in lr_chain_of router_lowered "global" "inbound".

Definition global_forward : chain :=
  Eval vm_compute in lr_chain_of router_lowered "global" "forward".

Definition global_postrouting : chain :=
  Eval vm_compute in lr_chain_of router_lowered "global" "postrouting".

Definition global_chains : list (string * chain) :=
  Eval vm_compute in lr_chains_of router_lowered "global".

Definition global_hooks : list hooked_chain :=
  Eval vm_compute in lr_hooks_of router_lowered "global".

