(* AUTO-GENERATED from ../../rulesets/ruleset.nft by nft2coq (extracted/nft_emit.ml). DO NOT EDIT.
   This is the parser's SURFACE output as a Coq [sruleset]; the tables,
   chains, hooks and set/map declarations the proofs reason about are the
   VERIFIED lowering [Lower.lower_ruleset] applied to it (no hand-written
   bytes here).  A refused construct fails [ruleset_lowers_ok] (fail-loud). *)

From Stdlib Require Import List String ZArith.
From Nft Require Import Bytes Verdict Packet Bytecode Syntax Semantics Nftval Elab.
From Nft Require Import Surface.Ast Surface.Lower Gen_Support.
Import ListNotations.
Open Scope string_scope.

Definition ruleset_surface : sruleset :=
  [TopNop;

   (TopTable {| st_family := "inet"; st_name := "firewall";
      st_items := [(TChain {| sc_name := "inbound_ipv4";
        sc_items := [] |});
      (TChain {| sc_name := "inbound_ipv6";
        sc_items := [(IRule [(CMatch {| sm_keys := [["icmpv6"; "type"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVSym "nd-neighbor-solicit"); (SVSym "nd-router-advert"); (SVSym "nd-neighbor-advert")]) |} |});
           (CVerdict SVaccept)])] |});
      (TChain {| sc_name := "inbound";
        sc_items := [(ITypeHook "filter" "input" false 0);
         (IPolicy SVdrop);
         (IRule [(CVmap [["ct"; "state"]] [((SVSym "established"), SVaccept); ((SVSym "related"), SVaccept); ((SVSym "invalid"), SVdrop)])]);
         (IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "lo")) |} |});
           (CVerdict SVaccept)]);
         (IRule [(CVmap [["meta"; "protocol"]] [((SVSym "ip"), (SVjump "inbound_ipv4")); ((SVSym "ip6"), (SVjump "inbound_ipv6"))])]);
         (IRule [(CMatch {| sm_keys := [["tcp"; "dport"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVNum 22); (SVNum 80); (SVNum 443)]) |} |});
           (CVerdict SVaccept)])] |});
      (TChain {| sc_name := "forward";
        sc_items := [(ITypeHook "filter" "forward" false 0);
         (IPolicy SVdrop)] |})] |})].

Definition ifindex_pins (s : string) : option nat :=
  if String.eqb s "lo" then Some 1%nat else None.

Example ruleset_lowers_ok : lower_ok ifindex_pins ruleset_surface = true.
Proof. vm_compute. reflexivity. Qed.

Definition ruleset_lowered : lowered_ruleset :=
  Eval vm_compute in lower_or_empty ifindex_pins ruleset_surface.

Definition decls : set_decls := Eval vm_compute in lr_set_decls ruleset_lowered.

Definition base_env : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => [];
     e_ifaddrs := (fun _ => []); e_ifaddrs6 := (fun _ => []);
     e_limit := fun _ => 0; e_quota := fun _ => 0; e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

Definition gen_env : env := env_with_sets base_env decls.

(* ===== table inet firewall ===== *)

Definition firewall_inbound_ipv4 : chain :=
  Eval vm_compute in lr_chain_of ruleset_lowered "firewall" "inbound_ipv4".

Definition firewall_inbound_ipv6 : chain :=
  Eval vm_compute in lr_chain_of ruleset_lowered "firewall" "inbound_ipv6".

Definition firewall_inbound : chain :=
  Eval vm_compute in lr_chain_of ruleset_lowered "firewall" "inbound".

Definition firewall_forward : chain :=
  Eval vm_compute in lr_chain_of ruleset_lowered "firewall" "forward".

Definition firewall_chains : list (string * chain) :=
  Eval vm_compute in lr_chains_of ruleset_lowered "firewall".

Definition firewall_hooks : list hooked_chain :=
  Eval vm_compute in lr_hooks_of ruleset_lowered "firewall".

