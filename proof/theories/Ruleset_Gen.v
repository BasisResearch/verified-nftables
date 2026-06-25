(* AUTO-GENERATED from ../../ruleset.nft by nft2coq (extracted/nft_emit.ml). DO NOT EDIT.
   This is the parser's output as Coq terms: the chains and the set/map
   declarations their lookups read.  Properties proved about these terms
   are properties of the parsed ruleset (and, via compile_table_correct, of
   the installed bytecode). *)

From Stdlib Require Import List String.
From Nft Require Import Bytes Verdict Packet Syntax Semantics.
Import ListNotations.
Open Scope string_scope.

Definition decls : set_decls :=
  {| sd_sets := [("__set0", [([135], [135]); ([134], [134]); ([136], [136])]);
   ("__set3", [([0; 22], [0; 22]); ([0; 80], [0; 80]); ([1; 187], [1; 187])])];
   sd_vmaps := [("__map1", [([0; 0; 0; 2], [0; 0; 0; 2], Accept); ([0; 0; 0; 4], [0; 0; 0; 4], Accept); ([0; 0; 0; 1], [0; 0; 0; 1], Drop)]);
   ("__map2", [([8; 0], [8; 0], (Jump "inbound_ipv4")); ([134; 221], [134; 221], (Jump "inbound_ipv6"))])];
   sd_maps := [] |}.

Definition base_env : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => [];
     e_ifaddrs := (fun _ => []); e_ifaddrs6 := (fun _ => []);
     e_limit := fun _ => 0; e_quota := fun _ => 0; e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

Definition gen_env : env := env_with_sets base_env decls.

(* ===== table inet firewall ===== *)

Definition firewall_inbound_ipv4 : chain :=
  {| c_policy := Continue;
   c_rules := [] |}.

Definition firewall_inbound_ipv6 : chain :=
  {| c_policy := Continue;
   c_rules := [{| r_body := [(BMatch (MEq FMetaNfproto [10]));
             (BMatch (MEq FMetaL4proto [58]));
             (BMatch (MConcatSet [FIcmpType] false "__set0"))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}] |}.

Definition firewall_inbound : chain :=
  {| c_policy := Drop;
   c_rules := [{| r_body := [];
     r_verdict := Continue; r_vmap := (Some {| vm_fields := []; vm_keyf := (Some (FCtState, [])); vm_name := "__map1" |});
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaIifname [108; 111; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [];
     r_verdict := Continue; r_vmap := (Some {| vm_fields := []; vm_keyf := (Some (FMetaProtocol, [])); vm_name := "__map2" |});
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaL4proto [6]));
             (BMatch (MConcatSet [FThDport] false "__set3"))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}] |}.

Definition firewall_forward : chain :=
  {| c_policy := Drop;
   c_rules := [] |}.

Definition firewall_chains : list (string * chain) :=
  [("inbound_ipv4", firewall_inbound_ipv4);
   ("inbound_ipv6", firewall_inbound_ipv6);
   ("inbound", firewall_inbound);
   ("forward", firewall_forward)].

