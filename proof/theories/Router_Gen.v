(* AUTO-GENERATED from ../../router.nft by nft2coq (extracted/nft_emit.ml). DO NOT EDIT.
   This is the parser's output as Coq terms: the chains and the set/map
   declarations their lookups read.  Properties proved about these terms
   are properties of the parsed ruleset (and, via compile_table_correct, of
   the installed bytecode). *)

From Stdlib Require Import List String.
From Nft Require Import Bytes Verdict Packet Syntax Semantics.
Import ListNotations.
Open Scope string_scope.

Definition decls : set_decls :=
  {| sd_sets := [];
   sd_vmaps := [("__map0", [([6; 0; 22], [6; 0; 22], Accept); ([17; 0; 53], [17; 0; 53], Accept); ([6; 0; 53], [6; 0; 53], Accept); ([17; 0; 67], [17; 0; 67], Accept)]);
   ("__map1", [([0; 0; 0; 2], [0; 0; 0; 2], Accept); ([0; 0; 0; 4], [0; 0; 0; 4], Accept); ([0; 0; 0; 1], [0; 0; 0; 1], Drop)]);
   ("__map2", [([108; 111; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [108; 111; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], Accept); ([112; 112; 112; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [112; 112; 112; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], (Jump "inbound_world")); ([101; 116; 104; 49; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [101; 116; 104; 49; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], (Jump "inbound_private"))]);
   ("__map3", [([0; 0; 0; 2], [0; 0; 0; 2], Accept); ([0; 0; 0; 4], [0; 0; 0; 4], Accept); ([0; 0; 0; 1], [0; 0; 0; 1], Drop)])];
   sd_maps := [] |}.

Definition base_env : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => [];
     e_ifaddrs := (fun _ => []); e_ifaddrs6 := (fun _ => []);
     e_limit := fun _ => 0; e_quota := fun _ => 0; e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

Definition gen_env : env := env_with_sets base_env decls.

(* ===== table ip global ===== *)

Definition global_inbound_world : chain :=
  {| c_policy := Continue;
   c_rules := [{| r_body := [(BMatch (MEq FIp4Saddr [81; 209; 165; 42]));
             (BMatch (MEq FMetaL4proto [6]));
             (BMatch (MEq FThDport [0; 22]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}] |}.

Definition global_inbound_private : chain :=
  {| c_policy := Continue;
   c_rules := [{| r_body := [(BMatch (MEq FMetaL4proto [1]));
             (BMatch (MEq FIcmpType [8]));
             (BMatch (MLimit {| ls_rate := 5; ls_unit := 0; ls_burst := 5; ls_bytes := false; ls_flags := 0 |}))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [];
     r_verdict := Continue; r_vmap := (Some {| vm_fields := [FIp4Protocol; FThDport]; vm_keyf := None; vm_name := "__map0" |});
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}] |}.

Definition global_inbound : chain :=
  {| c_policy := Drop;
   c_rules := [{| r_body := [];
     r_verdict := Continue; r_vmap := (Some {| vm_fields := []; vm_keyf := (Some (FCtState, [])); vm_name := "__map1" |});
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [];
     r_verdict := Continue; r_vmap := (Some {| vm_fields := []; vm_keyf := (Some (FMetaIifname, [])); vm_name := "__map2" |});
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}] |}.

Definition global_forward : chain :=
  {| c_policy := Drop;
   c_rules := [{| r_body := [];
     r_verdict := Continue; r_vmap := (Some {| vm_fields := []; vm_keyf := (Some (FCtState, [])); vm_name := "__map3" |});
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaIifname [101; 116; 104; 49; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}] |}.

Definition global_postrouting : chain :=
  {| c_policy := Accept;
   c_rules := [{| r_body := [(BMatch (MMasked FIp4Saddr false [255; 255; 0; 0] [0; 0; 0; 0] [192; 168; 0; 0]));
             (BMatch (MEq FMetaOifname [112; 112; 112; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := (Some {| nat_imms := []; nat_field := None; nat_map := None; nat_src := None; nat_kind := "masq"; nat_family := "ip"; nat_amin := None; nat_amax := None; nat_pmin := None; nat_pmax := None; nat_flags := 0 |}); r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}] |}.

Definition global_chains : list (string * chain) :=
  [("inbound_world", global_inbound_world);
   ("inbound_private", global_inbound_private);
   ("inbound", global_inbound);
   ("forward", global_forward);
   ("postrouting", global_postrouting)].

Definition global_hooks : list hooked_chain :=
  [{| hc_hook := Hinput; hc_prio := 0; hc_env := global_chains; hc_base := global_inbound |};
   {| hc_hook := Hforward; hc_prio := 0; hc_env := global_chains; hc_base := global_forward |};
   {| hc_hook := Hpostrouting; hc_prio := 100; hc_env := global_chains; hc_base := global_postrouting |}].

