(* AUTO-GENERATED from ../../rulesets/router.nft by nft2coq (extracted/nft_emit.ml). DO NOT EDIT.
   This is the parser's output as Coq terms: the chains and the set/map
   declarations their lookups read.  Properties proved about these terms
   are properties of the parsed ruleset (and, via compile_table_correct, of
   the installed bytecode). *)

From Stdlib Require Import List String ZArith.
From Nft Require Import Bytes Verdict Packet Bytecode Syntax Semantics Nftval Elab.
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
   c_rules := [{| r_body := [(BMatch (elab_m (TMEq FIp4Saddr (ip4 81 209 165 42))));
             (BDep (elab_m (TMEq FMetaL4proto (VInteger 1 6))));
             (BMatch (elab_m (TMEq FThDport (VPort 22))))];
     r_outcome := OVerdict Accept; r_after := [] |}] |}.

Definition global_inbound_private : chain :=
  {| c_policy := Continue;
   c_rules := [{| r_body := [(BDep (elab_m (TMEq FMetaL4proto (VInteger 1 1))));
             (BMatch (elab_m (TMEq FIcmpType (VInteger 1 8))));
             (BMatch (MLimit {| ls_rate := 5; ls_unit := 0; ls_burst := 5; ls_bytes := false; ls_flags := 0 |}))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [];
     r_outcome := OVmap {| vm_fields := [FIp4Protocol; FThDport]; vm_keyf := None; vm_name := "__map0" |}; r_after := [] |}] |}.

Definition global_inbound : chain :=
  {| c_policy := Drop;
   c_rules := [{| r_body := [];
     r_outcome := OVmap {| vm_fields := []; vm_keyf := (Some (FCtState, [])); vm_name := "__map1" |}; r_after := [] |};

   {| r_body := [];
     r_outcome := OVmap {| vm_fields := []; vm_keyf := (Some (FMetaIifname, [])); vm_name := "__map2" |}; r_after := [] |}] |}.

Definition global_forward : chain :=
  {| c_policy := Drop;
   c_rules := [{| r_body := [];
     r_outcome := OVmap {| vm_fields := []; vm_keyf := (Some (FCtState, [])); vm_name := "__map3" |}; r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq FMetaIifname (ifname "eth1"))))];
     r_outcome := OVerdict Accept; r_after := [] |}] |}.

Definition global_postrouting : chain :=
  {| c_policy := Accept;
   c_rules := [{| r_body := [(BMatch (elab_m (MPrefix FIp4Saddr CEq (ip4 192 168 0 0) 16)));
             (BMatch (elab_m (TMEq FMetaOifname (ifname "ppp0"))))];
     r_outcome := ONat {| nat_addr_imm := None; nat_field := None; nat_map := None; nat_src := None; nat_extra := NXnone; nat_kind := NKmasq; nat_family := NFip4; nat_flags := 0 |}; r_after := [] |}] |}.

Definition global_chains : list (string * chain) :=
  [("inbound_world", global_inbound_world);
   ("inbound_private", global_inbound_private);
   ("inbound", global_inbound);
   ("forward", global_forward);
   ("postrouting", global_postrouting)].

Definition global_hooks : list hooked_chain :=
  [{| hc_hook := Hinput; hc_prio := (0)%Z; hc_env := global_chains; hc_base := global_inbound |};
   {| hc_hook := Hforward; hc_prio := (0)%Z; hc_env := global_chains; hc_base := global_forward |};
   {| hc_hook := Hpostrouting; hc_prio := (100)%Z; hc_env := global_chains; hc_base := global_postrouting |}].

