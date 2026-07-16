(* AUTO-GENERATED from ../../rulesets/optiplex.nft by nft2coq (extracted/nft_emit.ml). DO NOT EDIT.
   This is the parser's output as Coq terms: the chains and the set/map
   declarations their lookups read.  Properties proved about these terms
   are properties of the parsed ruleset (and, via compile_table_correct, of
   the installed bytecode). *)

From Stdlib Require Import List String ZArith.
From Nft Require Import Bytes Verdict Packet Bytecode Syntax Semantics Nftval Elab.
Import ListNotations.
Open Scope string_scope.

Definition decls : set_decls :=
  {| sd_sets := [("vmaddrs", [(SEl [192; 168; 51; 20]); (SEl [192; 168; 51; 14]); (SEl [192; 168; 51; 15]); (SEl [192; 168; 51; 12]); (SEl [192; 168; 51; 10]); (SEl [192; 168; 51; 1]); (SEl [192; 168; 51; 21]); (SEl [192; 168; 51; 22]); (SEl [192; 168; 51; 23]); (SEl [192; 168; 51; 24])]);
   ("vmantispoof", [(SEl [192; 168; 51; 20; 105; 110; 99; 45; 98; 117; 100; 103; 101; 0; 0; 0; 0; 0; 0; 0]); (SEl [192; 168; 51; 14; 105; 110; 99; 45; 118; 105; 107; 117; 110; 0; 0; 0; 0; 0; 0; 0]); (SEl [192; 168; 51; 15; 105; 110; 99; 45; 102; 114; 101; 115; 104; 0; 0; 0; 0; 0; 0; 0]); (SEl [192; 168; 51; 12; 118; 98; 45; 103; 101; 110; 116; 111; 111; 0; 0; 0; 0; 0; 0; 0]); (SEl [192; 168; 51; 10; 118; 98; 45; 104; 97; 115; 115; 0; 0; 0; 0; 0; 0; 0; 0; 0]); (SEl [192; 168; 51; 1; 118; 108; 97; 110; 46; 50; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0]); (SEl [192; 168; 51; 21; 118; 98; 45; 109; 101; 109; 111; 115; 0; 0; 0; 0; 0; 0; 0; 0]); (SEl [192; 168; 51; 22; 118; 98; 45; 105; 115; 115; 111; 0; 0; 0; 0; 0; 0; 0; 0; 0]); (SEl [192; 168; 51; 23; 118; 98; 45; 110; 116; 102; 121; 0; 0; 0; 0; 0; 0; 0; 0; 0]); (SEl [192; 168; 51; 24; 118; 98; 45; 99; 111; 108; 108; 0; 0; 0; 0; 0; 0; 0; 0; 0])]);
   ("__set0", [(SEl [6]); (SEl [17])]);
   ("__set1", [(SEl [108; 97; 110; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]); (SEl [104; 111; 109; 101; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])]);
   ("__set2", [(SEl [187; 112]); (SEl [187; 117]); (SEl [187; 138]); (SEl [187; 126]); (SEl [187; 127]); (SEl [187; 128]); (SEl [187; 130])]);
   ("__set3", [(SEl [0; 0; 0; 2]); (SEl [0; 0; 0; 4])]);
   ("__set4", [(SEl [0; 22]); (SEl [0; 80]); (SEl [1; 187]); (SEl [4; 222])]);
   ("__set5", [(SRange [116; 115] [116; 118]); (SEl [105; 137]); (SEl [106; 81]); (SEl [31; 107])]);
   ("__set6", [(SEl [153; 0; 0; 0]); (SEl [0; 1; 0; 0])]);
   ("__set7", [(SEl [118; 98; 45; 106; 101; 108; 108; 121; 0; 0; 0; 0; 0; 0; 0; 0]); (SEl [118; 98; 45; 115; 97; 98; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]); (SEl [118; 98; 45; 114; 97; 100; 97; 114; 0; 0; 0; 0; 0; 0; 0; 0])])];
   sd_vmaps := [];
   sd_maps := [] |}.

Definition base_env : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => [];
     e_ifaddrs := (fun _ => []); e_ifaddrs6 := (fun _ => []);
     e_limit := fun _ => 0; e_quota := fun _ => 0; e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

Definition gen_env : env := env_with_sets base_env decls.

(* ===== table inet filter ===== *)

Definition filter_prerouting : chain :=
  {| c_policy := Accept;
   c_rules := [{| r_body := [(BMatch (elab_m (TMEq FMetaIifname (ifname "home"))));
             (BMatch (elab_m (TMEq (FFib "daddr" FRtype) (VFibType 2))));
             (BMatch (MConcatSet [FMetaL4proto] false "__set0"));
             (BMatch (elab_m (TMEq FThDport (VPort 3389))));
             (BStmt (SMetaSet MKmark (VImm [153; 0; 0; 0])));
             (BStmt (SLog "prefix [nft:rdppre]"))];
     r_outcome := ONat {| nat_addr_imm := (Some [192; 168; 51; 186]); nat_field := None; nat_map := None; nat_src := None; nat_extra := NXnone; nat_kind := NKdnat; nat_family := NFip4; nat_flags := 0 |}; r_after := [] |};

   {| r_body := [(BMatch (MConcatSet [FMetaIifname] false "__set1"));
             (BMatch (elab_m (TMEq (FFib "daddr" FRtype) (VFibType 2))));
             (BMatch (MConcatSet [FMetaL4proto] false "__set0"));
             (BMatch (MConcatSet [FThDport] false "__set2"));
             (BStmt (SMetaSet MKmark (VImm [153; 0; 0; 0])));
             (BStmt (SLog "prefix [nft:rdppre]"))];
     r_outcome := ONat {| nat_addr_imm := (Some [192; 168; 51; 186]); nat_field := None; nat_map := None; nat_src := None; nat_extra := NXnone; nat_kind := NKdnat; nat_family := NFip4; nat_flags := 0 |}; r_after := [] |};

   {| r_body := [(BMatch (MConcatSet [FMetaIifname] false "__set1"));
             (BMatch (elab_m (TMEq (FFib "daddr" FRtype) (VFibType 2))));
             (BMatch (MConcatSet [FMetaL4proto] false "__set0"));
             (BMatch (MConcatSet [FThDport] false "__set2"));
             (BStmt (SMetaSet MKmark (VImm [153; 0; 0; 0])));
             (BStmt (SLog "prefix [nft:rdppre]"))];
     r_outcome := ONat {| nat_addr_imm := (Some [192; 168; 51; 186]); nat_field := None; nat_map := None; nat_src := None; nat_extra := NXnone; nat_kind := NKdnat; nat_family := NFip4; nat_flags := 0 |}; r_after := [] |}] |}.

Definition filter_postrouting : chain :=
  {| c_policy := Accept;
   c_rules := [{| r_body := [(BMatch (elab_m (TMEq FMetaMark (VHostInt 4 153))));
             (BStmt (SLog "prefix [nft:rdppost]"))];
     r_outcome := ONat {| nat_addr_imm := None; nat_field := None; nat_map := None; nat_src := None; nat_extra := NXnone; nat_kind := NKmasq; nat_family := NFinet; nat_flags := 0 |}; r_after := [] |}] |}.

Definition filter_input : chain :=
  {| c_policy := Drop;
   c_rules := [{| r_body := [(BMatch (MConcatSet [FCtState] false "__set3"))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq FMetaIif (VHostInt 4 1))))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BDep (elab_m (TMEq FMetaNfproto (VInteger 1 2))));
             (BMatch (elab_m (TMEq FIp4Protocol (VInteger 1 1))))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq FMetaL4proto (VInteger 1 58))))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq FMetaIifname (ifname "br.20"))));
             (BDep (elab_m (TMEq FMetaL4proto (VInteger 1 6))));
             (BMatch (elab_m (TMEq FThDport (VPort 443))))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq FMetaIifname (ifname "br.20"))));
             (BDep (elab_m (TMEq FMetaL4proto (VInteger 1 17))));
             (BMatch (elab_m (TMEq FThDport (VPort 51820))))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq FMetaIifname (ifname "lan0"))));
             (BDep (elab_m (TMEq FMetaNfproto (VInteger 1 2))));
             (BMatch (elab_m (MPrefix FIp4Saddr CEq (ip4 192 168 50 0) 24)));
             (BDep (elab_m (TMEq FMetaL4proto (VInteger 1 6))));
             (BMatch (elab_m (TMEq FThDport (VPort 2049))))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq FMetaIifname (ifname "vlan.25"))));
             (BDep (elab_m (TMEq FMetaL4proto (VInteger 1 17))));
             (BMatch (elab_m (TMEq FThDport (VPort 67))))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (MConcatSet [FMetaIifname] false "__set1"));
             (BDep (elab_m (TMEq FMetaL4proto (VInteger 1 6))));
             (BMatch (MConcatSet [FThDport] false "__set4"))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (MConcatSet [FMetaIifname] false "__set1"));
             (BMatch (MConcatSet [FMetaL4proto] false "__set0"));
             (BMatch (elab_m (TMEq FThDport (VPort 22000))))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq FMetaIifname (ifname "lan0"))));
             (BDep (elab_m (TMEq FMetaL4proto (VInteger 1 6))));
             (BMatch (MConcatSet [FThDport] false "__set5"))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq FMetaIifname (ifname "lan0"))));
             (BDep (elab_m (TMEq FMetaL4proto (VInteger 1 17))));
             (BMatch (elab_m (TMEq FThDport (VPort 29810))))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq FMetaIifname (ifname "lan0"))));
             (BDep (elab_m (TMEq FMetaL4proto (VInteger 1 17))));
             (BMatch (elab_m (TMEq FThDport (VPort 45747))));
             (BStmt (SLog "prefix [nft:wg]"))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq FMetaIifname (ifname "immich"))));
             (BMatch (MConcatSet [FMetaL4proto] false "__set0"));
             (BMatch (elab_m (TMEq FThDport (VPort 53))))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq FMetaPkttype (VInteger 1 0))));
             (BMatch (MLimit {| ls_rate := 5; ls_unit := 0; ls_burst := 5; ls_bytes := false; ls_flags := 0 |}));
             (BStmt (SCounter 0 0))];
     r_outcome := OVerdict (Reject 2 3); r_after := [] |};

   {| r_body := [(BStmt (SLog "prefix [nft:reject]"));
             (BStmt (SCounter 0 0))];
     r_outcome := ONone; r_after := [] |}] |}.

Definition filter_forward : chain :=
  {| c_policy := Drop;
   c_rules := [{| r_body := [(BStmt (SLog "prefix [forwarding]"))];
     r_outcome := ONone; r_after := [] |};

   {| r_body := [(BMatch (elab_m (MWildcard FMetaIifname [112; 111; 100; 109; 97; 110])))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq FMetaIifname (ifname "immich"))))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (MConcatSet [FCtState] false "__set3"))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (MConcatSet [FMetaMark] false "__set6"));
             (BStmt (SLog "prefix [nft:rdpforward]"))];
     r_outcome := OVerdict Accept; r_after := [] |}] |}.

Definition filter_chains : list (string * chain) :=
  [("prerouting", filter_prerouting);
   ("postrouting", filter_postrouting);
   ("input", filter_input);
   ("forward", filter_forward)].

Definition filter_hooks : list hooked_chain :=
  [{| hc_hook := Hprerouting; hc_prio := (-100)%Z; hc_env := filter_chains; hc_base := filter_prerouting |};
   {| hc_hook := Hpostrouting; hc_prio := (100)%Z; hc_env := filter_chains; hc_base := filter_postrouting |};
   {| hc_hook := Hinput; hc_prio := (0)%Z; hc_env := filter_chains; hc_base := filter_input |};
   {| hc_hook := Hforward; hc_prio := (0)%Z; hc_env := filter_chains; hc_base := filter_forward |}].

(* ===== table bridge vmfilter ===== *)

Definition vmfilter_vm : chain :=
  {| c_policy := Continue;
   c_rules := [{| r_body := [(BMatch (elab_m (TMEq FMetaIifname (ifname "vlan.20"))));
             (BDep (elab_m (TMEq FMetaL4proto (VInteger 1 17))));
             (BMatch (elab_m (TMEq FThSport (VPort 67))))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq FMetaOifname (ifname "vlan.20"))))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (MConcatSet [FMetaIifname] false "__set7"));
             (BMatch (MConcatSet [FMetaOifname] false "__set7"))];
     r_outcome := OVerdict Accept; r_after := [] |}] |}.

Definition vmfilter_iot : chain :=
  {| c_policy := Continue;
   c_rules := [{| r_body := [];
     r_outcome := OVerdict Accept; r_after := [] |}] |}.

Definition vmfilter_cam : chain :=
  {| c_policy := Continue;
   c_rules := [{| r_body := [];
     r_outcome := OVerdict Accept; r_after := [] |}] |}.

Definition vmfilter_scanner : chain :=
  {| c_policy := Continue;
   c_rules := [{| r_body := [];
     r_outcome := OVerdict Accept; r_after := [] |}] |}.

Definition vmfilter_output : chain :=
  {| c_policy := Accept;
   c_rules := [{| r_body := [(BMatch (elab_m (TMEq (FMetaGen MKbri_oifname) (ifname "br.20"))));
             (BDep (elab_m (TMEq FMetaProtocol (VInteger 2 2048))));
             (BMatch (MConcatSet [FIp4Daddr] false "vmaddrs"));
             (BMatch (MConcatSet [FIp4Daddr; FMetaOifname] true "vmantispoof"))];
     r_outcome := OVerdict Drop; r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq (FMetaGen MKbri_oifname) (ifname "br.1"))));
             (BDep (elab_m (TMEq FMetaProtocol (VInteger 2 2048))));
             (BMatch (elab_m (TMEq FIp4Daddr (ip4 192 168 100 2))));
             (BMatch (elab_m (TMNeq FMetaOifname (ifname "vb-hass"))))];
     r_outcome := OVerdict Drop; r_after := [] |}] |}.

Definition vmfilter_forward : chain :=
  {| c_policy := Drop;
   c_rules := [{| r_body := [(BMatch (elab_m (TMEq FEtherType (VInteger 2 2054))))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (MConcatSet [FCtState] false "__set3"))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BDep (elab_m (TMEq FMetaProtocol (VInteger 2 2048))));
             (BMatch (elab_m (TMEq FIp4Protocol (VInteger 1 1))))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq FMetaL4proto (VInteger 1 58))))];
     r_outcome := OVerdict Accept; r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq (FMetaGen MKbri_iifname) (ifname "br.1"))))];
     r_outcome := OVerdict (Goto "iot"); r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq (FMetaGen MKbri_iifname) (ifname "br.20"))))];
     r_outcome := OVerdict (Goto "vm"); r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq (FMetaGen MKbri_iifname) (ifname "br.3"))))];
     r_outcome := OVerdict (Goto "scanner"); r_after := [] |};

   {| r_body := [(BMatch (elab_m (TMEq (FMetaGen MKbri_iifname) (ifname "br.110"))))];
     r_outcome := OVerdict (Goto "cam"); r_after := [] |}] |}.

Definition vmfilter_chains : list (string * chain) :=
  [("vm", vmfilter_vm);
   ("iot", vmfilter_iot);
   ("cam", vmfilter_cam);
   ("scanner", vmfilter_scanner);
   ("output", vmfilter_output);
   ("forward", vmfilter_forward)].

Definition vmfilter_hooks : list hooked_chain :=
  [{| hc_hook := Houtput; hc_prio := (0)%Z; hc_env := vmfilter_chains; hc_base := vmfilter_output |};
   {| hc_hook := Hforward; hc_prio := (0)%Z; hc_env := vmfilter_chains; hc_base := vmfilter_forward |}].

