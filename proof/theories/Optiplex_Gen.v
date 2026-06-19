(* AUTO-GENERATED from ../../optiplex.nft by nft2coq (extracted/nft_emit.ml). DO NOT EDIT.
   This is the parser's output as Coq terms: the chains and the set/map
   declarations their lookups read.  Properties proved about these terms
   are properties of the parsed ruleset (and, via compile_table_correct, of
   the installed bytecode). *)

From Stdlib Require Import List String.
From Nft Require Import Bytes Verdict Packet Syntax Semantics.
Import ListNotations.
Open Scope string_scope.

Definition decls : set_decls :=
  {| sd_sets := [("vmaddrs", [([192; 168; 51; 20], [192; 168; 51; 20]); ([192; 168; 51; 14], [192; 168; 51; 14]); ([192; 168; 51; 15], [192; 168; 51; 15]); ([192; 168; 51; 12], [192; 168; 51; 12]); ([192; 168; 51; 10], [192; 168; 51; 10]); ([192; 168; 51; 1], [192; 168; 51; 1]); ([192; 168; 51; 21], [192; 168; 51; 21]); ([192; 168; 51; 22], [192; 168; 51; 22]); ([192; 168; 51; 23], [192; 168; 51; 23]); ([192; 168; 51; 24], [192; 168; 51; 24])]);
   ("vmantispoof", [([192; 168; 51; 20; 105; 110; 99; 45; 98; 117; 100; 103; 101; 0; 0; 0; 0; 0; 0; 0], [192; 168; 51; 20; 105; 110; 99; 45; 98; 117; 100; 103; 101; 0; 0; 0; 0; 0; 0; 0]); ([192; 168; 51; 14; 105; 110; 99; 45; 118; 105; 107; 117; 110; 0; 0; 0; 0; 0; 0; 0], [192; 168; 51; 14; 105; 110; 99; 45; 118; 105; 107; 117; 110; 0; 0; 0; 0; 0; 0; 0]); ([192; 168; 51; 15; 105; 110; 99; 45; 102; 114; 101; 115; 104; 0; 0; 0; 0; 0; 0; 0], [192; 168; 51; 15; 105; 110; 99; 45; 102; 114; 101; 115; 104; 0; 0; 0; 0; 0; 0; 0]); ([192; 168; 51; 12; 118; 98; 45; 103; 101; 110; 116; 111; 111; 0; 0; 0; 0; 0; 0; 0], [192; 168; 51; 12; 118; 98; 45; 103; 101; 110; 116; 111; 111; 0; 0; 0; 0; 0; 0; 0]); ([192; 168; 51; 10; 118; 98; 45; 104; 97; 115; 115; 0; 0; 0; 0; 0; 0; 0; 0; 0], [192; 168; 51; 10; 118; 98; 45; 104; 97; 115; 115; 0; 0; 0; 0; 0; 0; 0; 0; 0]); ([192; 168; 51; 1; 118; 108; 97; 110; 46; 50; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0], [192; 168; 51; 1; 118; 108; 97; 110; 46; 50; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0]); ([192; 168; 51; 21; 118; 98; 45; 109; 101; 109; 111; 115; 0; 0; 0; 0; 0; 0; 0; 0], [192; 168; 51; 21; 118; 98; 45; 109; 101; 109; 111; 115; 0; 0; 0; 0; 0; 0; 0; 0]); ([192; 168; 51; 22; 118; 98; 45; 105; 115; 115; 111; 0; 0; 0; 0; 0; 0; 0; 0; 0], [192; 168; 51; 22; 118; 98; 45; 105; 115; 115; 111; 0; 0; 0; 0; 0; 0; 0; 0; 0]); ([192; 168; 51; 23; 118; 98; 45; 110; 116; 102; 121; 0; 0; 0; 0; 0; 0; 0; 0; 0], [192; 168; 51; 23; 118; 98; 45; 110; 116; 102; 121; 0; 0; 0; 0; 0; 0; 0; 0; 0]); ([192; 168; 51; 24; 118; 98; 45; 99; 111; 108; 108; 0; 0; 0; 0; 0; 0; 0; 0; 0], [192; 168; 51; 24; 118; 98; 45; 99; 111; 108; 108; 0; 0; 0; 0; 0; 0; 0; 0; 0])]);
   ("__set0", [([6], [6]); ([17], [17])]);
   ("__set1", [([108; 97; 110; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [108; 97; 110; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]); ([104; 111; 109; 101; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [104; 111; 109; 101; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])]);
   ("__set2", [([6], [6]); ([17], [17])]);
   ("__set3", [([187; 112], [187; 112]); ([187; 117], [187; 117]); ([187; 138], [187; 138]); ([187; 126], [187; 126]); ([187; 127], [187; 127]); ([187; 128], [187; 128]); ([187; 130], [187; 130])]);
   ("__set4", [([108; 97; 110; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [108; 97; 110; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]); ([104; 111; 109; 101; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [104; 111; 109; 101; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])]);
   ("__set5", [([6], [6]); ([17], [17])]);
   ("__set6", [([187; 112], [187; 112]); ([187; 117], [187; 117]); ([187; 138], [187; 138]); ([187; 126], [187; 126]); ([187; 127], [187; 127]); ([187; 128], [187; 128]); ([187; 130], [187; 130])]);
   ("__set7", [([0; 0; 0; 2], [0; 0; 0; 2]); ([0; 0; 0; 4], [0; 0; 0; 4])]);
   ("__set8", [([108; 97; 110; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [108; 97; 110; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]); ([104; 111; 109; 101; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [104; 111; 109; 101; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])]);
   ("__set9", [([0; 22], [0; 22]); ([0; 80], [0; 80]); ([1; 187], [1; 187]); ([4; 222], [4; 222])]);
   ("__set10", [([108; 97; 110; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [108; 97; 110; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]); ([104; 111; 109; 101; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0], [104; 111; 109; 101; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])]);
   ("__set11", [([6], [6]); ([17], [17])]);
   ("__set12", [([116; 115], [116; 118]); ([105; 137], [105; 137]); ([106; 81], [106; 81]); ([31; 107], [31; 107])]);
   ("__set13", [([6], [6]); ([17], [17])]);
   ("__set14", [([0; 0; 0; 2], [0; 0; 0; 2]); ([0; 0; 0; 4], [0; 0; 0; 4])]);
   ("__set15", [([153; 0; 0; 0], [153; 0; 0; 0]); ([0; 1; 0; 0], [0; 1; 0; 0])]);
   ("__set16", [([118; 98; 45; 106; 101; 108; 108; 121; 115; 101; 101; 114; 114; 0; 0; 0], [118; 98; 45; 106; 101; 108; 108; 121; 115; 101; 101; 114; 114; 0; 0; 0]); ([118; 98; 45; 115; 97; 98; 110; 122; 98; 100; 0; 0; 0; 0; 0; 0], [118; 98; 45; 115; 97; 98; 110; 122; 98; 100; 0; 0; 0; 0; 0; 0]); ([118; 98; 45; 114; 97; 100; 97; 114; 0; 0; 0; 0; 0; 0; 0; 0], [118; 98; 45; 114; 97; 100; 97; 114; 0; 0; 0; 0; 0; 0; 0; 0])]);
   ("__set17", [([118; 98; 45; 106; 101; 108; 108; 121; 115; 101; 101; 114; 114; 0; 0; 0], [118; 98; 45; 106; 101; 108; 108; 121; 115; 101; 101; 114; 114; 0; 0; 0]); ([118; 98; 45; 115; 97; 98; 110; 122; 98; 100; 0; 0; 0; 0; 0; 0], [118; 98; 45; 115; 97; 98; 110; 122; 98; 100; 0; 0; 0; 0; 0; 0]); ([118; 98; 45; 114; 97; 100; 97; 114; 0; 0; 0; 0; 0; 0; 0; 0], [118; 98; 45; 114; 97; 100; 97; 114; 0; 0; 0; 0; 0; 0; 0; 0])]);
   ("__set18", [([0; 0; 0; 2], [0; 0; 0; 2]); ([0; 0; 0; 4], [0; 0; 0; 4])])];
   sd_vmaps := [];
   sd_maps := [] |}.

Definition base_env : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => [];
     e_ifaddr := (fun _ => []); e_ifaddr6 := (fun _ => []);
     e_limit := fun _ => 0; e_quota := fun _ => 0; e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

Definition gen_env : env := env_with_sets base_env decls.

(* ===== table inet filter ===== *)

Definition filter_prerouting : chain :=
  {| c_policy := Accept;
   c_rules := [{| r_body := [(BMatch (MEq FMetaIifname [104; 111; 109; 101; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]));
             (BMatch (MEq (FFib "daddr" FRtype) [0; 0; 0; 2]));
             (BMatch (MConcatSet [FMetaL4proto] false "__set0"));
             (BMatch (MEq FThDport [13; 61]));
             (BStmt (SMetaSet MKmark (VImm [153; 0; 0; 0])));
             (BStmt (SLog "[nft:rdppre]"))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MConcatSet [FMetaIifname] false "__set1"));
             (BMatch (MEq (FFib "daddr" FRtype) [0; 0; 0; 2]));
             (BMatch (MConcatSet [FMetaL4proto] false "__set2"));
             (BMatch (MConcatSet [FThDport] false "__set3"));
             (BStmt (SMetaSet MKmark (VImm [153; 0; 0; 0])));
             (BStmt (SLog "[nft:rdppre]"))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MConcatSet [FMetaIifname] false "__set4"));
             (BMatch (MEq (FFib "daddr" FRtype) [0; 0; 0; 2]));
             (BMatch (MConcatSet [FMetaL4proto] false "__set5"));
             (BMatch (MConcatSet [FThDport] false "__set6"));
             (BStmt (SMetaSet MKmark (VImm [153; 0; 0; 0])));
             (BStmt (SLog "[nft:rdppre]"))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}] |}.

Definition filter_postrouting : chain :=
  {| c_policy := Accept;
   c_rules := [{| r_body := [(BMatch (MEq FMetaMark [153; 0; 0; 0]));
             (BStmt (SLog "[nft:rdppost]"))];
     r_verdict := Accept; r_vmap := None;
     r_nat := (Some {| nat_imms := []; nat_field := None; nat_map := None; nat_src := None; nat_kind := "masq"; nat_family := "ip"; nat_amin := None; nat_amax := None; nat_pmin := None; nat_pmax := None; nat_flags := 0 |}); r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}] |}.

Definition filter_input : chain :=
  {| c_policy := Drop;
   c_rules := [{| r_body := [(BMatch (MConcatSet [FCtState] false "__set7"))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaIif [1; 0; 0; 0]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaNfproto [2]));
             (BMatch (MEq FIp4Protocol [1]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaL4proto [58]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaIifname [98; 114; 46; 50; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]));
             (BMatch (MEq FMetaL4proto [6]));
             (BMatch (MEq FThDport [1; 187]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaIifname [98; 114; 46; 50; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]));
             (BMatch (MEq FMetaL4proto [17]));
             (BMatch (MEq FThDport [202; 108]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaIifname [108; 97; 110; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]));
             (BMatch (MEq FMetaNfproto [2]));
             (BMatch (MMasked FIp4Saddr false [255; 255; 255; 0] [0; 0; 0; 0] [192; 168; 50; 0]));
             (BMatch (MEq FMetaL4proto [6]));
             (BMatch (MEq FThDport [8; 1]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaIifname [118; 108; 97; 110; 46; 50; 53; 0; 0; 0; 0; 0; 0; 0; 0; 0]));
             (BMatch (MEq FMetaL4proto [17]));
             (BMatch (MEq FThDport [0; 67]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MConcatSet [FMetaIifname] false "__set8"));
             (BMatch (MEq FMetaL4proto [6]));
             (BMatch (MConcatSet [FThDport] false "__set9"))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MConcatSet [FMetaIifname] false "__set10"));
             (BMatch (MConcatSet [FMetaL4proto] false "__set11"));
             (BMatch (MEq FThDport [85; 240]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaIifname [108; 97; 110; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]));
             (BMatch (MEq FMetaL4proto [6]));
             (BMatch (MConcatSet [FThDport] false "__set12"))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaIifname [108; 97; 110; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]));
             (BMatch (MEq FMetaL4proto [17]));
             (BMatch (MEq FThDport [116; 114]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaIifname [108; 97; 110; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]));
             (BMatch (MEq FMetaL4proto [17]));
             (BMatch (MEq FThDport [178; 179]));
             (BStmt (SLog "[nft:wg]"))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaIifname [105; 109; 109; 105; 99; 104; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]));
             (BMatch (MConcatSet [FMetaL4proto] false "__set13"));
             (BMatch (MEq FThDport [0; 53]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaPkttype [0]));
             (BMatch (MLimit {| ls_rate := 5; ls_unit := 0; ls_burst := 5; ls_bytes := false; ls_flags := 0 |}));
             (BStmt (SCounter 0 0))];
     r_verdict := (Reject 0 0); r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BStmt (SLog "[nft:reject]"));
             (BStmt (SCounter 0 0))];
     r_verdict := Continue; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}] |}.

Definition filter_forward : chain :=
  {| c_policy := Drop;
   c_rules := [{| r_body := [(BStmt (SLog "[forwarding]"))];
     r_verdict := Continue; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaIifname [112; 111; 100; 109; 97; 110]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaIifname [105; 109; 109; 105; 99; 104; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MConcatSet [FCtState] false "__set14"))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MConcatSet [FMetaMark] false "__set15"));
             (BStmt (SLog "[nft:rdpforward]"))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}] |}.

Definition filter_chains : list (string * chain) :=
  [("prerouting", filter_prerouting);
   ("postrouting", filter_postrouting);
   ("input", filter_input);
   ("forward", filter_forward)].

(* ===== table bridge vmfilter ===== *)

Definition vmfilter_vm : chain :=
  {| c_policy := Continue;
   c_rules := [{| r_body := [(BMatch (MEq FMetaIifname [118; 108; 97; 110; 46; 50; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0]));
             (BMatch (MEq FMetaL4proto [17]));
             (BMatch (MEq FThSport [0; 67]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaOifname [118; 108; 97; 110; 46; 50; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MConcatSet [FMetaIifname] false "__set16"));
             (BMatch (MConcatSet [FMetaOifname] false "__set17"))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}] |}.

Definition vmfilter_iot : chain :=
  {| c_policy := Continue;
   c_rules := [{| r_body := [];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}] |}.

Definition vmfilter_cam : chain :=
  {| c_policy := Continue;
   c_rules := [{| r_body := [];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}] |}.

Definition vmfilter_scanner : chain :=
  {| c_policy := Continue;
   c_rules := [{| r_body := [];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}] |}.

Definition vmfilter_output : chain :=
  {| c_policy := Accept;
   c_rules := [{| r_body := [(BMatch (MEq (FMetaGen MKbri_oifname) [98; 114; 46; 50; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]));
             (BMatch (MConcatSet [FIp4Daddr] false "vmaddrs"));
             (BMatch (MConcatSet [FIp4Daddr; FMetaOifname] true "vmantispoof"))];
     r_verdict := Drop; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq (FMetaGen MKbri_oifname) [98; 114; 46; 49; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]));
             (BMatch (MEq FIp4Daddr [192; 168; 100; 2]));
             (BMatch (MNeq FMetaOifname [118; 98; 45; 104; 97; 115; 115; 0; 0; 0; 0; 0; 0; 0; 0; 0]))];
     r_verdict := Drop; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}] |}.

Definition vmfilter_forward : chain :=
  {| c_policy := Drop;
   c_rules := [{| r_body := [(BMatch (MEq FEtherType [8; 6]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MConcatSet [FCtState] false "__set18"))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FIp4Protocol [1]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq FMetaL4proto [58]))];
     r_verdict := Accept; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq (FMetaGen MKbri_iifname) [98; 114; 46; 49; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]))];
     r_verdict := (Goto "iot"); r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq (FMetaGen MKbri_iifname) [98; 114; 46; 50; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]))];
     r_verdict := (Goto "vm"); r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq (FMetaGen MKbri_iifname) [98; 114; 46; 51; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]))];
     r_verdict := (Goto "scanner"); r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BMatch (MEq (FMetaGen MKbri_iifname) [98; 114; 46; 49; 49; 48; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]))];
     r_verdict := (Goto "cam"); r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |};

   {| r_body := [(BStmt (SLog "[nft:bridge]"));
             (BStmt (SCounter 0 0))];
     r_verdict := Continue; r_vmap := None;
     r_nat := None; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}] |}.

Definition vmfilter_chains : list (string * chain) :=
  [("vm", vmfilter_vm);
   ("iot", vmfilter_iot);
   ("cam", vmfilter_cam);
   ("scanner", vmfilter_scanner);
   ("output", vmfilter_output);
   ("forward", vmfilter_forward)].

