(* AUTO-GENERATED from ../../rulesets/optiplex.nft by nft2coq (extracted/nft_emit.ml). DO NOT EDIT.
   This is the parser's SURFACE output as a Coq [sruleset]; the tables,
   chains, hooks and set/map declarations the proofs reason about are the
   VERIFIED lowering [Lower.lower_ruleset] applied to it (no hand-written
   bytes here).  A refused construct fails [optiplex_lowers_ok] (fail-loud). *)

From Stdlib Require Import List String ZArith.
From Nft Require Import Bytes Verdict Packet Bytecode Syntax Semantics Nftval Elab.
From Nft Require Import Surface.Ast Surface.Lower Gen_Support.
Import ListNotations.
Open Scope string_scope.

Definition optiplex_surface : sruleset :=
  [(TopDefine "windows" (sip4 192 168 51 186));

   (TopDefine "lan" (SVSym "lan0"));

   TopNop;

   TopNop;

   (TopTable {| st_family := "inet"; st_name := "filter";
      st_items := [(TChain {| sc_name := "prerouting";
        sc_items := [(ITypeHook "nat" "prerouting" true 100);
         (IPolicy SVaccept);
         (IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "home")) |} |});
           (CMatch {| sm_keys := [["fib"; "daddr"; "type"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "local")) |} |});
           (CMatch {| sm_keys := [["meta"; "l4proto"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVSym "tcp"); (SVSym "udp")]) |} |});
           (CMatch {| sm_keys := [["th"; "dport"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVNum 3389)) |} |});
           (CStmt (StMetaSet "mark" (SVNum 153)));
           (CStmt (StLog "prefix [nft:rdppre]"));
           (CStmt (StDnat (Some (SVVar "windows")) None []))]);
         (IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVVar "lan"); (SVSym "home")]) |} |});
           (CMatch {| sm_keys := [["fib"; "daddr"; "type"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "local")) |} |});
           (CMatch {| sm_keys := [["meta"; "l4proto"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVSym "tcp"); (SVSym "udp")]) |} |});
           (CMatch {| sm_keys := [["th"; "dport"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVNum 47984); (SVNum 47989); (SVNum 48010); (SVNum 47998); (SVNum 47999); (SVNum 48000); (SVNum 48002)]) |} |});
           (CStmt (StMetaSet "mark" (SVNum 153)));
           (CStmt (StLog "prefix [nft:rdppre]"));
           (CStmt (StDnat (Some (SVVar "windows")) None []))]);
         (IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVVar "lan"); (SVSym "home")]) |} |});
           (CMatch {| sm_keys := [["fib"; "daddr"; "type"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "local")) |} |});
           (CMatch {| sm_keys := [["meta"; "l4proto"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVSym "tcp"); (SVSym "udp")]) |} |});
           (CMatch {| sm_keys := [["th"; "dport"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVNum 47984); (SVNum 47989); (SVNum 48010); (SVNum 47998); (SVNum 47999); (SVNum 48000); (SVNum 48002)]) |} |});
           (CStmt (StMetaSet "mark" (SVNum 153)));
           (CStmt (StLog "prefix [nft:rdppre]"));
           (CStmt (StDnat (Some (SVVar "windows")) None []))])] |});
      (TChain {| sc_name := "postrouting";
        sc_items := [(ITypeHook "nat" "postrouting" false 100);
         (IPolicy SVaccept);
         (IRule [(CMatch {| sm_keys := [["mark"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVNum 153)) |} |});
           (CStmt (StLog "prefix [nft:rdppost]"));
           (CStmt (StMasquerade []))])] |});
      (TChain {| sc_name := "input";
        sc_items := [(ITypeHook "filter" "input" false 0);
         (IPolicy SVdrop);
         (IRule [(CMatch {| sm_keys := [["ct"; "state"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVSym "established"); (SVSym "related")]) |} |});
           (CVerdict SVaccept);
           (CStmt (StComment "allow tracked connections"))]);
         (IRule [(CMatch {| sm_keys := [["iif"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "lo")) |} |});
           (CVerdict SVaccept);
           (CStmt (StComment "allow from loopback"))]);
         (IRule [(CMatch {| sm_keys := [["ip"; "protocol"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "icmp")) |} |});
           (CVerdict SVaccept);
           (CStmt (StComment "allow icmp"))]);
         (IRule [(CMatch {| sm_keys := [["meta"; "l4proto"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "ipv6-icmp")) |} |});
           (CVerdict SVaccept);
           (CStmt (StComment "allow icmp v6"))]);
         (IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "br.20")) |} |});
           (CMatch {| sm_keys := [["tcp"; "dport"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "https")) |} |});
           (CVerdict SVaccept);
           (CStmt (StComment "allow incoming https request from the vms"))]);
         (IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "br.20")) |} |});
           (CMatch {| sm_keys := [["udp"; "dport"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVNum 51820)) |} |});
           (CVerdict SVaccept);
           (CStmt (StComment "allow incoming wireguard"))]);
         (IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVVar "lan")) |} |});
           (CMatch {| sm_keys := [["ip"; "saddr"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVPrefix (sip4 192 168 50 0) 24)) |} |});
           (CMatch {| sm_keys := [["tcp"; "dport"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVNum 2049)) |} |});
           (CVerdict SVaccept);
           (CStmt (StComment "give everyone access to nfs share"))]);
         (IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "vlan.25")) |} |});
           (CMatch {| sm_keys := [["udp"; "dport"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVNum 67)) |} |});
           (CVerdict SVaccept);
           (CStmt (StComment "allow incoming printer dhcp request"))]);
         (IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVVar "lan"); (SVSym "home")]) |} |});
           (CMatch {| sm_keys := [["tcp"; "dport"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVSym "ssh"); (SVSym "http"); (SVSym "https"); (SVNum 1246)]) |} |});
           (CVerdict SVaccept);
           (CStmt (StComment "allow services"))]);
         (IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVVar "lan"); (SVSym "home")]) |} |});
           (CMatch {| sm_keys := [["meta"; "l4proto"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVSym "tcp"); (SVSym "udp")]) |} |});
           (CMatch {| sm_keys := [["th"; "dport"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVNum 22000)) |} |});
           (CVerdict SVaccept);
           (CStmt (StComment "allow syncthing"))]);
         (IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVVar "lan")) |} |});
           (CMatch {| sm_keys := [["tcp"; "dport"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVRange (SVNum 29811) (SVNum 29814)); (SVNum 27017); (SVNum 27217); (SVNum 8043)]) |} |});
           (CVerdict SVaccept);
           (CStmt (StComment "allow omada"))]);
         (IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVVar "lan")) |} |});
           (CMatch {| sm_keys := [["udp"; "dport"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVNum 29810)) |} |});
           (CVerdict SVaccept);
           (CStmt (StComment "allow omada"))]);
         (IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVVar "lan")) |} |});
           (CMatch {| sm_keys := [["udp"; "dport"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVNum 45747)) |} |});
           (CStmt (StLog "prefix [nft:wg]"));
           (CVerdict SVaccept);
           (CStmt (StComment "allow wireguard"))]);
         (IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "immich")) |} |});
           (CMatch {| sm_keys := [["meta"; "l4proto"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVSym "tcp"); (SVSym "udp")]) |} |});
           (CMatch {| sm_keys := [["th"; "dport"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVNum 53)) |} |});
           (CVerdict SVaccept)]);
         (IRule [(CMatch {| sm_keys := [["pkttype"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "host")) |} |});
           (CStmt (StLimit 5 "second" false 5 false));
           (CStmt StCounter);
           (CVerdict (SVreject "icmpx type admin-prohibited"))]);
         (IRule [(CStmt (StLog "prefix [nft:reject]"));
           (CStmt StCounter)])] |});
      (TChain {| sc_name := "forward";
        sc_items := [(ITypeHook "filter" "forward" false 0);
         (IPolicy SVdrop);
         (IRule [(CStmt (StLog "prefix [forwarding]"))]);
         (IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "podman*")) |} |});
           (CVerdict SVaccept)]);
         (IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "immich")) |} |});
           (CVerdict SVaccept)]);
         (IRule [(CMatch {| sm_keys := [["ct"; "state"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVSym "established"); (SVSym "related")]) |} |});
           (CVerdict SVaccept);
           (CStmt (StComment "allow tracked connections"))]);
         (IRule [(CMatch {| sm_keys := [["mark"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVNum 153); (SVNum 256)]) |} |});
           (CStmt (StLog "prefix [nft:rdpforward]"));
           (CVerdict SVaccept)])] |})] |});

   (TopTable {| st_family := "bridge"; st_name := "vmfilter";
      st_items := [(TSet {| sd_name := "vmaddrs"; sd_is_map := false; sd_type := ["ipv4_addr"]; sd_flags := ["constant"];
            sd_elements := [((sip4 192 168 51 20), None); ((sip4 192 168 51 14), None); ((sip4 192 168 51 15), None); ((sip4 192 168 51 12), None); ((sip4 192 168 51 10), None); ((sip4 192 168 51 1), None); ((sip4 192 168 51 21), None); ((sip4 192 168 51 22), None); ((sip4 192 168 51 23), None); ((sip4 192 168 51 24), None)] |});
      (TSet {| sd_name := "vmantispoof"; sd_is_map := false; sd_type := ["ipv4_addr"; "ifname"]; sd_flags := ["constant"];
            sd_elements := [((SVConcat [(sip4 192 168 51 20); (SVSym "inc-budge")]), None); ((SVConcat [(sip4 192 168 51 14); (SVSym "inc-vikun")]), None); ((SVConcat [(sip4 192 168 51 15); (SVSym "inc-fresh")]), None); ((SVConcat [(sip4 192 168 51 12); (SVSym "vb-gentoo")]), None); ((SVConcat [(sip4 192 168 51 10); (SVSym "vb-hass")]), None); ((SVConcat [(sip4 192 168 51 1); (SVSym "vlan.20")]), None); ((SVConcat [(sip4 192 168 51 21); (SVSym "vb-memos")]), None); ((SVConcat [(sip4 192 168 51 22); (SVSym "vb-isso")]), None); ((SVConcat [(sip4 192 168 51 23); (SVSym "vb-ntfy")]), None); ((SVConcat [(sip4 192 168 51 24); (SVSym "vb-coll")]), None)] |});
      (TChain {| sc_name := "vm";
        sc_items := [(IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "vlan.20")) |} |});
           (CMatch {| sm_keys := [["udp"; "sport"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVNum 67)) |} |});
           (CVerdict SVaccept)]);
         (IRule [(CMatch {| sm_keys := [["oifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "vlan.20")) |} |});
           (CVerdict SVaccept)]);
         (IRule [(CMatch {| sm_keys := [["iifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVSym "vb-jelly"); (SVSym "vb-sab"); (SVSym "vb-radar")]) |} |});
           (CMatch {| sm_keys := [["oifname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVSym "vb-jelly"); (SVSym "vb-sab"); (SVSym "vb-radar")]) |} |});
           (CVerdict SVaccept)])] |});
      (TChain {| sc_name := "iot";
        sc_items := [(IRule [(CVerdict SVaccept)])] |});
      (TChain {| sc_name := "cam";
        sc_items := [(IRule [(CVerdict SVaccept)])] |});
      (TChain {| sc_name := "scanner";
        sc_items := [(IRule [(CVerdict SVaccept)])] |});
      (TChain {| sc_name := "output";
        sc_items := [(ITypeHook "filter" "output" false 0);
         (IPolicy SVaccept);
         (IRule [(CMatch {| sm_keys := [["meta"; "obrname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "br.20")) |} |});
           (CMatch {| sm_keys := [["ip"; "daddr"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEref "vmaddrs") |} |});
           (CMatch {| sm_keys := [["ip"; "daddr"]; ["oifname"]]; sm_rhs := {| sr_op := SOpNe; sr_neg := true; sr_payload := (SSEref "vmantispoof") |} |});
           (CVerdict SVdrop)]);
         (IRule [(CMatch {| sm_keys := [["meta"; "obrname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "br.1")) |} |});
           (CMatch {| sm_keys := [["ip"; "daddr"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (sip4 192 168 100 2)) |} |});
           (CMatch {| sm_keys := [["oifname"]]; sm_rhs := {| sr_op := SOpNe; sr_neg := true; sr_payload := (SSEvalue (SVSym "vb-hass")) |} |});
           (CVerdict SVdrop)])] |});
      (TChain {| sc_name := "forward";
        sc_items := [(ITypeHook "filter" "forward" false 0);
         (IPolicy SVdrop);
         (IRule [(CMatch {| sm_keys := [["ether"; "type"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "arp")) |} |});
           (CVerdict SVaccept)]);
         (IRule [(CMatch {| sm_keys := [["ct"; "state"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEset [(SVSym "established"); (SVSym "related")]) |} |});
           (CVerdict SVaccept)]);
         (IRule [(CMatch {| sm_keys := [["ip"; "protocol"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "icmp")) |} |});
           (CVerdict SVaccept);
           (CStmt (StComment "allow icmp"))]);
         (IRule [(CMatch {| sm_keys := [["meta"; "l4proto"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "ipv6-icmp")) |} |});
           (CVerdict SVaccept);
           (CStmt (StComment "allow icmp v6"))]);
         (IRule [(CMatch {| sm_keys := [["meta"; "ibrname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "br.1")) |} |});
           (CVerdict (SVgoto "iot"))]);
         (IRule [(CMatch {| sm_keys := [["meta"; "ibrname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "br.20")) |} |});
           (CVerdict (SVgoto "vm"))]);
         (IRule [(CMatch {| sm_keys := [["meta"; "ibrname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "br.3")) |} |});
           (CVerdict (SVgoto "scanner"))]);
         (IRule [(CMatch {| sm_keys := [["meta"; "ibrname"]]; sm_rhs := {| sr_op := SOpImplicit; sr_neg := false; sr_payload := (SSEvalue (SVSym "br.110")) |} |});
           (CVerdict (SVgoto "cam"))])] |})] |})].

Definition ifindex_pins (s : string) : option nat :=
  if String.eqb s "lo" then Some 1%nat else None.

Example optiplex_lowers_ok : lower_ok ifindex_pins optiplex_surface = true.
Proof. vm_compute. reflexivity. Qed.

Definition optiplex_lowered : lowered_ruleset :=
  Eval vm_compute in lower_or_empty ifindex_pins optiplex_surface.

Definition decls : set_decls := Eval vm_compute in lr_set_decls optiplex_lowered.

Definition base_env : env :=
  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];
     e_routes := []; e_rt := fun _ => [];
     e_ifaddrs := (fun _ => []); e_ifaddrs6 := (fun _ => []);
     e_limit := fun _ => 0; e_quota := fun _ => 0; e_connlimit := fun _ => [];
     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.

Definition gen_env : env := env_with_sets base_env decls.

(* ===== table inet filter ===== *)

Definition filter_prerouting : chain :=
  Eval vm_compute in lr_chain_of optiplex_lowered "filter" "prerouting".

Definition filter_postrouting : chain :=
  Eval vm_compute in lr_chain_of optiplex_lowered "filter" "postrouting".

Definition filter_input : chain :=
  Eval vm_compute in lr_chain_of optiplex_lowered "filter" "input".

Definition filter_forward : chain :=
  Eval vm_compute in lr_chain_of optiplex_lowered "filter" "forward".

Definition filter_chains : list (string * chain) :=
  Eval vm_compute in lr_chains_of optiplex_lowered "filter".

Definition filter_hooks : list hooked_chain :=
  Eval vm_compute in lr_hooks_of optiplex_lowered "filter".

(* ===== table bridge vmfilter ===== *)

Definition vmfilter_vm : chain :=
  Eval vm_compute in lr_chain_of optiplex_lowered "vmfilter" "vm".

Definition vmfilter_iot : chain :=
  Eval vm_compute in lr_chain_of optiplex_lowered "vmfilter" "iot".

Definition vmfilter_cam : chain :=
  Eval vm_compute in lr_chain_of optiplex_lowered "vmfilter" "cam".

Definition vmfilter_scanner : chain :=
  Eval vm_compute in lr_chain_of optiplex_lowered "vmfilter" "scanner".

Definition vmfilter_output : chain :=
  Eval vm_compute in lr_chain_of optiplex_lowered "vmfilter" "output".

Definition vmfilter_forward : chain :=
  Eval vm_compute in lr_chain_of optiplex_lowered "vmfilter" "forward".

Definition vmfilter_chains : list (string * chain) :=
  Eval vm_compute in lr_chains_of optiplex_lowered "vmfilter".

Definition vmfilter_hooks : list hooked_chain :=
  Eval vm_compute in lr_hooks_of optiplex_lowered "vmfilter".

