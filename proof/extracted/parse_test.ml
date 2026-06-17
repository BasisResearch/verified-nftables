(* Validation harness + CLI for the .nft frontend (TODO 9 / milestone M1).

   With NO arguments (`make parse-test`) it runs three checks:

   (A) Parse ../../ruleset.nft and run the *extracted* DSL semantics
       (Semantics.eval_table) on concrete packets, asserting the verdicts match
       the eight properties proved by hand in ../theories/Example_Ruleset.v.  This
       is an oracle INDEPENDENT of nft: it shows the parser builds an AST that
       *means* what the machine-checked proofs say the ruleset means.

   (B) Parse the ruleset from proof/difftest.sh and assert the resulting `input`
       chain is STRUCTURALLY EQUAL to the hand-built AST in extracted/glue.ml,
       which `make difftest` already shows compiles byte-identically to live nft.
       So the parser inherits that nft-faithfulness, with no nft needed at test
       time (this is where the implicit-l4proto-dependency lowering is pinned).

   (C) Best-effort: if `nft` runs here, also do the live round-trip
       parse |> compile_optimized |> render  vs  `nft --debug=netlink`,
       comparing the `[ ... ]` expression lines (whitespace-normalised).  Skipped
       cleanly if nft/unshare are unavailable.

   With a file argument it acts as a CLI: parse the file and print the compiled
   netlink bytecode of each base chain.  Untrusted glue. *)

module L = Stdlib.List
module S = Stdlib.String

let fails = ref 0
let check name cond =
  Printf.printf "  %-46s %s\n" name (if cond then "ok" else (incr fails; "FAIL"));
  ()

let verdict_str = function
  | Verdict.Accept -> "accept" | Verdict.Drop -> "drop"
  | Verdict.Continue -> "continue" | Verdict.Reject _ -> "reject"
  | Verdict.Queue _ -> "queue" | Verdict.Jump n -> "jump " ^ n
  | Verdict.Goto n -> "goto " ^ n | Verdict.Return -> "return"

(* ---------- concrete packet construction (mirrors semtest.ml) ---------- *)

let dummy0 _ = []
let mk_pkt ~env ?(ct = dummy0) ?(protocol = []) ?(l4proto = []) ?(iifname = [])
           ?(th = []) () : Packet.packet =
  { Packet.pkt_env = env;
    pkt_meta = (fun k -> match k with
      | Packet.MKprotocol -> protocol | Packet.MKl4proto -> l4proto
      | Packet.MKiifname -> iifname | _ -> []);
    pkt_ct = ct; pkt_sock = dummy0;
    pkt_eh = (fun _ _ _ _ _ -> []);
    pkt_lh = []; pkt_nh = []; pkt_th = th; pkt_ih = []; pkt_tnl = [];
    pkt_fibkey = (fun _ -> []);
    pkt_numgen = dummy0; pkt_osf = [];
    pkt_tunnel = (fun _ -> []); pkt_symhash = (fun _ _ -> []);
    pkt_xfrm = (fun _ _ _ -> []); pkt_ctdir = (fun _ _ -> []);
    pkt_inner = (fun _ _ _ _ -> []) }

(* wire constants, matching Example_Ruleset.v *)
let cts_invalid = [0;0;0;1] and cts_established = [0;0;0;2]
and cts_related = [0;0;0;4] and cts_new = [0;0;0;8]
let eth_ip = [8;0] and eth_ip6 = [134;221]
let l4_tcp = [6] and l4_icmp6 = [58]
let if_lo = [108;111] and if_eth = [101;116;104;48]
let icmp6_nd_nsol = [135]
let port n = [n / 256; n mod 256]
let ct_state v = (fun (k : Packet.ct_key) -> match k with Packet.CKstate -> v | _ -> [])
let th_dport p = [0;0] @ port p           (* sport(2) ++ dport(2) *)
let th_icmptype t = [t]                    (* icmp/icmpv6 type at transport offset 0 *)
let ascii s = L.init (S.length s) (fun i -> Char.code (S.get s i))

(* ---------- (A) ruleset.nft vs Example_Ruleset.v ---------- *)

let check_ruleset_nft () =
  Printf.printf "=== (A) ../../ruleset.nft vs Example_Ruleset.v (extracted eval_table) ===\n";
  let parsed = Nft_parse.parse_file "../../ruleset.nft" in
  let env = parsed.Nft_lower.p_env in
  let chains = Nft_lower.chains_of parsed ~table:"firewall" in
  let inbound = Nft_lower.find_chain parsed ~table:"firewall" ~chain:"inbound" in
  let forward = Nft_lower.find_chain parsed ~table:"firewall" ~chain:"forward" in
  let fuel = 8 in
  let run c p = Semantics.eval_table fuel chains c p in
  let want name c p expected =
    let got = run c p in
    Printf.printf "    %-26s -> %-8s (want %s)\n" name (verdict_str got) (verdict_str expected);
    check name (got = expected)
  in
  (* the eight Example_Ruleset.v theorems, as executable packets *)
  want "established_accepted" inbound
    (mk_pkt ~env ~ct:(ct_state cts_established) ()) Verdict.Accept;
  want "invalid_dropped" inbound
    (mk_pkt ~env ~ct:(ct_state cts_invalid) ()) Verdict.Drop;
  want "loopback_accepted" inbound
    (mk_pkt ~env ~ct:(ct_state cts_new) ~iifname:if_lo ()) Verdict.Accept;
  want "ssh_accepted" inbound
    (mk_pkt ~env ~ct:(ct_state cts_new) ~iifname:if_eth ~protocol:eth_ip
       ~l4proto:l4_tcp ~th:(th_dport 22) ()) Verdict.Accept;
  want "smtp_dropped" inbound
    (mk_pkt ~env ~ct:(ct_state cts_new) ~iifname:if_eth ~protocol:eth_ip
       ~l4proto:l4_tcp ~th:(th_dport 25) ()) Verdict.Drop;
  want "ipv6_closed_port_dropped" inbound
    (mk_pkt ~env ~ct:(ct_state cts_new) ~iifname:if_eth ~protocol:eth_ip6
       ~l4proto:l4_tcp ~th:(th_dport 25) ()) Verdict.Drop;
  want "ipv6_nd_accepted" inbound
    (mk_pkt ~env ~ct:(ct_state cts_new) ~iifname:if_eth ~protocol:eth_ip6
       ~l4proto:l4_icmp6 ~th:(th_icmptype 135) ()) Verdict.Accept;
  ignore icmp6_nd_nsol;
  want "forward_drops_all" forward (mk_pkt ~env ()) Verdict.Drop;
  Printf.printf "\n"

(* ---------- (B) difftest ruleset vs glue.ml's known-good AST ---------- *)

let difftest_src =
  "table ip filter {\n\
  \  chain input {\n\
  \    type filter hook input priority 0; policy drop;\n\
  \    tcp dport 22 accept\n\
  \    ip saddr 10.1.2.3 drop\n\
  \    tcp sport 80 accept\n\
  \    ip daddr 192.168.1.1 tcp dport 443 accept\n\
  \  }\n\
  }\n"

(* the hand-built AST from extracted/glue.ml (proven byte-identical to nft) *)
let expected_input_chain : Syntax.chain =
  let bm m = Syntax.BMatch m in
  let meq f v = Syntax.MEq (f, v) in
  let dep = meq Syntax.FMetaL4proto [6] in
  let rule body v : Syntax.rule =
    { Syntax.r_body = body; r_verdict = v; r_vmap = None; r_nat = None;
      r_tproxy = None; r_fwd = None; r_queue = None; r_after = [] } in
  { Syntax.c_policy = Verdict.Drop;
    c_rules = [
      rule [ bm dep; bm (meq Syntax.FThDport [0;22]) ] Verdict.Accept;
      rule [ bm (meq Syntax.FIp4Saddr [10;1;2;3]) ] Verdict.Drop;
      rule [ bm dep; bm (meq Syntax.FThSport [0;80]) ] Verdict.Accept;
      rule [ bm (meq Syntax.FIp4Daddr [192;168;1;1]); bm dep;
             bm (meq Syntax.FThDport [1;187]) ] Verdict.Accept;
    ] }

let check_difftest_ast () =
  Printf.printf "=== (B) difftest.sh ruleset vs glue.ml's known-good AST ===\n";
  let parsed = Nft_parse.parse_string difftest_src in
  let got = Nft_lower.find_chain parsed ~table:"filter" ~chain:"input" in
  check "input chain == hand-built AST" (got = expected_input_chain);
  if got <> expected_input_chain then begin
    Printf.printf "    got %d rules, expected %d\n"
      (L.length got.Syntax.c_rules) (L.length expected_input_chain.Syntax.c_rules)
  end;
  Printf.printf "\n"

(* ---------- (C) best-effort live nft round-trip ---------- *)

let exprs_of (text : string) : string list =
  S.split_on_char '\n' text
  |> L.filter_map (fun ln ->
       let t = S.trim ln in
       if S.length t >= 2 && S.get t 0 = '[' && S.get t 1 = ' ' then Some t else None)

(* `nft --debug=netlink` renders a register value as little-endian 32-bit words,
   zero-padded to a 4-byte boundary (this differs from codec.ml, which targets the
   corpus .t.payload big-endian format).  We render the small instruction subset
   the difftest ruleset uses; an instruction outside it raises Exit -> skip (C). *)
let le_data (d : Bytes.data) : string =
  let a = Stdlib.Array.of_list d in let n = Stdlib.Array.length a in
  let words = (n + 3) / 4 in
  let buf = Buffer.create 16 in
  for w = 0 to words - 1 do
    if w > 0 then Buffer.add_char buf ' ';
    let v = ref 0 in
    for k = 0 to 3 do
      let idx = w * 4 + k in
      let b = if idx < n then Stdlib.Array.get a idx else 0 in
      v := !v lor (b lsl (8 * k))
    done;
    Buffer.add_string buf (Printf.sprintf "0x%08x" !v)
  done;
  Buffer.contents buf

let nl_instr (i : Bytecode.instr) : string = match i with
  | Bytecode.IMetaLoad (k, dst) ->
      Printf.sprintf "[ meta load %s => reg %d ]" (Codec.name_of_meta k) dst
  | Bytecode.IPayloadLoad (b, off, len, dst) ->
      Printf.sprintf "[ payload load %db @ %s header + %d => reg %d ]"
        len (Codec.name_of_base b) off dst
  | Bytecode.ICmp (op, src, v) ->
      Printf.sprintf "[ cmp %s reg %d %s ]" (Codec.cmpop_name op) src (le_data v)
  | Bytecode.IImmediate v ->
      let vn = (match v with Verdict.Accept -> "accept" | Verdict.Drop -> "drop"
                           | Verdict.Continue -> "continue" | _ -> "reject") in
      Printf.sprintf "[ immediate reg 0 %s ]" vn
  | _ -> raise Exit

let render_netlink (prog : Bytecode.program) : string list =
  L.concat_map (fun rp -> L.map nl_instr rp) prog

let check_live_nft () =
  Printf.printf "=== (C) live nft round-trip (best-effort) ===\n";
  let tmp = Filename.temp_file "parsetest" ".nft" in
  let oc = open_out tmp in output_string oc difftest_src; close_out oc;
  let out = Filename.temp_file "parsetest" ".bc" in
  let cmd = Printf.sprintf
    "unshare -rn nft --debug=netlink -f %s > %s 2>/dev/null"
    (Filename.quote tmp) (Filename.quote out) in
  let rc = Sys.command cmd in
  if rc <> 0 then Printf.printf "  SKIP (nft unavailable / no namespace, rc=%d)\n\n" rc
  else begin
    let ic = open_in out in
    let n = in_channel_length ic in
    let nft_text = really_input_string ic n in close_in ic;
    let parsed = Nft_parse.parse_string difftest_src in
    let input = Nft_lower.find_chain parsed ~table:"filter" ~chain:"input" in
    let compile_opt c = Compile.compile_chain (Optimize.optimize_chain c) in
    (match render_netlink (compile_opt input) with
     | exception Exit -> Printf.printf "  SKIP (instruction outside the local renderer)\n"
     | b ->
         let a = exprs_of nft_text in
         check "parse|>compile|>render == nft exprs" (a = b);
         if a <> b then begin
           Printf.printf "    --- nft (%d) ---\n" (L.length a);
           L.iter (fun l -> Printf.printf "    %s\n" l) a;
           Printf.printf "    --- ours (%d) ---\n" (L.length b);
           L.iter (fun l -> Printf.printf "    %s\n" l) b
         end);
    Printf.printf "\n"
  end

(* ---------- (D) optiplex.nft anti-spoofing (extracted eval_table) ----------
   Cross-checks the EXTRACTED parser against the Coq theorems in
   theories/Optiplex_Antispoof.v: parse ../../optiplex.nft, run the extracted
   eval_table on the same spoof / legitimate packets, and assert the verdicts
   the proofs establish (vikunja/gentoo spoofs -> Drop; the bound pair -> Accept).
   The proofs are about nft2coq's emitted AST; this confirms the OCaml runtime
   path agrees with it. *)

(* a bridge frame: obrname / oifname metas + an IPv4 daddr at network offset 16 *)
let mk_bridge ~env ~obrname ~oifname ~daddr : Packet.packet =
  { (mk_pkt ~env ()) with
    Packet.pkt_meta = (fun k -> match k with
      | Packet.MKbri_oifname -> obrname | Packet.MKoifname -> oifname | _ -> []);
    pkt_nh = (Stdlib.List.init 16 (fun _ -> 0)) @ daddr }

let check_optiplex_antispoof () =
  Printf.printf "=== (D) optiplex.nft anti-spoofing vs Optiplex_Antispoof.v ===\n";
  let parsed = Nft_parse.parse_file "../../optiplex.nft" in
  let env = parsed.Nft_lower.p_env in
  let chains = Nft_lower.chains_of parsed ~table:"vmfilter" in
  let output = Nft_lower.find_chain parsed ~table:"vmfilter" ~chain:"output" in
  let run ~obrname ~oifname ~daddr =
    Semantics.eval_table 4 chains output
      (mk_bridge ~env ~obrname:(ascii obrname) ~oifname:(ascii oifname)
         ~daddr) in
  let ip x = [192;168;51;x] in
  let want name v exp =
    Printf.printf "    %-30s -> %-8s (want %s)\n" name (verdict_str v) (verdict_str exp);
    check name (v = exp) in
  (* vikunja (inc-vikun) sending to budget's .20: blocked *)
  want "vikunja_cannot_spoof_budget"
    (run ~obrname:"br.20" ~oifname:"inc-vikun" ~daddr:(ip 20)) Verdict.Drop;
  (* gentoo (vb-gentoo) sending to hass's .10: blocked *)
  want "gentoo_cannot_spoof_hass"
    (run ~obrname:"br.20" ~oifname:"vb-gentoo" ~daddr:(ip 10)) Verdict.Drop;
  (* budget out its OWN interface inc-budge: allowed (policy accept) *)
  want "budget_legitimate_allowed"
    (run ~obrname:"br.20" ~oifname:"inc-budge" ~daddr:(ip 20)) Verdict.Accept;
  (* ADVERSARIAL gaps (Optiplex_Antispoof_Gaps.v): the binding is unenforced
     for any address not in @vmaddrs, and on any egress port other than br.20 *)
  want "GAP: spoof to unlisted .13"
    (run ~obrname:"br.20" ~oifname:"inc-budge" ~daddr:(ip 13)) Verdict.Accept;
  want "GAP: protected .20 via br.3"
    (run ~obrname:"br.3" ~oifname:"vb-evil" ~daddr:(ip 20)) Verdict.Accept;
  Printf.printf "\n"

(* ---------- (E) optiplex.nft firewall mark vs Optiplex_Mark.v ----------
   Parse optiplex.nft and confirm the extracted write/match semantics agree with
   the mark theorems: the prerouting RDP rule sets meta mark to 0x99, and the
   postrouting masquerade rule fires exactly on a 0x99-marked packet. *)

let mark99 = [0;0;0;153]
let data_eq (a : int list) (b : int list) = (a = b)

(* a packet for the prerouting RDP rule: iifname=home, fib daddr type=local
   (via a route returning type=2), tcp, dport 3389 *)
let mk_rdp ~env ~dport : Packet.packet =
  let env_fib =
    { env with Packet.e_routes =
        [ (([0], [255]),
           (fun (r : Packet.fib_result) ->
              match r with Packet.FRtype -> [0;0;0;2] | _ -> [])) ] } in
  { (mk_pkt ~env:env_fib ()) with
    Packet.pkt_meta = (fun k -> match k with
      | Packet.MKiifname -> ascii "home" | Packet.MKl4proto -> [6] | _ -> []);
    pkt_fibkey = (fun _ -> [0]);
    pkt_th = [0;0] @ dport }

(* a packet carrying a given meta mark *)
let mk_marked ~env ~mark : Packet.packet =
  { (mk_pkt ~env ()) with
    Packet.pkt_meta = (fun k -> match k with Packet.MKmark -> mark | _ -> []) }

let check_optiplex_mark () =
  Printf.printf "=== (E) optiplex.nft firewall mark vs Optiplex_Mark.v ===\n";
  let parsed = Nft_parse.parse_file "../../optiplex.nft" in
  let env = parsed.Nft_lower.p_env in
  let pre1  = Stdlib.List.nth
    (Nft_lower.find_chain parsed ~table:"filter" ~chain:"prerouting").Syntax.c_rules 0 in
  let post1 = Stdlib.List.nth
    (Nft_lower.find_chain parsed ~table:"filter" ~chain:"postrouting").Syntax.c_rules 0 in
  (* Property 1: RDP/3389 traffic leaves the prerouting rule marked 0x99 *)
  let marked = Syntax.field_value Syntax.FMetaMark
                 (Semantics.dsl_writes pre1 (mk_rdp ~env ~dport:[13;61])) in
  Printf.printf "    rdp_traffic_marked         -> mark=%s (want 0x99)\n"
    (S.concat ":" (Stdlib.List.map string_of_int marked));
  check "rdp_traffic_marked" (data_eq marked mark99);
  (* Property 1b: non-RDP (dport 22) is not marked (stays unset = []) *)
  let unmarked = Syntax.field_value Syntax.FMetaMark
                   (Semantics.dsl_writes pre1 (mk_rdp ~env ~dport:[0;22])) in
  check "non_rdp_not_marked" (data_eq unmarked []);
  (* Property 2: the masquerade rule is gated on the mark *)
  check "marked_is_masqueraded"
    (Semantics.rule_applies post1 (mk_marked ~env ~mark:mark99) = true);
  check "unmarked_not_masqueraded"
    (Semantics.rule_applies post1 (mk_marked ~env ~mark:[0;0;0;0]) = false);
  (* Property 3: end-to-end — prerouting's mark drives postrouting's masquerade *)
  check "rdp_flow_marks_and_masquerades"
    (Semantics.rule_applies post1
       (Semantics.dsl_writes pre1 (mk_rdp ~env ~dport:[13;61])) = true);
  Printf.printf "\n"

(* ---------- CLI: parse a file and print compiled bytecode ---------- *)

let cli (path : string) =
  let parsed = Nft_parse.parse_file path in
  L.iter (fun (fam, tname, chains) ->
    L.iter (fun (cname, c) ->
      Printf.printf "# table %s %s / chain %s (policy %s)\n"
        fam tname cname (verdict_str c.Syntax.c_policy);
      let prog = Compile.compile_chain (Optimize.optimize_chain c) in
      print_endline (Codec.render_program prog);
      print_newline ())
      chains)
    parsed.Nft_lower.p_tables

let () =
  if Stdlib.Array.length Sys.argv > 1 then cli Sys.argv.(1)
  else begin
    check_ruleset_nft ();
    check_optiplex_antispoof ();
    check_optiplex_mark ();
    check_difftest_ast ();
    check_live_nft ();
    if !fails = 0 then Printf.printf "ALL PARSER CHECKS PASSED\n"
    else (Printf.printf "%d PARSER CHECK(S) FAILED\n" !fails; exit 1)
  end
