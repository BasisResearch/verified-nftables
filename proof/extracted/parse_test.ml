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
    pkt_inner = (fun _ _ _ _ -> []);
    (* a well-formed (non-fragment) packet whose L4 header was parsed, so transport
       payload loads succeed; transport-reading tests pad [th] to its read width *)
    pkt_have_l4 = true; pkt_fragoff = 0 }

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
let th_flags fl = L.init 13 (fun _ -> 0) @ [fl]  (* flags byte at transport+13 *)
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
  (* REGRESSION (NFT_BREAK soundness fix): a packet with NO usable transport header
     (pkt_have_l4 = false, empty pkt_th) must NOT match `tcp dport != 22`; the
     payload read BREAKs (the kernel NFT_BREAKs) so the rule does not fire and the
     packet reaches the chain's `policy accept`.  The OLD truncating model
     spuriously dropped it ([] != [0;22] -> match -> Drop). *)
  let dropneq_chain : Syntax.chain =
    { Syntax.c_policy = Verdict.Accept;
      c_rules = [ { Syntax.r_body = [ Syntax.BMatch (Syntax.MNeq (Syntax.FThDport, [0;22])) ];
                    r_verdict = Verdict.Drop; r_vmap = None; r_nat = None;
                    r_tproxy = None; r_fwd = None; r_queue = None; r_after = [] } ] } in
  let bad_pkt = { (mk_pkt ~env ()) with Packet.pkt_have_l4 = false; pkt_th = [] } in
  want "nft_break: no-L4 tcp dport!=22 -> accept" dropneq_chain bad_pkt Verdict.Accept;
  let frag_pkt = { (mk_pkt ~env ()) with Packet.pkt_fragoff = 8; pkt_th = [9;9;9;9] } in
  want "nft_break: fragment tcp dport!=22 -> accept" dropneq_chain frag_pkt Verdict.Accept;
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
   Parse optiplex.nft and run a packet through WHOLE chains (extracted
   eval_chain_trace / eval_chain_mut), watching the mark the packet carries
   before and after each chain — the end-to-end traversal the proofs establish. *)

let mark99 = [0;0;0;153]
let data_eq (a : int list) (b : int list) = (a = b)
let show d = S.concat ":" (Stdlib.List.map string_of_int d)

(* a streaming packet (dport 48010): iifname=home, fib daddr type=local (via a
   route returning type=2), tcp.  Not the 3389 RDP port — so it flows PAST
   prerouting rule 1 and is marked by rule 2. *)
let mk_pkt_dport ~env ~dport : Packet.packet =
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

let mark_of p = Syntax.field_value Syntax.FMetaMark p

let check_optiplex_mark () =
  Printf.printf "=== (E) optiplex.nft firewall mark vs Optiplex_Mark.v ===\n";
  let parsed = Nft_parse.parse_file "../../optiplex.nft" in
  let env = parsed.Nft_lower.p_env in
  let prerouting  = Nft_lower.find_chain parsed ~table:"filter" ~chain:"prerouting" in
  let postrouting = Nft_lower.find_chain parsed ~table:"filter" ~chain:"postrouting" in
  (* a game-streaming packet enters with NO mark *)
  let p_in = mk_pkt_dport ~env ~dport:[187;138] in   (* dport 48010 *)
  Printf.printf "    packet in:  mark=%s\n" (let m = mark_of p_in in if m=[] then "(unset)" else show m);
  (* traverse the WHOLE prerouting chain; observe the verdict AND the packet out *)
  let (v_pre, p_out) = Semantics.eval_chain_trace prerouting p_in in
  Printf.printf "    prerouting: verdict=%s, packet out mark=%s\n"
    (verdict_str v_pre) (show (mark_of p_out));
  check "prerouting accepts" (v_pre = Verdict.Accept);
  check "prerouting marks the packet 0x99" (data_eq (mark_of p_out) mark99);
  (* carry that packet to postrouting; the mark drives masquerade (accept) *)
  let v_post = Semantics.eval_chain_mut postrouting p_out in
  Printf.printf "    postrouting (on marked packet): verdict=%s\n" (verdict_str v_post);
  check "postrouting accepts the marked packet" (v_post = Verdict.Accept);
  (* and the masquerade rule specifically fires on the marked packet *)
  let post1 = Stdlib.List.nth postrouting.Syntax.c_rules 0 in
  check "masquerade rule fires on mark" (Semantics.rule_applies post1 p_out = true);
  (* masquerade SOURCE-NAT: the packet leaving postrouting has its ip saddr
     rewritten to the address of the interface it exits (e_ifaddr oifname). *)
  let eth0 = ascii "eth0" and eth0_ip = [203;0;113;5] in   (* TEST-NET-3 *)
  let env_if = { env with Packet.e_ifaddr = (fun n -> if n = eth0 then eth0_ip else []) } in
  let p_masq =                                             (* marked, exits eth0 *)
    { (mk_pkt ~env:env_if ()) with
      Packet.pkt_meta = (fun k -> match k with
        | Packet.MKmark -> mark99 | Packet.MKoifname -> eth0 | _ -> []);
      pkt_nh = Stdlib.List.init 20 (fun _ -> 0) } in       (* saddr starts 0.0.0.0 *)
  let saddr_in  = Syntax.field_value Syntax.FIp4Saddr p_masq in
  let (_, p_masq_out) = Semantics.eval_chain_trace postrouting p_masq in
  let saddr_out = Syntax.field_value Syntax.FIp4Saddr p_masq_out in
  Printf.printf "    masquerade: ip saddr  %s -> %s  (eth0's IP)\n"
    (show saddr_in) (show saddr_out);
  check "masquerade rewrites saddr to exit-iface IP" (data_eq saddr_out eth0_ip);
  (* contrast: an RDP/3389 packet is marked at rule 1; an unmarked packet at
     postrouting does NOT masquerade *)
  let (_, p_rdp_out) = Semantics.eval_chain_trace prerouting (mk_pkt_dport ~env ~dport:[13;61]) in
  check "RDP/3389 also marked 0x99" (data_eq (mark_of p_rdp_out) mark99);
  check "unmarked packet not masqueraded"
    (Semantics.rule_applies post1 (mk_pkt ~env ()) = false);
  Printf.printf "\n"

(* (F) dnat DESTINATION-NAT: a parsed `dnat to <ip>` rewrites the packet's IPv4
   destination address (the analogue of masquerade's source rewrite).  Confirms
   the parser lowers dnat into a nat_spec carrying the target in register 1, and
   that Semantics.apply_nat performs NF_NAT_MANIP_DST in the trace. *)
let check_dnat_rewrite () =
  Printf.printf "=== (F) dnat destination-NAT rewrite ===\n";
  let src =
    "table ip nat {\n\
    \  chain prerouting {\n\
    \    type nat hook prerouting priority dstnat; policy accept;\n\
    \    dnat to 10.0.0.1\n\
    \  }\n\
     }\n" in
  let parsed = Nft_parse.parse_string src in
  let env = parsed.Nft_lower.p_env in
  let prerouting = Nft_lower.find_chain parsed ~table:"nat" ~chain:"prerouting" in
  let r0 = Stdlib.List.nth prerouting.Syntax.c_rules 0 in
  check "dnat lowers to a nat_spec (not a bare Accept)" (r0.Syntax.r_nat <> None);
  (* a packet whose destination starts 192.168.0.9 (nh bytes 16..19) *)
  let nh = [0x45;0;0;0; 0;0;0;0; 64;6;0;0; 1;2;3;4; 192;168;0;9] in
  let p_in = { (mk_pkt ~env ()) with Packet.pkt_nh = nh } in
  let daddr_in = Syntax.field_value Syntax.FIp4Daddr p_in in
  let (v, p_out) = Semantics.eval_chain_trace prerouting p_in in
  let daddr_out = Syntax.field_value Syntax.FIp4Daddr p_out in
  Printf.printf "    dnat: ip daddr  %s -> %s  (target 10.0.0.1)\n"
    (show daddr_in) (show daddr_out);
  check "dnat is a terminal accept" (v = Verdict.Accept);
  check "dnat rewrites ip daddr to the target" (data_eq daddr_out [10;0;0;1]);
  check "dnat does NOT touch ip saddr"
    (data_eq (Syntax.field_value Syntax.FIp4Saddr p_out) [1;2;3;4]);
  Printf.printf "\n"

(* (G) FAMILY-AWARE NAT: an ip6 dnat/snat rewrites the 128-bit IPv6 address slot
   (dst @24 len 16 / src @8 len 16, where FIp6Daddr/FIp6Saddr read), NOT the IPv4
   slot.  The kernel picks 32 vs 128 bits by family (nat_addrlen,
   netlink_linearize.c:1237).  Before the fix, apply_nat ignored nat_family and
   spliced a 16-byte literal into the 4-byte IPv4 slot: the IPv6 address was never
   set and the header was shifted by 12 bytes.  No parser surface for ip6 NAT yet,
   so this is built at the Semantics level from a hand spec. *)
let check_ip6_nat () =
  Printf.printf "=== (G) family-aware ip6 NAT rewrite ===\n";
  let tgt6 = Stdlib.List.init 16 (fun _ -> 0xAA) in
  let mk_spec kind =
    { Syntax.nat_imms = [(1, tgt6)]; nat_field = None; nat_map = None;
      nat_src = None; nat_kind = kind; nat_family = Syntax.nat_fam_ip6;
      nat_amin = None; nat_amax = None; nat_pmin = None; nat_pmax = None;
      nat_flags = 0 } in
  let mk_rule sp =
    { Syntax.r_body = []; r_verdict = Verdict.Continue; r_vmap = None;
      r_nat = Some sp; r_tproxy = None; r_fwd = None; r_queue = None;
      r_after = [] } in
  (* a 40-byte IPv6 header: src bytes 8..23, dst bytes 24..39 distinct *)
  let nh = Stdlib.List.init 40 (fun i -> i) in
  let env =
    (Nft_parse.parse_string
       "table ip6 nat {\n  chain c { type nat hook prerouting priority 0; }\n}\n")
      .Nft_lower.p_env in
  let p_in = { (mk_pkt ~env ()) with Packet.pkt_nh = nh } in
  (* ip6 dnat: the IPv6 destination (bytes 24..39) becomes the target *)
  let p_d = Semantics.apply_nat (mk_rule (mk_spec Syntax.nat_dnat_kind)) p_in in
  let d6 = Syntax.field_value Syntax.FIp6Daddr p_d in
  Printf.printf "    ip6 dnat: ip6 daddr -> %s\n" (show d6);
  check "ip6 dnat sets the 16-byte IPv6 destination to the target"
    (data_eq d6 tgt6);
  check "ip6 dnat preserves the network-header length (no shift/corruption)"
    (Stdlib.List.length p_d.Packet.pkt_nh = Stdlib.List.length nh);
  check "ip6 dnat does NOT touch the IPv6 source"
    (data_eq (Syntax.field_value Syntax.FIp6Saddr p_d)
             (Syntax.field_value Syntax.FIp6Saddr p_in));
  (* ip6 snat: the IPv6 source (bytes 8..23) becomes the target *)
  let p_s = Semantics.apply_nat (mk_rule (mk_spec Syntax.nat_snat_kind)) p_in in
  check "ip6 snat sets the 16-byte IPv6 source to the target"
    (data_eq (Syntax.field_value Syntax.FIp6Saddr p_s) tgt6);
  check "ip6 snat preserves the network-header length"
    (Stdlib.List.length p_s.Packet.pkt_nh = Stdlib.List.length nh);
  (* sanity: an ip dnat still rewrites the IPv4 slot (regression for the v4 path) *)
  let v4spec =
    { Syntax.nat_imms = [(1, [10;0;0;1])]; nat_field = None; nat_map = None;
      nat_src = None; nat_kind = Syntax.nat_dnat_kind; nat_family = Syntax.nat_fam_ip4;
      nat_amin = None; nat_amax = None; nat_pmin = None; nat_pmax = None;
      nat_flags = 0 } in
  let p4 = Semantics.apply_nat (mk_rule v4spec) p_in in
  check "ip (v4) dnat still rewrites the IPv4 destination slot"
    (data_eq (Syntax.field_value Syntax.FIp4Daddr p4) [10;0;0;1]);
  Printf.printf "\n"

(* (H) iif/oif NUMERIC INTERFACE-INDEX lowering.  iif/oif read the numeric
   interface INDEX (LMeta MKiif/MKoif).  nft resolves the name to a 4-byte
   host-endian (little-endian on x86) integer at LOAD time and the kernel
   compares the skb's numeric index against it (meta.c ifindex_type; golden
   tests/py/any/meta.t.payload: `meta iif "lo"` => cmp 0x00000001).  The parser
   must lower iif/oif to that index encoding, NOT the ASCII name bytes (which are
   correct only for iifname/oifname). *)
let check_iif_index () =
  Printf.printf "=== (H) iif/oif numeric interface-index lowering ===\n";
  let src =
    "table ip t {\n\
    \  chain c {\n\
    \    type filter hook input priority 0; policy accept;\n\
    \    iif lo accept\n\
    \    iif 7 accept\n\
    \    oif lo accept\n\
    \  }\n\
     }\n" in
  let parsed = Nft_parse.parse_string src in
  let c = Nft_lower.find_chain parsed ~table:"t" ~chain:"c" in
  let env = parsed.Nft_lower.p_env in
  let body i = (Stdlib.List.nth c.Syntax.c_rules i).Syntax.r_body in
  (* `iif lo` => the loopback index 1, little-endian; NOT ASCII "lo" = [108;111] *)
  check "iif lo lowers to numeric index [1;0;0;0] (not ASCII)"
    (body 0 = [Syntax.BMatch (Syntax.MEq (Syntax.FMetaIif, [1;0;0;0]))]);
  (* numeric form `iif 7` => [7;0;0;0] *)
  check "iif 7 lowers to numeric index [7;0;0;0]"
    (body 1 = [Syntax.BMatch (Syntax.MEq (Syntax.FMetaIif, [7;0;0;0]))]);
  (* `oif lo` => FMetaOif with the same index encoding *)
  check "oif lo lowers to numeric index [1;0;0;0] on FMetaOif"
    (body 2 = [Syntax.BMatch (Syntax.MEq (Syntax.FMetaOif, [1;0;0;0]))]);
  (* the lowered matchcond matches a packet that genuinely arrived on lo *)
  let mk_iif idx =
    { (mk_pkt ~env ()) with
      Packet.pkt_meta = (fun k -> match k with Packet.MKiif -> idx | _ -> []) } in
  let m_lo = Syntax.MEq (Syntax.FMetaIif, [1;0;0;0]) in
  check "iif lo matches a packet whose numeric iif = 1 (real nft matches)"
    (Semantics.eval_matchcond m_lo (mk_iif [1;0;0;0]) = true);
  check "iif lo does NOT match a packet on a different iface (index 2)"
    (Semantics.eval_matchcond m_lo (mk_iif [2;0;0;0]) = false);
  check "iif lo does NOT match the impossible ASCII-meta packet"
    (Semantics.eval_matchcond m_lo (mk_iif (ascii "lo")) = false);
  Printf.printf "\n"

(* (I) SINGLE POSITIVE `ct state X` BITMASK lowering.  ct_state has
   .basetype = bitmask_type (ct.c:54), and the relational evaluator
   (evaluate.c:2792-2797) rewrites OP_IMPLICIT over a TYPE_BITMASK basetype to
   OP_EQ for EVERY bitmask type EXCEPT TYPE_CT_STATE.  So a single positive
   `ct state established` stays an implicit bitmask test, emitted (golden
   tests/py/any/ct.t.payload:35-40) as
     [ bitwise reg1 = (reg1 & 0x00000002) ^ 0x0 ]  [ cmp neq reg1 0x0 ]
   i.e. it matches iff (state & 2) != 0, NOT state == 2.  The parser must lower
   it to MMasked (FCtState, neg=true, mask=X, xor=0, val=0), which the model
   evaluates as eval_cmp CNe ((state & X) ^ 0) 0 = (state & X) != 0.  The set
   form `{...}` stays an exact set lookup (MConcatSet) and the negated single
   form `ct state != X` stays a plain cmp neq (MNeq) — both already correct. *)
let check_ct_state () =
  Printf.printf "=== (I) single positive `ct state X` bitmask lowering ===\n";
  let src =
    "table ip t {\n\
    \  chain c {\n\
    \    type filter hook input priority 0; policy accept;\n\
    \    ct state established accept\n\
    \    ct state new accept\n\
    \    ct state != established accept\n\
    \    ct state {established, related} accept\n\
    \  }\n\
     }\n" in
  let parsed = Nft_parse.parse_string src in
  let c = Nft_lower.find_chain parsed ~table:"t" ~chain:"c" in
  let env = parsed.Nft_lower.p_env in
  let body i = (Stdlib.List.nth c.Syntax.c_rules i).Syntax.r_body in
  (* `ct state established` => bitmask test (state & 2) != 0, NOT MEq *)
  check "ct state established lowers to MMasked bitmask test (not MEq)"
    (body 0 = [Syntax.BMatch
       (Syntax.MMasked (Syntax.FCtState, true, [0;0;0;2], [0;0;0;0], [0;0;0;0]))]);
  (* `ct state new` => bitmask test (state & 8) != 0 *)
  check "ct state new lowers to MMasked bitmask test"
    (body 1 = [Syntax.BMatch
       (Syntax.MMasked (Syntax.FCtState, true, [0;0;0;8], [0;0;0;0], [0;0;0;0]))]);
  (* `ct state != established` stays a plain cmp neq (MNeq) — already correct *)
  check "ct state != established stays MNeq (plain cmp neq)"
    (body 2 = [Syntax.BMatch (Syntax.MNeq (Syntax.FCtState, [0;0;0;2]))]);
  (* the set form `{...}` stays an exact set lookup (MConcatSet) *)
  check "ct state {established, related} stays a set lookup (MConcatSet)"
    (match body 3 with
     | [Syntax.BMatch (Syntax.MConcatSet ([Syntax.FCtState], false, _))] -> true
     | _ -> false);
  (* the established rule ACCEPTS a packet with the established bit set together
     with another bit (state = 2|64 = 66) — real nft accepts (66 & 2 = 2 != 0),
     the old MEq model rejected it (66 <> 2). *)
  let m_estab = Syntax.MMasked (Syntax.FCtState, true, [0;0;0;2], [0;0;0;0], [0;0;0;0]) in
  let mk_ct st = mk_pkt ~env ~ct:(ct_state st) () in
  check "ct state established matches state = established|untracked = 66 (real nft accepts)"
    (Semantics.eval_matchcond m_estab (mk_ct [0;0;0;66]) = true);
  check "ct state established matches a pure established state = 2"
    (Semantics.eval_matchcond m_estab (mk_ct [0;0;0;2]) = true);
  check "ct state established does NOT match a state without the established bit (state = 8)"
    (Semantics.eval_matchcond m_estab (mk_ct [0;0;0;8]) = false);
  (* the OLD (buggy) MEq lowering rejects the established|untracked packet *)
  let m_old = Syntax.MEq (Syntax.FCtState, [0;0;0;2]) in
  check "the OLD MEq lowering wrongly rejected state = 66 (regression guard)"
    (Semantics.eval_matchcond m_old (mk_ct [0;0;0;66]) = false);
  Printf.printf "\n"

(* (J) SINGLE POSITIVE `tcp flags X` BITMASK lowering.  tcp_flag_type has
   .basetype = &bitmask_type (proto.c:583-591); the OP_IMPLICIT->OP_EQ rewrite
   (evaluate.c:2792-2797) does NOT fire for it, so a bare `tcp flags X` stays an
   implicit bitmask test, emitted (golden inet/tcp.t.payload:331-337) as
     [ bitwise reg1 = (reg1 & X) ^ 0 ]  [ cmp neq reg1 0 ]
   i.e. (flags & X) != 0, NOT flags == X.  The four written operators differ
   (tests/py/inet/tcp.t:69-74):
     implicit `tcp flags X`    -> MMasked (FTcpFlags, neg=true,  [X], [0], [0])
     bang     `tcp flags ! X`  -> MMasked (FTcpFlags, neg=false, [X], [0], [0])
     explicit `tcp flags == X` -> MEq  (FTcpFlags, [X])
     explicit `tcp flags != X` -> MNeq (FTcpFlags, [X])
   Before the fix `tcp flags` was Unsupported, and the only buildable encoding
   (MEq) wrongly rejected every multi-flag packet (e.g. SYN|ACK for `tcp flags
   syn`). *)
let check_tcp_flags () =
  Printf.printf "=== (J) single positive `tcp flags X` bitmask lowering ===\n";
  let src =
    "table inet t {\n\
    \  chain c {\n\
    \    type filter hook input priority 0; policy accept;\n\
    \    tcp flags syn accept\n\
    \    tcp flags ! syn accept\n\
    \    tcp flags == syn accept\n\
    \    tcp flags != cwr accept\n\
    \  }\n\
     }\n" in
  let parsed = Nft_parse.parse_string src in
  let c = Nft_lower.find_chain parsed ~table:"t" ~chain:"c" in
  let env = parsed.Nft_lower.p_env in
  (* the l4proto-tcp dependency is prepended; the tcp-flags match is the LAST
     body item of each rule *)
  let last_match i =
    let b = (Stdlib.List.nth c.Syntax.c_rules i).Syntax.r_body in
    Stdlib.List.nth b (Stdlib.List.length b - 1) in
  (* `tcp flags syn` => (flags & 0x02) != 0, MMasked neg=true — NOT MEq *)
  check "tcp flags syn lowers to MMasked bitmask test (not MEq)"
    (last_match 0 = Syntax.BMatch
       (Syntax.MMasked (Syntax.FTcpFlags, true, [2], [0], [0])));
  (* `tcp flags ! syn` => (flags & 0x02) == 0, MMasked neg=false *)
  check "tcp flags ! syn lowers to MMasked (flags & syn) == 0"
    (last_match 1 = Syntax.BMatch
       (Syntax.MMasked (Syntax.FTcpFlags, false, [2], [0], [0])));
  (* `tcp flags == syn` => exact equality, MEq *)
  check "tcp flags == syn lowers to exact MEq"
    (last_match 2 = Syntax.BMatch (Syntax.MEq (Syntax.FTcpFlags, [2])));
  (* `tcp flags != cwr` => plain cmp neq, MNeq *)
  check "tcp flags != cwr lowers to plain MNeq"
    (last_match 3 = Syntax.BMatch (Syntax.MNeq (Syntax.FTcpFlags, [128])));
  (* THE KEY behavioural case: a SYN|ACK packet (flags = 0x12 = 18). *)
  let mk_fl fl = mk_pkt ~env ~l4proto:l4_tcp ~th:(th_flags fl) () in
  let m_syn = Syntax.MMasked (Syntax.FTcpFlags, true, [2], [0], [0]) in
  check "tcp flags syn matches a SYN|ACK packet (flags=0x12) — real nft accepts"
    (Semantics.eval_matchcond m_syn (mk_fl 18) = true);
  check "tcp flags syn matches a pure SYN packet (flags=0x02)"
    (Semantics.eval_matchcond m_syn (mk_fl 2) = true);
  check "tcp flags syn does NOT match ACK-only (flags=0x10)"
    (Semantics.eval_matchcond m_syn (mk_fl 16) = false);
  (* the OLD (only buildable) MEq encoding wrongly rejected SYN|ACK *)
  let m_old = Syntax.MEq (Syntax.FTcpFlags, [2]) in
  check "the OLD MEq encoding wrongly rejected SYN|ACK (regression guard)"
    (Semantics.eval_matchcond m_old (mk_fl 18) = false);
  (* explicit `== syn` is genuine equality: rejects SYN|ACK, accepts pure SYN *)
  let m_eq = Syntax.MEq (Syntax.FTcpFlags, [2]) in
  check "tcp flags == syn (explicit) rejects SYN|ACK, accepts pure SYN"
    (Semantics.eval_matchcond m_eq (mk_fl 18) = false
     && Semantics.eval_matchcond m_eq (mk_fl 2) = true);
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
    check_dnat_rewrite ();
    check_ip6_nat ();
    check_iif_index ();
    check_ct_state ();
    check_tcp_flags ();
    check_difftest_ast ();
    check_live_nft ();
    if !fails = 0 then Printf.printf "ALL PARSER CHECKS PASSED\n"
    else (Printf.printf "%d PARSER CHECK(S) FAILED\n" !fails; exit 1)
  end
