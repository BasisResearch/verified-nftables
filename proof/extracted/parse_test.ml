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
let mk_pkt ~env ?(ct = dummy0) ?(protocol = []) ?(l4proto = []) ?(nfproto = [])
           ?(iifname = []) ?(th = []) ?(flow = []) () : Packet.packet =
  { Packet.pkt_env = env;
    pkt_meta = (fun k -> match k with
      | Packet.MKprotocol -> protocol | Packet.MKl4proto -> l4proto
      | Packet.MKnfproto -> nfproto
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
    pkt_have_l2 = true;
    pkt_have_l4 = true; pkt_fragoff = 0; pkt_flow = flow; pkt_untracked = false;
    pkt_ctdir_orig = true }

(* wire constants, matching Example_Ruleset.v *)
let cts_invalid = [0;0;0;1] and cts_established = [0;0;0;2]
and cts_related = [0;0;0;4] and cts_new = [0;0;0;8]
let eth_ip = [8;0] and eth_ip6 = [134;221]
let l4_tcp = [6] and l4_icmp6 = [58]
(* 16-byte (IFNAMSIZ) zero-padded ifname registers, matching the kernel's
   full-buffer exact compare. *)
let if_lo  = [108;111; 0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0]          (* "lo" *)
and if_eth = [101;116;104;48; 0;0;0;0; 0;0;0;0; 0;0;0;0]        (* "eth0" *)
let icmp6_nd_nsol = [135]
let port n = [n / 256; n mod 256]
let ct_state v = (fun (k : Packet.ct_key) -> match k with Packet.CKstate -> v | _ -> [])
let th_dport p = [0;0] @ port p           (* sport(2) ++ dport(2) *)
let th_flags fl = L.init 13 (fun _ -> 0) @ [fl]  (* flags byte at transport+13 *)
let th_icmptype t = [t]                    (* icmp/icmpv6 type at transport offset 0 *)
let ascii s = L.init (S.length s) (fun i -> Char.code (S.get s i))
(* An interface-name register is a fixed 16-byte (IFNAMSIZ) zero-padded buffer;
   the kernel compares the full 16 bytes for an exact name match, so a packet's
   iif/oif/obr/ibr name register holds the name zero-padded to 16 bytes. *)
let ifname16 s =
  let b = ascii s in
  let n = L.length b in
  if n >= 16 then b else b @ L.init (16 - n) (fun _ -> 0)

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
  (* a genuine IPv6 packet has nfproto = NFPROTO_IPV6 = 10; the inet icmpv6 rule
     now carries the implicit `meta nfproto == 10` guard (icmpv6 is IPv6-only). *)
  want "ipv6_nd_accepted" inbound
    (mk_pkt ~env ~ct:(ct_state cts_new) ~iifname:if_eth ~protocol:eth_ip6
       ~nfproto:[10] ~l4proto:l4_icmp6 ~th:(th_icmptype 135) ()) Verdict.Accept;
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
      (mk_bridge ~env ~obrname:(ifname16 obrname) ~oifname:(ifname16 oifname)
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

let mark99 = [153;0;0;0]   (* 0x99 host-endian (little-endian), matching the LE meta/ct mark encoding *)
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
      | Packet.MKiifname -> ifname16 "home" | Packet.MKl4proto -> [6] | _ -> []);
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
  let (v_pre, p_out) = Semantics.eval_chain_trace Semantics.Hprerouting prerouting p_in in
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
  let (_, p_masq_out) = Semantics.eval_chain_trace Semantics.Hpostrouting postrouting p_masq in
  let saddr_out = Syntax.field_value Syntax.FIp4Saddr p_masq_out in
  Printf.printf "    masquerade: ip saddr  %s -> %s  (eth0's IP)\n"
    (show saddr_in) (show saddr_out);
  check "masquerade rewrites saddr to exit-iface IP" (data_eq saddr_out eth0_ip);
  (* contrast: an RDP/3389 packet is marked at rule 1; an unmarked packet at
     postrouting does NOT masquerade *)
  let (_, p_rdp_out) = Semantics.eval_chain_trace Semantics.Hprerouting prerouting (mk_pkt_dport ~env ~dport:[13;61]) in
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
  let (v, p_out) = Semantics.eval_chain_trace Semantics.Hprerouting prerouting p_in in
  let daddr_out = Syntax.field_value Syntax.FIp4Daddr p_out in
  Printf.printf "    dnat: ip daddr  %s -> %s  (target 10.0.0.1)\n"
    (show daddr_in) (show daddr_out);
  check "dnat is a terminal accept" (v = Verdict.Accept);
  check "dnat rewrites ip daddr to the target" (data_eq daddr_out [10;0;0;1]);
  check "dnat does NOT touch ip saddr"
    (data_eq (Syntax.field_value Syntax.FIp4Saddr p_out) [1;2;3;4]);
  (* The IPv4 HEADER CHECKSUM (network bytes 10..11) is NOT left stale: the kernel
     runs csum_replace4(&iph->check, old_daddr, new_daddr) in the same step as the
     address rewrite (nf_nat_proto.c:329-333).  The model now updates it
     incrementally (RFC 1624) via set_nh_addr_ip4/csum_update_field. *)
  let ipck_in  = Packet.slice p_in.Packet.pkt_nh  10 2 in
  let ipck_out = Packet.slice p_out.Packet.pkt_nh 10 2 in
  let ipck_exp = Bytes.csum_update_field ipck_in [192;168;0;9] [10;0;0;1] in
  Printf.printf "    dnat: ip checksum  %s -> %s  (csum_replace4; expected %s)\n"
    (show ipck_in) (show ipck_out) (show ipck_exp);
  check "dnat UPDATES the IPv4 header checksum (not left stale)"
    (not (data_eq ipck_out ipck_in));
  check "dnat IP checksum is the RFC-1624 incremental update (csum_replace4)"
    (data_eq ipck_out ipck_exp);
  (* (F') `dnat to A:PORT` ALSO rewrites the L4 DESTINATION port (transport bytes
     2..3).  The parser must carry the port into nat_pmin/nat_pmax, and
     Semantics.apply_nat must write the big-endian port into the TCP/UDP header
     (kernel nft_nat.c:57-60 + nf_nat_proto.c). *)
  let src_p =
    "table ip nat {\n\
    \  chain prerouting {\n\
    \    type nat hook prerouting priority dstnat; policy accept;\n\
    \    dnat to 10.0.0.1:8080\n\
    \  }\n\
     }\n" in
  let parsed_p = Nft_parse.parse_string src_p in
  let env_p = parsed_p.Nft_lower.p_env in
  let pre_p = Nft_lower.find_chain parsed_p ~table:"nat" ~chain:"prerouting" in
  let rp = Stdlib.List.nth pre_p.Syntax.c_rules 0 in
  let ns = match rp.Syntax.r_nat with Some n -> n | None -> failwith "no nat_spec" in
  check "dnat to A:PORT carries the port into nat_pmin" (ns.Syntax.nat_pmin = Some 8080);
  check "dnat to A:PORT carries the port into nat_pmax" (ns.Syntax.nat_pmax = Some 8080);
  (* a packet with dport=80 in the transport header (bytes 2..3 = [0;80]) *)
  let th = [0;0; 0;80; 0;0;0;0] in
  let p_in2 = { (mk_pkt ~env:env_p ()) with Packet.pkt_nh = nh; pkt_th = th } in
  let dport_in = Packet.read_payload Packet.PTransport 2 2 p_in2 in
  let (_, p_out2) = Semantics.eval_chain_trace Semantics.Hprerouting pre_p p_in2 in
  let dport_out = Packet.read_payload Packet.PTransport 2 2 p_out2 in
  Printf.printf "    dnat:port: th dport  %s -> %s  (target :8080 = 0x1f90)\n"
    (show dport_in) (show dport_out);
  check "dnat to A:PORT rewrites th dport to the big-endian port (8080=0x1f90)"
    (data_eq dport_out [0x1f; 0x90]);
  check "dnat to A:PORT also rewrites ip daddr to the address operand"
    (data_eq (Syntax.field_value Syntax.FIp4Daddr p_out2) [10;0;0;1]);
  (* (F'') PORT-ONLY `dnat to :PORT`: the kernel sets only the proto register
     (NFTNL_EXPR_NAT_REG_PROTO_MIN), NOT the addr register, so nft_nat_eval
     rewrites ONLY the L4 destination port and leaves the L3 destination ADDRESS
     byte-for-byte unchanged (nft_nat.c:114 vs :120, two independent register
     guards).  Previously the parser dropped this to a bare Accept; and the
     Semantics, if it lowered, spliced an EMPTY address slot, deleting 4 bytes of
     the IP header.  Now it must preserve daddr and rewrite only dport. *)
  let src_po =
    "table ip nat {\n\
    \  chain prerouting {\n\
    \    type nat hook prerouting priority dstnat; policy accept;\n\
    \    dnat to :80\n\
    \  }\n\
     }\n" in
  let parsed_po = Nft_parse.parse_string src_po in
  let env_po = parsed_po.Nft_lower.p_env in
  let pre_po = Nft_lower.find_chain parsed_po ~table:"nat" ~chain:"prerouting" in
  let rpo = Stdlib.List.nth pre_po.Syntax.c_rules 0 in
  let nso = match rpo.Syntax.r_nat with
    | Some n -> n | None -> failwith "port-only dnat dropped to bare Accept" in
  check "dnat to :PORT lowers to a real nat_spec (not a bare Accept)"
    (rpo.Syntax.r_nat <> None);
  check "dnat to :PORT carries the port into nat_pmin" (nso.Syntax.nat_pmin = Some 80);
  check "dnat to :PORT has NO address operand (nat_has_addr = false)"
    (Semantics.nat_has_addr nso = false);
  let th_po = [0;0; 0;25; 0;0;0;0] in
  let p_in3 = { (mk_pkt ~env:env_po ()) with Packet.pkt_nh = nh; pkt_th = th_po } in
  let daddr_in3 = Syntax.field_value Syntax.FIp4Daddr p_in3 in
  let (_, p_out3) = Semantics.eval_chain_trace Semantics.Hprerouting pre_po p_in3 in
  let daddr_out3 = Syntax.field_value Syntax.FIp4Daddr p_out3 in
  let dport_out3 = Packet.read_payload Packet.PTransport 2 2 p_out3 in
  Printf.printf "    dnat :80: ip daddr  %s -> %s (preserved); th dport -> %s (= 0x0050)\n"
    (show daddr_in3) (show daddr_out3) (show dport_out3);
  check "dnat to :PORT PRESERVES ip daddr (no address rewrite, no header truncation)"
    (data_eq daddr_out3 daddr_in3);
  check "dnat to :PORT preserves the network-header length (no 4-byte deletion)"
    (Stdlib.List.length p_out3.Packet.pkt_nh = Stdlib.List.length nh);
  check "dnat to :PORT rewrites th dport to the big-endian port (80=0x0050)"
    (data_eq dport_out3 [0x00; 0x50]);
  (* (F''') FLOW-STATEFUL NAT: the mapping is established ONCE on the first packet of
     a flow and STORED in the conntrack entry (kernel nf_nat_setup_info:
     get_unique_tuple + nf_conntrack_alter_reply on the UNCONFIRMED packet,
     nf_nat_core.c:778-803); every LATER (confirmed) packet of the same flow reuses
     the STORED tuple WITHOUT re-evaluating the rule operand (returns NF_ACCEPT,
     rewrite from stored tuple via nf_nat_manip_pkt).  The model now mirrors this:
     env carries a flow-keyed e_nat table; apply_nat computes+stores on the first
     packet (e_nat flow = None) and reuses on later packets (e_nat flow = Some m).
     We use `dnat to ip saddr` — an operand that VARIES per packet — so the fix is
     observable: two same-flow packets with different saddrs get the SAME (packet-1)
     destination.  Built at the Semantics level (no parser surface for `to ip saddr`). *)
  let dnat_saddr_spec : Syntax.nat_spec =
    { Syntax.nat_imms = []; nat_field = Some (Syntax.FIp4Saddr, []); nat_map = None;
      nat_src = None; nat_kind = Syntax.nat_dnat_kind; nat_family = Syntax.nat_fam_ip4;
      nat_amin = None; nat_amax = None; nat_pmin = None; nat_pmax = None; nat_flags = 0 } in
  let dnat_saddr_rule : Syntax.rule =
    { Syntax.r_body = []; r_verdict = Verdict.Accept; r_vmap = None;
      r_nat = Some dnat_saddr_spec; r_tproxy = None; r_fwd = None;
      r_queue = None; r_after = [] } in
  let dnat_saddr_chain : Syntax.chain =
    { Syntax.c_policy = Verdict.Drop; c_rules = [dnat_saddr_rule] } in
  let flow0 = [7;7] in
  (* a 20-byte IPv4 header with the given source address @12..15 (dst @16..19) *)
  let mk_nh saddr = [0x45;0;0;20; 0;0;0;0; 64;6;0;0] @ saddr @ [9;9;9;9] in
  (* packet 1 of the flow: saddr 1.1.1.1 — establishes + stores the mapping *)
  let f1 = { (mk_pkt ~env ~flow:flow0 ()) with Packet.pkt_nh = mk_nh [1;1;1;1];
             pkt_have_l4 = false } in
  let (_, f1_out) =
    Semantics.eval_chain_trace Semantics.Hprerouting dnat_saddr_chain f1 in
  let d1 = Syntax.field_value Syntax.FIp4Daddr f1_out in
  check "dnat to ip saddr: packet 1 dnat's dst to its own saddr (1.1.1.1)"
    (data_eq d1 [1;1;1;1]);
  check "the NAT mapping is STORED in the flow-keyed e_nat after packet 1"
    ((f1_out.Packet.pkt_env).Packet.e_nat flow0
       = Some ((Some [9;9;9;9], Some [1;1;1;1]), None));
  (* packet 2 of the SAME flow: DIFFERENT saddr 2.2.2.2, threaded through the env
     packet 1 left — it must reuse packet 1's STORED destination (1.1.1.1), NOT its
     own saddr.  This is the property that was UNSOUND (provably divergent) before. *)
  let f2 = { (mk_pkt ~env:(f1_out.Packet.pkt_env) ~flow:flow0 ())
             with Packet.pkt_nh = mk_nh [2;2;2;2]; pkt_have_l4 = false } in
  let (_, f2_out) =
    Semantics.eval_chain_trace Semantics.Hprerouting dnat_saddr_chain f2 in
  let d2 = Syntax.field_value Syntax.FIp4Daddr f2_out in
  Printf.printf "    dnat-to-saddr flow: pkt1 dst=%s  pkt2 dst=%s (same stored mapping)\n"
    (show d1) (show d2);
  check "packet 2 of the SAME flow reuses packet 1's STORED dnat dst (1.1.1.1, kernel-correct)"
    (data_eq d2 [1;1;1;1]);
  check "packet 2 does NOT dnat to its OWN saddr (2.2.2.2) — operand not re-evaluated"
    (not (data_eq d2 [2;2;2;2]));
  (* a packet on a DIFFERENT flow establishes its OWN mapping (flow-scoped) *)
  let g = { (mk_pkt ~env:(f1_out.Packet.pkt_env) ~flow:[8;8] ())
            with Packet.pkt_nh = mk_nh [2;2;2;2]; pkt_have_l4 = false } in
  let (_, g_out) =
    Semantics.eval_chain_trace Semantics.Hprerouting dnat_saddr_chain g in
  check "a DIFFERENT flow establishes its own mapping (dnat dst = its own saddr 2.2.2.2)"
    (data_eq (Syntax.field_value Syntax.FIp4Daddr g_out) [2;2;2;2]);
  (* REPLY-DIRECTION un-NAT (Round-5 fix): a fixed `dnat to 8.8.8.8` establishes the
     mapping on the original-direction packet (client 1.1.1.1 -> router 9.9.9.9 =>
     dst 8.8.8.8).  The REPLY packet of the SAME flow (server 8.8.8.8 -> client
     1.1.1.1, pkt_ctdir_orig = false) must have its SOURCE un-DNAT'd back to 9.9.9.9
     and its DESTINATION left untouched — the kernel's nf_nat_packet direction
     inversion.  Before the fix the model re-applied the forward dnat forward (reply
     dst -> 8.8.8.8) and left the reply src stale. *)
  let dnat88_spec : Syntax.nat_spec =
    { Syntax.nat_imms = [(1, [8;8;8;8])]; nat_field = None; nat_map = None;
      nat_src = None; nat_kind = Syntax.nat_dnat_kind; nat_family = Syntax.nat_fam_ip4;
      nat_amin = None; nat_amax = None; nat_pmin = None; nat_pmax = None; nat_flags = 0 } in
  let dnat88_rule : Syntax.rule =
    { Syntax.r_body = []; r_verdict = Verdict.Accept; r_vmap = None;
      r_nat = Some dnat88_spec; r_tproxy = None; r_fwd = None;
      r_queue = None; r_after = [] } in
  let dnat88_chain : Syntax.chain =
    { Syntax.c_policy = Verdict.Drop; c_rules = [dnat88_rule] } in
  let rflow = [3;3] in
  let fwd_in = { (mk_pkt ~env ~flow:rflow ())
                 with Packet.pkt_nh = mk_nh [1;1;1;1]; pkt_have_l4 = false } in
  let (_, fwd_out) =
    Semantics.eval_chain_trace Semantics.Hprerouting dnat88_chain fwd_in in
  check "reply-dir: forward packet dnat's dst 9.9.9.9 -> 8.8.8.8"
    (data_eq (Syntax.field_value Syntax.FIp4Daddr fwd_out) [8;8;8;8]);
  (* reply packet, threaded through the env the forward packet established *)
  let rep_in = { (mk_pkt ~env:(fwd_out.Packet.pkt_env) ~flow:rflow ())
                 with Packet.pkt_nh = mk_nh [8;8;8;8];
                 pkt_have_l4 = false; pkt_ctdir_orig = false } in
  (* mk_nh appends [9;9;9;9] as the dst; the reply's dst should be the client. Build
     the reply with dst = client 1.1.1.1 explicitly. *)
  let rep_in = { rep_in with Packet.pkt_nh =
                 [0x45;0;0;20; 0;0;0;0; 64;6;0;0] @ [8;8;8;8] @ [1;1;1;1] } in
  let (_, rep_out) =
    Semantics.eval_chain_trace Semantics.Hprerouting dnat88_chain rep_in in
  check "reply-dir: reply SOURCE un-DNAT'd 8.8.8.8 -> 9.9.9.9 (inverse manip)"
    (data_eq (Syntax.field_value Syntax.FIp4Saddr rep_out) [9;9;9;9]);
  check "reply-dir: reply DESTINATION left untouched (1.1.1.1)"
    (data_eq (Syntax.field_value Syntax.FIp4Daddr rep_out) [1;1;1;1]);
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
  let p_d = Semantics.apply_nat Semantics.Hprerouting (mk_rule (mk_spec Syntax.nat_dnat_kind)) p_in in
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
  let p_s = Semantics.apply_nat Semantics.Hprerouting (mk_rule (mk_spec Syntax.nat_snat_kind)) p_in in
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
  let p4 = Semantics.apply_nat Semantics.Hprerouting (mk_rule v4spec) p_in in
  check "ip (v4) dnat still rewrites the IPv4 destination slot"
    (data_eq (Syntax.field_value Syntax.FIp4Daddr p4) [10;0;0;1]);
  (* --- ip6 masquerade is FAMILY-AWARE end-to-end (the kernel dispatches by
     family: nft_masq.c NFPROTO_IPV6 -> nf_nat_masquerade_ipv6, which rewrites the
     whole 16-byte IPv6 source via ipv6_dev_get_saddr).  `ip6 masquerade` is valid
     and in the corpus (tests/py/ip6/masquerade.t).  Before the fix the parser
     lowered masquerade with nat_family = "" (family-blind), and apply_nat spliced
     the 4-byte IPv4 e_ifaddr into the middle of the IPv6 source. --- *)
  let parsed6 =
    Nft_parse.parse_string
      "table ip6 nat {\n\
      \  chain post {\n\
      \    type nat hook postrouting priority srcnat; policy accept;\n\
      \    masquerade\n\
      \  }\n\
       }\n" in
  let post6 = Nft_lower.find_chain parsed6 ~table:"nat" ~chain:"post" in
  let mr = Stdlib.List.nth post6.Syntax.c_rules 0 in
  (match mr.Syntax.r_nat with
   | Some ns ->
       check "ip6 masquerade lowers to nat_family = \"ip6\" (was \"\", family-blind)"
         (ns.Syntax.nat_family = Syntax.nat_fam_ip6)
   | None -> check "ip6 masquerade lowers to a nat_spec" false);
  (* the exit interface's IPv6 address (16 bytes, all 0xBB) via e_ifaddr6; the IPv4
     e_ifaddr is a DIFFERENT value, to prove masquerade picks the IPv6 one *)
  let if6 = Stdlib.List.init 16 (fun _ -> 0xBB) in
  let env6 = parsed6.Nft_lower.p_env in
  let env6 = { env6 with Packet.e_ifaddr = (fun _ -> [9;9;9;9]);
                         e_ifaddr6 = (fun _ -> if6) } in
  let p6 = { (mk_pkt ~env:env6 ()) with Packet.pkt_nh = nh } in
  let src6_in = Syntax.field_value Syntax.FIp6Saddr p6 in
  let (_, p6_out) = Semantics.eval_chain_trace Semantics.Hpostrouting post6 p6 in
  let src6_out = Syntax.field_value Syntax.FIp6Saddr p6_out in
  Printf.printf "    ip6 masquerade: ip6 saddr  %s -> %s  (exit iface's IPv6)\n"
    (show src6_in) (show src6_out);
  check "ip6 masquerade rewrites the FULL 16-byte IPv6 source to e_ifaddr6"
    (data_eq src6_out if6);
  check "ip6 masquerade preserves the network-header length (no shift/corruption)"
    (Stdlib.List.length p6_out.Packet.pkt_nh = Stdlib.List.length nh);
  check "ip6 masquerade does NOT use the 4-byte IPv4 e_ifaddr"
    (not (data_eq src6_out [9;9;9;9]));
  Printf.printf "\n"

(* (G') HOOK-DEPENDENT redirect.  `redirect` is a destination-NAT whose target
   the kernel core picks by the HOOK (nf_nat_redirect_ipv4/ipv6, branch on
   hooknum): at the OUTPUT hook (NF_INET_LOCAL_OUT) "local packets go to
   loopback" (127.0.0.1 / ::1); at PRE_ROUTING it uses the inbound interface's
   primary address.  nft_redir_validate permits exactly {prerouting, output}.
   Semantics.apply_nat now threads the hook; before the fix it was hook-blind and
   always used the iif address, which is kernel-incorrect at the output hook. *)
let check_redir_hook () =
  Printf.printf "=== (G') hook-dependent redirect destination ===\n";
  let mk_spec fam =
    { Syntax.nat_imms = []; nat_field = None; nat_map = None; nat_src = None;
      nat_kind = Syntax.nat_redir_kind; nat_family = fam;
      nat_amin = None; nat_amax = None; nat_pmin = None; nat_pmax = None;
      nat_flags = 0 } in
  let mk_rule sp =
    { Syntax.r_body = []; r_verdict = Verdict.Continue; r_vmap = None;
      r_nat = Some sp; r_tproxy = None; r_fwd = None; r_queue = None;
      r_after = [] } in
  (* inbound interface eth0 has a non-loopback primary address 203.0.113.5 *)
  let eth0 = ascii "eth0" and eth0_ip = [203;0;113;5] in
  let env =
    { (Nft_parse.parse_string
         "table ip nat {\n  chain c { type nat hook output priority 0; }\n}\n")
        .Nft_lower.p_env
      with Packet.e_ifaddr = (fun n -> if n = eth0 then eth0_ip else []) } in
  let nh = [0x45;0;0;0; 0;0;0;0; 64;6;0;0; 1;2;3;4; 192;168;0;9] in
  let p_in =
    { (mk_pkt ~env ()) with
      Packet.pkt_meta = (fun k -> match k with Packet.MKiifname -> eth0 | _ -> []);
      pkt_nh = nh } in
  (* OUTPUT hook: destination forced to the loopback 127.0.0.1 (NOT eth0's IP) *)
  let p_out = Semantics.apply_nat Semantics.Houtput (mk_rule (mk_spec Syntax.nat_fam_ip4)) p_in in
  let d_out = Syntax.field_value Syntax.FIp4Daddr p_out in
  Printf.printf "    redirect@output:     ip daddr -> %s  (want 127.0.0.1)\n" (show d_out);
  check "output-hook redirect forces daddr to 127.0.0.1" (data_eq d_out [127;0;0;1]);
  check "output-hook redirect does NOT use the iif address" (not (data_eq d_out eth0_ip));
  (* PRE_ROUTING hook: destination becomes the inbound interface's address *)
  let p_pre = Semantics.apply_nat Semantics.Hprerouting (mk_rule (mk_spec Syntax.nat_fam_ip4)) p_in in
  let d_pre = Syntax.field_value Syntax.FIp4Daddr p_pre in
  Printf.printf "    redirect@prerouting: ip daddr -> %s  (want eth0's IP)\n" (show d_pre);
  check "prerouting-hook redirect uses the iif address" (data_eq d_pre eth0_ip);
  check "redirect diverges by hook (output<>prerouting)" (not (data_eq d_out d_pre));
  (* IPv6 output-hook redirect -> ::1 *)
  let nh6 = Stdlib.List.init 40 (fun i -> i) in
  let p6_in = { (mk_pkt ~env ()) with Packet.pkt_nh = nh6;
      Packet.pkt_meta = (fun k -> match k with Packet.MKiifname -> eth0 | _ -> []) } in
  let p6_out = Semantics.apply_nat Semantics.Houtput (mk_rule (mk_spec Syntax.nat_fam_ip6)) p6_in in
  let d6 = Syntax.field_value Syntax.FIp6Daddr p6_out in
  check "ip6 output-hook redirect forces daddr to ::1"
    (data_eq d6 [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;1]);
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
  (* iif/oif are BYTEORDER_HOST_ENDIAN (src/meta.c NFT_META_IIF/OIF templates,
     `4 * 8, BYTEORDER_HOST_ENDIAN`), exactly like ct/meta mark.  So an ORDERED or
     RANGE match on them is an ordered comparison and nft inserts the mandatory
     `byteorder reg = hton(reg,4,4)` before the range and stores the bounds
     network-order (evaluate.c expr_evaluate_relational range/ordered default
     -> BYTEORDER_BIG_ENDIAN on every operand), exactly as for `ct mark 2-5`.
     The lowering must therefore route iif/oif ranges through the same hton path
     as mark (MRangeT + TByteorder), NOT a bare LE-byte MRange (which data_le
     would compare big-endian -> wrong verdict). *)
  let src_r =
    "table ip t {\n\
    \  chain c {\n\
    \    type filter hook input priority 0; policy drop;\n\
    \    iif 2-5 accept\n\
    \    oif 2-5 accept\n\
    \  }\n\
     }\n" in
  let p_r = Nft_parse.parse_string src_r in
  let c_r = Nft_lower.find_chain p_r ~table:"t" ~chain:"c" in
  let body_r i = match (Stdlib.List.nth c_r.Syntax.c_rules i).Syntax.r_body with
    | Syntax.BMatch m :: _ -> m | _ -> failwith "no iif/oif range match" in
  (* (1) lowering shape: MRangeT FMetaIif/FMetaOif [hton(4,4)] with BE bounds *)
  (match body_r 0 with
   | Syntax.MRangeT (Syntax.FMetaIif, [Syntax.TByteorder (true, 4, 4)], false,
                     lo, hi) ->
       check "iif range lowers to MRangeT FMetaIif + hton(4,4)" true;
       check "iif range bounds are network-order (BE) [0;0;0;2]..[0;0;0;5]"
         (data_eq lo [0;0;0;2] && data_eq hi [0;0;0;5])
   | _ ->
       check "iif range lowers to MRangeT FMetaIif + hton(4,4)" false;
       check "iif range bounds are network-order (BE) [0;0;0;2]..[0;0;0;5]" false);
  (match body_r 1 with
   | Syntax.MRangeT (Syntax.FMetaOif, [Syntax.TByteorder (true, 4, 4)], false,
                     lo, hi) ->
       check "oif range lowers to MRangeT FMetaOif + hton(4,4)" true;
       check "oif range bounds are network-order (BE) [0;0;0;2]..[0;0;0;5]"
         (data_eq lo [0;0;0;2] && data_eq hi [0;0;0;5])
   | _ ->
       check "oif range lowers to MRangeT FMetaOif + hton(4,4)" false;
       check "oif range bounds are network-order (BE) [0;0;0;2]..[0;0;0;5]" false);
  (* (2) behavioural: a packet with iif index 3 (host-endian LE [3;0;0;0]) is IN
     [2,5].  The old bare-MRange path compared the LE bytes big-endian -> NO match
     (the proven divergence: nft ACCEPTS, model REJECTED).  With the hton
     transform the field becomes [0;0;0;3] BE -> 2<=3<=5 -> match. *)
  let mc_iif_r = body_r 0 in
  check "iif=3 matches range 2-5 (numeric, post-hton; old model REJECTED it)"
    (Semantics.eval_matchcond mc_iif_r (mk_iif [3;0;0;0]) = true);
  check "iif=1 does NOT match range 2-5 (below low bound)"
    (Semantics.eval_matchcond mc_iif_r (mk_iif [1;0;0;0]) = false);
  check "iif=256 does NOT match range 2-5 (would spuriously match if LE-lex on byte 0)"
    (Semantics.eval_matchcond mc_iif_r (mk_iif [0;1;0;0]) = false);
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
    \    ct state new,established,related,untracked accept\n\
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
  (* COMMA-LIST `ct state new,established,related,untracked` is NOT a set: nft's
     expr_evaluate_list (evaluate.c:1854-1888) OR-folds the four bitmask members
     into one constant new|established|related|untracked = 8|2|4|64 = 0x4e and
     emits the implicit-bitmask test (state & 0x4e) != 0 — golden ct.t.payload:1-5
     `bitwise reg1 = (reg1 & 0x4e) ^ 0 ; cmp neq reg1 0`.  Distinct from the BRACE
     set form above (real lookup).  Before the fix the parser collapsed both to
     SEset -> MConcatSet, so the comma form mis-lowered to a set membership that
     REJECTS a multi-bit state (e.g. 0x06 = established|related) which nft accepts. *)
  let m_comma = Syntax.MMasked (Syntax.FCtState, true, [0;0;0;0x4e], [0;0;0;0], [0;0;0;0]) in
  check "ct state new,established,related,untracked OR-folds to (state & 0x4e) != 0"
    (body 4 = [Syntax.BMatch m_comma]);
  (* the comma OR-mask ACCEPTS state = 0x06 (established|related): 0x06 & 0x4e != 0 *)
  check "comma list matches state = established|related = 0x06 (real nft accepts)"
    (Semantics.eval_matchcond m_comma (mk_ct [0;0;0;6]) = true);
  (* it still rejects a state with none of the listed bits (e.g. invalid = 1) *)
  check "comma list does NOT match state = invalid = 1 (no listed bit set)"
    (Semantics.eval_matchcond m_comma (mk_ct [0;0;0;1]) = false);
  (* the OLD set-membership lowering (before the fix the comma form collapsed to
     SEset -> MConcatSet) wrongly REJECTED state = 0x06: the model's set_mem
     requires an EXACT element, and 0x06 is not one of {8,2,4,64}.  This is the
     bytecode/semantic divergence the fix closes (golden ct.t.payload comma form
     is bitwise+cmp, NOT lookup). *)
  check "the OLD set-membership lowering wrongly REJECTED state = 0x06 (regression guard)"
    (Bytes.set_mem [0;0;0;6]
       [([0;0;0;8],[0;0;0;8]); ([0;0;0;2],[0;0;0;2]);
        ([0;0;0;4],[0;0;0;4]); ([0;0;0;64],[0;0;0;64])] = false);
  Printf.printf "\n"

(* (I') `ct mark set V` PERSISTS across packets of a flow (cross-packet conntrack).
   Kernel nft_ct.c: nft_ct_set_eval writes V into the SHARED conntrack entry
   (WRITE_ONCE(ct->mark)), so a later packet of the SAME flow reads it back
   (nft_ct_get_eval: READ_ONCE(ct->mark)).  The model now stores writable ct keys
   (mark/label) in the flow-keyed env table e_ct (keyed by pkt_flow), threaded across
   packets by eval_chain_mut_env/set_env — so packet 2 of the flow observes packet 1's
   `ct mark set`, and a DIFFERENT flow does not.  Mirrors Red_CtMark_Crosspkt.v. *)
let check_ct_mark_crosspkt () =
  Printf.printf "=== (I') ct mark set persists across packets of a flow ===\n";
  let src =
    "table ip t {\n\
    \  chain c {\n\
    \    type filter hook prerouting priority 0; policy drop;\n\
    \    ct mark set 0x99 accept\n\
    \  }\n\
     }\n" in
  let parsed = Nft_parse.parse_string src in
  let c = Nft_lower.find_chain parsed ~table:"t" ~chain:"c" in
  let env = parsed.Nft_lower.p_env in
  (* the rule lowers to a single ct-mark-set statement (writable key) *)
  check "ct mark set 0x99 lowers to SCtSet CKmark (VImm 0x99-le)"
    ((Stdlib.List.nth c.Syntax.c_rules 0).Syntax.r_body
       = [Syntax.BStmt (Syntax.SCtSet (Packet.CKmark, Syntax.VImm mark99))]);
  let flow_a = [10;0;0;1] and flow_b = [10;0;0;2] in
  (* packet 1 of flow A runs the chain; capture the env it leaves *)
  let p1 = mk_pkt ~env ~flow:flow_a () in
  let (v1, e1) = Semantics.eval_chain_mut_env c p1 in
  check "packet 1 of the flow is accepted (ct mark set; accept)" (v1 = Verdict.Accept);
  check "ct mark set 0x99 is recorded in the shared flow table e_ct"
    (data_eq (e1.Packet.e_ct flow_a Packet.CKmark) mark99);
  (* packet 2 of the SAME flow, with its OWN per-packet ct oracle = 0x07, threaded
     through e1: it reads back the flow mark 0x99 the kernel stored, NOT its oracle *)
  let oracle7 k = (match k with Packet.CKmark -> [7;0;0;0] | _ -> []) in
  let p2_same = Semantics.set_env (mk_pkt ~env ~ct:oracle7 ~flow:flow_a ()) e1 in
  check "packet 2 of the SAME flow reads back the persisted ct mark 0x99 (kernel-correct)"
    (data_eq (Syntax.field_value Syntax.FCtMark p2_same) mark99);
  check "the persisted flow mark overrides packet 2's own ct oracle (0x07)"
    (not (data_eq (Syntax.field_value Syntax.FCtMark p2_same) [7;0;0;0]));
  (* a packet on a DIFFERENT flow does NOT inherit the mark (flow-scoped, not global) *)
  let p2_other = Semantics.set_env (mk_pkt ~env ~ct:oracle7 ~flow:flow_b ()) e1 in
  check "a packet on a DIFFERENT flow does NOT see the mark (flow-scoped persistence)"
    (not (data_eq (Syntax.field_value Syntax.FCtMark p2_other) mark99));
  Printf.printf "\n"

(* (V) INTERVAL/range verdict-map keys.  A real nftables verdict map is the
   rbtree set type, declared NFT_SET_INTERVAL | NFT_SET_MAP
   (net/netfilter/nft_set_rbtree.c), so a vmap key may be a RANGE/prefix and the
   lookup is an interval search: `tcp dport vmap { 0-100 : drop, 101 : accept }`
   DROPS a packet with dport INSIDE [0,100] (e.g. 80) — it does NOT need an exact
   key match.  Before the fix [e_vmap] held POINT (key,verdict) pairs and
   [assoc_verdict] did exact equality, so an interior key MISSED and the parser
   could not even parse a range vmap key.  Now [e_vmap] entries are [lo,hi,verdict]
   intervals and [assoc_verdict] returns the verdict of the first entry whose
   interval contains the key (symmetric with the named-set [set_mem]). *)
let check_interval_vmap () =
  Printf.printf "=== (V) interval/range verdict-map keys (NFT_SET_INTERVAL | NFT_SET_MAP) ===\n";
  let src =
    "table inet t {\n\
    \  chain c {\n\
    \    type filter hook input priority 0; policy accept;\n\
    \    tcp dport vmap { 0-100 : drop, 101 : accept }\n\
    \  }\n\
     }\n" in
  (* (1) it PARSES — the old point-only grammar raised a syntax error on `0-100`. *)
  let parsed = Nft_parse.parse_string src in
  check "an interval (range) vmap key PARSES (0-100 : drop)" true;
  let c = Nft_lower.find_chain parsed ~table:"t" ~chain:"c" in
  let env = parsed.Nft_lower.p_env in
  (* (2) the lowered vmap carries a genuine INTERVAL entry: lo=[0;0] hi=[0;100],
     i.e. a non-degenerate [lo,hi] (not a point [k,k]). *)
  let vm_name = match (Stdlib.List.hd c.Syntax.c_rules).Syntax.r_vmap with
    | Some vm -> vm.Syntax.vm_name | None -> failwith "no vmap lowered" in
  let ents = env.Packet.e_vmap vm_name in
  let has_iv = Stdlib.List.exists (fun ((lo, hi), _) -> lo <> hi) ents in
  check "the range key lowers to a non-degenerate [lo,hi] interval entry" has_iv;
  (* (3) behaviour: dport 80 is INSIDE [0,100] -> Drop (the unsound case the model
     previously got wrong: it fell through to the accept policy). *)
  let pkt dport = mk_pkt ~env ~l4proto:l4_tcp ~th:(th_dport dport) () in
  check "dport 80 (inside 0-100) -> DROP (interval lookup; was wrongly accepted)"
    (Semantics.eval_chain c (pkt 80) = Verdict.Drop);
  check "dport 0 (lower bound) -> DROP"
    (Semantics.eval_chain c (pkt 0) = Verdict.Drop);
  check "dport 100 (upper bound) -> DROP"
    (Semantics.eval_chain c (pkt 100) = Verdict.Drop);
  (* (4) the point key 101 still matches exactly -> Accept. *)
  check "dport 101 (exact point key) -> ACCEPT"
    (Semantics.eval_chain c (pkt 101) = Verdict.Accept);
  (* (5) a key OUTSIDE every interval misses -> falls through to accept policy. *)
  check "dport 200 (outside all keys) -> falls through to accept policy"
    (Semantics.eval_chain c (pkt 200) = Verdict.Accept);
  Printf.printf "\n"

(* (I'') `notrack` forces ct state to UNTRACKED for the rest of the traversal, so a
   LATER `ct state` read observes NF_CT_STATE_UNTRACKED_BIT (= 64).  Kernel nft_ct.c:
   nft_notrack_eval calls nf_ct_set(skb, NULL, IP_CT_UNTRACKED); nft_ct_get_eval's
   NFT_CT_STATE case then returns NF_CT_STATE_UNTRACKED_BIT.  The model now applies
   set_untracked on SNotrack/INotrack (body_writes/run_rule_writes), threaded across
   rules by eval_chain_mut, and do_load (LCt CKstate) returns [0;0;0;64] when
   pkt_untracked.  So `notrack ; ct state untracked accept` ACCEPTS every packet, even
   one whose ct-state oracle was a tracked state (new = 8).  Mirrors Red_Notrack.v. *)
let check_notrack () =
  Printf.printf "=== (I'') notrack forces ct state untracked (later ct state read sees it) ===\n";
  let untracked = [0;0;0;64] in   (* NF_CT_STATE_UNTRACKED_BIT *)
  (* `ct state untracked`: single-positive bitmask form (state & 64) != 0 *)
  let m_untracked =
    Syntax.MMasked (Syntax.FCtState, true, untracked, [0;0;0;0], [0;0;0;0]) in
  let notrack_only : Syntax.rule =
    { Syntax.r_body = [ Syntax.BStmt Syntax.SNotrack ]; r_verdict = Verdict.Continue;
      r_vmap = None; r_nat = None; r_tproxy = None; r_fwd = None; r_queue = None;
      r_after = [] } in
  let ctstate_rule : Syntax.rule =
    { Syntax.r_body = [ Syntax.BMatch m_untracked ]; r_verdict = Verdict.Accept;
      r_vmap = None; r_nat = None; r_tproxy = None; r_fwd = None; r_queue = None;
      r_after = [] } in
  let chain : Syntax.chain =
    { Syntax.c_policy = Verdict.Drop; c_rules = [ notrack_only; ctstate_rule ] } in
  let env = { Packet.e_set = (fun _ -> []); e_vmap = (fun _ -> []); e_map = (fun _ -> []);
              e_routes = []; e_rt = (fun _ -> []); e_limit = (fun _ -> 0);
              e_quota = (fun _ -> 0); e_ifaddr = (fun _ -> []); e_ifaddr6 = (fun _ -> []);
              e_connlimit = (fun _ -> 0); e_ct = (fun _ _ -> []); e_nat = (fun _ -> None); e_numgen = (fun _ -> 0) } in
  (* a packet whose ct-state ORACLE is `new` (= 8): genuinely tracked.  The notrack
     in rule 1 overrides this before rule 2's `ct state untracked` match. *)
  let oracle_new k = (match k with Packet.CKstate -> [0;0;0;8] | _ -> []) in
  let p = mk_pkt ~env ~ct:oracle_new ~flow:[7;7] () in
  (* the notrack write threads into rule 2: the threaded packet reads UNTRACKED *)
  let p1 = Semantics.dsl_writes notrack_only p in
  check "notrack sets pkt_untracked := true" (p1.Packet.pkt_untracked);
  check "after notrack, ct state read returns NF_CT_STATE_UNTRACKED_BIT (64)"
    (data_eq (Syntax.do_load (Syntax.LCt Packet.CKstate) p1) untracked);
  check "the `ct state untracked` match SUCCEEDS on the threaded packet"
    (Semantics.eval_matchcond m_untracked p1);
  (* the threading evaluator ACCEPTS the originally-`new` packet (kernel-correct);
     without the fix it DROPPED it (notrack a no-op, stale oracle read) *)
  check "notrack ; ct state untracked accept ACCEPTS a `new` packet (kernel-correct)"
    (Semantics.eval_chain_mut chain p = Verdict.Accept);
  (* and the same chain DROPS the packet if rule 1 is removed (no notrack => oracle 8,
     (8 & 64) = 0 => no match => Drop policy): the acceptance is DUE TO notrack *)
  let chain_no_notrack : Syntax.chain =
    { Syntax.c_policy = Verdict.Drop; c_rules = [ ctstate_rule ] } in
  check "without the preceding notrack the same packet is DROPPED (effect is real)"
    (Semantics.eval_chain_mut chain_no_notrack p = Verdict.Drop);
  Printf.printf "\n"

(* exthdr / TCP-option VALUE load not-present guard.  Kernel nft_exthdr_tcp_eval
   `goto err` -> NFT_BREAK when the requested option is ABSENT (VALUE load), so
   the rule does not match and the chain falls through to its policy (Accept).
   An EXISTENCE load (present=true) never breaks (stores 0).  Before the fix the
   exthdr value was a pure oracle that always matched -> kernel-false Drop. *)
let check_exthdr_present () =
  Printf.printf "=== exthdr/TCP-option VALUE load not-present guard (NFT_BREAK) ===\n";
  let maxseg_val = [5;180] in   (* 1460 = 0x05B4, the maxseg option value *)
  (* `tcp option maxseg size 1460`: VALUE load, htype=2, off=2, len=2. *)
  let f_maxseg = Syntax.FExthdr (Packet.EPtcpopt, 2, 2, 2, false) in
  let maxseg_drop : Syntax.rule =
    { Syntax.r_body = [ Syntax.BMatch (Syntax.MEq (f_maxseg, maxseg_val)) ];
      r_verdict = Verdict.Drop; r_vmap = None; r_nat = None; r_tproxy = None;
      r_fwd = None; r_queue = None; r_after = [] } in
  let chain : Syntax.chain =
    { Syntax.c_policy = Verdict.Accept; c_rules = [ maxseg_drop ] } in
  let env = { Packet.e_set = (fun _ -> []); e_vmap = (fun _ -> []); e_map = (fun _ -> []);
              e_routes = []; e_rt = (fun _ -> []); e_limit = (fun _ -> 0);
              e_quota = (fun _ -> 0); e_ifaddr = (fun _ -> []); e_ifaddr6 = (fun _ -> []);
              e_connlimit = (fun _ -> 0); e_ct = (fun _ _ -> []); e_nat = (fun _ -> None);
              e_numgen = (fun _ -> 0) } in
  (* ABSENT: existence oracle (present=true) returns [0]; the value oracle returns
     the matching bytes anyway (the impossible-in-kernel state the model used to
     admit).  The guard must REFUSE to load the value, so the chain ACCEPTS. *)
  let eh_absent _ _ _ _ pr = if pr then [0] else maxseg_val in
  let p_absent = { (mk_pkt ~env ()) with Packet.pkt_eh = eh_absent } in
  check "VALUE load of an ABSENT tcp option is NOT loadable"
    (not (Syntax.field_loadable f_maxseg p_absent));
  check "EXISTENCE load (present=true) IS loadable even when absent"
    (Syntax.field_loadable (Syntax.FExthdr (Packet.EPtcpopt, 2, 0, 0, true)) p_absent);
  check "absent maxseg -> NFT_BREAK -> chain ACCEPTS (eval_chain, kernel-correct)"
    (Semantics.eval_chain chain p_absent = Verdict.Accept);
  check "absent maxseg -> chain ACCEPTS (eval_chain_mut, kernel-correct)"
    (Semantics.eval_chain_mut chain p_absent = Verdict.Accept);
  (* PRESENT: existence oracle returns [1]; the value matches -> DROP. *)
  let eh_present _ _ _ _ pr = if pr then [1] else maxseg_val in
  let p_present = { (mk_pkt ~env ()) with Packet.pkt_eh = eh_present } in
  check "PRESENT maxseg with matching value -> chain DROPS (eval_chain)"
    (Semantics.eval_chain chain p_present = Verdict.Drop);
  check "PRESENT maxseg with matching value -> chain DROPS (eval_chain_mut)"
    (Semantics.eval_chain_mut chain p_present = Verdict.Drop);
  Printf.printf "\n"

(* (I''') INTRA-RULE notrack->ct-state: `ct notrack ct state untracked accept` in ONE
   rule.  The kernel runs a rule's expressions left-to-right (nf_tables_core.c
   nft_rule_dp_for_each_expr): nft_notrack_eval latches IP_CT_UNTRACKED, then the SAME
   rule's `ct state untracked` (nft_ct_get_eval NFT_CT_STATE) reads
   NF_CT_STATE_UNTRACKED_BIT and matches -> ACCEPT.  The model now threads
   set_untracked into a rule's OWN later matches/terminal (rule_applies_walk/outcome/
   run_rule), so the single-rule idiom ACCEPTS, matching the kernel.  Before the fix
   the match was evaluated against the original (still-tracked, oracle=8) packet, the
   match FAILED, and the model PROVED a kernel-false Drop. *)
let check_notrack_intra () =
  Printf.printf "=== (I''') intra-rule notrack ; ct state untracked accept (same rule) ===\n";
  let untracked = [0;0;0;64] in
  let m_untracked =
    Syntax.MMasked (Syntax.FCtState, true, untracked, [0;0;0;0], [0;0;0;0]) in
  (* ONE rule: SNotrack statement BEFORE the ct-state match. *)
  let intra_rule : Syntax.rule =
    { Syntax.r_body = [ Syntax.BStmt Syntax.SNotrack; Syntax.BMatch m_untracked ];
      r_verdict = Verdict.Accept; r_vmap = None; r_nat = None; r_tproxy = None;
      r_fwd = None; r_queue = None; r_after = [] } in
  let chain : Syntax.chain =
    { Syntax.c_policy = Verdict.Drop; c_rules = [ intra_rule ] } in
  let env = { Packet.e_set = (fun _ -> []); e_vmap = (fun _ -> []); e_map = (fun _ -> []);
              e_routes = []; e_rt = (fun _ -> []); e_limit = (fun _ -> 0);
              e_quota = (fun _ -> 0); e_ifaddr = (fun _ -> []); e_ifaddr6 = (fun _ -> []);
              e_connlimit = (fun _ -> 0); e_ct = (fun _ _ -> []); e_nat = (fun _ -> None); e_numgen = (fun _ -> 0) } in
  let oracle_new k = (match k with Packet.CKstate -> [0;0;0;8] | _ -> []) in
  let p = mk_pkt ~env ~ct:oracle_new ~flow:[7;7] () in
  (* the rule's own statement->match ordering: the match now SUCCEEDS *)
  check "intra-rule: the rule APPLIES (notrack latch seen by its own later match)"
    (Semantics.rule_applies intra_rule p);
  check "intra-rule: eval_chain ACCEPTS a `new` packet (kernel-correct)"
    (Semantics.eval_chain chain p = Verdict.Accept);
  check "intra-rule: eval_chain_mut ACCEPTS too"
    (Semantics.eval_chain_mut chain p = Verdict.Accept);
  (* the verified compiler agrees: the compiled bytecode runs to the same verdict *)
  check "intra-rule: the COMPILED chain ACCEPTS (compile_chain_correct instance)"
    (Semantics.run_chain (Compile.compile_chain chain) chain.Syntax.c_policy p
       = Verdict.Accept);
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

(* ---------- (L) meta nfproto is the NFPROTO L3 family, not L4 proto ----------
   `meta nfproto` reads the netfilter family register (NFPROTO family), a
   distinct 1-byte datatype from the L4/IP-protocol space.  datatype.c
   nfproto_tbl maps only ipv4=NFPROTO_IPV4=2 and ipv6=NFPROTO_IPV6=10.  Golden
   inet/meta.t.payload: `meta nfproto ipv4` => cmp eq reg1 0x02,
   `meta nfproto ipv6` => cmp eq reg1 0x0a.  These corpus rules (inet/meta.t:6-7
   ;ok) were UNSUPPORTED before the fix because nfproto was wired to sym_l4proto
   (tcp=6/udp=17/... — no ipv4/ipv6). *)
let check_meta_nfproto () =
  Printf.printf "=== (L) meta nfproto -> NFPROTO family (ipv4=2, ipv6=10) ===\n";
  let src =
    "table inet t {\n\
    \  chain c {\n\
    \    type filter hook input priority 0; policy accept;\n\
    \    meta nfproto ipv4 accept\n\
    \    meta nfproto ipv6 accept\n\
    \    meta nfproto 2 accept\n\
    \  }\n\
     }\n" in
  let parsed = Nft_parse.parse_string src in
  let c = Nft_lower.find_chain parsed ~table:"t" ~chain:"c" in
  let body i = (Stdlib.List.nth c.Syntax.c_rules i).Syntax.r_body in
  (* `meta nfproto ipv4` => MEq FMetaNfproto [2] (NFPROTO_IPV4), matching the
     golden `cmp eq reg1 0x02` (FMetaNfproto reads MKnfproto, width 1). *)
  check "meta nfproto ipv4 lowers to MEq FMetaNfproto [2]"
    (body 0 = [Syntax.BMatch (Syntax.MEq (Syntax.FMetaNfproto, [2]))]);
  (* `meta nfproto ipv6` => MEq FMetaNfproto [10] (NFPROTO_IPV6), golden 0x0a. *)
  check "meta nfproto ipv6 lowers to MEq FMetaNfproto [10]"
    (body 1 = [Syntax.BMatch (Syntax.MEq (Syntax.FMetaNfproto, [10]))]);
  (* numeric form is byte-truncated (already worked, kept faithful). *)
  check "meta nfproto 2 (numeric) lowers to MEq FMetaNfproto [2]"
    (body 2 = [Syntax.BMatch (Syntax.MEq (Syntax.FMetaNfproto, [2]))]);
  (* the buggy l4proto table never had ipv4/ipv6, so this would have raised
     Unsupported — guard that nfproto is NOT taking an l4proto value (6=tcp). *)
  check "meta nfproto ipv4 is NOT the l4proto encoding (tcp=6)"
    (body 0 <> [Syntax.BMatch (Syntax.MEq (Syntax.FMetaNfproto, [6]))]);
  Printf.printf "\n"

(* ---------- (L') implicit `meta nfproto` guard before inet ip/ip6 matches ----
   In a multi-L3 family (inet) a chain sees BOTH IPv4 and IPv6 packets, so real
   nft inserts an implicit network-protocol dependency before every ip/ip6
   payload match: `[ meta load nfproto ] [ cmp eq reg1 0x02 ]` for IPv4 (0x0a for
   IPv6) — payload.c payload_gen_dependency / payload_add_dependency; golden
   tests/py/inet/ip_tcp.t.payload + sets.t.payload.inet.  This guard is what makes
   `ip saddr X` in an inet table mean "IPv4 packet AND saddr==X", not just
   "network bytes 12..15 == X" (those bytes are part of the SOURCE ADDRESS in an
   IPv6 header).  In a SINGLE-L3 family (ip/ip6) the chain sees only one network
   protocol and nft emits NO guard.  Before the fix the lowering dropped the guard
   for every family, so an inet `ip saddr 10.1.2.3` rule wrongly matched an IPv6
   packet whose pkt_nh[12..15] = 10.1.2.3 and Accepted it. *)
let check_inet_nfproto_dep () =
  Printf.printf "=== (L') implicit meta nfproto guard before inet ip/ip6 matches ===\n";
  (* the .nft frontend has no IPv6 address literal yet, so the parse-side checks
     use `ip saddr`; the ip6 guard (FMetaNfproto [10]) is exercised by the
     key_field DNfproto [10] mapping and the optiplex/ruleset Gen regeneration. *)
  let src fam =
    Printf.sprintf
      "table %s t {\n\
      \  chain c {\n\
      \    type filter hook input priority 0; policy drop;\n\
      \    ip saddr 10.1.2.3 accept\n\
      \  }\n\
       }\n" fam in
  let body fam i =
    let p = Nft_parse.parse_string (src fam) in
    let c = Nft_lower.find_chain p ~table:"t" ~chain:"c" in
    (Stdlib.List.nth c.Syntax.c_rules i).Syntax.r_body in
  (* inet: ip saddr is guarded by `meta nfproto == 2` BEFORE the FIp4Saddr match *)
  check "inet ip saddr is guarded by FMetaNfproto [2] (nfproto dep, then match)"
    (match body "inet" 0 with
     | Syntax.BMatch (Syntax.MEq (Syntax.FMetaNfproto, [2]))
       :: Syntax.BMatch (Syntax.MEq (Syntax.FIp4Saddr, _)) :: _ -> true
     | _ -> false);
  (* the OLD lowering produced a SINGLE body item with no guard (regression) *)
  check "inet ip saddr is NOT a lone FIp4Saddr match (the dropped-guard bug)"
    (body "inet" 0 <> [Syntax.BMatch (Syntax.MEq (Syntax.FIp4Saddr, [10;1;2;3]))]);
  (* single-L3 family (ip): nft emits no guard, so the body is just the match *)
  check "ip-table ip saddr has NO nfproto guard (single-L3 family)"
    (body "ip" 0 = [Syntax.BMatch (Syntax.MEq (Syntax.FIp4Saddr, [10;1;2;3]))]);
  (* ---- behavioural divergence the guard fixes ---- *)
  let env =
    (Nft_parse.parse_string
       "table inet t {\n  chain c {\n    type filter hook input priority 0; policy accept;\n  }\n}\n")
      .Nft_lower.p_env in
  (* network bytes 12..15 = 10.1.2.3.  In an IPv4 header that's the SOURCE
     ADDRESS; in an IPv6 header it's part of the (longer) source address. *)
  let nh_v4 = [0;0;0;0; 0;0;0;0; 0;0;0;0; 10;1;2;3] in
  let mk_with_nfproto nfp nh =
    { (mk_pkt ~env ()) with
      Packet.pkt_nh = nh;
      pkt_meta = (fun k -> match k with Packet.MKnfproto -> nfp | _ -> []) } in
  let p_v4 = mk_with_nfproto [2]  nh_v4 in   (* genuine IPv4 packet *)
  let p_v6 = mk_with_nfproto [10] nh_v4 in   (* IPv6 packet, same byte pattern *)
  let guarded : Syntax.chain =
    { Syntax.c_policy = Verdict.Drop;
      c_rules = [ { Syntax.r_body =
                      [ Syntax.BMatch (Syntax.MEq (Syntax.FMetaNfproto, [2]));
                        Syntax.BMatch (Syntax.MEq (Syntax.FIp4Saddr, [10;1;2;3])) ];
                    r_verdict = Verdict.Accept; r_vmap = None; r_nat = None;
                    r_tproxy = None; r_fwd = None; r_queue = None; r_after = [] } ] } in
  let unguarded : Syntax.chain =     (* the OLD, buggy lowering *)
    { Syntax.c_policy = Verdict.Drop;
      c_rules = [ { Syntax.r_body =
                      [ Syntax.BMatch (Syntax.MEq (Syntax.FIp4Saddr, [10;1;2;3])) ];
                    r_verdict = Verdict.Accept; r_vmap = None; r_nat = None;
                    r_tproxy = None; r_fwd = None; r_queue = None; r_after = [] } ] } in
  check "guarded inet rule ACCEPTS the genuine IPv4 packet (nft accepts)"
    (Semantics.eval_chain guarded p_v4 = Verdict.Accept);
  check "guarded inet rule DROPS the IPv6 packet (nft falls through to drop)"
    (Semantics.eval_chain guarded p_v6 = Verdict.Drop);
  check "the OLD unguarded rule WRONGLY accepted the IPv6 packet (regression guard)"
    (Semantics.eval_chain unguarded p_v6 = Verdict.Accept);
  Printf.printf "\n"

(* ---------- (L'') implicit `meta nfproto` guard before inet icmp/icmpv6 -------
   icmp is an IPv4-only L4 protocol and icmpv6 an IPv6-only one, so in a multi-L3
   family (inet) nft pins BOTH the network protocol AND the transport protocol:
   `[ meta load nfproto ][ cmp 0x02 ] [ meta load l4proto ][ cmp 0x01 ]` before an
   `icmp` match (0x0a / 0x3a for icmpv6) — golden inet/icmp.t.payload:
   `# icmp type echo-request` and `# icmpv6 type echo-request`.  tcp/udp are valid
   over both families and get ONLY the l4proto guard, so this is the icmp special
   case (CONTRAST inet/tcp.t.payload `# tcp dport 22` -> l4proto only, no nfproto).
   A SINGLE-L3 family (ip/ip6) emits NO nfproto guard (golden ip/icmp.t.payload.ip:
   `# icmp type echo-request accept` -> l4proto only).  Before the fix the lowering
   emitted only the l4proto guard for inet icmp, so the model wrongly matched an
   IPv6 packet whose l4proto==1 and transport byte 0 == 8. *)
let check_inet_icmp_nfproto_dep () =
  Printf.printf "=== (L'') implicit meta nfproto guard before inet icmp/icmpv6 ===\n";
  let src fam sel =
    Printf.sprintf
      "table %s t {\n\
      \  chain c {\n\
      \    type filter hook input priority 0; policy drop;\n\
      \    %s type echo-request accept\n\
      \  }\n\
       }\n" fam sel in
  let body fam sel =
    let p = Nft_parse.parse_string (src fam sel) in
    let c = Nft_lower.find_chain p ~table:"t" ~chain:"c" in
    (Stdlib.List.nth c.Syntax.c_rules 0).Syntax.r_body in
  (* inet icmp: nfproto==2 THEN l4proto==1 THEN icmp.type==8 (golden byte order) *)
  check "inet icmp type is guarded by FMetaNfproto [2] THEN FMetaL4proto [1]"
    (match body "inet" "icmp" with
     | Syntax.BMatch (Syntax.MEq (Syntax.FMetaNfproto, [2]))
       :: Syntax.BMatch (Syntax.MEq (Syntax.FMetaL4proto, [1]))
       :: Syntax.BMatch (Syntax.MEq (Syntax.FIcmpType, [8])) :: _ -> true
     | _ -> false);
  (* inet icmpv6: nfproto==10 THEN l4proto==58 THEN icmpv6.type==128 *)
  check "inet icmpv6 type is guarded by FMetaNfproto [10] THEN FMetaL4proto [58]"
    (match body "inet" "icmpv6" with
     | Syntax.BMatch (Syntax.MEq (Syntax.FMetaNfproto, [10]))
       :: Syntax.BMatch (Syntax.MEq (Syntax.FMetaL4proto, [58]))
       :: Syntax.BMatch (Syntax.MEq (Syntax.FIcmpType, [128])) :: _ -> true
     | _ -> false);
  (* the OLD lowering emitted ONLY the l4proto guard (no nfproto) — regression *)
  check "inet icmp is NOT just [l4proto==1 ; icmp.type==8] (the dropped-guard bug)"
    (body "inet" "icmp" <>
      [ Syntax.BMatch (Syntax.MEq (Syntax.FMetaL4proto, [1]));
        Syntax.BMatch (Syntax.MEq (Syntax.FIcmpType, [8])) ]);
  (* single-L3 family (ip): nft emits no nfproto guard, just l4proto + the match *)
  check "ip-table icmp has NO nfproto guard (single-L3 family), l4proto only"
    (body "ip" "icmp" =
      [ Syntax.BMatch (Syntax.MEq (Syntax.FMetaL4proto, [1]));
        Syntax.BMatch (Syntax.MEq (Syntax.FIcmpType, [8])) ]);
  (* ---- behavioural divergence the guard fixes ---- *)
  let env =
    (Nft_parse.parse_string
       "table inet t {\n  chain c {\n    type filter hook input priority 0; policy accept;\n  }\n}\n")
      .Nft_lower.p_env in
  (* an IPv6 packet whose kernel-computed l4proto is 1 (next-header 1) and whose
     transport byte 0 is 8: the model's UNGUARDED body wrongly matched it. *)
  let mk_with nfp l4p th =
    { (mk_pkt ~env ()) with
      Packet.pkt_th = th;
      pkt_meta = (fun k -> match k with
        | Packet.MKnfproto -> nfp | Packet.MKl4proto -> l4p | _ -> []) } in
  let p_v4 = mk_with [2]  [1] [8] in   (* genuine IPv4 icmp echo-request *)
  let p_v6 = mk_with [10] [1] [8] in   (* IPv6 packet, l4proto 1 + th byte 8 *)
  let guarded : Syntax.chain =
    { Syntax.c_policy = Verdict.Drop;
      c_rules = [ { Syntax.r_body =
                      [ Syntax.BMatch (Syntax.MEq (Syntax.FMetaNfproto, [2]));
                        Syntax.BMatch (Syntax.MEq (Syntax.FMetaL4proto, [1]));
                        Syntax.BMatch (Syntax.MEq (Syntax.FIcmpType, [8])) ];
                    r_verdict = Verdict.Accept; r_vmap = None; r_nat = None;
                    r_tproxy = None; r_fwd = None; r_queue = None; r_after = [] } ] } in
  let unguarded : Syntax.chain =     (* the OLD, buggy lowering: l4proto only *)
    { Syntax.c_policy = Verdict.Drop;
      c_rules = [ { Syntax.r_body =
                      [ Syntax.BMatch (Syntax.MEq (Syntax.FMetaL4proto, [1]));
                        Syntax.BMatch (Syntax.MEq (Syntax.FIcmpType, [8])) ];
                    r_verdict = Verdict.Accept; r_vmap = None; r_nat = None;
                    r_tproxy = None; r_fwd = None; r_queue = None; r_after = [] } ] } in
  check "guarded inet icmp rule ACCEPTS the genuine IPv4 packet (nft accepts)"
    (Semantics.eval_chain guarded p_v4 = Verdict.Accept);
  check "guarded inet icmp rule DROPS the IPv6 packet (nft falls through to drop)"
    (Semantics.eval_chain guarded p_v6 = Verdict.Drop);
  check "the OLD unguarded icmp rule WRONGLY accepted the IPv6 packet (regression)"
    (Semantics.eval_chain unguarded p_v6 = Verdict.Accept);
  Printf.printf "\n"

(* ---------- (K) synproxy is verdict-bearing, not a no-op ----------
   The DSL `synproxy` statement was verdict-neutral; the kernel
   (nft_synproxy.c) STOPS traversal for a TCP SYN/ACK (NF_STOLEN/NF_DROP),
   BREAKs for a non-TCP packet (NFT_BREAK), and CONTINUEs otherwise.  A chain
   whose only rule is `synproxy` (policy accept) now DROPs a SYN packet, drops
   an ACK packet, accepts (falls through) a bare-RST TCP packet, and accepts
   (rule does not apply) a non-TCP packet — it is NOT a constant no-op. *)
let check_synproxy () =
  Printf.printf "=== (K) synproxy is verdict-bearing (not a no-op) ===\n";
  (* the synproxy verdict is env-independent; take an env from a trivial parse *)
  let env =
    (Nft_parse.parse_string
       "table inet t {\n  chain c {\n    type filter hook input priority 0; policy accept;\n  }\n}\n")
      .Nft_lower.p_env in
  (* the SSynproxy statement is not on the .nft frontend, so build the AST directly *)
  let rule : Syntax.rule =
    { Syntax.r_body = [ Syntax.BStmt (Syntax.SSynproxy (1460, 7)) ];
      r_verdict = Verdict.Continue; r_vmap = None; r_nat = None;
      r_tproxy = None; r_fwd = None; r_queue = None; r_after = [] } in
  let chain : Syntax.chain = { Syntax.c_policy = Verdict.Accept; c_rules = [ rule ] } in
  let mk_tcp fl = mk_pkt ~env ~l4proto:l4_tcp ~th:(th_flags fl) () in
  let non_tcp = { (mk_pkt ~env ()) with Packet.pkt_th = []; pkt_have_l4 = false } in
  check "synproxy STOPS a TCP SYN packet (NF_STOLEN -> Drop)"
    (Semantics.eval_chain chain (mk_tcp 2) = Verdict.Drop);
  check "synproxy STOPS a TCP ACK packet (NF_STOLEN/NF_DROP -> Drop)"
    (Semantics.eval_chain chain (mk_tcp 16) = Verdict.Drop);
  check "synproxy CONTINUEs a bare-RST TCP packet (falls through to policy accept)"
    (Semantics.eval_chain chain (mk_tcp 4) = Verdict.Accept);
  check "synproxy does NOT apply to a non-TCP packet (NFT_BREAK -> policy accept)"
    (Semantics.eval_chain chain non_tcp = Verdict.Accept);
  (* the red agent's no-op claim is refuted: not constant across packets *)
  check "synproxy is NOT a verdict no-op (SYN vs RST differ)"
    (Semantics.eval_chain chain (mk_tcp 2) <> Semantics.eval_chain chain (mk_tcp 4));
  (* the compiled bytecode agrees (compile_chain_correct) *)
  let pol = chain.Syntax.c_policy in
  let prog = Compile.compile_chain chain in
  check "compiled bytecode STOPS the SYN packet too"
    (Semantics.run_chain prog pol (mk_tcp 2) = Verdict.Drop);
  Printf.printf "\n"

(* (L) CONCATENATED interval/range set: per-field (cross-product) membership.
   A concatenated set (NFT_SET_CONCAT) is matched FIELD-BY-FIELD against each
   field's own [lo,hi] — the set is the cross-product of per-field intervals, NOT
   one flat lexicographic interval over the concatenation (nf_tables.h
   NFTA_SET_FIELD_LEN; evaluate.c:1819 field_len[]; netlink_linearize.c:126-129
   one register slot per field).  Golden 2-D range element
   tests/py/inet/sets.t.payload.inet:32 `0a000000 . 000a - 0affffff . 0017`.
   For `ip daddr . tcp dport { 10.0.0.0/8 . 10-23 }` and a packet
   (daddr 10.0.0.5, dport 100): per-field daddr IS in [10.0.0.0,10.255.255.255]
   but dport 100 is NOT in [10,23] -> kernel REJECTS; the old flat lexicographic
   set_mem ACCEPTED (unsound).  This check pins the per-field semantics. *)
let check_concat_iv () =
  Printf.printf "=== (L) concatenated range set is per-field, not flat-lexicographic ===\n";
  let src =
    "table ip t {\n\
    \  chain c {\n\
    \    type filter hook input priority 0; policy accept;\n\
    \    ip daddr . tcp dport { 10.0.0.0/8 . 10-23 } accept\n\
    \  }\n\
     }\n" in
  let parsed = Nft_parse.parse_string src in
  let c = Nft_lower.find_chain parsed ~table:"t" ~chain:"c" in
  let env = parsed.Nft_lower.p_env in
  let body0 = (Stdlib.List.nth c.Syntax.c_rules 0).Syntax.r_body in
  (* the match lowers to a 2-field MConcatSet whose stored element is the per-field
     concatenation lo = 10.0.0.0 ++ dport 10, hi = 10.255.255.255 ++ dport 23.
     (A `meta l4proto tcp` dependency item may be prepended because `tcp dport`
     reads the transport header, so we search the body for the concat match.) *)
  let the_concat =
    L.find_opt (function
      | Syntax.BMatch (Syntax.MConcatSet ([Syntax.FIp4Daddr; _], false, _)) -> true
      | _ -> false) body0 in
  let set_name = match the_concat with
    | Some (Syntax.BMatch (Syntax.MConcatSet (_, _, nm))) -> Some nm
    | _ -> None in
  check "ip daddr . tcp dport {CIDR . range} lowers to a 2-field MConcatSet"
    (set_name <> None);
  let nm = match set_name with Some n -> n | None -> "" in
  let elems = env.Packet.e_set nm in
  (* NFT_SET_CONCAT register-slot layout: each field occupies a whole 4-byte
     register slot, field bytes at the FRONT + trailing zero padding (kernel
     netlink_padded_len / one register per field; golden corpus shows a 2-byte
     dport in its slot as e.g. 0050).  daddr (4 bytes) fills its slot exactly;
     the 2-byte dport bound is zero-padded to 4 bytes ([0;10;0;0] / [0;23;0;0]). *)
  check "the stored concat element is per-field, each in its 4-byte register slot: [10.0.0.0..10.255.255.255] . [10..23] (dport slot-padded)"
    (elems = [ ([10;0;0;0] @ port 10 @ [0;0], [10;255;255;255] @ port 23 @ [0;0]) ]);
  (* a packet inside daddr's range but OUTSIDE dport's range: kernel rejects *)
  let mk_pkt2 ~daddr ~dport =
    { (mk_pkt ~env ~l4proto:l4_tcp ~th:(th_dport dport) ()) with
      Packet.pkt_nh = (L.init 16 (fun _ -> 0)) @ daddr } in
  let p_bad  = mk_pkt2 ~daddr:[10;0;0;5] ~dport:100 in   (* dport 100 not in [10,23] *)
  let p_good = mk_pkt2 ~daddr:[10;0;0;5] ~dport:20  in   (* both fields in range *)
  let p_dout = mk_pkt2 ~daddr:[11;0;0;5] ~dport:20  in   (* daddr out of range *)
  let m = match the_concat with
    | Some (Syntax.BMatch mc) -> mc | _ -> failwith "no concat match" in
  check "REJECTS daddr in-range but dport OUT of range (kernel drops; old flat model wrongly accepted)"
    (Semantics.eval_matchcond m p_bad = false);
  check "ACCEPTS only when BOTH fields are in their own range"
    (Semantics.eval_matchcond m p_good = true);
  check "REJECTS daddr out of range (even with dport in range)"
    (Semantics.eval_matchcond m p_dout = false);
  (* the OLD flat-lexicographic set_mem wrongly accepted p_bad: demonstrate the
     divergence directly on the stored element. *)
  check "flat set_mem over the concatenation WOULD accept the bad packet (the bug)"
    (Bytes.set_mem ([10;0;0;5] @ port 100) elems = true);
  check "per-field concat_set_mem REJECTS it (the fix)"
    (Bytes.concat_set_mem [ [10;0;0;5]; port 100 ] elems = false);
  (* the compiled bytecode agrees with the spec (compile_chain_correct) *)
  let prog = Compile.compile_chain c in
  check "compiled bytecode REJECTS the bad packet too (run_chain = policy, rule skipped)"
    (Semantics.run_chain prog c.Syntax.c_policy p_bad = Verdict.Accept
     && Semantics.eval_chain c p_bad = Verdict.Accept);
  (* SUB-4-BYTE NON-LAST field register padding (worklist #4 core fix): a 2-byte
     [tcp sport] in the FIRST position must occupy a full 4-byte register slot, so
     the kernel's element of `{ 80 . 443 }` is [00 50 00 00][01 bb 00 00], NOT the
     contiguous [00 50][01 bb].  Both the stored element and the lookup key advance
     a whole register per field (netlink_linearize.c).  The OLD spec split by raw
     widths [2;2] and would have expected/produced the unpadded contiguous layout,
     diverging from the kernel.  We pin the slot-padded layout end-to-end. *)
  let src2 =
    "table ip t {\n\
    \  chain c {\n\
    \    type filter hook input priority 0; policy accept;\n\
    \    tcp sport . tcp dport { 80 . 443 } accept\n\
    \  }\n\
     }\n" in
  let parsed2 = Nft_parse.parse_string src2 in
  let c2 = Nft_lower.find_chain parsed2 ~table:"t" ~chain:"c" in
  let env2 = parsed2.Nft_lower.p_env in
  let body2 = (Stdlib.List.nth c2.Syntax.c_rules 0).Syntax.r_body in
  let the_concat2 =
    L.find_opt (function
      | Syntax.BMatch (Syntax.MConcatSet ([Syntax.FThSport; Syntax.FThDport], false, _)) -> true
      | _ -> false) body2 in
  let nm2 = match the_concat2 with
    | Some (Syntax.BMatch (Syntax.MConcatSet (_, _, n))) -> n | _ -> "" in
  let elems2 = env2.Packet.e_set nm2 in
  check "tcp sport . tcp dport {80 . 443}: sub-4-byte NON-LAST sport is padded to its 4-byte slot ([00 50 00 00][01 bb 00 00])"
    (elems2 = [ (port 80 @ [0;0] @ port 443 @ [0;0], port 80 @ [0;0] @ port 443 @ [0;0]) ]);
  let m2 = match the_concat2 with
    | Some (Syntax.BMatch mc) -> mc | _ -> failwith "no sport.dport concat" in
  (* transport header is sport(2) ++ dport(2) *)
  let mk_p2 ~sport ~dport =
    mk_pkt ~env:env2 ~l4proto:l4_tcp ~th:(port sport @ port dport) () in
  check "matches the exact (80,443) pair the kernel matches against the padded element"
    (Semantics.eval_matchcond m2 (mk_p2 ~sport:80 ~dport:443) = true);
  check "rejects (80, 444): dport differs"
    (Semantics.eval_matchcond m2 (mk_p2 ~sport:80 ~dport:444) = false);
  check "rejects (81, 443): non-last sport differs (would be missed if sport's slot were mis-split)"
    (Semantics.eval_matchcond m2 (mk_p2 ~sport:81 ~dport:443) = false);
  Printf.printf "\n"

(* (M) NON-WILDCARD interface-name match is an EXACT 16-byte zero-padded compare,
   NOT a short prefix.  nft stores the ifname register as the full IFNAMSIZ=16-byte
   buffer and compares a literal non-wildcard name in full, zero-padded; only a
   trailing-'*' wildcard emits a SHORT prefix cmp.  Golden tests/py/any/meta.t.payload:
     meta iifname "dummy0" => cmp eq reg1 0x64756d6d 0x79300000 0x00000000 0x00000000
                              (16 bytes: "dummy0" + 10 zeros);
     meta iifname "dummy*" => cmp eq reg1 0x64756d6d 0x79  (5-byte prefix, the only one).
   The parser previously emitted the bare unpadded name for BOTH, collapsing them
   into one prefix match -> unsoundly matched same-prefix interfaces the kernel
   rejects (e.g. `iifname dummy0` also matching "dummy0extra"). *)
let check_ifname_exact () =
  Printf.printf "=== (M) non-wildcard ifname is an exact 16-byte compare, not a prefix ===\n";
  let src =
    "table ip t {\n\
    \  chain c {\n\
    \    type filter hook input priority 0; policy accept;\n\
    \    iifname \"dummy0\" accept\n\
    \    iifname \"dummy*\" accept\n\
    \    iifname \"dummy\\*\" accept\n\
    \  }\n\
     }\n" in
  let parsed = Nft_parse.parse_string src in
  let c = Nft_lower.find_chain parsed ~table:"t" ~chain:"c" in
  let env = parsed.Nft_lower.p_env in
  let body i = (Stdlib.List.nth c.Syntax.c_rules i).Syntax.r_body in
  let dummy0_16 = ifname16 "dummy0" in   (* "dummy0" + 10 zero bytes, 16 total *)
  (* exact name -> full 16-byte zero-padded literal (golden payload:198-199) *)
  check "iifname \"dummy0\" lowers to a 16-byte zero-padded literal"
    (body 0 = [Syntax.BMatch (Syntax.MEq (Syntax.FMetaIifname, dummy0_16))]);
  check "the 16-byte literal is exactly \"dummy0\"+10 zeros"
    (Stdlib.List.length dummy0_16 = 16
     && dummy0_16 = [0x64;0x75;0x6d;0x6d;0x79;0x30; 0;0;0;0; 0;0;0;0; 0;0]);
  (* trailing-'*' wildcard -> SHORT 5-byte prefix literal (golden payload:224-225) *)
  check "iifname \"dummy*\" stays a 5-byte prefix literal (wildcard)"
    (body 1 = [Syntax.BMatch (Syntax.MEq (Syntax.FMetaIifname, ascii "dummy"))]);
  (* an ESCAPED trailing star `dummy\*` is a LITERAL '*' in the name (NOT a
     wildcard): exact, 16-byte zero-padded with 0x2a at byte 5 (golden
     payload:227-230 `[ cmp eq reg1 0x64756d6d 0x792a0000 ... ]`). *)
  check "iifname \"dummy\\*\" is a literal '*' -> 16-byte exact (\"dummy*\"+pad)"
    (body 2 = [Syntax.BMatch (Syntax.MEq (Syntax.FMetaIifname, ifname16 "dummy*"))]);
  (* end-to-end: a packet on the DISTINCT interface "dummy0extra" (16-byte reg) is
     REJECTED by the exact rule but the wildcard would match its prefix. *)
  let mk_iifn nm =
    { (mk_pkt ~env ()) with
      Packet.pkt_meta = (fun k -> match k with Packet.MKiifname -> nm | _ -> []) } in
  let reg_d0e = [0x64;0x75;0x6d;0x6d;0x79;0x30;0x65;0x78;0x74;0x72;0x61; 0;0;0;0;0] in
  let m_exact = Syntax.MEq (Syntax.FMetaIifname, dummy0_16) in
  let m_wild  = Syntax.MEq (Syntax.FMetaIifname, ascii "dummy") in
  check "exact `iifname dummy0` MATCHES the interface it names"
    (Semantics.eval_matchcond m_exact (mk_iifn dummy0_16) = true);
  check "exact `iifname dummy0` REJECTS the distinct iface dummy0extra (the fix; kernel drops)"
    (Semantics.eval_matchcond m_exact (mk_iifn reg_d0e) = false);
  check "the OLD unpadded literal WOULD wrongly accept dummy0extra (the bug)"
    (Semantics.eval_matchcond (Syntax.MEq (Syntax.FMetaIifname, ascii "dummy0"))
       (mk_iifn reg_d0e) = true);
  check "the `*` wildcard correctly remains a prefix match (matches dummy0extra)"
    (Semantics.eval_matchcond m_wild (mk_iifn reg_d0e) = true);
  (* compiled bytecode agrees with the spec on the distinct interface *)
  let prog = Compile.compile_chain c in
  check "compiled bytecode also rejects dummy0extra at the exact rule (= policy accept, both rules skip)"
    (Semantics.run_chain prog c.Syntax.c_policy (mk_iifn [0x7a;0x7a;0x7a; 0;0;0;0;0; 0;0;0;0; 0;0;0;0]) = Verdict.Accept);
  Printf.printf "\n"

(* ---------- (L) limiter `over` / invert flag flips the verdict ----------
   Real nftables limit/quota/connlimit carry an "over" (invert) bit (bit 0 of
   the flags field).  The kernel XORs the under/not-exceeded test with that bit:
     nft_limit.c:48,52   nft_quota.c:43   nft_connlimit.c:47.
   The parser sets ls_flags bit 0 for `limit rate over N/unit`, and
   Semantics.eval_matchcond_body now XORs the over-bit with `0 < remaining`. *)
let check_limit_over () =
  Printf.printf "=== (L) limiter `over`/invert flag flips the verdict ===\n";
  let src =
    "table ip t {\n\
    \  chain c {\n\
    \    type filter hook input priority 0; policy accept;\n\
    \    limit rate 10/second accept\n\
    \    limit rate over 10/second drop\n\
    \  }\n\
     }\n" in
  let parsed = Nft_parse.parse_string src in
  let c = Nft_lower.find_chain parsed ~table:"t" ~chain:"c" in
  let env = parsed.Nft_lower.p_env in
  let body i = (Stdlib.List.nth c.Syntax.c_rules i).Syntax.r_body in
  (* `limit rate 10/second` => MLimit with ls_flags bit 0 = 0 (non-inverted) *)
  check "limit rate 10/second lowers to MLimit with ls_flags=0 (non-over)"
    (match body 0 with
     | [Syntax.BMatch (Syntax.MLimit s)] -> s.Packet.ls_flags = 0
     | _ -> false);
  (* `limit rate over 10/second` => MLimit with ls_flags bit 0 = 1 (inverted) *)
  check "limit rate over 10/second lowers to MLimit with ls_flags=1 (over/inverted)"
    (match body 1 with
     | [Syntax.BMatch (Syntax.MLimit s)] -> s.Packet.ls_flags = 1
     | _ -> false);
  (* extract the two specs and pin the semantic flip for a SHARED oracle. *)
  let spec_of i = match body i with
    | [Syntax.BMatch (Syntax.MLimit s)] -> s | _ -> assert false in
  let s_under = spec_of 0 and s_over = spec_of 1 in
  (* env where the limiter is UNDER (tokens remain): e_limit returns 1 (>0). *)
  let env_under = { env with Packet.e_limit = (fun _ -> 1) } in
  (* env where the limiter is EXCEEDED: e_limit returns 0. *)
  let env_over  = { env with Packet.e_limit = (fun _ -> 0) } in
  let m_under = Syntax.MLimit s_under and m_over = Syntax.MLimit s_over in
  (* UNDER the rate: the plain `limit` MATCHES (continue/accept), the `over`
     limiter does NOT (it only fires on the flood) — opposite verdicts. *)
  check "under the rate: plain `limit` matches but `limit over` does NOT (flip)"
    (Semantics.eval_matchcond m_under (mk_pkt ~env:env_under ()) = true
     && Semantics.eval_matchcond m_over (mk_pkt ~env:env_under ()) = false);
  (* EXCEEDING the rate: the plain `limit` stops (no match) while the `over`
     limiter MATCHES — the standard anti-flood `limit rate over X drop` idiom. *)
  check "exceeding the rate: plain `limit` misses but `limit over` matches (flip)"
    (Semantics.eval_matchcond m_under (mk_pkt ~env:env_over ()) = false
     && Semantics.eval_matchcond m_over (mk_pkt ~env:env_over ()) = true);
  (* The flag is genuinely read: for the SAME oracle, over and non-over disagree. *)
  check "over and non-over give opposite verdicts for the same oracle (flag honoured)"
    (Semantics.eval_matchcond m_over (mk_pkt ~env:env_under ())
       <> Semantics.eval_matchcond m_under (mk_pkt ~env:env_under ()));
  (* CROSS-PACKET CONSUMPTION (the blue fix): a `limit` is a SHARED, CONSUMING token
     bucket, not a stateless per-packet oracle.  Build a one-rule chain
     `limit rate 10/second accept`, policy DROP, against an env whose bucket holds
     exactly ONE token.  Thread packet 1 -> its verdict + the env it LEAVES; build
     packet 2 of the SAME flow carrying that env; run again.  The kernel ACCEPTS
     packet 1 (one token), the bucket EMPTIES, and packet 2 of the depleted bucket
     is DROPPED (chain policy).  The OLD per-packet oracle proved BOTH accepted. *)
  let rule_accept =
    { Syntax.r_body = [Syntax.BMatch m_under]; r_verdict = Verdict.Accept;
      r_vmap = None; r_nat = None; r_tproxy = None; r_fwd = None;
      r_queue = None; r_after = [] } in
  let chain_lim = { Syntax.c_policy = Verdict.Drop; c_rules = [rule_accept] } in
  let env_one = { env with Packet.e_limit = (fun _ -> 1) } in
  let p1 = mk_pkt ~env:env_one ~flow:[1;1] () in
  let (v1, e_after) = Semantics.eval_chain_mut_env chain_lim p1 in
  let p2 = mk_pkt ~env:e_after ~flow:[1;1] () in
  let (v2, _) = Semantics.eval_chain_mut_env chain_lim p2 in
  check "consuming bucket: packet 1 ACCEPTED (one token available)"
    (v1 = Verdict.Accept);
  check "consuming bucket: token CONSUMED (env left by packet 1 has 0 tokens)"
    (e_after.Packet.e_limit s_under = 0);
  check "consuming bucket: packet 2 of the depleted bucket DROPPED (policy)"
    (v2 = Verdict.Drop);
  check "consecutive packets get DIFFERENT verdicts (a rate limit actually limits)"
    (v1 <> v2);
  Printf.printf "\n"

(* (M) fib route-type symbol -> RTN_ constant.  The Menhir frontend's
   sym_fibtype must encode each `fib ... type SYM` surface symbol as the kernel
   RTN_ route-type constant (rtnetlink.h:262-275 / nftables src/fib.c).  The
   anycast symbol is RTN_ANYCAST=4 and MUST NOT collide with blackhole
   (RTN_BLACKHOLE=6); a previous mis-encoding gave anycast=6, conflating the two
   and inverting the verdict on anycast/blackhole packets.  KFibType compares the
   4-byte field exactly (MEq), so the bug is purely the lowering constant. *)
let check_fib_type () =
  Printf.printf "=== (N) fib route-type symbol -> RTN_ constant ===\n";
  let src =
    "table inet t {\n\
    \  chain c {\n\
    \    type filter hook prerouting priority 0; policy accept;\n\
    \    fib daddr type anycast accept\n\
    \    fib daddr type blackhole accept\n\
    \    fib daddr type multicast accept\n\
    \    fib daddr type unicast accept\n\
    \  }\n\
     }\n" in
  let parsed = Nft_parse.parse_string src in
  let c = Nft_lower.find_chain parsed ~table:"t" ~chain:"c" in
  let body i = (Stdlib.List.nth c.Syntax.c_rules i).Syntax.r_body in
  let rtype i = match body i with
    | [Syntax.BMatch (Syntax.MEq (Syntax.FFib (_, Packet.FRtype), v))] -> Some v
    | _ -> None in
  (* anycast = RTN_ANYCAST = 4, NOT 6 (the old RTN_BLACKHOLE collision). *)
  check "fib daddr type anycast lowers to RTN_ANYCAST=4 ([0;0;0;4])"
    (rtype 0 = Some [0;0;0;4]);
  check "fib daddr type blackhole lowers to RTN_BLACKHOLE=6 ([0;0;0;6])"
    (rtype 1 = Some [0;0;0;6]);
  (* the two distinct route types must NOT compile to identical bytecode. *)
  check "anycast and blackhole encode to DIFFERENT constants (no collision)"
    (rtype 0 <> rtype 1);
  check "fib daddr type multicast lowers to RTN_MULTICAST=5 ([0;0;0;5])"
    (rtype 2 = Some [0;0;0;5]);
  check "fib daddr type unicast lowers to RTN_UNICAST=1 ([0;0;0;1])"
    (rtype 3 = Some [0;0;0;1]);
  (* behavioural: a packet whose looked-up route type is 4 (anycast) matches the
     anycast rule and NOT the blackhole rule; type 6 (blackhole) is the reverse. *)
  let m_any = match body 0 with [Syntax.BMatch m] -> m | _ -> assert false in
  let m_bh  = match body 1 with [Syntax.BMatch m] -> m | _ -> assert false in
  let env = parsed.Nft_lower.p_env in
  let mk_rtype t =
    let env' = { env with Packet.e_routes =
      [ (([0], [255]),
         (fun (r : Packet.fib_result) ->
            match r with Packet.FRtype -> t | _ -> [])) ] } in
    { (mk_pkt ~env:env' ()) with Packet.pkt_fibkey = (fun _ -> [0]) } in
  check "route type 4 (anycast) matches the anycast rule, not blackhole"
    (Semantics.eval_matchcond m_any (mk_rtype [0;0;0;4]) = true
     && Semantics.eval_matchcond m_bh (mk_rtype [0;0;0;4]) = false);
  check "route type 6 (blackhole) matches the blackhole rule, not anycast"
    (Semantics.eval_matchcond m_bh (mk_rtype [0;0;0;6]) = true
     && Semantics.eval_matchcond m_any (mk_rtype [0;0;0;6]) = false);
  Printf.printf "\n"

(* (O) HOST-ENDIAN MARK RANGE: `meta mark` / `ct mark` are BYTEORDER_HOST_ENDIAN
   4-byte integers (nft_meta.c `*dest = skb->mark;`; src/ct.c:52 / src/meta.c:106).
   For an ORDERED or RANGE comparison nft ALWAYS inserts `byteorder reg = hton(reg,
   4, 4)` before the range so the byte-lexicographic register compare runs over
   network bytes and is therefore NUMERIC (golden any/ct.t.payload `ct mark
   0x32-0x45` -> `[ ct load mark => reg 1 ] [ byteorder reg 1 = hton(reg 1,4,4) ]
   [ range eq reg 1 0x00000032 0x00000045 ]`).  The frontend previously lowered
   `mark 0x5-0xff` to a bare MRange over host-endian bytes with NO hton, comparing
   the wrong byte order: a mark=16 packet (stored LE [16;0;0;0]) was compared as if
   big-endian -> out of range -> WRONG.  Now KMark is stored host-endian (LE) like
   the kernel and a range lowers to MRangeT with the hton transform + network-order
   bounds, so the test is numeric and faithful. *)
let check_mark_range () =
  Printf.printf "=== (O) host-endian mark range (hton before range) ===\n";
  let src =
    "table ip filter {\n\
    \  chain input {\n\
    \    type filter hook input priority 0; policy drop;\n\
    \    meta mark 0x5-0xff accept\n\
    \  }\n\
     }\n" in
  let parsed = Nft_parse.parse_string src in
  let env = parsed.Nft_lower.p_env in
  let input = Nft_lower.find_chain parsed ~table:"filter" ~chain:"input" in
  let r0 = Stdlib.List.nth input.Syntax.c_rules 0 in
  let mc = match r0.Syntax.r_body with
    | Syntax.BMatch m :: _ -> m | _ -> failwith "no mark match" in
  (* (1) lowering shape: MRangeT FMetaMark [hton(4,4)] with network-order bounds *)
  (match mc with
   | Syntax.MRangeT (Syntax.FMetaMark, [Syntax.TByteorder (true, 4, 4)], false,
                     lo, hi) ->
       check "mark range lowers to MRangeT + hton(4,4)" true;
       check "range bounds are network-order (BE) [0;0;0;5]..[0;0;0;255]"
         (data_eq lo [0;0;0;5] && data_eq hi [0;0;0;255])
   | _ ->
       check "mark range lowers to MRangeT + hton(4,4)" false;
       check "range bounds are network-order (BE) [0;0;0;5]..[0;0;0;255]" false);
  (* (2) behavioural: a mark=16 packet (host-endian LE [16;0;0;0]) is IN [5,255].
     Old bare-MRange path compared LE bytes big-endian -> NO match (wrong).  With
     the hton transform the field becomes [0;0;0;16] BE -> 5<=16<=255 -> match. *)
  let mk_mark le = { (mk_pkt ~env ()) with
    Packet.pkt_meta = (fun k -> match k with Packet.MKmark -> le | _ -> []) } in
  let mark16 = [16;0;0;0] in          (* 0x10 host-endian *)
  let mark256 = [0;1;0;0] in          (* 0x100 host-endian: out of [5,255] numerically *)
  let mark1 = [1;0;0;0] in            (* 0x01 host-endian: below 5 *)
  check "mark=0x10 matches range 0x5-0xff (numeric, post-hton)"
    (Semantics.eval_matchcond mc (mk_mark mark16) = true);
  check "mark=0x100 does NOT match 0x5-0xff (would spuriously match if LE-lex)"
    (Semantics.eval_matchcond mc (mk_mark mark256) = false);
  check "mark=0x1 does NOT match 0x5-0xff (below low bound)"
    (Semantics.eval_matchcond mc (mk_mark mark1) = false);
  (* (3) eq is unaffected: `meta mark 0x99` stays MEq over the host-endian (LE)
     constant [153;0;0;0] (NO byteorder; memcmp eq is order-independent). *)
  let src_eq =
    "table ip filter {\n\
    \  chain input {\n\
    \    type filter hook input priority 0; policy drop;\n\
    \    meta mark 0x99 accept\n\
    \  }\n\
     }\n" in
  let p_eq = Nft_parse.parse_string src_eq in
  let c_eq = Nft_lower.find_chain p_eq ~table:"filter" ~chain:"input" in
  let mc_eq = match (Stdlib.List.nth c_eq.Syntax.c_rules 0).Syntax.r_body with
    | Syntax.BMatch m :: _ -> m | _ -> failwith "no eq match" in
  (match mc_eq with
   | Syntax.MEq (Syntax.FMetaMark, [153;0;0;0]) ->
       check "mark eq stays MEq over host-endian (LE) constant, no byteorder" true
   | _ -> check "mark eq stays MEq over host-endian (LE) constant, no byteorder" false);
  Printf.printf "\n"

(* (O') HOST-ENDIAN MARK INTERVAL SET: an INTERVAL set on a host-endian field
   (`ct mark { 0x100-0x200 }`) is ALSO an ordered comparison, so nft inserts the
   SAME mandatory `byteorder reg = hton(reg,4,4)` before the `lookup` and stores
   the interval bounds network-order (golden any/ct.t.payload: an interval mark
   set forces the hton; an exact-element set `{0x32,0x2222}` does not).  The
   frontend previously lowered the SEset path to a bare MConcatSet with LE bounds
   and NO byteorder, so [set_mem]'s big-endian [data_le] compared the LE-stored
   bounds in the wrong byte order: the model REJECTED a mark numerically inside
   the interval that nft ACCEPTS.  Now an interval set over a host-endian field
   lowers to MSetT + hton(4,4) with BE bounds (mirroring the Round-7 direct-range
   fix on the set path), while an EXACT-only set stays a bare MConcatSet (memcmp
   eq is order-independent — nft emits no hton there either). *)
let check_mark_set () =
  Printf.printf "=== (O') host-endian mark interval set (hton before lookup) ===\n";
  let chain_of src =
    let p = Nft_parse.parse_string src in
    (p, Nft_lower.find_chain p ~table:"filter" ~chain:"input") in
  let mc_of c = match (Stdlib.List.nth c.Syntax.c_rules 0).Syntax.r_body with
    | Syntax.BMatch m :: _ -> m | _ -> failwith "no match" in
  (* (1) INTERVAL set: MSetT FCtMark [hton(4,4)] with NETWORK-order (BE) bounds *)
  let src_iv =
    "table ip filter {\n\
    \  chain input {\n\
    \    type filter hook input priority 0; policy drop;\n\
    \    ct mark { 0x100-0x200 } accept\n\
    \  }\n\
     }\n" in
  let (p_iv, c_iv) = chain_of src_iv in
  let env_iv = p_iv.Nft_lower.p_env in
  let mc_iv = mc_of c_iv in
  (match mc_iv with
   | Syntax.MSetT (Syntax.FCtMark, [Syntax.TByteorder (true, 4, 4)], false, nm) ->
       check "interval mark set lowers to MSetT + hton(4,4)" true;
       check "interval set bounds are network-order (BE) [0;0;1;0]..[0;0;2;0]"
         (env_iv.Packet.e_set nm = [ ([0;0;1;0], [0;0;2;0]) ])
   | _ ->
       check "interval mark set lowers to MSetT + hton(4,4)" false;
       check "interval set bounds are network-order (BE) [0;0;1;0]..[0;0;2;0]" false);
  (* (2) behavioural: a packet with ct mark 0x150 (host-endian LE [80;1;0;0]) is
     numerically inside [0x100,0x200].  The OLD bare-MConcatSet path compared the
     LE bound big-endian and REJECTED it (the proven divergence); with the hton
     transform the field becomes [0;0;1;80] BE and 0x100<=0x150<=0x200 -> match. *)
  (* ct mark is a WRITABLE/PERSISTENT key: a `ct mark` MATCH reads the SHARED
     flow-keyed conntrack table e_ct (at the packet's flow), not the per-packet ct
     oracle.  So seed the mark via e_ct for this packet's (default []) flow. *)
  let mk_ctmark le =
    let env_m = { env_iv with Packet.e_ct =
      (fun fl (k : Packet.ct_key) ->
         match k with Packet.CKmark when fl = [] -> le | _ -> []) } in
    mk_pkt ~env:env_m () in
  check "ct mark 0x150 matches { 0x100-0x200 } (numeric, post-hton; old model REJECTED it)"
    (Semantics.eval_matchcond mc_iv (mk_ctmark [80;1;0;0]) = true);
  check "ct mark 0x80 does NOT match { 0x100-0x200 } (below low bound)"
    (Semantics.eval_matchcond mc_iv (mk_ctmark [128;0;0;0]) = false);
  check "ct mark 0x300 does NOT match { 0x100-0x200 } (above high bound)"
    (Semantics.eval_matchcond mc_iv (mk_ctmark [0;3;0;0]) = false);
  (* directly exhibit the OLD bug on the BE-stored element: the LE-compared bound
     would have rejected 0x150 (matching the infidelity's coqtop proof). *)
  check "the BUG: LE-stored bounds compared big-endian reject 0x150 (old behaviour)"
    (Bytes.set_mem [80;1;0;0] [ ([0;1;0;0], [0;2;0;0]) ] = false);
  check "the FIX: BE-stored bounds + hton'd field accept 0x150"
    (Bytes.set_mem (Bytes.data_byteorder true 4 4 [80;1;0;0]) [ ([0;0;1;0], [0;0;2;0]) ] = true);
  (* (3) EXACT-only set stays a bare MConcatSet over host-endian (LE) constants,
     NO byteorder (nft emits no hton for `ct mark { 0x32, 0x2222 }`). *)
  let src_ex =
    "table ip filter {\n\
    \  chain input {\n\
    \    type filter hook input priority 0; policy drop;\n\
    \    ct mark { 0x32, 0x2222 } accept\n\
    \  }\n\
     }\n" in
  let (p_ex, c_ex) = chain_of src_ex in
  let env_ex = p_ex.Nft_lower.p_env in
  let mc_ex = mc_of c_ex in
  (match mc_ex with
   | Syntax.MConcatSet ([Syntax.FCtMark], false, nm) ->
       check "exact mark set stays a bare MConcatSet (no byteorder transform)" true;
       (* host-endian (LE) point elements: 0x32=[50;0;0;0], 0x2222=[34;34;0;0] *)
       check "exact set elements are host-endian (LE) points, no hton"
         (env_ex.Packet.e_set nm = [ ([50;0;0;0],[50;0;0;0]); ([34;34;0;0],[34;34;0;0]) ])
   | _ ->
       check "exact mark set stays a bare MConcatSet (no byteorder transform)" false;
       check "exact set elements are host-endian (LE) points, no hton" false);
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

(* ---------- (J) jump/goto are NOT silently ignored (jump-aware eval_table) ----------
   REGRESSION for the "compile_chain_correct certifies a jump-IGNORING semantics"
   infidelity.  The environment-free eval_chain treats a `jump deny` as a benign
   fall-through and returns the base policy (Accept here); the FAITHFUL, jump-aware
   eval_table runs the target chain, so a `jump`/`goto` to a chain that DROPs must
   DROP (matches nf_tables_core.c JUMP/GOTO dispatch). *)
let check_jump_aware () =
  Printf.printf "=== (J) jump/goto run the target chain (jump-aware eval_table) ===\n";
  let env =
    (Nft_parse.parse_string
       "table ip filter {\n  chain c { type filter hook input priority 0; }\n}\n")
      .Nft_lower.p_env in
  let mk_rule v : Syntax.rule =
    { Syntax.r_body = []; r_verdict = v; r_vmap = None; r_nat = None;
      r_tproxy = None; r_fwd = None; r_queue = None; r_after = [] } in
  let deny : Syntax.chain =
    { Syntax.c_policy = Verdict.Accept; c_rules = [ mk_rule Verdict.Drop ] } in
  let chains = [ ("deny", deny) ] in
  let jump_base : Syntax.chain =
    { Syntax.c_policy = Verdict.Accept; c_rules = [ mk_rule (Verdict.Jump "deny") ] } in
  let goto_base : Syntax.chain =
    { Syntax.c_policy = Verdict.Accept; c_rules = [ mk_rule (Verdict.Goto "deny") ] } in
  let p = mk_pkt ~env () in
  let vj = Semantics.eval_table 10 chains jump_base p in
  let vg = Semantics.eval_table 10 chains goto_base p in
  (* the OLD jump-ignoring eval_chain returns the base policy Accept; flag that too *)
  let veval_chain = Semantics.eval_chain jump_base p in
  Printf.printf "    jump deny -> %s (want drop);  goto deny -> %s (want drop)\n"
    (verdict_str vj) (verdict_str vg);
  Printf.printf "    (env-free eval_chain ignores the jump -> %s)\n" (verdict_str veval_chain);
  check "jump deny runs target chain -> drop" (vj = Verdict.Drop);
  check "goto deny runs target chain -> drop" (vg = Verdict.Drop);
  check "env-free eval_chain would IGNORE the jump (-> accept)"
    (veval_chain = Verdict.Accept);
  Printf.printf "\n"

let () =
  if Stdlib.Array.length Sys.argv > 1 then cli Sys.argv.(1)
  else begin
    check_ruleset_nft ();
    check_jump_aware ();
    check_optiplex_antispoof ();
    check_optiplex_mark ();
    check_dnat_rewrite ();
    check_ip6_nat ();
    check_redir_hook ();
    check_iif_index ();
    check_ct_state ();
    check_ct_mark_crosspkt ();
    check_notrack ();
    check_notrack_intra ();
    check_exthdr_present ();
    check_interval_vmap ();
    check_tcp_flags ();
    check_meta_nfproto ();
    check_inet_nfproto_dep ();
    check_inet_icmp_nfproto_dep ();
    check_synproxy ();
    check_concat_iv ();
    check_ifname_exact ();
    check_limit_over ();
    check_fib_type ();
    check_mark_range ();
    check_mark_set ();
    check_difftest_ast ();
    check_live_nft ();
    if !fails = 0 then Printf.printf "ALL PARSER CHECKS PASSED\n"
    else (Printf.printf "%d PARSER CHECK(S) FAILED\n" !fails; exit 1)
  end
