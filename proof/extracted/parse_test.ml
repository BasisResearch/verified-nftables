(* Validation harness + CLI for the .nft frontend (TODO 9 / milestone M1).

   With NO arguments (`make parse-test`) it runs three checks:

   (A) Parse ../../rulesets/ruleset.nft and run the *extracted* DSL semantics
       (Semantics.eval_table) on concrete packets, asserting the verdicts match
       the eight properties proved by hand in ../theories/Examples/Example_Ruleset.v.  This
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
(* Conntrack keys are read from the SHARED, flow-keyed table [e_ct] at the
   packet's flow (kernel nf_ct_get(skb) selects the entry by tuple).  So a test
   that wants `ct state X` on this packet must record X in the env's [e_ct] at
   this packet's [flow]; [mk_pkt] does that by wrapping the env's [e_ct] with an
   override at [flow]. *)
let mk_pkt ~env ?ct ?(protocol = []) ?(l4proto = []) ?(nfproto = [])
           ?(iifname = []) ?(th = []) ?(flow = []) () : Packet.env * Packet.packet =
  (* Only override the env's flow-keyed [e_ct] when a per-packet ct map was
     explicitly supplied (the legacy `~ct:(ct_state ...)` idiom); otherwise leave
     the caller's env [e_ct] intact (some tests seed [e_ct] directly). *)
  let env =
    match ct with
    | None -> env
    | Some ct ->
        { env with Packet.e_ct =
            (fun fl k -> if fl = flow then ct k else env.Packet.e_ct fl k) } in
  (env,
  { Packet.pkt_meta = (fun k -> match k with
      | Packet.MKprotocol -> protocol | Packet.MKl4proto -> l4proto
      | Packet.MKnfproto -> nfproto
      | Packet.MKiifname -> iifname | _ -> []);
    pkt_sock = dummy0;
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
    pkt_ctdir_orig = true; pkt_ct_present = true })

(* A test packet-in-context is an (env, packet) PAIR: the shared mutable world
   plus one skb.  Every evaluator takes them as SEPARATE arguments
   (eval : ... -> env -> packet -> ...); these helpers apply one to a pair. *)
let ev_mc m (e, p) = Semantics.eval_matchcond m e p
let ev_chain c (e, p) = Semantics.eval_chain c e p
let ev_chain_mut c (e, p) = Semantics.eval_chain_mut c e p
let ev_chain_mut_env c (e, p) = Semantics.eval_chain_mut_env c e p
let ev_chain_trace h c (e, p) = Semantics.eval_chain_trace h c e p
let ev_table fuel cs c (e, p) = Semantics.eval_table fuel cs c e p
let run_chain_vm prog pol (e, p) = Semantics.run_chain prog pol e p
let rule_applies_on r (e, p) = Semantics.rule_applies r e p
let apply_nat_on h r (e, p) = Semantics.apply_nat h r e p
let dsl_writes_on r (e, p) = Semantics.dsl_writes r e p
let fv f (e, p) = Syntax.field_value f e p
let dload l (e, p) = Syntax.do_load l e p
(* update the PACKET half of a pair (record-update on the skb) *)
let wire f (e, p) = (e, f p)

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
  Printf.printf "=== (A) ../../rulesets/ruleset.nft vs Example_Ruleset.v (extracted eval_table) ===\n";
  let parsed = Nft_parse.parse_file "../../rulesets/ruleset.nft" in
  let env = parsed.Nft_inject.p_env in
  let chains = Nft_inject.chains_of parsed ~table:"firewall" in
  let inbound = Nft_inject.find_chain parsed ~table:"firewall" ~chain:"inbound" in
  let forward = Nft_inject.find_chain parsed ~table:"firewall" ~chain:"forward" in
  let fuel = 8 in
  let run c ep = ev_table fuel chains c ep in
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
                    r_outcome = Syntax.OVerdict Verdict.Drop; r_after = [] } ] } in
  let bad_pkt = wire (fun p -> { p with Packet.pkt_have_l4 = false; pkt_th = [] }) (mk_pkt ~env ()) in
  want "nft_break: no-L4 tcp dport!=22 -> accept" dropneq_chain bad_pkt Verdict.Accept;
  let frag_pkt = wire (fun p -> { p with Packet.pkt_fragoff = 8; pkt_th = [9;9;9;9] }) (mk_pkt ~env ()) in
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
    { Syntax.r_body = body; r_outcome = Syntax.OVerdict v; r_after = [] } in
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
  let got = Nft_inject.find_chain parsed ~table:"filter" ~chain:"input" in
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
    let input = Nft_inject.find_chain parsed ~table:"filter" ~chain:"input" in
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
   theories/Examples/Optiplex_Antispoof.v: parse ../../rulesets/optiplex.nft, run the extracted
   eval_table on the same spoof / legitimate packets, and assert the verdicts
   the proofs establish (vikunja/gentoo spoofs -> Drop; the bound pair -> Accept).
   The proofs are about nft2coq's emitted AST; this confirms the OCaml runtime
   path agrees with it. *)

(* a bridge frame: obrname / oifname metas + an IPv4 daddr at network offset 16.
   It is an IPv4 ethertype frame (meta protocol == ETH_P_IP 0x0800), matching the
   `meta protocol == 0x0800` dependency nft prepends before an `ip <field>` match
   in a bridge/netdev L2 chain (see nft_lower ensure_dep1 / arp+ip L2 guards). *)
let mk_bridge ~env ~obrname ~oifname ~daddr : Packet.env * Packet.packet =
  wire (fun p ->
    { p with
      Packet.pkt_meta = (fun k -> match k with
        | Packet.MKbri_oifname -> obrname | Packet.MKoifname -> oifname
        | Packet.MKprotocol -> [0x08; 0x00] | _ -> []);
      pkt_nh = (Stdlib.List.init 16 (fun _ -> 0)) @ daddr })
    (mk_pkt ~env ())

let check_optiplex_antispoof () =
  Printf.printf "=== (D) optiplex.nft anti-spoofing vs Optiplex_Antispoof.v ===\n";
  let parsed = Nft_parse.parse_file "../../rulesets/optiplex.nft" in
  let env = parsed.Nft_inject.p_env in
  let chains = Nft_inject.chains_of parsed ~table:"vmfilter" in
  let output = Nft_inject.find_chain parsed ~table:"vmfilter" ~chain:"output" in
  let run ~obrname ~oifname ~daddr =
    ev_table 4 chains output
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

(* Compatibility constructor for the multi-address interface model: an interface
   whose only address is the global primary [v] (or NO address when [v = []]).
   Packet.e_ifaddr / e_ifaddr6 select this single primary, so [e_ifaddr] of such a
   list is exactly [v] — the same observable as the old single-address oracle. *)
let ifaddrs_of (v : int list) : Packet.ifaddr list =
  if v = [] then []
  else [ { Packet.ifa_local = v; ifa_secondary = false; ifa_scope = 0 } ]

(* a streaming packet (dport 48010): iifname=home, fib daddr type=local (via a
   route returning type=2), tcp.  Not the 3389 RDP port — so it flows PAST
   prerouting rule 1 and is marked by rule 2. *)
let mk_pkt_dport ~env ~dport : Packet.env * Packet.packet =
  let env_fib =
    { env with Packet.e_routes =
        [ (([0], [255]),
           (fun (r : Packet.fib_result) ->
              match r with Packet.FRtype -> [2;0;0;0] | _ -> [])) ] } in
  wire (fun p ->
    { p with
      Packet.pkt_meta = (fun k -> match k with
        | Packet.MKiifname -> ifname16 "home" | Packet.MKl4proto -> [6] | _ -> []);
      pkt_fibkey = (fun _ -> [0]);
      pkt_th = [0;0] @ dport })
    (mk_pkt ~env:env_fib ())

let mark_of ep = fv Syntax.FMetaMark ep

let check_optiplex_mark () =
  Printf.printf "=== (E) optiplex.nft firewall mark vs Optiplex_Mark.v ===\n";
  let parsed = Nft_parse.parse_file "../../rulesets/optiplex.nft" in
  let env = parsed.Nft_inject.p_env in
  let prerouting  = Nft_inject.find_chain parsed ~table:"filter" ~chain:"prerouting" in
  let postrouting = Nft_inject.find_chain parsed ~table:"filter" ~chain:"postrouting" in
  (* a game-streaming packet enters with NO mark *)
  let p_in = mk_pkt_dport ~env ~dport:[187;138] in   (* dport 48010 *)
  Printf.printf "    packet in:  mark=%s\n" (let m = mark_of p_in in if m=[] then "(unset)" else show m);
  (* traverse the WHOLE prerouting chain; observe the verdict AND the packet out *)
  let (v_pre, p_out) = ev_chain_trace Semantics.Hprerouting prerouting p_in in
  Printf.printf "    prerouting: verdict=%s, packet out mark=%s\n"
    (verdict_str v_pre) (show (mark_of p_out));
  check "prerouting accepts" (v_pre = Verdict.Accept);
  check "prerouting marks the packet 0x99" (data_eq (mark_of p_out) mark99);
  (* carry that packet to postrouting; the mark drives masquerade (accept) *)
  let v_post = ev_chain_mut postrouting p_out in
  Printf.printf "    postrouting (on marked packet): verdict=%s\n" (verdict_str v_post);
  check "postrouting accepts the marked packet" (v_post = Verdict.Accept);
  (* and the masquerade rule specifically fires on the marked packet *)
  let post1 = Stdlib.List.nth postrouting.Syntax.c_rules 0 in
  check "masquerade rule fires on mark" (rule_applies_on post1 p_out = true);
  (* masquerade SOURCE-NAT: the packet leaving postrouting has its ip saddr
     rewritten to the address of the interface it exits (e_ifaddr oifname). *)
  let eth0 = ifname16 "eth0" and eth0_ip = [203;0;113;5] in   (* TEST-NET-3; 16-byte iface register *)
  let env_if = { env with Packet.e_ifaddrs = (fun n -> ifaddrs_of (if n = eth0 then eth0_ip else [])) } in
  let p_masq =                                             (* marked, exits eth0 *)
    wire (fun p ->
      { p with
        Packet.pkt_meta = (fun k -> match k with
          | Packet.MKmark -> mark99 | Packet.MKoifname -> eth0 | _ -> []);
        pkt_nh = Stdlib.List.init 20 (fun _ -> 0) })
      (mk_pkt ~env:env_if ()) in                           (* saddr starts 0.0.0.0 *)
  let saddr_in  = fv Syntax.FIp4Saddr p_masq in
  let (_, p_masq_out) = ev_chain_trace Semantics.Hpostrouting postrouting p_masq in
  let saddr_out = fv Syntax.FIp4Saddr p_masq_out in
  Printf.printf "    masquerade: ip saddr  %s -> %s  (eth0's IP)\n"
    (show saddr_in) (show saddr_out);
  check "masquerade rewrites saddr to exit-iface IP" (data_eq saddr_out eth0_ip);
  (* contrast: an RDP/3389 packet is marked at rule 1; an unmarked packet at
     postrouting does NOT masquerade *)
  let (_, p_rdp_out) = ev_chain_trace Semantics.Hprerouting prerouting (mk_pkt_dport ~env ~dport:[13;61]) in
  check "RDP/3389 also marked 0x99" (data_eq (mark_of p_rdp_out) mark99);
  check "unmarked packet not masqueraded"
    (rule_applies_on post1 (mk_pkt ~env ()) = false);
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
  let env = parsed.Nft_inject.p_env in
  let prerouting = Nft_inject.find_chain parsed ~table:"nat" ~chain:"prerouting" in
  let r0 = Stdlib.List.nth prerouting.Syntax.c_rules 0 in
  check "dnat lowers to a nat_spec (not a bare Accept)" (Syntax.r_nat r0 <> None);
  (* a packet whose destination starts 192.168.0.9 (nh bytes 16..19) *)
  let nh = [0x45;0;0;0; 0;0;0;0; 64;6;0;0; 1;2;3;4; 192;168;0;9] in
  let p_in = wire (fun p -> { p with Packet.pkt_nh = nh }) (mk_pkt ~env ()) in
  let daddr_in = fv Syntax.FIp4Daddr p_in in
  let (v, p_out) = ev_chain_trace Semantics.Hprerouting prerouting p_in in
  let daddr_out = fv Syntax.FIp4Daddr p_out in
  Printf.printf "    dnat: ip daddr  %s -> %s  (target 10.0.0.1)\n"
    (show daddr_in) (show daddr_out);
  check "dnat is a terminal accept" (v = Verdict.Accept);
  check "dnat rewrites ip daddr to the target" (data_eq daddr_out [10;0;0;1]);
  check "dnat does NOT touch ip saddr"
    (data_eq (fv Syntax.FIp4Saddr p_out) [1;2;3;4]);
  (* The IPv4 HEADER CHECKSUM (network bytes 10..11) is NOT left stale: the kernel
     runs csum_replace4(&iph->check, old_daddr, new_daddr) in the same step as the
     address rewrite (nf_nat_proto.c:329-333).  The model now updates it
     incrementally (RFC 1624) via set_nh_addr_ip4/csum_update_field. *)
  let ipck_in  = Packet.slice (snd p_in).Packet.pkt_nh  10 2 in
  let ipck_out = Packet.slice (snd p_out).Packet.pkt_nh 10 2 in
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
  let env_p = parsed_p.Nft_inject.p_env in
  let pre_p = Nft_inject.find_chain parsed_p ~table:"nat" ~chain:"prerouting" in
  let rp = Stdlib.List.nth pre_p.Syntax.c_rules 0 in
  let ns = match Syntax.r_nat rp with Some n -> n | None -> failwith "no nat_spec" in
  check "dnat to A:PORT carries the port (8080=0x1f90) into nat_extra"
    (ns.Syntax.nat_extra = Syntax.NXimm (None, Some ([0x1f; 0x90]), None));
  (* a packet with dport=80 in the transport header (bytes 2..3 = [0;80]) *)
  let th = [0;0; 0;80; 0;0;0;0] in
  let p_in2 = wire (fun p -> { p with Packet.pkt_nh = nh; pkt_th = th }) (mk_pkt ~env:env_p ()) in
  let dport_in = Packet.read_payload Packet.PTransport 2 2 (snd p_in2) in
  let (_, p_out2) = ev_chain_trace Semantics.Hprerouting pre_p p_in2 in
  let dport_out = Packet.read_payload Packet.PTransport 2 2 (snd p_out2) in
  Printf.printf "    dnat:port: th dport  %s -> %s  (target :8080 = 0x1f90)\n"
    (show dport_in) (show dport_out);
  check "dnat to A:PORT rewrites th dport to the big-endian port (8080=0x1f90)"
    (data_eq dport_out [0x1f; 0x90]);
  check "dnat to A:PORT also rewrites ip daddr to the address operand"
    (data_eq (fv Syntax.FIp4Daddr p_out2) [10;0;0;1]);
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
  let env_po = parsed_po.Nft_inject.p_env in
  let pre_po = Nft_inject.find_chain parsed_po ~table:"nat" ~chain:"prerouting" in
  let rpo = Stdlib.List.nth pre_po.Syntax.c_rules 0 in
  let nso = match Syntax.r_nat rpo with
    | Some n -> n | None -> failwith "port-only dnat dropped to bare Accept" in
  check "dnat to :PORT lowers to a real nat_spec (not a bare Accept)"
    (Syntax.r_nat rpo <> None);
  check "dnat to :PORT carries the port (80=0x0050) into nat_extra"
    (nso.Syntax.nat_extra = Syntax.NXimm (None, Some ([0; 80]), None));
  check "dnat to :PORT has NO address operand (nat_has_addr = false)"
    (Semantics.nat_has_addr nso = false);
  let th_po = [0;0; 0;25; 0;0;0;0] in
  let p_in3 = wire (fun p -> { p with Packet.pkt_nh = nh; pkt_th = th_po }) (mk_pkt ~env:env_po ()) in
  let daddr_in3 = fv Syntax.FIp4Daddr p_in3 in
  let (_, p_out3) = ev_chain_trace Semantics.Hprerouting pre_po p_in3 in
  let daddr_out3 = fv Syntax.FIp4Daddr p_out3 in
  let dport_out3 = Packet.read_payload Packet.PTransport 2 2 (snd p_out3) in
  Printf.printf "    dnat :80: ip daddr  %s -> %s (preserved); th dport -> %s (= 0x0050)\n"
    (show daddr_in3) (show daddr_out3) (show dport_out3);
  check "dnat to :PORT PRESERVES ip daddr (no address rewrite, no header truncation)"
    (data_eq daddr_out3 daddr_in3);
  check "dnat to :PORT preserves the network-header length (no 4-byte deletion)"
    (Stdlib.List.length (snd p_out3).Packet.pkt_nh = Stdlib.List.length nh);
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
    { Syntax.nat_addr_imm = None; nat_field = Some (Syntax.FIp4Saddr, []); nat_map = None;
      nat_src = None; nat_kind = Syntax.nat_dnat_kind; nat_family = Syntax.nat_fam_ip4;
      nat_extra = Syntax.NXnone; nat_flags = 0 } in
  let dnat_saddr_rule : Syntax.rule =
    { Syntax.r_body = []; r_outcome = Syntax.ONat dnat_saddr_spec; r_after = [] } in
  let dnat_saddr_chain : Syntax.chain =
    { Syntax.c_policy = Verdict.Drop; c_rules = [dnat_saddr_rule] } in
  let flow0 = [7;7] in
  (* a 20-byte IPv4 header with the given source address @12..15 (dst @16..19) *)
  let mk_nh saddr = [0x45;0;0;20; 0;0;0;0; 64;6;0;0] @ saddr @ [9;9;9;9] in
  (* packet 1 of the flow: saddr 1.1.1.1 — establishes + stores the mapping *)
  let f1 = wire (fun p -> { p with Packet.pkt_nh = mk_nh [1;1;1;1];
             pkt_have_l4 = false }) (mk_pkt ~env ~flow:flow0 ()) in
  let (_, f1_out) =
    ev_chain_trace Semantics.Hprerouting dnat_saddr_chain f1 in
  let d1 = fv Syntax.FIp4Daddr f1_out in
  check "dnat to ip saddr: packet 1 dnat's dst to its own saddr (1.1.1.1)"
    (data_eq d1 [1;1;1;1]);
  check "the NAT mapping is STORED in the flow-keyed e_nat after packet 1"
    ((fst f1_out).Packet.e_nat flow0
       = Some (((Some [9;9;9;9], Some [1;1;1;1]), None), None));
  (* packet 2 of the SAME flow: DIFFERENT saddr 2.2.2.2, threaded through the env
     packet 1 left — it must reuse packet 1's STORED destination (1.1.1.1), NOT its
     own saddr.  This is the property that was UNSOUND (provably divergent) before. *)
  let f2 = wire (fun p -> { p with Packet.pkt_nh = mk_nh [2;2;2;2]; pkt_have_l4 = false })
             (mk_pkt ~env:(fst f1_out) ~flow:flow0 ()) in
  let (_, f2_out) =
    ev_chain_trace Semantics.Hprerouting dnat_saddr_chain f2 in
  let d2 = fv Syntax.FIp4Daddr f2_out in
  Printf.printf "    dnat-to-saddr flow: pkt1 dst=%s  pkt2 dst=%s (same stored mapping)\n"
    (show d1) (show d2);
  check "packet 2 of the SAME flow reuses packet 1's STORED dnat dst (1.1.1.1, kernel-correct)"
    (data_eq d2 [1;1;1;1]);
  check "packet 2 does NOT dnat to its OWN saddr (2.2.2.2) — operand not re-evaluated"
    (not (data_eq d2 [2;2;2;2]));
  (* a packet on a DIFFERENT flow establishes its OWN mapping (flow-scoped) *)
  let g = wire (fun p -> { p with Packet.pkt_nh = mk_nh [2;2;2;2]; pkt_have_l4 = false })
            (mk_pkt ~env:(fst f1_out) ~flow:[8;8] ()) in
  let (_, g_out) =
    ev_chain_trace Semantics.Hprerouting dnat_saddr_chain g in
  check "a DIFFERENT flow establishes its own mapping (dnat dst = its own saddr 2.2.2.2)"
    (data_eq (fv Syntax.FIp4Daddr g_out) [2;2;2;2]);
  (* REPLY-DIRECTION un-NAT: a fixed `dnat to 8.8.8.8` establishes the
     mapping on the original-direction packet (client 1.1.1.1 -> router 9.9.9.9 =>
     dst 8.8.8.8).  The REPLY packet of the SAME flow (server 8.8.8.8 -> client
     1.1.1.1, pkt_ctdir_orig = false) must have its SOURCE un-DNAT'd back to 9.9.9.9
     and its DESTINATION left untouched — the kernel's nf_nat_packet direction
     inversion.  Before the fix the model re-applied the forward dnat forward (reply
     dst -> 8.8.8.8) and left the reply src stale. *)
  let dnat88_spec : Syntax.nat_spec =
    { Syntax.nat_addr_imm = Some [8;8;8;8]; nat_field = None; nat_map = None;
      nat_src = None; nat_kind = Syntax.nat_dnat_kind; nat_family = Syntax.nat_fam_ip4;
      nat_extra = Syntax.NXnone; nat_flags = 0 } in
  let dnat88_rule : Syntax.rule =
    { Syntax.r_body = []; r_outcome = Syntax.ONat dnat88_spec; r_after = [] } in
  let dnat88_chain : Syntax.chain =
    { Syntax.c_policy = Verdict.Drop; c_rules = [dnat88_rule] } in
  let rflow = [3;3] in
  let fwd_in = wire (fun p -> { p with Packet.pkt_nh = mk_nh [1;1;1;1]; pkt_have_l4 = false })
                 (mk_pkt ~env ~flow:rflow ()) in
  let (_, fwd_out) =
    ev_chain_trace Semantics.Hprerouting dnat88_chain fwd_in in
  check "reply-dir: forward packet dnat's dst 9.9.9.9 -> 8.8.8.8"
    (data_eq (fv Syntax.FIp4Daddr fwd_out) [8;8;8;8]);
  (* reply packet, threaded through the env the forward packet established *)
  let rep_in = wire (fun p -> { p with Packet.pkt_nh = mk_nh [8;8;8;8];
                 pkt_have_l4 = false; pkt_ctdir_orig = false })
                 (mk_pkt ~env:(fst fwd_out) ~flow:rflow ()) in
  (* mk_nh appends [9;9;9;9] as the dst; the reply's dst should be the client. Build
     the reply with dst = client 1.1.1.1 explicitly. *)
  let rep_in = wire (fun p -> { p with Packet.pkt_nh =
                 [0x45;0;0;20; 0;0;0;0; 64;6;0;0] @ [8;8;8;8] @ [1;1;1;1] }) rep_in in
  let (_, rep_out) =
    ev_chain_trace Semantics.Hprerouting dnat88_chain rep_in in
  check "reply-dir: reply SOURCE un-DNAT'd 8.8.8.8 -> 9.9.9.9 (inverse manip)"
    (data_eq (fv Syntax.FIp4Saddr rep_out) [9;9;9;9]);
  check "reply-dir: reply DESTINATION left untouched (1.1.1.1)"
    (data_eq (fv Syntax.FIp4Daddr rep_out) [1;1;1;1]);
  (* REPLY-DIRECTION PORT un-NAT: `dnat to 8.8.8.8:8080` rewrites the
     forward packet's DESTINATION port 80 -> 8080; the kernel's nf_nat_manip_pkt(REPLY)
     un-rewrites the reply's SOURCE port from 8080 back to the original 80
     (tcp_manip_pkt: `*portptr = newport`).  Before the fix the model left the reply
     ports byte-for-byte unchanged, so the reply's source port stayed stuck at 8080. *)
  let dnat_port_spec : Syntax.nat_spec =
    { Syntax.nat_addr_imm = Some [8;8;8;8]; nat_field = None; nat_map = None;
      nat_src = None; nat_kind = Syntax.nat_dnat_kind; nat_family = Syntax.nat_fam_ip4;
      nat_extra = Syntax.NXimm (None, Some ([31; 144]), None);
      nat_flags = 0 } in
  let dnat_port_rule : Syntax.rule =
    { Syntax.r_body = []; r_outcome = Syntax.ONat dnat_port_spec; r_after = [] } in
  let dnat_port_chain : Syntax.chain =
    { Syntax.c_policy = Verdict.Drop; c_rules = [dnat_port_rule] } in
  let pflow = [5;5] in
  (* th = sport ++ dport ++ payload; forward sport 4444 ([17;92]), dport 80 ([0;80]) *)
  let mk_th sport dport = sport @ dport @ [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0] in
  let pf_in = wire (fun p -> { p with Packet.pkt_nh = [0x45;0;0;20; 0;0;0;0; 64;6;0;0] @ [1;1;1;1] @ [9;9;9;9];
                pkt_th = mk_th [17;92] [0;80]; pkt_have_l4 = false })
                (mk_pkt ~env ~flow:pflow ()) in
  let (_, pf_out) =
    ev_chain_trace Semantics.Hprerouting dnat_port_chain pf_in in
  check "reply-dir port: forward packet dnat's DEST port 80 -> 8080"
    (data_eq (Packet.slice (snd pf_out).Packet.pkt_th 2 2) [31;144]);
  (* reply: server 8.8.8.8:8080 -> client; sport = 8080 ([31;144]) *)
  let pr_in = wire (fun p -> { p with Packet.pkt_nh = [0x45;0;0;20; 0;0;0;0; 64;6;0;0] @ [8;8;8;8] @ [1;1;1;1];
                pkt_th = mk_th [31;144] [17;92]; pkt_have_l4 = false;
                pkt_ctdir_orig = false })
                (mk_pkt ~env:(fst pf_out) ~flow:pflow ()) in
  let (_, pr_out) =
    ev_chain_trace Semantics.Hprerouting dnat_port_chain pr_in in
  check "reply-dir port: reply SOURCE port un-DNAT'd 8080 -> 80 (inverse manip)"
    (data_eq (Packet.slice (snd pr_out).Packet.pkt_th 0 2) [0;80]);
  check "reply-dir port: reply SOURCE port no longer stuck at dnat target 8080"
    (not (data_eq (Packet.slice (snd pr_out).Packet.pkt_th 0 2) [31;144]));
  check "reply-dir port: reply DEST port left untouched (client port 4444)"
    (data_eq (Packet.slice (snd pr_out).Packet.pkt_th 2 2) [17;92]);
  (* ct DIRECTION selector == NAT manip direction: in the kernel both
     the `ct direction` selector (nft_ct.c:86) and the NAT forward/reply decision
     (nf_nat_core.c:872) are CTINFO2DIR(ctinfo) of the SAME skb, so they are EQUAL.
     The model now derives `ct direction` from pkt_ctdir_orig (the model's
     CTINFO2DIR(ctinfo)), so the FORWARD packet reads ORIGINAL [0] and the REPLY
     packet reads REPLY [1] — never decoupled.  Before the fix `ct direction` was a
     free e_ct oracle byte that could disagree with the NAT layer. *)
  check "ct direction: forward (NAT original-dir) packet reads ORIGINAL [0]"
    (data_eq (dload (Syntax.LCt Packet.CKdirection) fwd_in) [0]);
  check "ct direction: reply (NAT reply-dir, un-NAT'd) packet reads REPLY [1]"
    (data_eq (dload (Syntax.LCt Packet.CKdirection) rep_in) [1]);
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
    { Syntax.nat_addr_imm = Some tgt6; nat_field = None; nat_map = None;
      nat_src = None; nat_kind = kind; nat_family = Syntax.nat_fam_ip6;
      nat_extra = Syntax.NXnone;
      nat_flags = 0 } in
  let mk_rule sp =
    { Syntax.r_body = []; r_outcome = Syntax.ONat sp; r_after = [] } in
  (* a 40-byte IPv6 header: src bytes 8..23, dst bytes 24..39 distinct *)
  let nh = Stdlib.List.init 40 (fun i -> i) in
  let env =
    (Nft_parse.parse_string
       "table ip6 nat {\n  chain c { type nat hook prerouting priority 0; }\n}\n")
      .Nft_inject.p_env in
  let p_in = wire (fun p -> { p with Packet.pkt_nh = nh }) (mk_pkt ~env ()) in
  (* ip6 dnat: the IPv6 destination (bytes 24..39) becomes the target *)
  let p_d = apply_nat_on Semantics.Hprerouting (mk_rule (mk_spec Syntax.nat_dnat_kind)) p_in in
  let d6 = fv Syntax.FIp6Daddr p_d in
  Printf.printf "    ip6 dnat: ip6 daddr -> %s\n" (show d6);
  check "ip6 dnat sets the 16-byte IPv6 destination to the target"
    (data_eq d6 tgt6);
  check "ip6 dnat preserves the network-header length (no shift/corruption)"
    (Stdlib.List.length (snd p_d).Packet.pkt_nh = Stdlib.List.length nh);
  check "ip6 dnat does NOT touch the IPv6 source"
    (data_eq (fv Syntax.FIp6Saddr p_d)
             (fv Syntax.FIp6Saddr p_in));
  (* ip6 snat: the IPv6 source (bytes 8..23) becomes the target *)
  let p_s = apply_nat_on Semantics.Hprerouting (mk_rule (mk_spec Syntax.nat_snat_kind)) p_in in
  check "ip6 snat sets the 16-byte IPv6 source to the target"
    (data_eq (fv Syntax.FIp6Saddr p_s) tgt6);
  check "ip6 snat preserves the network-header length"
    (Stdlib.List.length (snd p_s).Packet.pkt_nh = Stdlib.List.length nh);
  (* sanity: an ip dnat still rewrites the IPv4 slot (regression for the v4 path) *)
  let v4spec =
    { Syntax.nat_addr_imm = Some [10;0;0;1]; nat_field = None; nat_map = None;
      nat_src = None; nat_kind = Syntax.nat_dnat_kind; nat_family = Syntax.nat_fam_ip4;
      nat_extra = Syntax.NXnone;
      nat_flags = 0 } in
  let p4 = apply_nat_on Semantics.Hprerouting (mk_rule v4spec) p_in in
  check "ip (v4) dnat still rewrites the IPv4 destination slot"
    (data_eq (fv Syntax.FIp4Daddr p4) [10;0;0;1]);
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
  let post6 = Nft_inject.find_chain parsed6 ~table:"nat" ~chain:"post" in
  let mr = Stdlib.List.nth post6.Syntax.c_rules 0 in
  (match Syntax.r_nat mr with
   | Some ns ->
       check "ip6 masquerade lowers to nat_family = \"ip6\" (was \"\", family-blind)"
         (ns.Syntax.nat_family = Syntax.nat_fam_ip6)
   | None -> check "ip6 masquerade lowers to a nat_spec" false);
  (* the exit interface's IPv6 address (16 bytes, all 0xBB) via e_ifaddr6; the IPv4
     e_ifaddr is a DIFFERENT value, to prove masquerade picks the IPv6 one *)
  let if6 = Stdlib.List.init 16 (fun _ -> 0xBB) in
  let env6 = parsed6.Nft_inject.p_env in
  let env6 = { env6 with Packet.e_ifaddrs = (fun _ -> ifaddrs_of [9;9;9;9]);
                         e_ifaddrs6 = (fun _ -> ifaddrs_of if6) } in
  let p6 = wire (fun p -> { p with Packet.pkt_nh = nh }) (mk_pkt ~env:env6 ()) in
  let src6_in = fv Syntax.FIp6Saddr p6 in
  let (_, p6_out) = ev_chain_trace Semantics.Hpostrouting post6 p6 in
  let src6_out = fv Syntax.FIp6Saddr p6_out in
  Printf.printf "    ip6 masquerade: ip6 saddr  %s -> %s  (exit iface's IPv6)\n"
    (show src6_in) (show src6_out);
  check "ip6 masquerade rewrites the FULL 16-byte IPv6 source to e_ifaddr6"
    (data_eq src6_out if6);
  check "ip6 masquerade preserves the network-header length (no shift/corruption)"
    (Stdlib.List.length (snd p6_out).Packet.pkt_nh = Stdlib.List.length nh);
  check "ip6 masquerade does NOT use the 4-byte IPv4 e_ifaddr"
    (not (data_eq src6_out [9;9;9;9]));
  Printf.printf "\n";
  (* --- inet-table masquerade is RUNTIME-DISPATCHED by the PACKET's L3 family.
     ONE inet-table masquerade rule serves BOTH IPv4 and IPv6 packets; the kernel
     dispatches at runtime (nft_masq_inet_eval: `switch (nft_pf(pkt))` ->
     NFPROTO_IPV4 -> nf_nat_masquerade_ipv4 (4-byte slot) vs NFPROTO_IPV6 ->
     nf_nat_masquerade_ipv6 (16-byte slot via ipv6_dev_get_saddr)).  Before this fix
     the parser STATICALLY pinned nat_family = "ip" for inet, so an IPv6 packet got
     the 4-byte IPv4 address spliced into the MIDDLE of its 16-byte source (bytes
     10..15 mangled) and a no-IPv4-addr interface SPURIOUSLY DROPPED the IPv6 packet.
     The fix lowers inet-table masquerade to nat_family = "inet", which the data-plane
     resolves per-packet via [pkt_l3_family]. --- *)
  let parsed_inet =
    Nft_parse.parse_string
      "table inet nat {\n\
      \  chain post {\n\
      \    type nat hook postrouting priority srcnat; policy accept;\n\
      \    masquerade\n\
      \  }\n\
       }\n" in
  let post_inet = Nft_inject.find_chain parsed_inet ~table:"nat" ~chain:"post" in
  let mr_inet = Stdlib.List.nth post_inet.Syntax.c_rules 0 in
  (match Syntax.r_nat mr_inet with
   | Some ns ->
       check "inet masquerade lowers to nat_family = \"inet\" (runtime-dispatched, NOT pinned \"ip\")"
         (ns.Syntax.nat_family = Syntax.nat_fam_inet)
   | None -> check "inet masquerade lowers to a nat_spec" false);
  (* exit interface: IPv4 = 9.9.9.9, IPv6 = 0xBB*16 (a DIFFERENT value) *)
  let inet_if6 = Stdlib.List.init 16 (fun _ -> 0xBB) in
  let env_inet = parsed_inet.Nft_inject.p_env in
  let env_inet = { env_inet with Packet.e_ifaddrs = (fun _ -> ifaddrs_of [9;9;9;9]);
                                 e_ifaddrs6 = (fun _ -> ifaddrs_of inet_if6) } in
  (* (a) IPv6 packet (nfproto = NFPROTO_IPV6 = 10): full 16-byte IPv6 rewrite. *)
  let p_inet6 = wire (fun p -> { p with Packet.pkt_nh = nh }) (mk_pkt ~env:env_inet ~nfproto:[10] ()) in
  let s6_in  = fv Syntax.FIp6Saddr p_inet6 in
  let (_, p_inet6_out) = ev_chain_trace Semantics.Hpostrouting post_inet p_inet6 in
  let s6_out = fv Syntax.FIp6Saddr p_inet6_out in
  Printf.printf "    inet masquerade, IPv6 pkt: ip6 saddr %s -> %s\n" (show s6_in) (show s6_out);
  check "inet masquerade on an IPv6 packet rewrites the FULL 16-byte IPv6 source to e_ifaddr6"
    (data_eq s6_out inet_if6);
  check "inet masquerade on an IPv6 packet does NOT splice the 4-byte IPv4 addr"
    (not (data_eq (Stdlib.List.filteri (fun i _ -> i >= 10 && i < 16) s6_out) [9;9;9;9]));
  check "inet masquerade preserves the IPv6 network-header length"
    (Stdlib.List.length (snd p_inet6_out).Packet.pkt_nh = Stdlib.List.length nh);
  (* (b) IPv4 packet (nfproto = NFPROTO_IPV4 = 2) through the SAME rule: 4-byte slot. *)
  let nh4 = [0x45;0;0;0; 0;0;0;0; 64;6;0;0; 1;2;3;4; 192;168;0;9] in
  let p_inet4 = wire (fun p -> { p with Packet.pkt_nh = nh4 }) (mk_pkt ~env:env_inet ~nfproto:[2] ()) in
  let (_, p_inet4_out) = ev_chain_trace Semantics.Hpostrouting post_inet p_inet4 in
  let s4_out = fv Syntax.FIp4Daddr p_inet4_out in
  ignore s4_out;
  check "inet masquerade on an IPv4 packet rewrites the 4-byte IPv4 source to e_ifaddr"
    (data_eq (fv Syntax.FIp4Saddr p_inet4_out) [9;9;9;9]);
  (* (c) interface with an IPv6 address but NO IPv4 address: an IPv6 packet must be
     MASQUERADED (kernel uses the IPv6 address), NOT dropped. *)
  let env_noip4 = { env_inet with Packet.e_ifaddrs = (fun _ -> []);
                                  e_ifaddrs6 = (fun _ -> ifaddrs_of inet_if6) } in
  let p_noip4 = wire (fun p -> { p with Packet.pkt_nh = nh }) (mk_pkt ~env:env_noip4 ~nfproto:[10] ()) in
  let (v_noip4, p_noip4_out) = ev_chain_trace Semantics.Hpostrouting post_inet p_noip4 in
  check "inet masquerade: no-IPv4-addr iface does NOT drop an IPv6 packet (kernel masqs via IPv6)"
    (v_noip4 <> Verdict.Drop);
  check "inet masquerade: that IPv6 packet IS masqueraded to the IPv6 addr"
    (data_eq (fv Syntax.FIp6Saddr p_noip4_out) inet_if6);
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
    { Syntax.nat_addr_imm = None; nat_field = None; nat_map = None; nat_src = None;
      nat_kind = Syntax.nat_redir_kind; nat_family = fam;
      nat_extra = Syntax.NXnone;
      nat_flags = 0 } in
  let mk_rule sp =
    { Syntax.r_body = []; r_outcome = Syntax.ONat sp; r_after = [] } in
  (* inbound interface eth0 has a non-loopback primary address 203.0.113.5 *)
  let eth0 = ifname16 "eth0" and eth0_ip = [203;0;113;5] in   (* 16-byte iface register *)
  let env =
    { (Nft_parse.parse_string
         "table ip nat {\n  chain c { type nat hook output priority 0; }\n}\n")
        .Nft_inject.p_env
      with Packet.e_ifaddrs = (fun n -> ifaddrs_of (if n = eth0 then eth0_ip else [])) } in
  let nh = [0x45;0;0;0; 0;0;0;0; 64;6;0;0; 1;2;3;4; 192;168;0;9] in
  let p_in =
    wire (fun p ->
      { p with
        Packet.pkt_meta = (fun k -> match k with Packet.MKiifname -> eth0 | _ -> []);
        pkt_nh = nh }) (mk_pkt ~env ()) in
  (* OUTPUT hook: destination forced to the loopback 127.0.0.1 (NOT eth0's IP) *)
  let p_out = apply_nat_on Semantics.Houtput (mk_rule (mk_spec Syntax.nat_fam_ip4)) p_in in
  let d_out = fv Syntax.FIp4Daddr p_out in
  Printf.printf "    redirect@output:     ip daddr -> %s  (want 127.0.0.1)\n" (show d_out);
  check "output-hook redirect forces daddr to 127.0.0.1" (data_eq d_out [127;0;0;1]);
  check "output-hook redirect does NOT use the iif address" (not (data_eq d_out eth0_ip));
  (* PRE_ROUTING hook: destination becomes the inbound interface's address *)
  let p_pre = apply_nat_on Semantics.Hprerouting (mk_rule (mk_spec Syntax.nat_fam_ip4)) p_in in
  let d_pre = fv Syntax.FIp4Daddr p_pre in
  Printf.printf "    redirect@prerouting: ip daddr -> %s  (want eth0's IP)\n" (show d_pre);
  check "prerouting-hook redirect uses the iif address" (data_eq d_pre eth0_ip);
  check "redirect diverges by hook (output<>prerouting)" (not (data_eq d_out d_pre));
  (* IPv6 output-hook redirect -> ::1 *)
  let nh6 = Stdlib.List.init 40 (fun i -> i) in
  let p6_in = wire (fun p -> { p with Packet.pkt_nh = nh6;
      Packet.pkt_meta = (fun k -> match k with Packet.MKiifname -> eth0 | _ -> []) }) (mk_pkt ~env ()) in
  let p6_out = apply_nat_on Semantics.Houtput (mk_rule (mk_spec Syntax.nat_fam_ip6)) p6_in in
  let d6 = fv Syntax.FIp6Daddr p6_out in
  check "ip6 output-hook redirect forces daddr to ::1"
    (data_eq d6 [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;1]);
  (* NAT-core NF_DROP when the interface has no usable address.  The kernel DROPS:
     nf_nat_redirect_ipv4 PREROUTING `if (!newdst.ip) return NF_DROP;`
     (nf_nat_redirect.c:71-74); nf_nat_masquerade_ipv4 `if (!newsrc) return NF_DROP;`
     (nf_nat_masquerade.c:54-58).  e_ifaddr = [] is exactly that condition. *)
  let env_noaddr = { env with Packet.e_ifaddrs = (fun _ -> []); e_ifaddrs6 = (fun _ -> []) } in
  let p_noaddr = wire (fun p -> { p with
                   Packet.pkt_meta = (fun k -> match k with Packet.MKiifname -> eth0 | _ -> []);
                   pkt_nh = nh }) (mk_pkt ~env:env_noaddr ()) in
  let redir_chain : Syntax.chain =
    { Syntax.c_policy = Verdict.Drop;
      c_rules = [ mk_rule (mk_spec Syntax.nat_fam_ip4) ] } in
  let (vr_pre, pr_pre) = ev_chain_trace Semantics.Hprerouting redir_chain p_noaddr in
  check "prerouting redirect with NO inbound address DROPS (kernel NF_DROP)"
    (vr_pre = Verdict.Drop);
  check "the dropped redirect packet is left UNREWRITTEN (no empty-address splice)"
    (data_eq (fv Syntax.FIp4Daddr pr_pre)
             (fv Syntax.FIp4Daddr p_noaddr));
  (* but the verified CONTROL-PLANE (mut) verdict is unaffected: the drop is a
     data-plane-only refinement, so eval_chain_mut still Accepts. *)
  check "control-plane eval_chain_mut still ACCEPTS the redirect (data-plane-only drop)"
    (ev_chain_mut redir_chain p_noaddr = Verdict.Accept);
  (* output-hook redirect targets loopback, so it NEVER drops even with no address *)
  check "output-hook redirect with no address still ACCEPTS (loopback target)"
    (fst (ev_chain_trace Semantics.Houtput redir_chain p_noaddr) = Verdict.Accept);
  (* masquerade likewise drops at postrouting when the exit interface has no address *)
  let masq_spec =
    { Syntax.nat_addr_imm = None; nat_field = None; nat_map = None; nat_src = None;
      nat_kind = Syntax.nat_masq_kind; nat_family = Syntax.nat_fam_ip4;
      nat_extra = Syntax.NXnone; nat_flags = 0 } in
  let masq_chain : Syntax.chain =
    { Syntax.c_policy = Verdict.Drop;
      c_rules = [ mk_rule masq_spec ] } in
  check "postrouting masquerade with NO exit address DROPS (kernel NF_DROP)"
    (fst (ev_chain_trace Semantics.Hpostrouting masq_chain p_noaddr) = Verdict.Drop);
  (* with the address restored, both accept again *)
  let env_addr = { env with Packet.e_ifaddrs = (fun _ -> ifaddrs_of [203;0;113;5]) } in
  let p_addr = (env_addr, snd p_noaddr) in
  check "redirect/masquerade ACCEPT once the interface has an address"
    (fst (ev_chain_trace Semantics.Hprerouting redir_chain p_addr) = Verdict.Accept
     && fst (ev_chain_trace Semantics.Hpostrouting masq_chain p_addr) = Verdict.Accept);
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
  let c = Nft_inject.find_chain parsed ~table:"t" ~chain:"c" in
  let env = parsed.Nft_inject.p_env in
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
    wire (fun p ->
      { p with Packet.pkt_meta = (fun k -> match k with Packet.MKiif -> idx | _ -> []) })
      (mk_pkt ~env ()) in
  let m_lo = Syntax.MEq (Syntax.FMetaIif, [1;0;0;0]) in
  check "iif lo matches a packet whose numeric iif = 1 (real nft matches)"
    (ev_mc m_lo (mk_iif [1;0;0;0]) = true);
  check "iif lo does NOT match a packet on a different iface (index 2)"
    (ev_mc m_lo (mk_iif [2;0;0;0]) = false);
  check "iif lo does NOT match the impossible ASCII-meta packet"
    (ev_mc m_lo (mk_iif (ascii "lo")) = false);
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
  let c_r = Nft_inject.find_chain p_r ~table:"t" ~chain:"c" in
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
    (ev_mc mc_iif_r (mk_iif [3;0;0;0]) = true);
  check "iif=1 does NOT match range 2-5 (below low bound)"
    (ev_mc mc_iif_r (mk_iif [1;0;0;0]) = false);
  check "iif=256 does NOT match range 2-5 (would spuriously match if LE-lex on byte 0)"
    (ev_mc mc_iif_r (mk_iif [0;1;0;0]) = false);
  Printf.printf "\n"

(* (I) SINGLE POSITIVE `ct state X` BITMASK lowering.  ct_state has
   .basetype = bitmask_type (ct.c:54), and the relational evaluator
   (evaluate.c:2792-2797) rewrites OP_IMPLICIT over a TYPE_BITMASK basetype to
   OP_EQ for EVERY bitmask type EXCEPT TYPE_CT_STATE.  So a single positive
   `ct state established` stays an implicit bitmask test, emitted (golden
   tests/py/any/ct.t.payload:35-40) as
     [ bitwise reg1 = (reg1 & 0x00000002) ^ 0x0 ]  [ cmp neq reg1 0x0 ]
   i.e. it matches iff (state & 2) != 0, NOT state == 2.  The parser must lower
   it to MMasked (FCtState, CNe, mask=X, xor=0, val=0), which the model
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
  let c = Nft_inject.find_chain parsed ~table:"t" ~chain:"c" in
  let env = parsed.Nft_inject.p_env in
  let body i = (Stdlib.List.nth c.Syntax.c_rules i).Syntax.r_body in
  (* `ct state established` => bitmask test (state & 2) != 0, NOT MEq *)
  check "ct state established lowers to MMasked bitmask test (not MEq)"
    (body 0 = [Syntax.BMatch
       (Syntax.MMasked (Syntax.FCtState, Bytecode.CNe, [0;0;0;2], [0;0;0;0], [0;0;0;0]))]);
  (* `ct state new` => bitmask test (state & 8) != 0 *)
  check "ct state new lowers to MMasked bitmask test"
    (body 1 = [Syntax.BMatch
       (Syntax.MMasked (Syntax.FCtState, Bytecode.CNe, [0;0;0;8], [0;0;0;0], [0;0;0;0]))]);
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
  let m_estab = Syntax.MMasked (Syntax.FCtState, Bytecode.CNe, [0;0;0;2], [0;0;0;0], [0;0;0;0]) in
  let mk_ct st = mk_pkt ~env ~ct:(ct_state st) () in
  check "ct state established matches state = established|untracked = 66 (real nft accepts)"
    (ev_mc m_estab (mk_ct [0;0;0;66]) = true);
  check "ct state established matches a pure established state = 2"
    (ev_mc m_estab (mk_ct [0;0;0;2]) = true);
  check "ct state established does NOT match a state without the established bit (state = 8)"
    (ev_mc m_estab (mk_ct [0;0;0;8]) = false);
  (* the OLD (buggy) MEq lowering rejects the established|untracked packet *)
  let m_old = Syntax.MEq (Syntax.FCtState, [0;0;0;2]) in
  check "the OLD MEq lowering wrongly rejected state = 66 (regression guard)"
    (ev_mc m_old (mk_ct [0;0;0;66]) = false);
  (* COMMA-LIST `ct state new,established,related,untracked` is NOT a set: nft's
     expr_evaluate_list (evaluate.c:1854-1888) OR-folds the four bitmask members
     into one constant new|established|related|untracked = 8|2|4|64 = 0x4e and
     emits the implicit-bitmask test (state & 0x4e) != 0 — golden ct.t.payload:1-5
     `bitwise reg1 = (reg1 & 0x4e) ^ 0 ; cmp neq reg1 0`.  Distinct from the BRACE
     set form above (real lookup).  Before the fix the parser collapsed both to
     SEset -> MConcatSet, so the comma form mis-lowered to a set membership that
     REJECTS a multi-bit state (e.g. 0x06 = established|related) which nft accepts. *)
  let m_comma = Syntax.MMasked (Syntax.FCtState, Bytecode.CNe, [0;0;0;0x4e], [0;0;0;0], [0;0;0;0]) in
  check "ct state new,established,related,untracked OR-folds to (state & 0x4e) != 0"
    (body 4 = [Syntax.BMatch m_comma]);
  (* the comma OR-mask ACCEPTS state = 0x06 (established|related): 0x06 & 0x4e != 0 *)
  check "comma list matches state = established|related = 0x06 (real nft accepts)"
    (ev_mc m_comma (mk_ct [0;0;0;6]) = true);
  (* it still rejects a state with none of the listed bits (e.g. invalid = 1) *)
  check "comma list does NOT match state = invalid = 1 (no listed bit set)"
    (ev_mc m_comma (mk_ct [0;0;0;1]) = false);
  (* the OLD set-membership lowering (before the fix the comma form collapsed to
     SEset -> MConcatSet) wrongly REJECTED state = 0x06: the model's set_mem
     requires an EXACT element, and 0x06 is not one of {8,2,4,64}.  This is the
     bytecode/semantic divergence the fix closes (golden ct.t.payload comma form
     is bitwise+cmp, NOT lookup). *)
  check "the OLD set-membership lowering wrongly REJECTED state = 0x06 (regression guard)"
    (Bytes.set_mem [0;0;0;6]
       [([0;0;0;8],[0;0;0;8]); ([0;0;0;2],[0;0;0;2]);
        ([0;0;0;4],[0;0;0;4]); ([0;0;0;64],[0;0;0;64])] = false);
  (* FLOW-KEYED ct state (soundness): `ct state` is now read from the SHARED,
     flow-keyed conntrack table e_ct at the packet's flow, NOT a free per-packet
     oracle.  The kernel derives state from nf_ct_get(skb)'s entry, so the FIRST
     packet of a flow is NEW (established/related bits clear) and a fabricated packet
     CANNOT match `ct state established` with no flow history.  We model a NEW flow by
     seeding e_ct[flow][CKstate] = new (8); the established match must then FAIL. *)
  let mk_flow_state st flow =
    let env_st = { env with Packet.e_ct =
      (fun fl (k : Packet.ct_key) ->
         match k with Packet.CKstate when fl = flow -> st | _ -> []) } in
    mk_pkt ~env:env_st ~flow () in
  let new_flow = mk_flow_state [0;0;0;8] [42] in
  check "NEW-flow packet does NOT match `ct state established` (no flow history)"
    (ev_mc m_estab new_flow = false);
  (* an ESTABLISHED flow (one a prior packet established) DOES match — not vacuous *)
  let estab_flow = mk_flow_state [0;0;0;2] [42] in
  check "ESTABLISHED-flow packet matches `ct state established`"
    (ev_mc m_estab estab_flow = true);
  (* two packets of the SAME flow read CONSISTENT ct state (flow-keyed, not per-pkt) *)
  let same_flow_a = mk_flow_state [0;0;0;2] [99] in
  let same_flow_b = mk_pkt ~env:(fst same_flow_a) ~flow:[99] () in
  check "two packets of the same flow read consistent `ct state`"
    (dload (Syntax.LCt Packet.CKstate) same_flow_a
       = dload (Syntax.LCt Packet.CKstate) same_flow_b);
  Printf.printf "\n"

(* (I') `ct mark set V` PERSISTS across packets of a flow (cross-packet conntrack).
   Kernel nft_ct.c: nft_ct_set_eval writes V into the SHARED conntrack entry
   (WRITE_ONCE(ct->mark)), so a later packet of the SAME flow reads it back
   (nft_ct_get_eval: READ_ONCE(ct->mark)).  The model now stores writable ct keys
   (mark/label) in the flow-keyed env table e_ct (keyed by pkt_flow), threaded across
   packets by eval_chain_mut_env/set_env — so packet 2 of the flow observes packet 1's
   `ct mark set`, and a DIFFERENT flow does not.  Mirrors CtMark_CrossPacket.v. *)
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
  let c = Nft_inject.find_chain parsed ~table:"t" ~chain:"c" in
  let env = parsed.Nft_inject.p_env in
  (* the rule lowers to a single ct-mark-set statement (writable key) *)
  check "ct mark set 0x99 lowers to SCtSet CKmark (VImm 0x99-le)"
    ((Stdlib.List.nth c.Syntax.c_rules 0).Syntax.r_body
       = [Syntax.BStmt (Syntax.SCtSet (Packet.CKmark, Syntax.VImm mark99))]);
  let flow_a = [10;0;0;1] and flow_b = [10;0;0;2] in
  (* packet 1 of flow A runs the chain; capture the env it leaves *)
  let p1 = mk_pkt ~env ~flow:flow_a () in
  let (v1, e1) = ev_chain_mut_env c p1 in
  check "packet 1 of the flow is accepted (ct mark set; accept)" (v1 = Verdict.Accept);
  check "ct mark set 0x99 is recorded in the shared flow table e_ct"
    (data_eq (e1.Packet.e_ct flow_a Packet.CKmark) mark99);
  (* packet 2 of the SAME flow, with its OWN per-packet ct oracle = 0x07, threaded
     through e1: it reads back the flow mark 0x99 the kernel stored, NOT its oracle *)
  let oracle7 k = (match k with Packet.CKmark -> [7;0;0;0] | _ -> []) in
  let p2_same = (e1, snd (mk_pkt ~env ~ct:oracle7 ~flow:flow_a ())) in
  check "packet 2 of the SAME flow reads back the persisted ct mark 0x99 (kernel-correct)"
    (data_eq (fv Syntax.FCtMark p2_same) mark99);
  check "the persisted flow mark overrides packet 2's own ct oracle (0x07)"
    (not (data_eq (fv Syntax.FCtMark p2_same) [7;0;0;0]));
  (* a packet on a DIFFERENT flow does NOT inherit the mark (flow-scoped, not global) *)
  let p2_other = (e1, snd (mk_pkt ~env ~ct:oracle7 ~flow:flow_b ())) in
  check "a packet on a DIFFERENT flow does NOT see the mark (flow-scoped persistence)"
    (not (data_eq (fv Syntax.FCtMark p2_other) mark99));
  Printf.printf "\n"

(* (I''') `ct mark set` is a NO-OP on a packet with NO conntrack entry.  Kernel
   nft_ct_set_eval (net/netfilter/nft_ct.c:288-290) FIRST does
   `ct = nf_ct_get(skb, &ctinfo); if (ct == NULL || nf_ct_is_template(ct)) return;`,
   so when the packet has no entry the WRITE_ONCE(ct->mark, value) never runs and the
   shared flow table is untouched.  The model gates [set_ct] on [pkt_ct_present]:
   an entryless packet's `ct mark set` leaves e_ct unchanged, so a later same-flow
   ENTRY-PRESENT packet reads its OWN entry's mark, NOT the bogus value — and a
   `ct mark 0x99 accept` rule does NOT spuriously match in the model.  Dual of the
   notrack no-op guard (set_untracked). *)
let check_ct_set_noop () =
  Printf.printf "=== (I''') ct mark set is a NO-OP on a packet with no conntrack entry ===\n";
  let src =
    "table ip t {\n\
    \  chain c {\n\
    \    type filter hook prerouting priority 0; policy drop;\n\
    \    ct mark set 0x99 accept\n\
    \  }\n\
     }\n" in
  let parsed = Nft_parse.parse_string src in
  let c = Nft_inject.find_chain parsed ~table:"t" ~chain:"c" in
  let env = parsed.Nft_inject.p_env in
  let flow_a = [10;0;0;1] in
  (* packet 1 of flow A has NO conntrack entry (pkt_ct_present = false): the kernel
     no-op case.  Running the chain must NOT write the shared flow table. *)
  let p1 = wire (fun p -> { p with Packet.pkt_ct_present = false }) (mk_pkt ~env ~flow:flow_a ()) in
  let (v1, e1) = ev_chain_mut_env c p1 in
  check "entryless packet 1 is still accepted by the chain (ct mark set; accept)"
    (v1 = Verdict.Accept);
  check "ct mark set 0x99 on an ENTRYLESS packet leaves e_ct UNCHANGED (kernel no-op)"
    (data_eq (e1.Packet.e_ct flow_a Packet.CKmark)
             ((fst p1).Packet.e_ct flow_a Packet.CKmark));
  check "the bogus mark 0x99 was NOT recorded in the shared flow table"
    (not (data_eq (e1.Packet.e_ct flow_a Packet.CKmark) mark99));
  (* a later same-flow ENTRY-PRESENT packet 2, threaded through e1, reads ITS OWN
     entry's mark (env default [], here oracle 0x07 is shadowed by the flow table) —
     NOT the bogus 0x99 that the no-op write would have left. *)
  let oracle7 k = (match k with Packet.CKmark -> [7;0;0;0] | _ -> []) in
  let p2 = (e1, { (snd (mk_pkt ~env ~ct:oracle7 ~flow:flow_a ()))
                  with Packet.pkt_ct_present = true }) in
  check "later same-flow entry packet does NOT read back the bogus 0x99 (kernel-correct)"
    (not (data_eq (fv Syntax.FCtMark p2) mark99));
  (* CONTROL: with an ENTRY-PRESENT packet 1, the write DOES land (the persistence
     path is real, not disabled wholesale). *)
  let p1e = wire (fun p -> { p with Packet.pkt_ct_present = true }) (mk_pkt ~env ~flow:flow_a ()) in
  let (_, e1e) = ev_chain_mut_env c p1e in
  check "CONTROL: ct mark set on an ENTRY-PRESENT packet DOES record 0x99"
    (data_eq (e1e.Packet.e_ct flow_a Packet.CKmark) mark99);
  Printf.printf "\n"

(* (I'') ct/meta SET value width is KEY-SPECIFIC, not always the 4-byte mark
   register.  The kernel stores `ct zone` as a u16 (nft_ct.c nft_reg_load16 ->
   zone.id), `ct mark`/`ct event`/`meta mark`/`meta priority` as a u32, `ct
   label` as a 128-bit value, and `meta pkttype` as a u8.  The parser used to
   hardcode the 4-byte KMark shape for ALL of them, so `ct zone set 1` wrongly
   stored 4 bytes.  After the fix each key encodes at its own register width. *)
let check_ct_meta_set_width () =
  Printf.printf "=== (I'') ct/meta set value width is key-specific (zone u16, mark u32) ===\n";
  let body_of src ~table ~chain =
    let parsed = Nft_parse.parse_string src in
    let c = Nft_inject.find_chain parsed ~table ~chain in
    (Stdlib.List.nth c.Syntax.c_rules 0).Syntax.r_body in
  (* ct zone set 1 -> 2-byte (u16) host-endian value [1;0], NOT [1;0;0;0] *)
  let zb = body_of
    "table ip t {\n  chain c {\n    ct zone set 1\n  }\n}\n" ~table:"t" ~chain:"c" in
  check "ct zone set 1 lowers to SCtSet CKzone (VImm [1;0]) (u16, 2 bytes)"
    (zb = [Syntax.BStmt (Syntax.SCtSet (Packet.CKzone, Syntax.VImm [1;0]))]);
  check "ct zone value is exactly 2 bytes wide (kernel u16, not the 4-byte mark)"
    (match zb with
     | [Syntax.BStmt (Syntax.SCtSet (Packet.CKzone, Syntax.VImm v))] ->
         Stdlib.List.length v = 2
     | _ -> false);
  (* ct mark set 5 -> still 4-byte (u32) host-endian [5;0;0;0] *)
  let mb = body_of
    "table ip t {\n  chain c {\n    ct mark set 5\n  }\n}\n" ~table:"t" ~chain:"c" in
  check "ct mark set 5 still lowers to a 4-byte u32 value [5;0;0;0]"
    (mb = [Syntax.BStmt (Syntax.SCtSet (Packet.CKmark, Syntax.VImm [5;0;0;0]))]);
  (* meta mark set 7 -> 4-byte (u32) host-endian [7;0;0;0] *)
  let mmb = body_of
    "table ip t {\n  chain c {\n    mark set 7\n  }\n}\n" ~table:"t" ~chain:"c" in
  check "meta mark set 7 lowers to a 4-byte u32 value [7;0;0;0]"
    (mmb = [Syntax.BStmt (Syntax.SMetaSet (Packet.MKmark, Syntax.VImm [7;0;0;0]))]);
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
  let c = Nft_inject.find_chain parsed ~table:"t" ~chain:"c" in
  let env = parsed.Nft_inject.p_env in
  (* (2) the lowered vmap carries a genuine INTERVAL entry: lo=[0;0] hi=[0;100],
     i.e. a non-degenerate [lo,hi] (not a point [k,k]). *)
  let vm_name = match Syntax.r_vmap (Stdlib.List.hd c.Syntax.c_rules) with
    | Some vm -> vm.Syntax.vm_name | None -> failwith "no vmap lowered" in
  let ents = env.Packet.e_vmap vm_name in
  let has_iv = Stdlib.List.exists (fun ((lo, hi), _) -> lo <> hi) ents in
  check "the range key lowers to a non-degenerate [lo,hi] interval entry" has_iv;
  (* (3) behaviour: dport 80 is INSIDE [0,100] -> Drop (the unsound case the model
     previously got wrong: it fell through to the accept policy). *)
  let pkt dport = mk_pkt ~env ~l4proto:l4_tcp ~th:(th_dport dport) () in
  check "dport 80 (inside 0-100) -> DROP (interval lookup; was wrongly accepted)"
    (ev_chain c (pkt 80) = Verdict.Drop);
  check "dport 0 (lower bound) -> DROP"
    (ev_chain c (pkt 0) = Verdict.Drop);
  check "dport 100 (upper bound) -> DROP"
    (ev_chain c (pkt 100) = Verdict.Drop);
  (* (4) the point key 101 still matches exactly -> Accept. *)
  check "dport 101 (exact point key) -> ACCEPT"
    (ev_chain c (pkt 101) = Verdict.Accept);
  (* (5) a key OUTSIDE every interval misses -> falls through to accept policy. *)
  check "dport 200 (outside all keys) -> falls through to accept policy"
    (ev_chain c (pkt 200) = Verdict.Accept);
  Printf.printf "\n"

(* (I'') `notrack` forces ct state to UNTRACKED for the rest of the traversal, so a
   LATER `ct state` read observes NF_CT_STATE_UNTRACKED_BIT (= 64).  Kernel nft_ct.c:
   nft_notrack_eval calls nf_ct_set(skb, NULL, IP_CT_UNTRACKED); nft_ct_get_eval's
   NFT_CT_STATE case then returns NF_CT_STATE_UNTRACKED_BIT.  The model now applies
   set_untracked on SNotrack/INotrack (body_step/run_rule_step), threaded across
   rules by eval_chain_mut.  set_untracked mirrors nft_notrack_eval's guard
   `if (ct || ctinfo == IP_CT_UNTRACKED) return;`: it is a NO-OP when an entry already
   exists (pkt_ct_present = true) and otherwise sets pkt_untracked, so do_load
   (LCt CKstate) returns [0;0;0;64] only on a no-entry packet.  Thus
   `notrack ; ct state untracked accept` ACCEPTS a NO-ENTRY packet and DROPS an
   entry-present (e.g. ESTABLISHED) one.  Mirrors Notrack_CrossRule.v. *)
let check_notrack () =
  Printf.printf "=== (I'') notrack forces ct state untracked (later ct state read sees it) ===\n";
  let untracked = [0;0;0;64] in   (* NF_CT_STATE_UNTRACKED_BIT *)
  (* `ct state untracked`: single-positive bitmask form (state & 64) != 0 *)
  let m_untracked =
    Syntax.MMasked (Syntax.FCtState, Bytecode.CNe, untracked, [0;0;0;0], [0;0;0;0]) in
  let notrack_only : Syntax.rule =
    { Syntax.r_body = [ Syntax.BStmt Syntax.SNotrack ]; r_outcome = Syntax.ONone; r_after = [] } in
  let ctstate_rule : Syntax.rule =
    { Syntax.r_body = [ Syntax.BMatch m_untracked ]; r_outcome = Syntax.OVerdict Verdict.Accept; r_after = [] } in
  let chain : Syntax.chain =
    { Syntax.c_policy = Verdict.Drop; c_rules = [ notrack_only; ctstate_rule ] } in
  let env = { Packet.e_set = (fun _ -> []); e_vmap = (fun _ -> []); e_map = (fun _ -> []);
              e_routes = []; e_rt = (fun _ -> []); e_limit = (fun _ -> 0);
              e_quota = (fun _ -> 0); e_ifaddrs = (fun _ -> []); e_ifaddrs6 = (fun _ -> []);
              e_connlimit = (fun _ -> []); e_ct = (fun _ _ -> []); e_nat = (fun _ -> None); e_numgen = (fun _ -> 0) } in
  (* a NO-ENTRY packet (pkt_ct_present = false): nf_ct_get returns NULL, the only
     case where `notrack` has an effect (nft_notrack_eval's
     `if (ct || ctinfo == IP_CT_UNTRACKED) return;` guard).  The notrack in rule 1
     latches it untracked before rule 2's `ct state untracked` match. *)
  let oracle_new k = (match k with Packet.CKstate -> [0;0;0;8] | _ -> []) in
  let p = wire (fun q -> { q with Packet.pkt_ct_present = false })
            (mk_pkt ~env ~ct:oracle_new ~flow:[7;7] ()) in
  (* the notrack write threads into rule 2: the threaded packet reads UNTRACKED *)
  let p1 = dsl_writes_on notrack_only p in
  check "notrack sets pkt_untracked := true" ((snd p1).Packet.pkt_untracked);
  check "after notrack, ct state read returns NF_CT_STATE_UNTRACKED_BIT (64)"
    (data_eq (dload (Syntax.LCt Packet.CKstate) p1) untracked);
  check "the `ct state untracked` match SUCCEEDS on the threaded packet"
    (ev_mc m_untracked p1);
  (* the threading evaluator ACCEPTS the no-entry packet (kernel-correct);
     without the rule-walk fix it DROPPED it (notrack skipped, stale oracle read) *)
  check "notrack ; ct state untracked accept ACCEPTS a no-entry packet (kernel-correct)"
    (ev_chain_mut chain p = Verdict.Accept);
  (* and the same chain DROPS the packet if rule 1 is removed (no notrack => no-entry
     state INVALID = 1, (1 & 64) = 0 => no match => Drop policy): acceptance is DUE TO
     notrack *)
  let chain_no_notrack : Syntax.chain =
    { Syntax.c_policy = Verdict.Drop; c_rules = [ ctstate_rule ] } in
  check "without the preceding notrack the same packet is DROPPED (effect is real)"
    (ev_chain_mut chain_no_notrack p = Verdict.Drop);
  (* KERNEL GUARD: on a packet that ALREADY has a conntrack ENTRY, notrack is a NO-OP.
     With an ESTABLISHED entry the threaded `ct state` reads the live state [0;0;0;2],
     the `ct state untracked` match FAILS, and the chain DROPS. *)
  let env_est = { env with Packet.e_ct =
                    (fun _ k -> match k with Packet.CKstate -> [0;0;0;2] | _ -> []) } in
  let p_entry = wire (fun q -> { q with Packet.pkt_ct_present = true })
                  (mk_pkt ~env:env_est ~flow:[9;9] ()) in
  let p_entry1 = dsl_writes_on notrack_only p_entry in
  check "notrack is a NO-OP on an entry-present packet (pkt_untracked stays false)"
    (not (snd p_entry1).Packet.pkt_untracked);
  check "after a no-op notrack, ct state read returns the live ESTABLISHED state (2)"
    (data_eq (dload (Syntax.LCt Packet.CKstate) p_entry1) [0;0;0;2]);
  check "notrack ; ct state untracked DROPS an entry-present packet (kernel no-op)"
    (ev_chain_mut chain p_entry = Verdict.Drop);
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
      r_outcome = Syntax.OVerdict Verdict.Drop; r_after = [] } in
  let chain : Syntax.chain =
    { Syntax.c_policy = Verdict.Accept; c_rules = [ maxseg_drop ] } in
  let env = { Packet.e_set = (fun _ -> []); e_vmap = (fun _ -> []); e_map = (fun _ -> []);
              e_routes = []; e_rt = (fun _ -> []); e_limit = (fun _ -> 0);
              e_quota = (fun _ -> 0); e_ifaddrs = (fun _ -> []); e_ifaddrs6 = (fun _ -> []);
              e_connlimit = (fun _ -> []); e_ct = (fun _ _ -> []); e_nat = (fun _ -> None);
              e_numgen = (fun _ -> 0) } in
  (* ABSENT: existence oracle (present=true) returns [0]; the value oracle returns
     the matching bytes anyway (the impossible-in-kernel state the model used to
     admit).  The guard must REFUSE to load the value, so the chain ACCEPTS. *)
  let eh_absent _ _ _ _ pr = if pr then [0] else maxseg_val in
  let p_absent = wire (fun p -> { p with Packet.pkt_eh = eh_absent }) (mk_pkt ~env ()) in
  check "VALUE load of an ABSENT tcp option is NOT loadable"
    (not (Syntax.field_loadable f_maxseg (snd p_absent)));
  check "EXISTENCE load (present=true) IS loadable even when absent"
    (Syntax.field_loadable (Syntax.FExthdr (Packet.EPtcpopt, 2, 0, 0, true)) (snd p_absent));
  check "absent maxseg -> NFT_BREAK -> chain ACCEPTS (eval_chain, kernel-correct)"
    (ev_chain chain p_absent = Verdict.Accept);
  check "absent maxseg -> chain ACCEPTS (eval_chain_mut, kernel-correct)"
    (ev_chain_mut chain p_absent = Verdict.Accept);
  (* PRESENT: existence oracle returns [1]; the value matches -> DROP. *)
  let eh_present _ _ _ _ pr = if pr then [1] else maxseg_val in
  let p_present = wire (fun p -> { p with Packet.pkt_eh = eh_present }) (mk_pkt ~env ()) in
  check "PRESENT maxseg with matching value -> chain DROPS (eval_chain)"
    (ev_chain chain p_present = Verdict.Drop);
  check "PRESENT maxseg with matching value -> chain DROPS (eval_chain_mut)"
    (ev_chain_mut chain p_present = Verdict.Drop);
  Printf.printf "\n"

(* (I''') INTRA-RULE notrack->ct-state: `ct notrack ct state untracked accept` in ONE
   rule.  The kernel runs a rule's expressions left-to-right (nf_tables_core.c
   nft_rule_dp_for_each_expr): on a NO-ENTRY packet nft_notrack_eval latches
   IP_CT_UNTRACKED, then the SAME rule's `ct state untracked` (nft_ct_get_eval
   NFT_CT_STATE) reads NF_CT_STATE_UNTRACKED_BIT and matches -> ACCEPT; on an
   entry-present packet notrack is a no-op (its `if (ct || ...) return;` guard) so the
   match reads the live state and FAILS -> the chain DROPS.  The model threads
   set_untracked (which encodes that guard) into a rule's OWN later matches/terminal
   (rule_applies_walk/outcome/run_rule), so the single-rule idiom ACCEPTS a no-entry
   packet and DROPS an entry-present one, matching the kernel.  Before the rule-walk
   fix the match was evaluated against the original packet and PROVED a kernel-false
   Drop even on the no-entry packet. *)
let check_notrack_intra () =
  Printf.printf "=== (I''') intra-rule notrack ; ct state untracked accept (same rule) ===\n";
  let untracked = [0;0;0;64] in
  let m_untracked =
    Syntax.MMasked (Syntax.FCtState, Bytecode.CNe, untracked, [0;0;0;0], [0;0;0;0]) in
  (* ONE rule: SNotrack statement BEFORE the ct-state match. *)
  let intra_rule : Syntax.rule =
    { Syntax.r_body = [ Syntax.BStmt Syntax.SNotrack; Syntax.BMatch m_untracked ];
      r_outcome = Syntax.OVerdict Verdict.Accept; r_after = [] } in
  let chain : Syntax.chain =
    { Syntax.c_policy = Verdict.Drop; c_rules = [ intra_rule ] } in
  let env = { Packet.e_set = (fun _ -> []); e_vmap = (fun _ -> []); e_map = (fun _ -> []);
              e_routes = []; e_rt = (fun _ -> []); e_limit = (fun _ -> 0);
              e_quota = (fun _ -> 0); e_ifaddrs = (fun _ -> []); e_ifaddrs6 = (fun _ -> []);
              e_connlimit = (fun _ -> []); e_ct = (fun _ _ -> []); e_nat = (fun _ -> None); e_numgen = (fun _ -> 0) } in
  let oracle_new k = (match k with Packet.CKstate -> [0;0;0;8] | _ -> []) in
  (* NO-ENTRY packet (pkt_ct_present = false): the case where notrack has effect. *)
  let p = wire (fun q -> { q with Packet.pkt_ct_present = false })
            (mk_pkt ~env ~ct:oracle_new ~flow:[7;7] ()) in
  (* the rule's own statement->match ordering: the match now SUCCEEDS *)
  check "intra-rule: the rule APPLIES (notrack latch seen by its own later match)"
    (rule_applies_on intra_rule p);
  check "intra-rule: eval_chain ACCEPTS a no-entry packet (kernel-correct)"
    (ev_chain chain p = Verdict.Accept);
  check "intra-rule: eval_chain_mut ACCEPTS too"
    (ev_chain_mut chain p = Verdict.Accept);
  (* the verified compiler agrees: the compiled bytecode runs to the same verdict *)
  check "intra-rule: the COMPILED chain ACCEPTS (compile_chain_correct instance)"
    (run_chain_vm (Compile.compile_chain chain) chain.Syntax.c_policy p
       = Verdict.Accept);
  (* KERNEL GUARD: on an entry-present packet (ESTABLISHED), the intra-rule notrack is
     a NO-OP, the same-rule `ct state untracked` match FAILS, and the chain DROPS. *)
  let env_est = { env with Packet.e_ct =
                    (fun _ k -> match k with Packet.CKstate -> [0;0;0;2] | _ -> []) } in
  let p_entry = wire (fun q -> { q with Packet.pkt_ct_present = true })
                  (mk_pkt ~env:env_est ~flow:[9;9] ()) in
  check "intra-rule: the rule does NOT apply on an entry-present packet (notrack no-op)"
    (not (rule_applies_on intra_rule p_entry));
  check "intra-rule: eval_chain DROPS an entry-present packet (kernel no-op)"
    (ev_chain chain p_entry = Verdict.Drop);
  check "intra-rule: the COMPILED chain DROPS the entry-present packet too"
    (run_chain_vm (Compile.compile_chain chain) chain.Syntax.c_policy p_entry
       = Verdict.Drop);
  Printf.printf "\n"

(* (J) SINGLE POSITIVE `tcp flags X` BITMASK lowering.  tcp_flag_type has
   .basetype = &bitmask_type (proto.c:583-591); the OP_IMPLICIT->OP_EQ rewrite
   (evaluate.c:2792-2797) does NOT fire for it, so a bare `tcp flags X` stays an
   implicit bitmask test, emitted (golden inet/tcp.t.payload:331-337) as
     [ bitwise reg1 = (reg1 & X) ^ 0 ]  [ cmp neq reg1 0 ]
   i.e. (flags & X) != 0, NOT flags == X.  The four written operators differ
   (tests/py/inet/tcp.t:69-74):
     implicit `tcp flags X`    -> MMasked (FTcpFlags, CNe,   [X], [0], [0])
     bang     `tcp flags ! X`  -> MMasked (FTcpFlags, CEq, [X], [0], [0])
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
  let c = Nft_inject.find_chain parsed ~table:"t" ~chain:"c" in
  let env = parsed.Nft_inject.p_env in
  (* the l4proto-tcp dependency is prepended; the tcp-flags match is the LAST
     body item of each rule *)
  let last_match i =
    let b = (Stdlib.List.nth c.Syntax.c_rules i).Syntax.r_body in
    Stdlib.List.nth b (Stdlib.List.length b - 1) in
  (* `tcp flags syn` => (flags & 0x02) != 0, MMasked neg=true — NOT MEq *)
  check "tcp flags syn lowers to MMasked bitmask test (not MEq)"
    (last_match 0 = Syntax.BMatch
       (Syntax.MMasked (Syntax.FTcpFlags, Bytecode.CNe, [2], [0], [0])));
  (* `tcp flags ! syn` => (flags & 0x02) == 0, MMasked neg=false *)
  check "tcp flags ! syn lowers to MMasked (flags & syn) == 0"
    (last_match 1 = Syntax.BMatch
       (Syntax.MMasked (Syntax.FTcpFlags, Bytecode.CEq, [2], [0], [0])));
  (* `tcp flags == syn` => exact equality, MEq *)
  check "tcp flags == syn lowers to exact MEq"
    (last_match 2 = Syntax.BMatch (Syntax.MEq (Syntax.FTcpFlags, [2])));
  (* `tcp flags != cwr` => plain cmp neq, MNeq *)
  check "tcp flags != cwr lowers to plain MNeq"
    (last_match 3 = Syntax.BMatch (Syntax.MNeq (Syntax.FTcpFlags, [128])));
  (* THE KEY behavioural case: a SYN|ACK packet (flags = 0x12 = 18). *)
  let mk_fl fl = mk_pkt ~env ~l4proto:l4_tcp ~th:(th_flags fl) () in
  let m_syn = Syntax.MMasked (Syntax.FTcpFlags, Bytecode.CNe, [2], [0], [0]) in
  check "tcp flags syn matches a SYN|ACK packet (flags=0x12) — real nft accepts"
    (ev_mc m_syn (mk_fl 18) = true);
  check "tcp flags syn matches a pure SYN packet (flags=0x02)"
    (ev_mc m_syn (mk_fl 2) = true);
  check "tcp flags syn does NOT match ACK-only (flags=0x10)"
    (ev_mc m_syn (mk_fl 16) = false);
  (* the OLD (only buildable) MEq encoding wrongly rejected SYN|ACK *)
  let m_old = Syntax.MEq (Syntax.FTcpFlags, [2]) in
  check "the OLD MEq encoding wrongly rejected SYN|ACK (regression guard)"
    (ev_mc m_old (mk_fl 18) = false);
  (* explicit `== syn` is genuine equality: rejects SYN|ACK, accepts pure SYN *)
  let m_eq = Syntax.MEq (Syntax.FTcpFlags, [2]) in
  check "tcp flags == syn (explicit) rejects SYN|ACK, accepts pure SYN"
    (ev_mc m_eq (mk_fl 18) = false
     && ev_mc m_eq (mk_fl 2) = true);
  Printf.printf "\n"

(* ---------- (L) meta nfproto is the NFPROTO L3 family, not L4 proto ----------
   `meta nfproto` reads the netfilter family register (NFPROTO family), a
   distinct 1-byte datatype from the L4/IP-protocol space.  datatype.c
   nfproto_tbl maps only ipv4=NFPROTO_IPV4=2 and ipv6=NFPROTO_IPV6=10.  Golden
   inet/meta.t.payload: `meta nfproto ipv4` => cmp eq reg1 0x02,
   `meta nfproto ipv6` => cmp eq reg1 0x0a.  These corpus rules (inet/meta.t:6-7
   ;ok) were UNSUPPORTED before the fix because nfproto was wired to the
   L4-protocol table (tcp=6/udp=17/... — no ipv4/ipv6). *)
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
  let c = Nft_inject.find_chain parsed ~table:"t" ~chain:"c" in
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
    let c = Nft_inject.find_chain p ~table:"t" ~chain:"c" in
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
      .Nft_inject.p_env in
  (* network bytes 12..15 = 10.1.2.3.  In an IPv4 header that's the SOURCE
     ADDRESS; in an IPv6 header it's part of the (longer) source address. *)
  let nh_v4 = [0;0;0;0; 0;0;0;0; 0;0;0;0; 10;1;2;3] in
  let mk_with_nfproto nfp nh =
    wire (fun p ->
      { p with
        Packet.pkt_nh = nh;
        pkt_meta = (fun k -> match k with Packet.MKnfproto -> nfp | _ -> []) })
      (mk_pkt ~env ()) in
  let p_v4 = mk_with_nfproto [2]  nh_v4 in   (* genuine IPv4 packet *)
  let p_v6 = mk_with_nfproto [10] nh_v4 in   (* IPv6 packet, same byte pattern *)
  let guarded : Syntax.chain =
    { Syntax.c_policy = Verdict.Drop;
      c_rules = [ { Syntax.r_body =
                      [ Syntax.BMatch (Syntax.MEq (Syntax.FMetaNfproto, [2]));
                        Syntax.BMatch (Syntax.MEq (Syntax.FIp4Saddr, [10;1;2;3])) ];
                    r_outcome = Syntax.OVerdict Verdict.Accept; r_after = [] } ] } in
  let unguarded : Syntax.chain =     (* the OLD, buggy lowering *)
    { Syntax.c_policy = Verdict.Drop;
      c_rules = [ { Syntax.r_body =
                      [ Syntax.BMatch (Syntax.MEq (Syntax.FIp4Saddr, [10;1;2;3])) ];
                    r_outcome = Syntax.OVerdict Verdict.Accept; r_after = [] } ] } in
  check "guarded inet rule ACCEPTS the genuine IPv4 packet (nft accepts)"
    (ev_chain guarded p_v4 = Verdict.Accept);
  check "guarded inet rule DROPS the IPv6 packet (nft falls through to drop)"
    (ev_chain guarded p_v6 = Verdict.Drop);
  check "the OLD unguarded rule WRONGLY accepted the IPv6 packet (regression guard)"
    (ev_chain unguarded p_v6 = Verdict.Accept);
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
    let c = Nft_inject.find_chain p ~table:"t" ~chain:"c" in
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
      .Nft_inject.p_env in
  (* an IPv6 packet whose kernel-computed l4proto is 1 (next-header 1) and whose
     transport byte 0 is 8: the model's UNGUARDED body wrongly matched it. *)
  let mk_with nfp l4p th =
    wire (fun p ->
      { p with
        Packet.pkt_th = th;
        pkt_meta = (fun k -> match k with
          | Packet.MKnfproto -> nfp | Packet.MKl4proto -> l4p | _ -> []) })
      (mk_pkt ~env ()) in
  let p_v4 = mk_with [2]  [1] [8] in   (* genuine IPv4 icmp echo-request *)
  let p_v6 = mk_with [10] [1] [8] in   (* IPv6 packet, l4proto 1 + th byte 8 *)
  let guarded : Syntax.chain =
    { Syntax.c_policy = Verdict.Drop;
      c_rules = [ { Syntax.r_body =
                      [ Syntax.BMatch (Syntax.MEq (Syntax.FMetaNfproto, [2]));
                        Syntax.BMatch (Syntax.MEq (Syntax.FMetaL4proto, [1]));
                        Syntax.BMatch (Syntax.MEq (Syntax.FIcmpType, [8])) ];
                    r_outcome = Syntax.OVerdict Verdict.Accept; r_after = [] } ] } in
  let unguarded : Syntax.chain =     (* the OLD, buggy lowering: l4proto only *)
    { Syntax.c_policy = Verdict.Drop;
      c_rules = [ { Syntax.r_body =
                      [ Syntax.BMatch (Syntax.MEq (Syntax.FMetaL4proto, [1]));
                        Syntax.BMatch (Syntax.MEq (Syntax.FIcmpType, [8])) ];
                    r_outcome = Syntax.OVerdict Verdict.Accept; r_after = [] } ] } in
  check "guarded inet icmp rule ACCEPTS the genuine IPv4 packet (nft accepts)"
    (ev_chain guarded p_v4 = Verdict.Accept);
  check "guarded inet icmp rule DROPS the IPv6 packet (nft falls through to drop)"
    (ev_chain guarded p_v6 = Verdict.Drop);
  check "the OLD unguarded icmp rule WRONGLY accepted the IPv6 packet (regression)"
    (ev_chain unguarded p_v6 = Verdict.Accept);
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
      .Nft_inject.p_env in
  (* the SSynproxy statement is not on the .nft frontend, so build the AST directly *)
  let rule : Syntax.rule =
    { Syntax.r_body = [ Syntax.BStmt (Syntax.SSynproxy (1460, 7)) ];
      r_outcome = Syntax.ONone; r_after = [] } in
  let chain : Syntax.chain = { Syntax.c_policy = Verdict.Accept; c_rules = [ rule ] } in
  let mk_tcp fl = mk_pkt ~env ~l4proto:l4_tcp ~th:(th_flags fl) () in
  let non_tcp = wire (fun p -> { p with Packet.pkt_th = []; pkt_have_l4 = false }) (mk_pkt ~env ()) in
  check "synproxy STOPS a TCP SYN packet (NF_STOLEN -> Drop)"
    (ev_chain chain (mk_tcp 2) = Verdict.Drop);
  check "synproxy STOPS a TCP ACK packet (NF_STOLEN/NF_DROP -> Drop)"
    (ev_chain chain (mk_tcp 16) = Verdict.Drop);
  check "synproxy CONTINUEs a bare-RST TCP packet (falls through to policy accept)"
    (ev_chain chain (mk_tcp 4) = Verdict.Accept);
  check "synproxy does NOT apply to a non-TCP packet (NFT_BREAK -> policy accept)"
    (ev_chain chain non_tcp = Verdict.Accept);
  (* the red agent's no-op claim is refuted: not constant across packets *)
  check "synproxy is NOT a verdict no-op (SYN vs RST differ)"
    (ev_chain chain (mk_tcp 2) <> ev_chain chain (mk_tcp 4));
  (* the compiled bytecode agrees (compile_chain_correct) *)
  let pol = chain.Syntax.c_policy in
  let prog = Compile.compile_chain chain in
  check "compiled bytecode STOPS the SYN packet too"
    (run_chain_vm prog pol (mk_tcp 2) = Verdict.Drop);
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
  let c = Nft_inject.find_chain parsed ~table:"t" ~chain:"c" in
  let env = parsed.Nft_inject.p_env in
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
    wire (fun p -> { p with Packet.pkt_nh = (L.init 16 (fun _ -> 0)) @ daddr })
      (mk_pkt ~env ~l4proto:l4_tcp ~th:(th_dport dport) ()) in
  let p_bad  = mk_pkt2 ~daddr:[10;0;0;5] ~dport:100 in   (* dport 100 not in [10,23] *)
  let p_good = mk_pkt2 ~daddr:[10;0;0;5] ~dport:20  in   (* both fields in range *)
  let p_dout = mk_pkt2 ~daddr:[11;0;0;5] ~dport:20  in   (* daddr out of range *)
  let m = match the_concat with
    | Some (Syntax.BMatch mc) -> mc | _ -> failwith "no concat match" in
  check "REJECTS daddr in-range but dport OUT of range (kernel drops; old flat model wrongly accepted)"
    (ev_mc m p_bad = false);
  check "ACCEPTS only when BOTH fields are in their own range"
    (ev_mc m p_good = true);
  check "REJECTS daddr out of range (even with dport in range)"
    (ev_mc m p_dout = false);
  (* the OLD flat-lexicographic set_mem wrongly accepted p_bad: demonstrate the
     divergence directly on the stored element. *)
  check "flat set_mem over the concatenation WOULD accept the bad packet (the bug)"
    (Bytes.set_mem ([10;0;0;5] @ port 100) elems = true);
  check "per-field concat_set_mem REJECTS it (the fix)"
    (Bytes.concat_set_mem [ [10;0;0;5]; port 100 ] elems = false);
  (* the compiled bytecode agrees with the spec (compile_chain_correct) *)
  let prog = Compile.compile_chain c in
  check "compiled bytecode REJECTS the bad packet too (run_chain = policy, rule skipped)"
    (run_chain_vm prog c.Syntax.c_policy p_bad = Verdict.Accept
     && ev_chain c p_bad = Verdict.Accept);
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
  let c2 = Nft_inject.find_chain parsed2 ~table:"t" ~chain:"c" in
  let env2 = parsed2.Nft_inject.p_env in
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
    (ev_mc m2 (mk_p2 ~sport:80 ~dport:443) = true);
  check "rejects (80, 444): dport differs"
    (ev_mc m2 (mk_p2 ~sport:80 ~dport:444) = false);
  check "rejects (81, 443): non-last sport differs (would be missed if sport's slot were mis-split)"
    (ev_mc m2 (mk_p2 ~sport:81 ~dport:443) = false);
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
  let c = Nft_inject.find_chain parsed ~table:"t" ~chain:"c" in
  let env = parsed.Nft_inject.p_env in
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
    wire (fun p ->
      { p with Packet.pkt_meta = (fun k -> match k with Packet.MKiifname -> nm | _ -> []) })
      (mk_pkt ~env ()) in
  let reg_d0e = [0x64;0x75;0x6d;0x6d;0x79;0x30;0x65;0x78;0x74;0x72;0x61; 0;0;0;0;0] in
  let m_exact = Syntax.MEq (Syntax.FMetaIifname, dummy0_16) in
  let m_wild  = Syntax.MEq (Syntax.FMetaIifname, ascii "dummy") in
  check "exact `iifname dummy0` MATCHES the interface it names"
    (ev_mc m_exact (mk_iifn dummy0_16) = true);
  check "exact `iifname dummy0` REJECTS the distinct iface dummy0extra (the fix; kernel drops)"
    (ev_mc m_exact (mk_iifn reg_d0e) = false);
  check "the OLD unpadded literal WOULD wrongly accept dummy0extra (the bug)"
    (ev_mc (Syntax.MEq (Syntax.FMetaIifname, ascii "dummy0"))
       (mk_iifn reg_d0e) = true);
  check "the `*` wildcard correctly remains a prefix match (matches dummy0extra)"
    (ev_mc m_wild (mk_iifn reg_d0e) = true);
  (* compiled bytecode agrees with the spec on the distinct interface *)
  let prog = Compile.compile_chain c in
  check "compiled bytecode also rejects dummy0extra at the exact rule (= policy accept, both rules skip)"
    (run_chain_vm prog c.Syntax.c_policy (mk_iifn [0x7a;0x7a;0x7a; 0;0;0;0;0; 0;0;0;0; 0;0;0;0]) = Verdict.Accept);
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
    \    limit rate 1/second accept\n\
    \    limit rate over 1/second drop\n\
    \  }\n\
     }\n" in
  let parsed = Nft_parse.parse_string src in
  let c = Nft_inject.find_chain parsed ~table:"t" ~chain:"c" in
  let env = parsed.Nft_inject.p_env in
  let body i = (Stdlib.List.nth c.Syntax.c_rules i).Syntax.r_body in
  (* `limit rate 1/second` => MLimit with ls_flags bit 0 = 0 (non-inverted) *)
  check "limit rate 1/second lowers to MLimit with ls_flags=0 (non-over)"
    (match body 0 with
     | [Syntax.BMatch (Syntax.MLimit s)] -> s.Packet.ls_flags = 0
     | _ -> false);
  (* `limit rate over 1/second` => MLimit with ls_flags bit 0 = 1 (inverted) *)
  check "limit rate over 1/second lowers to MLimit with ls_flags=1 (over/inverted)"
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
    (ev_mc m_under (mk_pkt ~env:env_under ()) = true
     && ev_mc m_over (mk_pkt ~env:env_under ()) = false);
  (* EXCEEDING the rate: the plain `limit` stops (no match) while the `over`
     limiter MATCHES — the standard anti-flood `limit rate over X drop` idiom. *)
  check "exceeding the rate: plain `limit` misses but `limit over` matches (flip)"
    (ev_mc m_under (mk_pkt ~env:env_over ()) = false
     && ev_mc m_over (mk_pkt ~env:env_over ()) = true);
  (* The flag is genuinely read: for the SAME oracle, over and non-over disagree. *)
  check "over and non-over give opposite verdicts for the same oracle (flag honoured)"
    (ev_mc m_over (mk_pkt ~env:env_under ())
       <> ev_mc m_under (mk_pkt ~env:env_under ()));
  (* CROSS-PACKET CONSUMPTION (the blue fix): a `limit` is a SHARED, CONSUMING token
     bucket, not a stateless per-packet oracle.  Build a one-rule chain
     `limit rate 1/second accept`, policy DROP, against an env whose bucket holds
     exactly ONE token.  Thread packet 1 -> its verdict + the env it LEAVES; build
     packet 2 of the SAME flow carrying that env; run again.  The kernel ACCEPTS
     packet 1 (one token), the bucket EMPTIES, and packet 2 of the depleted bucket
     is DROPPED (chain policy).  The OLD per-packet oracle proved BOTH accepted. *)
  let rule_accept =
    { Syntax.r_body = [Syntax.BMatch m_under]; r_outcome = Syntax.OVerdict Verdict.Accept; r_after = [] } in
  let chain_lim = { Syntax.c_policy = Verdict.Drop; c_rules = [rule_accept] } in
  let env_one = { env with Packet.e_limit = (fun _ -> 1) } in
  let p1 = mk_pkt ~env:env_one ~flow:[1;1] () in
  let (v1, e_after) = ev_chain_mut_env chain_lim p1 in
  let p2 = mk_pkt ~env:e_after ~flow:[1;1] () in
  let (v2, _) = ev_chain_mut_env chain_lim p2 in
  check "consuming bucket: packet 1 ACCEPTED (one token available)"
    (v1 = Verdict.Accept);
  check "consuming bucket: token CONSUMED (env left by packet 1 has 0 tokens)"
    (e_after.Packet.e_limit s_under = 0);
  check "consuming bucket: packet 2 of the depleted bucket DROPPED (policy)"
    (v2 = Verdict.Drop);
  check "consecutive packets get DIFFERENT verdicts (a rate limit actually limits)"
    (v1 <> v2);
  (* RATE/UNIT ARE NOW LIVE (the core of this fix): the per-packet COST is
     window(unit)/rate, so a 1/second limiter (cost = 1 token) and a 1/hour
     limiter (cost = 3600 tokens) give DIFFERENT verdicts at the SAME bucket
     level.  Parse both, point e_limit at a 1-token bucket, and check the fast
     one passes while the slow one fails — the configured rate/unit are no longer
     inert (pre-fix they were never consulted in the dynamics). *)
  let src2 =
    "table ip t2 {\n\
    \  chain c {\n\
    \    type filter hook input priority 0; policy accept;\n\
    \    limit rate 1/second accept\n\
    \    limit rate 1/hour accept\n\
    \  }\n\
     }\n" in
  let p2parsed = Nft_parse.parse_string src2 in
  let c2 = Nft_inject.find_chain p2parsed ~table:"t2" ~chain:"c" in
  let body2 i = (Stdlib.List.nth c2.Syntax.c_rules i).Syntax.r_body in
  let spec2 i = match body2 i with
    | [Syntax.BMatch (Syntax.MLimit s)] -> s | _ -> assert false in
  let s_fast = spec2 0 and s_slow = spec2 1 in
  check "1/second and 1/hour lower to DIFFERENT units (rate/unit captured)"
    (s_fast.Packet.ls_unit <> s_slow.Packet.ls_unit);
  let env_tok = { env with Packet.e_limit = (fun _ -> 1) } in
  let pk = mk_pkt ~env:env_tok () in
  check "rate is LIVE: at a 1-token bucket, 1/second PASSES but 1/hour FAILS"
    (ev_mc (Syntax.MLimit s_fast) pk = true
     && ev_mc (Syntax.MLimit s_slow) pk = false);
  Printf.printf "\n"

(* (M) fib route-type symbol -> RTN_ constant.  The frontend must encode each
   `fib ... type SYM` surface symbol as the kernel RTN_ route-type constant
   (rtnetlink.h:262-275 / nftables src/fib.c).  The
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
  let c = Nft_inject.find_chain parsed ~table:"t" ~chain:"c" in
  let body i = (Stdlib.List.nth c.Syntax.c_rules i).Syntax.r_body in
  let rtype i = match body i with
    | [Syntax.BMatch (Syntax.MEq (Syntax.FFib (_, Packet.FRtype), v))] -> Some v
    | _ -> None in
  (* fib type is BYTEORDER_HOST_ENDIAN (src/fib.c:50), stored as a NATIVE u32 by
     the kernel (`*dst = res.type`, nft_fib_ipv4.c), so on the LE validate host the
     RTN_ value sits little-endian in the register: RTN_ANYCAST=4 -> [4;0;0;0]. *)
  check "fib daddr type anycast lowers to RTN_ANYCAST=4 ([4;0;0;0])"
    (rtype 0 = Some [4;0;0;0]);
  check "fib daddr type blackhole lowers to RTN_BLACKHOLE=6 ([6;0;0;0])"
    (rtype 1 = Some [6;0;0;0]);
  (* the two distinct route types must NOT compile to identical bytecode. *)
  check "anycast and blackhole encode to DIFFERENT constants (no collision)"
    (rtype 0 <> rtype 1);
  check "fib daddr type multicast lowers to RTN_MULTICAST=5 ([5;0;0;0])"
    (rtype 2 = Some [5;0;0;0]);
  check "fib daddr type unicast lowers to RTN_UNICAST=1 ([1;0;0;0])"
    (rtype 3 = Some [1;0;0;0]);
  (* behavioural: a packet whose looked-up route type is 4 (anycast) matches the
     anycast rule and NOT the blackhole rule; type 6 (blackhole) is the reverse.
     The route oracle bytes are the same host-endian u32 the register holds. *)
  let m_any = match body 0 with [Syntax.BMatch m] -> m | _ -> assert false in
  let m_bh  = match body 1 with [Syntax.BMatch m] -> m | _ -> assert false in
  let env = parsed.Nft_inject.p_env in
  let mk_rtype t =
    let env' = { env with Packet.e_routes =
      [ (([0], [255]),
         (fun (r : Packet.fib_result) ->
            match r with Packet.FRtype -> t | _ -> [])) ] } in
    wire (fun p -> { p with Packet.pkt_fibkey = (fun _ -> [0]) }) (mk_pkt ~env:env' ()) in
  check "route type 4 (anycast) matches the anycast rule, not blackhole"
    (ev_mc m_any (mk_rtype [4;0;0;0]) = true
     && ev_mc m_bh (mk_rtype [4;0;0;0]) = false);
  check "route type 6 (blackhole) matches the blackhole rule, not anycast"
    (ev_mc m_bh (mk_rtype [6;0;0;0]) = true
     && ev_mc m_any (mk_rtype [6;0;0;0]) = false);
  (* host-endian regression: the kernel-faithful RTN_LOCAL register [2;0;0;0]
     MATCHES `fib daddr type local`, and the byte-reversed big-endian word
     [0;0;0;2] (a value the LE kernel can never produce) does NOT. *)
  let src_local =
    "table inet t {\n\
    \  chain c { type filter hook prerouting priority 0; policy accept;\n\
    \    fib daddr type local accept\n\
    \  }\n\
     }\n" in
  let pl = Nft_parse.parse_string src_local in
  let cl = Nft_inject.find_chain pl ~table:"t" ~chain:"c" in
  let m_local = match (Stdlib.List.nth cl.Syntax.c_rules 0).Syntax.r_body with
    | [Syntax.BMatch m] -> m | _ -> assert false in
  let envl = pl.Nft_inject.p_env in
  let mk_rtype_l t =
    let env' = { envl with Packet.e_routes =
      [ (([0], [255]),
         (fun (r : Packet.fib_result) ->
            match r with Packet.FRtype -> t | _ -> [])) ] } in
    wire (fun p -> { p with Packet.pkt_fibkey = (fun _ -> [0]) }) (mk_pkt ~env:env' ()) in
  check "host-endian RTN_LOCAL [2;0;0;0] MATCHES `fib daddr type local`"
    (ev_mc m_local (mk_rtype_l [2;0;0;0]) = true);
  check "byte-reversed [0;0;0;2] (kernel-impossible on LE) does NOT match"
    (ev_mc m_local (mk_rtype_l [0;0;0;2]) = false);
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
  let env = parsed.Nft_inject.p_env in
  let input = Nft_inject.find_chain parsed ~table:"filter" ~chain:"input" in
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
  let mk_mark le = wire (fun p -> { p with
    Packet.pkt_meta = (fun k -> match k with Packet.MKmark -> le | _ -> []) }) (mk_pkt ~env ()) in
  let mark16 = [16;0;0;0] in          (* 0x10 host-endian *)
  let mark256 = [0;1;0;0] in          (* 0x100 host-endian: out of [5,255] numerically *)
  let mark1 = [1;0;0;0] in            (* 0x01 host-endian: below 5 *)
  check "mark=0x10 matches range 0x5-0xff (numeric, post-hton)"
    (ev_mc mc (mk_mark mark16) = true);
  check "mark=0x100 does NOT match 0x5-0xff (would spuriously match if LE-lex)"
    (ev_mc mc (mk_mark mark256) = false);
  check "mark=0x1 does NOT match 0x5-0xff (below low bound)"
    (ev_mc mc (mk_mark mark1) = false);
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
  let c_eq = Nft_inject.find_chain p_eq ~table:"filter" ~chain:"input" in
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
   lowers to MSetT + hton(4,4) with BE bounds (mirroring the direct-range
   fix on the set path), while an EXACT-only set stays a bare MConcatSet (memcmp
   eq is order-independent — nft emits no hton there either). *)
(* (N.of_nat crash regression) A literal above 2^30 (`meta mark 0x80000000` =
   2^31) is routed through the extracted [N.of_nat] on its way to the register
   bytes.  Coq's default [N.of_nat] realization goes through the NON-tail-recursive
   [Pos.of_succ_nat], so extraction recurses ~2^31 deep and blows the OCaml stack;
   the [Extract Constant N.of_nat] in Compiler/Extract.v gives it a log-depth
   realization.  This check merely COMPILES the literal — a revert of that Extract
   Constant turns the parse into a `Stack overflow`, reddening the parse-test gate. *)
let check_big_literal_no_overflow () =
  Printf.printf "=== (N.of_nat) 2^31 literal compiles without stack overflow ===\n";
  let src =
    "table ip filter {\n\
    \  chain input {\n\
    \    type filter hook input priority 0; policy drop;\n\
    \    meta mark 0x80000000 accept\n\
    \  }\n\
     }\n" in
  let parsed = Nft_parse.parse_string src in
  let input = Nft_inject.find_chain parsed ~table:"filter" ~chain:"input" in
  let mc = match (Stdlib.List.nth input.Syntax.c_rules 0).Syntax.r_body with
    | Syntax.BMatch m :: _ -> m | _ -> failwith "no mark match" in
  (match mc with
   | Syntax.MEq (Syntax.FMetaMark, [0;0;0;128]) ->
       check "meta mark 0x80000000 -> host-endian [0;0;0;128], no overflow" true
   | _ -> check "meta mark 0x80000000 -> host-endian [0;0;0;128], no overflow" false);
  Printf.printf "\n"

let check_mark_set () =
  Printf.printf "=== (O') host-endian mark interval set (hton before lookup) ===\n";
  let chain_of src =
    let p = Nft_parse.parse_string src in
    (p, Nft_inject.find_chain p ~table:"filter" ~chain:"input") in
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
  let env_iv = p_iv.Nft_inject.p_env in
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
    (ev_mc mc_iv (mk_ctmark [80;1;0;0]) = true);
  check "ct mark 0x80 does NOT match { 0x100-0x200 } (below low bound)"
    (ev_mc mc_iv (mk_ctmark [128;0;0;0]) = false);
  check "ct mark 0x300 does NOT match { 0x100-0x200 } (above high bound)"
    (ev_mc mc_iv (mk_ctmark [0;3;0;0]) = false);
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
  let env_ex = p_ex.Nft_inject.p_env in
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
    parsed.Nft_inject.p_tables

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
      .Nft_inject.p_env in
  let mk_rule v : Syntax.rule =
    { Syntax.r_body = []; r_outcome = Syntax.OVerdict v; r_after = [] } in
  let deny : Syntax.chain =
    { Syntax.c_policy = Verdict.Accept; c_rules = [ mk_rule Verdict.Drop ] } in
  let chains = [ ("deny", deny) ] in
  let jump_base : Syntax.chain =
    { Syntax.c_policy = Verdict.Accept; c_rules = [ mk_rule (Verdict.Jump "deny") ] } in
  let goto_base : Syntax.chain =
    { Syntax.c_policy = Verdict.Accept; c_rules = [ mk_rule (Verdict.Goto "deny") ] } in
  let p = mk_pkt ~env () in
  let vj = ev_table 10 chains jump_base p in
  let vg = ev_table 10 chains goto_base p in
  (* the OLD jump-ignoring eval_chain returns the base policy Accept; flag that too *)
  let veval_chain = ev_chain jump_base p in
  Printf.printf "    jump deny -> %s (want drop);  goto deny -> %s (want drop)\n"
    (verdict_str vj) (verdict_str vg);
  Printf.printf "    (env-free eval_chain ignores the jump -> %s)\n" (verdict_str veval_chain);
  check "jump deny runs target chain -> drop" (vj = Verdict.Drop);
  check "goto deny runs target chain -> drop" (vg = Verdict.Drop);
  check "env-free eval_chain would IGNORE the jump (-> accept)"
    (veval_chain = Verdict.Accept);
  Printf.printf "\n"

(* ---------- (L') connlimit counts CONNECTIONS, not PACKETS ----------
   Real nftables `connlimit`/`ct count` is a CONNECTION limiter: the kernel
   nft_connlimit_do_eval calls nf_conncount_add_skb, which DEDUPLICATES by
   connection tuple (returns -EEXIST and does NOT grow the count for an
   already-counted connection), then BREAKs iff `count > limit` (STRICT >).
   So `connlimit count 1` permits up to 2 DISTINCT connections, and ANY number
   of packets of ONE connection read count = 1 and are NEVER throttled.
   The OLD model decremented a per-PACKET bucket and BLOCKED the 2nd same-flow
   packet under `connlimit 1`; the fix makes e_connlimit a flow-keyed SET. *)
let check_connlimit_conn () =
  Printf.printf "=== (L') connlimit counts CONNECTIONS not PACKETS ===\n";
  let cl1 = { Packet.cl_count = 1; cl_flags = 0 } in
  let m = Syntax.MConnlimit cl1 in
  (* a one-rule chain `<conn under limit> accept`, policy DROP, starting from an
     env whose connlimit set is EMPTY (no connection counted yet). *)
  let rule = { Syntax.r_body = [Syntax.BMatch m]; r_outcome = Syntax.OVerdict Verdict.Accept; r_after = [] } in
  let chain = { Syntax.c_policy = Verdict.Drop; c_rules = [rule] } in
  let env0 =
    (Nft_parse.parse_string
       "table ip t { chain c { type filter hook input priority 0; policy accept; } }\n")
      .Nft_inject.p_env in
  let base_env = { env0 with Packet.e_connlimit = (fun _ -> []) } in
  (* TWO packets of the SAME connection (same flow id). *)
  let flowA = [10;0;0;1] in
  let p1 = mk_pkt ~env:base_env ~flow:flowA () in
  let (v1, e_after1) = ev_chain_mut_env chain p1 in
  let p2 = mk_pkt ~env:e_after1 ~flow:flowA () in
  let (v2, e_after2) = ev_chain_mut_env chain p2 in
  check "connlimit 1: packet 1 of a connection ACCEPTED (count 1 <= 1)"
    (v1 = Verdict.Accept);
  check "connlimit 1: packet 2 of the SAME connection ALSO ACCEPTED (dedup, count still 1)"
    (v2 = Verdict.Accept);
  check "connlimit 1: a single connection is NEVER throttled (both packets agree)"
    (v1 = v2);
  check "connlimit 1: same-flow re-add is a NO-OP (set holds exactly one connection)"
    (Stdlib.List.length (e_after2.Packet.e_connlimit cl1) = 1);
  (* a SECOND, DISTINCT connection: count becomes 2 > 1 -> BREAK -> policy DROP. *)
  let flowB = [10;0;0;2] in
  let p3 = mk_pkt ~env:e_after2 ~flow:flowB () in
  let (v3, _) = ev_chain_mut_env chain p3 in
  check "connlimit 1: a 2nd DISTINCT connection makes count 2 > 1 -> DROPPED"
    (v3 = Verdict.Drop);
  check "connlimit 1: PERMITS up to N+1=2 distinct connections, blocks the 2nd's overflow"
    (v1 = Verdict.Accept && v3 = Verdict.Drop);
  Printf.printf "\n"

(* A conntrack key (other than `ct state`) read on a packet with NO conntrack entry
   BREAKs the rule (kernel nft_ct.c:81-82 `if (ct == NULL) goto err`).  Drives the
   extracted DSL semantics over a `ct mark 0x10 accept`, policy DROP, chain on a
   no-entry packet ([pkt_ct_present = false]): the rule must NOT match, so the policy
   DROP stands — exactly as the kernel lets such a packet fall through. *)
let check_ct_no_entry () =
  Printf.printf "=== (M') ct non-state key on a NO-ENTRY packet BREAKs the rule ===\n";
  let env0 =
    (Nft_parse.parse_string
       "table ip t { chain c { type filter hook input priority 0; policy accept; } }\n")
      .Nft_inject.p_env in
  (* an env whose flow-keyed conntrack table WOULD report ct mark = 0x10 *)
  let base_env =
    { env0 with Packet.e_ct =
        (fun _ (k : Packet.ct_key) -> match k with Packet.CKmark -> [0;0;0;16] | _ -> []) } in
  (* `ct mark 0x10 accept`, policy DROP *)
  let m_mark = Syntax.MEq (Syntax.FCtMark, [0;0;0;16]) in
  let rule = { Syntax.r_body = [Syntax.BMatch m_mark]; r_outcome = Syntax.OVerdict Verdict.Accept; r_after = [] } in
  let chain = { Syntax.c_policy = Verdict.Drop; c_rules = [rule] } in
  (* TRACKED packet (entry present): rule matches -> ACCEPT *)
  let p_tracked = mk_pkt ~env:base_env ~flow:[1;1] () in
  let v_tracked = ev_chain_mut chain p_tracked in
  (* NO-ENTRY packet (untracked / INVALID): the same env, but pkt_ct_present = false *)
  let p_noentry = wire (fun p -> { p with Packet.pkt_ct_present = false }) p_tracked in
  let v_noentry = ev_chain_mut chain p_noentry in
  check "ct mark 0x10: a TRACKED packet (entry present) MATCHES -> ACCEPT"
    (v_tracked = Verdict.Accept);
  check "ct mark 0x10: a NO-ENTRY packet BREAKs the rule -> policy DROP"
    (v_noentry = Verdict.Drop);
  check "ct mark load_ok = false on a no-entry packet (kernel NFT_BREAK)"
    (not (Syntax.load_ok (Syntax.LCt Packet.CKmark) (snd p_noentry)));
  check "ct state load_ok = true on a no-entry packet (the lone always-readable key)"
    (Syntax.load_ok (Syntax.LCt Packet.CKstate) (snd p_noentry));
  check "ct state reads NF_CT_STATE_INVALID_BIT (0x01) on a no-entry packet"
    (data_eq (dload (Syntax.LCt Packet.CKstate) p_noentry) [0;0;0;1]);
  (* and `ct state invalid` (immediate [0;0;0;1], same as the parser's `invalid`
     keyword) MATCHES the no-entry packet, mirroring the kernel always-matching it *)
  check "ct state invalid matches a no-entry packet (register 0x01 == immediate 0x01)"
    (ev_mc
       (Syntax.MEq (Syntax.FCtState, [0;0;0;1])) p_noentry);
  Printf.printf "\n"

(* ---------- (P) numgen-freedom: discharged by THEOREM, sanity-pinned here ----------
   The mutation/cross-packet theorems (compile_chain_mut_correct /
   compile_seq_mut_correct, THEOREMS.md axis 2) hold under the source-AST
   hypothesis [rule_numgen_free], and Lower_Proofs.lower_ruleset_numgen_free
   discharges it for EVERY successful lowering (lower_rule refuses incremental
   numgen fail-loud, Lower.LEnumgen).  This check is therefore a SANITY pin of
   the extracted predicate, not the discharge itself: the four shipped
   rulesets are numgen-free, and the detector fires on a hand-built
   numgen-inc rule (non-vacuity). *)
let check_numgen_free () =
  Printf.printf "=== (P) rule_numgen_free sanity over all four parsed rulesets ===\n";
  L.iter (fun name ->
    let parsed = Nft_parse.parse_file ("../../rulesets/" ^ name) in
    L.iter (fun (_fam, tname, chains) ->
      L.iter (fun (cn, (c : Syntax.chain)) ->
        check (Printf.sprintf "numgen-free: %s %s/%s" name tname cn)
          (L.for_all Syntax.rule_numgen_free c.Syntax.c_rules))
        chains)
      parsed.Nft_inject.p_tables)
    ["ruleset.nft"; "optiplex.nft"; "router.nft"; "tutorial.nft"];
  (* the detector is not vacuous: an incremental numgen field trips it *)
  let ng = { Packet.ng_random = false; ng_mod = 2; ng_offset = 0 } in
  let broken = { Syntax.r_body = [Syntax.BMatch (Syntax.MEq (Syntax.FNumgen ng, [0;0;0;1]))];
                 r_outcome = Syntax.OVerdict Verdict.Accept; r_after = [] } in
  check "numgen-free detector fires on an incremental numgen match"
    (not (Syntax.rule_numgen_free broken));
  Printf.printf "\n"

(* ---------- (Q) ExtrOcamlNatInt seam: oversized limit rates rejected ----------
   The extracted [nat] is OCaml's 63-bit int (theories/Compiler/Extract.v);
   the frontend must reject any user-controlled nat that could push an
   extracted product past 2^62 (Semantics.lim_cost/lim_max multiply
   ls_rate/ls_burst by lim_window <= 604800).  These pins keep the rejection
   loud: before the guard, the first case silently wrapped into wrong
   bytecode and the third crashed with an uncaught int_of_string Failure. *)
let check_natint_guard () =
  Printf.printf "=== (Q) ExtrOcamlNatInt seam: oversized limit rates rejected loudly ===\n";
  let wrap body =
    "table ip t {\n chain c {\n  type filter hook input priority 0; policy accept;\n  "
    ^ body ^ "\n }\n}\n" in
  let rejected body =
    match Nft_parse.parse_string (wrap body) with
    | _ -> false
    | exception Nft_inject.Inject_error _ -> true
    | exception Nft_inject.Lower_error _ -> true
    | exception Nft_parse.Parse_error _ -> true in
  let accepted body =
    match Nft_parse.parse_string (wrap body) with
    | _ -> true
    | exception _ -> false in
  check "limit rate 9000000000000 mbytes/second REJECTED (used to wrap silently)"
    (rejected "limit rate 9000000000000 mbytes/second accept");
  check "limit burst beyond 2^40 REJECTED"
    (rejected "limit rate 5/second burst 2199023255553 packets accept");
  check "literal > OCaml max_int is a CLEAN error (no int_of_string crash)"
    (rejected "limit rate 99999999999999999999999999/second accept");
  check "in-range byte rate still accepted (limit rate 1025 kbytes/second)"
    (accepted "limit rate 1025 kbytes/second accept");
  Printf.printf "\n"

(* ---------- (R) typed-layer M1: the extracted Coq typechecker ----------
   theories/Surface/{Ast,Datatype,Symbols,Selector,Typecheck}.v, reached
   through the pure structural injection Nft_inject (the ONLY OCaml->Coq
   translation site).  Two sub-gates:
     (a) all four committed rulesets TYPECHECK (the checker accepts every
         construct the proofs are about — non-vacuity, accept direction);
     (b) every ../tests/illtyped/*.nft PARSES but is REJECTED — either by the
         M1 typechecker or LOUD by the verified Coq lowering ([lerr]): cross-type
         bitwise, unknown symbols, width overflow, set-type mismatch, non-bitmask
         comma lists, undefined defines, and the M4 statement-level refusals
         (unknown reject code / nat flag, non-literal tproxy, vmap+static verdict).
   The former KIND-PARITY sub-gate (OCaml `kind` table vs Coq encode) is gone with
   the OCaml kind table itself (M4/M-C); the datatype lattice's width/byteorder
   decisions are now pinned by Lower_Examples.kind_encode_coverage and exercised
   end-to-end by the 2532-rule corpus. *)

let parse_surface (path : string) : Nft_ast.sfile =
  (* include-expand AND apply config-management ops (delete/destroy/flush) — the
     same untrusted preprocessing the real driver runs, so a TopOp never reaches
     the injection (which refuses one). *)
  Nft_parse.preprocess (Filename.dirname path)
    (Nft_parse.parse_raw (Nft_parse.read_file path))

let check_typed_layer () =
  Printf.printf "=== (R) typed-layer: Coq surface typechecker over raw parse trees ===\n";
  (* (a) accept direction: the four committed rulesets *)
  let names = ["ruleset.nft"; "optiplex.nft"; "router.nft"; "tutorial.nft"] in
  let ok = L.filter (fun n ->
      let r =
        match parse_surface ("../../rulesets/" ^ n) with
        | exception e ->
            Printf.printf "  parse/inject %s: %s\n" n (Printexc.to_string e);
            false
        | raw -> Typecheck.typecheck_ruleset (Nft_inject.file raw) in
      check (Printf.sprintf "typecheck accepts %s" n) r; r)
    names in
  Printf.printf "TYPECHECK-RULESETS %d/4\n" (L.length ok);
  (* (b) reject direction: the illtyped suite (each file must PARSE — the
     rejection is the CHECKER's, not the grammar's) *)
  let dir = "../tests/illtyped" in
  let files =
    Sys.readdir dir |> Stdlib.Array.to_list
    |> L.filter (fun f -> Filename.check_suffix f ".nft")
    |> L.sort compare in
  let total = L.length files in
  if total < 4 then begin
    Printf.printf "  ILLTYPED suite too small (%d < 4)\n" total; incr fails
  end;
  let rejected = L.filter (fun f ->
      match parse_surface (Filename.concat dir f) with
      | exception e ->
          Printf.printf "  %-46s PARSE FAILED (%s)\n" f (Printexc.to_string e);
          incr fails; false
      | raw ->
          (* an ill-typed input is rejected either by the M1 Coq typechecker
             or LOUD by the verified Coq lowering ([lerr], surfaced as
             Nft_inject.Lower_error / Inject_error) — both are Coq-side
             refusals, never a silent OCaml byte fallback (M4 fail-loud). *)
          let lower_lerr =
            (try ignore (Nft_inject.lower raw); false
             with Nft_inject.Lower_error _ | Nft_inject.Inject_error _ -> true) in
          let r = not (Typecheck.typecheck_ruleset (Nft_inject.file raw)) || lower_lerr in
          check (Printf.sprintf "illtyped rejected: %s" f) r; r)
    files in
  Printf.printf "ILLTYPED-REJECT %d/%d\n" (L.length rejected) total;
  Printf.printf "\n"

(* ---------- NEW GATE: compile the host-order corpus blocks FROM SOURCE ----------
   `make corpus` reconstructs bytecode FROM the .payload and re-renders — it never
   runs the SOURCE parser+compiler, so it is BLIND to a host/network byteorder
   divergence in the compile path (which is exactly where the `meta mark`/`ct mark`
   plain-cmp reversal lived).  This gate closes that blind spot: for each
   .t.payload block whose header `# <src>` our parser accepts and whose compiled
   bytecode LOADS a BYTEORDER_HOST_ENDIAN field (mark / iif / oif / ct-mark /
   fib-type) in a plain cmp/range (no lookup/bitwise), it COMPILES <src> FROM
   SOURCE, renders it, and requires the result byte-identical to the block. *)

let read_lines path =
  let ic = open_in path in
  let rec go acc = match input_line ic with
    | l -> go (l :: acc)
    | exception End_of_file -> close_in ic; L.rev acc in
  go []

(* split a .t.payload file into blocks separated by blank lines *)
let payload_blocks path =
  let flush cur acc = if cur = [] then acc else L.rev cur :: acc in
  let rec go cur acc = function
    | [] -> L.rev (flush cur acc)
    | "" :: rest -> go [] (flush cur acc) rest
    | l :: rest -> go (l :: cur) acc rest in
  go [] [] (read_lines path)

let starts_bracket l = let s = S.trim l in S.length s > 0 && S.get s 0 = '['
let rec take_while p = function x :: xs when p x -> x :: take_while p xs | _ -> []
let has_prefix pre s = S.length s >= S.length pre && S.sub s 0 (S.length pre) = pre
(* the byteorder-bearing instruction lines: cmp / range immediates and the hton
   byteorder transform.  (The load line's SELECTOR text — e.g. a concatenated
   `fib daddr . iif` — is a separate rendering concern, not a byteorder one, so it
   is excluded from this gate's exact comparison.) *)
let is_value_line l =
  let s = S.trim l in
  has_prefix "[ cmp " s || has_prefix "[ range " s || has_prefix "[ byteorder " s

let bc_is_he_load i = Codec.bc_load_host_endian_reg i <> None
let bc_is_cmp_or_range = function
  | Bytecode.ICmp _ | Bytecode.IRange _ -> true | _ -> false
(* An ordered (range) match over a host-endian register carries the mandatory
   `byteorder hton` transform (Surface.Typed.range_hton over every BoHost
   dtype: mark/ifindex/fib-type AND meta length/skuid/skgid/cpu/cgroup/
   iifgroup/oifgroup, ct id/zone/expiration).  Its presence marks the block as
   an ordered host-endian match even when the raw LOAD is not in
   [bc_load_host_endian_reg]'s (equality-display) set — so this gate now COVERS
   the ordered-range class, not just the mark/ct-mark equality loads. *)
let bc_is_byteorder = function Bytecode.IByteorder _ -> true | _ -> false
let bc_only_load_bo_cmp = function
  | Bytecode.IMetaLoad _ | Bytecode.ICtLoad _ | Bytecode.IFibLoad _
  | Bytecode.IByteorder _ | Bytecode.ICmp _ | Bytecode.IRange _ -> true
  | _ -> false

let byteorder_gate files =
  let checked = ref 0 and passed = ref 0 and failed = ref 0 and skipped = ref 0 in
  L.iter (fun path ->
    L.iter (fun block ->
      match block with
      | hdr :: fam_line :: instrs
        when S.length hdr > 2 && S.get hdr 0 = '#' && starts_bracket
               (match instrs with i :: _ -> i | [] -> "") ->
          let src = S.trim (S.sub hdr 1 (S.length hdr - 1)) in
          (match S.split_on_char ' ' (S.trim fam_line)
                 |> L.filter (fun s -> s <> "") with
           | [fam; tbl; chn] ->
             let wrapped =
               Printf.sprintf "table %s %s {\n chain %s {\n  %s\n }\n}\n" fam tbl chn src in
             (match (try Some (Nft_parse.parse_string wrapped) with _ -> None) with
              | None -> incr skipped
              | Some parsed ->
                let progs = L.concat_map (fun (_f, _t, chains) ->
                    L.concat_map (fun (_cn, c) -> Compile.compile_chain c) chains)
                    parsed.Nft_inject.p_tables in
                (match progs with
                 | [rp] when (L.exists bc_is_he_load rp || L.exists bc_is_byteorder rp)
                             && L.exists bc_is_cmp_or_range rp
                             && L.for_all bc_only_load_bo_cmp rp ->
                     incr checked;
                     let ours = L.filter is_value_line (Codec.render_rule_lines rp) in
                     let theirs =
                       take_while starts_bracket instrs |> L.map S.trim
                       |> L.filter is_value_line in
                     if ours = theirs then incr passed
                     else (incr failed;
                       Printf.printf
                         "BYTEORDER-GATE MISMATCH  # %s\n  corpus: %s\n  ours:   %s\n"
                         src (S.concat " | " theirs) (S.concat " | " ours))
                 | _ -> incr skipped))
           | _ -> incr skipped)
      | _ -> ()) (payload_blocks path))
    files;
  Printf.printf "\n=== compile-from-source byteorder gate ===\n";
  Printf.printf
    "host-order cmp/range blocks compiled from source: %d  passed: %d  failed: %d  (skipped/oos: %d)\n"
    !checked !passed !failed !skipped;
  if !checked < 6 then
    (Printf.printf "FAIL: too few host-order blocks checked (gate vacuous?)\n"; exit 1);
  if !failed > 0 then
    (Printf.printf "FAIL: %d byteorder mismatch(es)\n" !failed; exit 1)
  else
    Printf.printf "OK: %d/%d host-order blocks: compile-from-source == corpus .payload\n"
      !passed !checked

(* ---------- SOURCE-SWEEP: a compile-from-source TRACKED-COUNT RATCHET ----------
   The byteorder-gate above is a red/green byte-identity gate on the narrow
   host-order class.  This sweep is BROADER: it compiles the `# <src>` header of
   EVERY `.t.payload` block from source, renders it, and diffs the whole rendered
   rule against the block's recorded instructions.  The corpus goldens are
   endian-unportable for hton'd host-endian constants (upstream nft-test.py -H
   fails those lines on x86-64) and several benign classes render differently, so
   a naive text sweep can never be red/green.  Instead it is a RATCHET: the pass
   count is pinned in the Makefile as a FLOOR, and a frontend regression that
   drops a block below the floor turns the build red — while the open
   display/optimization classes stay visible without freezing the gate.  The
   class B/C range fixes ADD passing blocks (their `byteorder hton` + big-endian
   bounds now match the corpus), lifting the floor. *)

(* line-numbered block splitter (blocks separated by blank lines) *)
let payload_blocks_ln path =
  let lines = read_lines path in
  let flush cur startln acc =
    match cur with [] -> acc | _ -> (startln, L.rev cur) :: acc in
  let rec go cur startln n acc = function
    | [] -> L.rev (flush cur startln acc)
    | "" :: rest -> go [] 0 (n + 1) (flush cur startln acc) rest
    | l :: rest ->
        let st = if cur = [] then n else startln in
        go (l :: cur) st (n + 1) acc rest in
  go [] 0 1 [] lines

(* upstream records `<file>.t.payload.<family>` per FAMILY; the `<fam> <tbl>
   <chn>` line inside a block is not authoritative (a stale ip4 line can head an
   inet-family recording), so the family is the filename suffix when present. *)
let family_of_payload_path path =
  let base = Filename.basename path in
  match Stdlib.String.split_on_char '.' base |> L.rev with
  | fam :: "payload" :: _ when fam <> "payload" -> Some fam
  | _ -> None

(* recordings are made in BASE chains; nft's dependency synthesis is
   context-sensitive, so the wrap must declare the hook. *)
let hook_line_of_chain chn =
  match chn with
  | "input" | "output" | "forward" | "prerouting" | "postrouting" ->
      Printf.sprintf "type filter hook %s priority 0;" chn
  | "ingress" | "egress" ->
      Printf.sprintf "type filter hook %s device lo priority 0;" chn
  | _ -> "type filter hook input priority 0;"

(* __set0 / __set12 -> __set%d (the corpus placeholder) *)
let normalise_set_names (s : string) : string =
  let b = Buffer.create (S.length s) in
  let n = S.length s in
  let is_digit c = c >= '0' && c <= '9' in
  let rec go i =
    if i >= n then ()
    else if i + 5 <= n && S.sub s i 5 = "__set" && i + 5 < n && is_digit (S.get s (i+5))
    then begin
      Buffer.add_string b "__set%d";
      let j = ref (i + 5) in
      while !j < n && is_digit (S.get s !j) do incr j done;
      go !j
    end else (Buffer.add_char b (S.get s i); go (i + 1)) in
  go 0; Buffer.contents b

let source_sweep files =
  let attempted = ref 0 and passed = ref 0 and parsefail = ref 0 and mism = ref 0 in
  L.iter (fun path ->
    L.iter (fun (ln, block) ->
      match block with
      | hdr :: fam_line :: instrs
        when S.length hdr > 2 && S.get hdr 0 = '#' && starts_bracket
               (match instrs with i :: _ -> i | [] -> "") ->
          let src = S.trim (S.sub hdr 1 (S.length hdr - 1)) in
          (match S.split_on_char ' ' (S.trim fam_line)
                 |> L.filter (fun s -> s <> "") with
           | [fam; tbl; chn] ->
             incr attempted;
             let fam = match family_of_payload_path path with
               | Some f -> f | None -> fam in
             let _where = Printf.sprintf "%s:%d" path ln in
             let wrapped =
               Printf.sprintf "table %s %s {\n chain %s {\n  %s\n  %s\n }\n}\n"
                 fam tbl chn (hook_line_of_chain chn) src in
             (match (try Some (Nft_parse.parse_string wrapped) with _ -> None) with
              | None -> incr parsefail
              | Some parsed ->
                (match
                   (try
                      (* Enable the adjacent-payload-load merge (Optimize_PayMerge,
                         corpus class I): nft ALWAYS performs this fusion
                         (stmt_reduce/payload_can_merge), so the source-side
                         bytecode is byte-identical only with the pass applied.
                         The pass is verdict-preserving (paymerge_chain_eval) and
                         merges exactly nft's cases; the host-endian xor fold
                         (class L) is NOT applied here — its blocks are
                         endian-unportable in the text corpus. *)
                      Some (L.concat_map (fun (_f, _t, chains) ->
                          L.concat_map (fun (_cn, c) ->
                            Compile.compile_chain (Optimize_PayMerge.paymerge_chain c))
                            chains)
                          parsed.Nft_inject.p_tables)
                    with _ -> None)
                 with
                 | None | Some [] -> incr parsefail
                 | Some rules ->
                     let ours =
                       L.concat_map Codec.render_rule_lines rules
                       |> L.map (fun l -> normalise_set_names (S.trim l)) in
                     let theirs = take_while starts_bracket instrs |> L.map S.trim in
                     if ours = theirs then incr passed else incr mism))
           | _ -> ())
      | _ -> ()) (payload_blocks_ln path))
    files;
  Printf.printf
    "SOURCE-SWEEP\tattempted=%d\tpass=%d\tparsefail=%d\tmismatch=%d\n"
    !attempted !passed !parsefail !mism;
  !passed

(* ratchet: PASS if the byte-identical count is >= the pinned floor. *)
let source_sweep_gate minpass files =
  let p = source_sweep files in
  if p < minpass then begin
    Printf.printf
      "SOURCE-SWEEP FAIL: pass=%d below pinned floor %d (a frontend regression dropped a block; investigate before lowering the floor)\n"
      p minpass;
    exit 1
  end else
    Printf.printf "SOURCE-SWEEP OK: pass=%d >= floor %d\n" p minpass

(* ---------- OBJECTS OK/FAIL SWEEP (T3) ----------
   Run the corpus `.t` RULE lines (the `;ok` / `;fail` reference forms) through
   the full frontend — parse + config-op apply + typecheck + verified lowering —
   and check the outcome against the corpus verdict.  Acceptance is BIDIRECTIONAL:
   every `;ok` rule must be ACCEPTED (all three stages succeed); every `;fail`
   rule must be REJECTED (parse error, or typecheck false, or a lowering lerr).

   Object DECLARATION lines (`%name type ...`) populate the table's object
   environment (the `;ok` ones only); their own `;ok`/`;fail` verdicts test deep
   object-body validity (helper protocol modules, ct-timeout policy state names,
   l3proto compatibility) which is kernel-module behaviour OUTSIDE this model, so
   the sweep scopes to RULE lines and LEDGERS the declaration-validity residual
   (DEVELOPMENT.md).  This is the tracked-count ratchet's oracle. *)
module OSweep = struct
  let starts_with s p =
    String.length s >= String.length p && String.sub s 0 (String.length p) = p

  (* split a `.t` line at its FINAL ';' into (payload, verdict) *)
  let split_verdict (l : string) : (string * string) option =
    match String.rindex_opt l ';' with
    | None -> None
    | Some i -> Some (String.sub l 0 i,
                      String.trim (String.sub l (i+1) (String.length l - i - 1)))

  (* `%NAME type SPEC` -> a real nft object declaration `KIND NAME { body }` *)
  let translate_decl (line : string) : string option =
    (* line begins with '%'; drop it, split NAME and the "type ..." remainder *)
    let body = String.trim (String.sub line 1 (String.length line - 1)) in
    match String.index_opt body ' ' with
    | None -> None
    | Some i ->
        let name = String.sub body 0 i in
        let rest = String.trim (String.sub body (i+1) (String.length body - i - 1)) in
        if not (starts_with rest "type ") then None else
        let spec = String.trim (String.sub rest 5 (String.length rest - 5)) in
        if starts_with spec "ct " then
          (* ct helper/timeout/expectation { body } *)
          let r = String.trim (String.sub spec 3 (String.length spec - 3)) in
          (match String.index_opt r '{' with
           | Some bi ->
               let kw = String.trim (String.sub r 0 bi) in
               let bd = String.sub r bi (String.length r - bi) in
               Some (Printf.sprintf "ct %s %s %s" kw name bd)
           | None -> Some (Printf.sprintf "ct %s %s { }" r name))
        else
          let ki = match String.index_opt spec ' ' with Some k -> k | None -> String.length spec in
          let kind = String.sub spec 0 ki in
          let rst = String.trim (String.sub spec ki (String.length spec - ki)) in
          if rst = "" then Some (Printf.sprintf "%s %s { }" kind name)
          else if rst.[0] = '{' then Some (Printf.sprintf "%s %s %s" kind name rst)
          else Some (Printf.sprintf "%s %s { %s }" kind name rst)

  (* accepted iff parse + typecheck + verified lowering all succeed *)
  let accepted (text : string) : bool =
    match (try Some (Nft_parse.parse_raw text) with _ -> None) with
    | None -> false
    | Some raw ->
        (try
           let surface = Nft_inject.file raw in
           Typecheck.typecheck_ruleset surface
           && (try ignore (Nft_inject.lower raw); true with _ -> false)
         with _ -> false)

  (* sweep one .t file; returns (rule lines matching their verdict, total rules) *)
  let sweep_file (path : string) : int * int =
    let ic = open_in path in
    let n = in_channel_length ic in
    let raw = really_input_string ic n in close_in ic;
    let lines = String.split_on_char '\n' raw in
    let table = ref "t" and chain = ref "c" and hook = ref "type filter hook input priority 0" in
    let decls = ref [] and rules = ref [] in
    L.iter (fun l0 ->
      let l = String.trim l0 in
      if l = "" || starts_with l "#" then ()
      else if starts_with l "*" then
        (match String.split_on_char ';' (String.sub l 1 (String.length l - 1)) with
         | _fam :: tbl :: chns :: _ -> table := tbl;
             (match String.split_on_char ',' chns with c :: _ -> chain := c | [] -> ())
         | _ -> ())
      else if starts_with l ":" then
        (match String.split_on_char ';' (String.sub l 1 (String.length l - 1)) with
         | _cn :: hk :: _ -> hook := String.trim hk | _ -> ())
      else match split_verdict l with
        | None -> ()
        | Some (payload, verdict) ->
            let payload = String.trim payload in
            if starts_with payload "%" then
              (if verdict = "ok" then
                 match translate_decl payload with Some d -> decls := d :: !decls | None -> ())
            else rules := (payload, verdict) :: !rules)
      lines;
    let decl_text = String.concat "\n  " (L.rev !decls) in
    let build rule =
      Printf.sprintf "table ip %s {\n  %s\n  chain %s {\n    %s\n    %s\n  }\n}\n"
        !table decl_text !chain !hook rule in
    let rules = L.rev !rules in
    let pass = L.fold_left (fun acc (rule, verdict) ->
        let got = accepted (build rule) in
        let want = (verdict = "ok") in
        if got = want then acc + 1
        else (Printf.printf "  MISS [%s want=%s got=%s]: %s\n"
                (Filename.basename path) verdict (if got then "ok" else "fail") rule; acc))
      0 rules in
    (pass, L.length rules)

  let sweep (files : string list) : int * int =
    L.fold_left (fun (p, t) f -> let (p', t') = sweep_file f in (p + p', t + t')) (0, 0) files
end

let objects_sweep_gate (floor : int) (files : string list) : unit =
  let (pass, total) = OSweep.sweep files in
  Printf.printf "OBJECTS-SWEEP %d/%d rule lines (floor %d)\n" pass total floor;
  if pass < floor then begin
    Printf.printf "OBJECTS-SWEEP FAIL: %d < floor %d (a reference form regressed)\n" pass floor;
    exit 1
  end

let () =
  match Stdlib.Array.to_list Sys.argv with
  | _ :: "byteorder-gate" :: files -> byteorder_gate files
  | _ :: "objects-sweep" :: floor :: files ->
      objects_sweep_gate (int_of_string floor) files
  | _ :: "source-sweep" :: files -> ignore (source_sweep files)
  | _ :: "source-sweep-gate" :: min :: files ->
      source_sweep_gate (int_of_string min) files
  | _ :: path :: _ -> cli path
  | _ ->
  begin
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
    check_ct_set_noop ();
    check_ct_meta_set_width ();
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
    check_connlimit_conn ();
  check_ct_no_entry ();
    check_fib_type ();
    check_mark_range ();
    check_mark_set ();
    check_big_literal_no_overflow ();
    check_numgen_free ();
    check_natint_guard ();
    check_typed_layer ();
    check_difftest_ast ();
    check_live_nft ();
    if !fails = 0 then Printf.printf "ALL PARSER CHECKS PASSED\n"
    else (Printf.printf "%d PARSER CHECK(S) FAILED\n" !fails; exit 1)
  end
