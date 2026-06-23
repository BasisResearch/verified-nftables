(* Executable witness of the correctness theorems.

   compile_chain_correct proves, in Rocq, that for every chain c and packet p
       run_chain (compile_chain c) (c_policy c) p = eval_chain c p
   i.e. the compiled bytecode filters every packet exactly as the DSL says, and
   optimize_chain_correct proves eval_chain (optimize_chain c) p = eval_chain c p.

   This runs the *extracted* DSL semantics, the *extracted* bytecode VM, and the
   *extracted* compiler/optimizer on a battery of concrete packets and checks both
   equalities hold — an end-to-end "real run" exercising the extraction pipeline
   the Rocq proof itself does not (the proof is about Coq terms). It uses the raw
   extracted modules directly (Nftc's facade is demoed separately by example.ml). *)

(* ---- tiny DSL builders over the raw extracted Syntax ---- *)
let meq f v : Syntax.matchcond = Syntax.MEq (f, v)
let mneq f v : Syntax.matchcond = Syntax.MNeq (f, v)
let mrange f lo hi : Syntax.matchcond = Syntax.MRange (f, false, lo, hi)
let mcmp f op v : Syntax.matchcond = Syntax.MCmp (f, op, v)
(* a single-field set-membership match against the NAMED set "set" (contents come
   from the runtime environment, not the rule) *)
let mset f : Syntax.matchcond = Syntax.MConcatSet ([f], false, "set")
let rule ms v : Syntax.rule =
  { Syntax.r_body = Stdlib.List.map (fun m -> Syntax.BMatch m) ms;
    r_verdict = v; r_vmap = None; r_nat = None; r_tproxy = None; r_fwd = None;
    r_queue = None; r_after = [] }
let chain pol rs : Syntax.chain = { Syntax.c_policy = pol; c_rules = rs }
(* a rule with an explicit body (matches AND statements interleaved) *)
let rule_b body v : Syntax.rule =
  { Syntax.r_body = body; r_verdict = v; r_vmap = None; r_nat = None;
    r_tproxy = None; r_fwd = None; r_queue = None; r_after = [] }

(* ---- the runtime environment (named set/map state the lookups read) ---- *)
let empty_env : Packet.env =
  { Packet.e_set = (fun _ -> []); e_vmap = (fun _ -> []); e_map = (fun _ -> []);
    e_routes = []; e_rt = (fun _ -> []); e_ifaddr = (fun _ -> []); e_ifaddr6 = (fun _ -> []);
    (* limiters default to 1 remaining token (0 < 1 -> the match passes) *)
    e_limit = (fun _ -> 1); e_quota = (fun _ -> 1); e_connlimit = (fun _ -> []);
    e_ct = (fun _ _ -> []); e_nat = (fun _ -> None); e_numgen = (fun _ -> 0) }
(* an environment whose rate-limiter "lim" has [n] remaining tokens *)
let env_limit n : Packet.env = { empty_env with Packet.e_limit = (fun _ -> n) }
(* an environment where the set/vmap [name] has the given contents *)
(* exact elements wrap as degenerate intervals (x,x) *)
let env_set name elems : Packet.env =
  { empty_env with Packet.e_set = (fun n -> if n = name then Stdlib.List.map (fun x -> (x, x)) elems else []) }
(* an interval/CIDR set: contents are [lo,hi] ranges *)
let env_set_iv name ivs : Packet.env =
  { empty_env with Packet.e_set = (fun n -> if n = name then ivs else []) }
let env_vmap name ents : Packet.env = { empty_env with Packet.e_vmap = (fun n -> if n = name then ents else []) }

(* ---- concrete packet construction ---- *)
let dummy0 _ = []
let mk_pkt ?(env = empty_env) ?(l4proto = [6]) ?(nh = []) ?(th = []) ?(fibkey = (fun _ -> []))
           ?(iifname = []) () : Packet.packet =
  { Packet.pkt_env = env;
    pkt_meta = (fun k -> match k with
                         | Packet.MKl4proto -> l4proto | Packet.MKiifname -> iifname | _ -> []);
    pkt_ct = dummy0; pkt_sock = dummy0;
    pkt_eh = (fun _ _ _ _ _ -> []);
    pkt_lh = []; pkt_nh = nh; pkt_th = th; pkt_ih = []; pkt_tnl = [];
    pkt_fibkey = fibkey;
    pkt_numgen = dummy0; pkt_osf = [];
    pkt_tunnel = (fun _ -> []);
    pkt_symhash = (fun _ _ -> []); pkt_xfrm = (fun _ _ _ -> []);
    pkt_ctdir = (fun _ _ -> []); pkt_inner = (fun _ _ _ _ -> []);
    (* well-formed, non-fragment, L4 header parsed: transport reads succeed *)
    pkt_have_l2 = true;
    pkt_have_l4 = true; pkt_fragoff = 0; pkt_flow = []; pkt_untracked = false;
    pkt_ctdir_orig = true; pkt_ct_present = true }

(* an IPv4 network header: src at offset 12, dst at offset 16 (4 bytes each) *)
let nh ~saddr ~daddr = (Stdlib.List.init 12 (fun _ -> 0)) @ saddr @ daddr
(* a TCP/UDP transport header: sport at 0, dport at offset 2 (2 bytes each) *)
let th ~dport = [0; 0] @ dport

let string_of_verdict = function
  | Verdict.Accept -> "accept" | Verdict.Drop -> "drop"
  | Verdict.Continue -> "continue" | Verdict.Reject _ -> "reject"
  | Verdict.Queue _ -> "queue"

(* run one chain over a battery of packets, checking DSL == VM == optimized at
   every packet; returns the number of mismatches. *)
let run_battery (fails : int ref) (title : string) (c : Syntax.chain) pkts =
  let prog  = Compile.compile_chain c in
  let copt  = Optimize.optimize_chain c in
  let progo = Compile.compile_chain copt in
  let pol   = c.Syntax.c_policy in
  Printf.printf "=== %s ===\n" title;
  Stdlib.List.iter (fun (name, p) ->
    let dsl  = Semantics.eval_chain c p in            (* what the DSL says *)
    let dslo = Semantics.eval_chain copt p in         (* optimizer preserves it *)
    let vm   = Semantics.run_chain prog  pol p in     (* compiled bytecode VM *)
    let vmo  = Semantics.run_chain progo pol p in     (* optimized + compiled *)
    let ok = dsl = vm && dsl = dslo && dsl = vmo in
    Printf.printf "  %-22s DSL=%-8s VM=%-8s opt=%-8s %s\n"
      name (string_of_verdict dsl) (string_of_verdict vm) (string_of_verdict vmo)
      (if ok then "ok" else "MISMATCH");
    if not ok then incr fails)
    pkts;
  Printf.printf "\n"

(* a single-field verdict-map rule (tcp) against the named map "portmap" — the
   entries live in the runtime environment (env_vmap), NOT the rule, exactly as
   the user observed they should.  [nat] adds a terminal that applies on a map
   miss (the vmap-then-terminal feature). *)
let vmap_rule ?(nat = None) f : Syntax.rule =
  { Syntax.r_body = [ Syntax.BMatch (meq Syntax.FMetaL4proto [6]) ];
    r_verdict = Verdict.Continue;
    r_vmap = Some { Syntax.vm_fields = [f]; vm_keyf = Some (f, []);
                    vm_name = "portmap" };
    r_nat = nat; r_tproxy = None; r_fwd = None; r_queue = None; r_after = [] }

let redirect : Syntax.nat_spec option =
  Some { Syntax.nat_imms = []; nat_field = None; nat_map = None; nat_src = None;
         nat_kind = "redir"; nat_family = ""; nat_amin = None; nat_amax = None;
         nat_pmin = None; nat_pmax = None; nat_flags = 0 }

let () =
  let fails = ref 0 in
  let l4_tcp = meq Syntax.FMetaL4proto [6] in
  (* (1) matches, an optimizable singleton range, an ordered cmp, neq, dead rule *)
  run_battery fails
    "matches / cmp / range / optimizer (compile_chain_correct + optimize_chain_correct)"
    (chain Verdict.Drop [
       rule [ l4_tcp; meq Syntax.FThDport [0; 22] ] Verdict.Accept;
       rule [ l4_tcp; mrange Syntax.FThDport [0; 80] [0; 80] ] Verdict.Accept;
       rule [ l4_tcp; mcmp Syntax.FThDport Bytecode.CLt [0; 20] ] Verdict.Continue;
       rule [ meq Syntax.FIp4Saddr [10; 0; 0; 1] ] Verdict.Drop;
       rule [ mneq Syntax.FIp4Daddr [192; 168; 1; 1] ] Verdict.Accept;
     ])
    [ "tcp dport 22",       mk_pkt ~th:(th ~dport:[0; 22]) ();
      "tcp dport 80",       mk_pkt ~th:(th ~dport:[0; 80]) ();
      "tcp dport 19",       mk_pkt ~th:(th ~dport:[0; 19]) ();
      "tcp dport 443",      mk_pkt ~nh:(nh ~saddr:[1;2;3;4] ~daddr:[8;8;8;8])
                                   ~th:(th ~dport:[1; 187]) ();
      "tcp saddr 10.0.0.1", mk_pkt ~nh:(nh ~saddr:[10;0;0;1] ~daddr:[8;8;8;8])
                                   ~th:(th ~dport:[1; 0]) ();
      "tcp daddr .1.1",     mk_pkt ~nh:(nh ~saddr:[1;2;3;4] ~daddr:[192;168;1;1])
                                   ~th:(th ~dport:[1; 0]) ();
      "udp dport 22",       mk_pkt ~l4proto:[17] ~th:(th ~dport:[0; 22]) () ];
  (* (2) a verdict map with REAL entries, then a terminal redirect on a miss;
     tests the vmap lookup (hit -> mapped verdict) and the vmap-then-terminal
     fall-through (miss -> redirect = Accept) that the corpus cannot exercise. *)
  let vm_env = env_vmap "portmap" [ (([0; 22], [0; 22]), Verdict.Drop);
                                    (([0; 80], [0; 80]), Verdict.Accept) ] in
  run_battery fails
    "verdict map portmap={22:drop,80:accept} (entries in the ENV) then redirect"
    (chain Verdict.Continue [ vmap_rule ~nat:redirect Syntax.FThDport ])
    [ "tcp dport 22 (hit drop)",  mk_pkt ~env:vm_env ~th:(th ~dport:[0; 22]) ();
      "tcp dport 80 (hit accept)", mk_pkt ~env:vm_env ~th:(th ~dport:[0; 80]) ();
      "tcp dport 443 (miss->redir)", mk_pkt ~env:vm_env ~th:(th ~dport:[1; 187]) ();
      "udp dport 22 (no match)",  mk_pkt ~env:vm_env ~l4proto:[17] ~th:(th ~dport:[0; 22]) () ];
  (* (3) set membership `tcp dport @set` where @set = {22,80} lives in the ENV —
     the contents are looked up by name at runtime, and the SAME rule sees a
     different result if the set changes (env_set with different elements). *)
  let set_env = env_set "set" [ [0; 22]; [0; 80] ] in
  run_battery fails
    "set membership tcp dport @set (elements {22,80} in the ENV, not the rule)"
    (chain Verdict.Drop [ rule [ l4_tcp; mset Syntax.FThDport ] Verdict.Accept ])
    [ "tcp dport 22 (in set)",  mk_pkt ~env:set_env ~th:(th ~dport:[0; 22]) ();
      "tcp dport 80 (in set)",  mk_pkt ~env:set_env ~th:(th ~dport:[0; 80]) ();
      "tcp dport 443 (not in)", mk_pkt ~env:set_env ~th:(th ~dport:[1; 187]) ();
      "tcp dport 22 but EMPTY set (drop)", mk_pkt ~th:(th ~dport:[0; 22]) () ];
  (* (3c) sets/maps as DECLARED OBJECTS (compile_chain_sets_correct): the set
     "set" is a table declaration with concrete elements; `lookup @set` reads
     exactly the DECLARED elements (e_set_declared).  Declaring {22,80} accepts
     dport 22; re-declaring the SAME-named set as {443} drops it — the verdict
     follows the declaration, not the rule. *)
  let decls elems : Semantics.set_decls =
    { Semantics.sd_sets = [ ("set", Stdlib.List.map (fun x -> (x, x)) elems) ];
      sd_vmaps = []; sd_maps = [] } in
  let env_decl elems = Semantics.env_with_sets empty_env (decls elems) in
  run_battery fails
    "set @set DECLARED {22,80} — lookup reads the declared elements"
    (chain Verdict.Drop [ rule [ l4_tcp; mset Syntax.FThDport ] Verdict.Accept ])
    [ "dport 22, @set={22,80} (accept)",  mk_pkt ~env:(env_decl [[0;22];[0;80]]) ~th:(th ~dport:[0; 22]) ();
      "dport 22, @set={443} (drop)",      mk_pkt ~env:(env_decl [[1;187]]) ~th:(th ~dport:[0; 22]) ();
      "dport 443, @set={443} (accept)",   mk_pkt ~env:(env_decl [[1;187]]) ~th:(th ~dport:[1; 187]) () ];
  (* (3b) INTERVAL set `tcp dport @r` where @r = {1024-65535} is a single range
     (a degenerate exact set would need 64512 elements) — exercises set_mem's
     interval membership that exact list membership cannot represent. *)
  let iv_env = env_set_iv "set" [ ([4; 0], [255; 255]) ] in
  run_battery fails
    "interval set tcp dport @r (range 1024-65535 in the ENV)"
    (chain Verdict.Drop [ rule [ l4_tcp; mset Syntax.FThDport ] Verdict.Accept ])
    [ "dport 1024 (low edge, in)",  mk_pkt ~env:iv_env ~th:(th ~dport:[4; 0]) ();
      "dport 8080 (mid, in)",       mk_pkt ~env:iv_env ~th:(th ~dport:[31; 144]) ();
      "dport 80 (below range, out)", mk_pkt ~env:iv_env ~th:(th ~dport:[0; 80]) () ];
  (* (4) control flow: a base chain that JUMPs to a user chain "tcp_in" — tests
     compile_table_correct (jump -> callee accept, or fall-through -> resume base
     -> policy drop). The single-base-chain corpus cannot exercise this. *)
  let fuel = 1000 in
  let tcp_in = chain Verdict.Continue [ rule [ meq Syntax.FThDport [0; 22] ] Verdict.Accept ] in
  let base   = chain Verdict.Drop     [ rule [ l4_tcp ] (Verdict.Jump "tcp_in") ] in
  let cenv   = [ ("tcp_in", tcp_in) ] in
  let cprog  = Compile.compile_env cenv and bprog = Compile.compile_chain base in
  Printf.printf "=== base chain `jump tcp_in` then policy (compile_table_correct) ===\n";
  Stdlib.List.iter (fun (name, p) ->
    let dsl = Semantics.eval_table fuel cenv base p in
    let vm  = Semantics.run_table  fuel cprog bprog base.Syntax.c_policy p in
    let ok = dsl = vm in
    Printf.printf "  %-32s DSL=%-8s VM=%-8s %s\n"
      name (string_of_verdict dsl) (string_of_verdict vm) (if ok then "ok" else "MISMATCH");
    if not ok then incr fails)
    [ "tcp dport 22 (jump->accept)",        mk_pkt ~th:(th ~dport:[0; 22]) ();
      "tcp dport 80 (jump->fallthru->drop)", mk_pkt ~th:(th ~dport:[0; 80]) ();
      "udp (rule skipped -> policy drop)",   mk_pkt ~l4proto:[17] ~th:(th ~dport:[0; 22]) () ];
  Printf.printf "\n";
  (* (4b) MULTI-TABLE dispatch (compile_ruleset_correct): two base chains at a
     hook run in order with netfilter verdict combination — base1 (policy accept)
     lets the packet continue; base2 drops tcp dport 22.  So a dport-22 packet is
     DROPPED (by base2) while a dport-80 packet is ACCEPTED (both fall through).
     The single-chain corpus cannot exercise cross-table dispatch. *)
  let base1 = chain Verdict.Accept [] in
  let base2 = chain Verdict.Accept [ rule [ l4_tcp; meq Syntax.FThDport [0; 22] ] Verdict.Drop ] in
  let bases = [ ([], base1); ([], base2) ] in
  let cbases = Stdlib.List.map
      (fun (cs, b) -> (Compile.compile_env cs, (Compile.compile_chain b, b.Syntax.c_policy))) bases in
  Printf.printf "=== two base chains at a hook (compile_ruleset_correct, netfilter combine) ===\n";
  Stdlib.List.iter (fun (name, p) ->
    let dsl = Semantics.eval_ruleset fuel bases p in
    let vm  = Semantics.run_ruleset  fuel cbases p in
    let ok = dsl = vm in
    Printf.printf "  %-32s DSL=%-8s VM=%-8s %s\n"
      name (string_of_verdict dsl) (string_of_verdict vm) (if ok then "ok" else "MISMATCH");
    if not ok then incr fails)
    [ "tcp dport 22 (base2 drops)",   mk_pkt ~th:(th ~dport:[0; 22]) ();
      "tcp dport 80 (both accept)",   mk_pkt ~th:(th ~dport:[0; 80]) () ];
  Printf.printf "\n";
  (* (4e) WILDCARD interface name: `iifname "eth"` as a 3-byte prefix cmp matches
     any interface whose name starts with "eth" (eth0, eth1, ...) — the kernel
     emits a short cmp value and compares only those bytes (eval_cmp CEq is now a
     prefix match).  "wlan0" does not match.  VM = DSL. *)
  run_battery fails
    "iifname \"eth\" (prefix) accept — wildcard interface match"
    (chain Verdict.Drop [ rule [ meq (Syntax.FMetaGen Packet.MKiifname) [101; 116; 104] ] Verdict.Accept ])
    [ "iifname eth0 (prefix match)",  mk_pkt ~iifname:[101; 116; 104; 48] ();      (* "eth0" *)
      "iifname eth1 (prefix match)",  mk_pkt ~iifname:[101; 116; 104; 49] ();      (* "eth1" *)
      "iifname wlan0 (no match)",     mk_pkt ~iifname:[119; 108; 97; 110; 48] () ];(* "wlan0" *)
  (* (4d) LONGEST-PREFIX-MATCH FIB: a routing table with one route 10.0.0.0/8 ->
     oif 3 lives in the ENV; `fib saddr oif` computes the oif via lpm_fib against
     the packet's source address (its fibkey).  The rule `fib saddr oif 3 accept`
     matches a packet routed out oif 3.  Computed (not oracle'd), and VM = DSL. *)
  let route_env =
    { empty_env with Packet.e_routes =
        [ (([10; 0; 0; 0], [10; 255; 255; 255]),
           (fun (r : Packet.fib_result) -> match r with Packet.FRoif -> [3] | _ -> [])) ] } in
  let fibkey_of addr = (fun (sel : string) -> if sel = "saddr" then addr else []) in
  run_battery fails
    "fib saddr oif 3 accept (LPM route 10.0.0.0/8 -> oif 3, in the ENV)"
    (chain Verdict.Drop [ rule [ meq (Syntax.FFib ("saddr", Packet.FRoif)) [3] ] Verdict.Accept ])
    [ "saddr 10.1.2.3 (routed via oif 3)",  mk_pkt ~env:route_env ~fibkey:(fibkey_of [10; 1; 2; 3]) ();
      "saddr 192.168.1.1 (no route)",       mk_pkt ~env:route_env ~fibkey:(fibkey_of [192; 168; 1; 1]) () ];
  (* (4c) STATEFUL ACCUMULATION (compile_seq_correct): a rate limiter shared
     across a packet sequence.  `tcp limit accept` (policy drop) accepts iff the
     limiter has tokens; each accept consumes one.  From 2 tokens, three tcp
     packets give [accept; accept; drop] — the third sees the depleted limiter,
     which a per-packet oracle could not express.  VM run = DSL run, packetwise. *)
  let lim_spec : Packet.limit_spec =
    { Packet.ls_rate = 2; ls_unit = 0; ls_burst = 0; ls_bytes = false; ls_flags = 0 } in
  let lim_chain = chain Verdict.Drop [ rule [ l4_tcp; Syntax.MLimit lim_spec ] Verdict.Accept ] in
  let lim_prog = Compile.compile_chain lim_chain in
  let step v (e : Packet.env) : Packet.env =
    match v with
    | Verdict.Accept -> { e with Packet.e_limit = (fun s -> (e.Packet.e_limit s) - 1) }
    | _ -> e in
  let ev_dsl e p = Semantics.eval_chain lim_chain (Semantics.set_env p e) in
  let ev_vm  e p = Semantics.run_chain lim_prog lim_chain.Syntax.c_policy (Semantics.set_env p e) in
  let pkts = [ mk_pkt ~th:(th ~dport:[0; 22]) (); mk_pkt ~th:(th ~dport:[0; 22]) ();
               mk_pkt ~th:(th ~dport:[0; 22]) () ] in
  let dsl_seq = Semantics.seq_eval ev_dsl step (env_limit 2) pkts in
  let vm_seq  = Semantics.seq_eval ev_vm  step (env_limit 2) pkts in
  Printf.printf "=== rate limiter shared across 3 packets (compile_seq_correct, 2 tokens) ===\n";
  Printf.printf "  DSL=[%s]  VM=[%s]  %s\n\n"
    (Stdlib.String.concat "; " (Stdlib.List.map string_of_verdict dsl_seq))
    (Stdlib.String.concat "; " (Stdlib.List.map string_of_verdict vm_seq))
    (if dsl_seq = vm_seq then "ok" else "MISMATCH");
  if dsl_seq <> vm_seq then incr fails;
  (* (5) Phase B: in-traversal mutation.  Rule 1 sets meta mark; rule 2 matches
     it.  Under the mutation-aware semantics (eval/run_chain_mut) the second rule
     observes the write and the packet is ACCEPTED; the old verdict-only eval_chain
     no-ops the set so it reads the original mark and falls through to DROP.  The
     witness shows (a) the compiler preserves the mutated verdict (DSL_mut = VM_mut)
     and (b) mutation actually changes the result (mut != no-mut). *)
  Printf.printf "=== counter; meta mark set 0x1; log ; meta mark 0x1 accept (mutation, mixed stmts) ===\n";
  (* the first rule MIXES non-set statements (counter, log) with the meta-set —
     exactly what the old `plain_simple` scope excluded; mut_wf now covers it. *)
  let mut_chain = chain Verdict.Drop [
    rule_b [ Syntax.BStmt (Syntax.SCounter (0, 0));
             Syntax.BStmt (Syntax.SMetaSet (Packet.MKmark, Syntax.VImm [1]));
             Syntax.BStmt (Syntax.SLog "") ] Verdict.Continue;
    rule_b [ Syntax.BMatch (meq Syntax.FMetaMark [1]) ] Verdict.Accept;
  ] in
  let mprog = Compile.compile_chain mut_chain in
  Stdlib.List.iter (fun (name, p) ->
    let dsl_mut   = Semantics.eval_chain_mut mut_chain p in
    let vm_mut    = Semantics.run_chain_mut  mprog mut_chain.Syntax.c_policy p in
    let dsl_nomut = Semantics.eval_chain mut_chain p in
    let ok = dsl_mut = vm_mut in
    Printf.printf "  %-22s mut: DSL=%-7s VM=%-7s | verdict-only DSL=%-7s %s\n"
      name (string_of_verdict dsl_mut) (string_of_verdict vm_mut) (string_of_verdict dsl_nomut)
      (if ok then "ok" else "MISMATCH");
    if not ok then incr fails;
    if dsl_mut = dsl_nomut then
      (Printf.printf "    (warning: mutation made no difference for this packet)\n"))
    [ "mark initially unset", mk_pkt () ];
  Printf.printf "\n";
  (* (5b) dynset feedback loop: the dynamic-SET mutation a `dynset` performs.
     Rule 1 is `add @learn {ip saddr}` — it inserts the packet's source address
     into the named set "learn"; rule 2 is `ip saddr @learn accept`.  Under the
     mutation-aware semantics the second rule's lookup observes the element rule 1
     learned and the packet is ACCEPTED; the old verdict-only model no-ops the
     dynset (verdict-neutral), so @learn stays EMPTY, the lookup misses, and the
     packet falls through to the DROP policy.  This is exactly the set-feedback the
     audit flagged as missing — the witness shows (a) the compiler preserves the
     fed-back verdict (DSL_mut = VM_mut) and (b) the feedback changes the result
     (mut accept != no-mut drop). *)
  Printf.printf "=== add @learn {ip saddr}; ip saddr @learn accept (dynset set feedback) ===\n";
  let dyn_chain = chain Verdict.Drop [
    rule_b [ Syntax.BStmt (Syntax.SDynset ("add", "learn", [Syntax.FIp4Saddr], [])) ] Verdict.Continue;
    rule_b [ Syntax.BMatch (Syntax.MConcatSet ([Syntax.FIp4Saddr], false, "learn")) ] Verdict.Accept;
  ] in
  let dprog = Compile.compile_chain dyn_chain in
  Stdlib.List.iter (fun (name, p) ->
    let dsl_mut   = Semantics.eval_chain_mut dyn_chain p in
    let vm_mut    = Semantics.run_chain_mut  dprog dyn_chain.Syntax.c_policy p in
    let dsl_nomut = Semantics.eval_chain dyn_chain p in
    let ok = dsl_mut = vm_mut in
    Printf.printf "  %-26s mut: DSL=%-7s VM=%-7s | verdict-only DSL=%-7s %s\n"
      name (string_of_verdict dsl_mut) (string_of_verdict vm_mut) (string_of_verdict dsl_nomut)
      (if ok then "ok" else "MISMATCH");
    if not ok then incr fails;
    if dsl_mut = dsl_nomut then
      Printf.printf "    (warning: dynset feedback made no difference for this packet)\n")
    [ "saddr 10.0.0.1 learned", mk_pkt ~nh:(nh ~saddr:[10;0;0;1] ~daddr:[8;8;8;8]) () ];
  Printf.printf "\n";
  (* (5c) MAP dynset feedback: `add @m {ip saddr : tcp dport}` learns a key->value
     entry; a later `meta mark set ip saddr map @m` reads it back, then a match on
     the mark accepts.  Combines map-dynset learning with meta mutation. *)
  Printf.printf "=== add @m {ip saddr : tcp dport}; meta mark set ip saddr map @m; meta mark 22 accept ===\n";
  let mapdyn_chain = chain Verdict.Drop [
    rule_b [ Syntax.BStmt (Syntax.SDynset ("add", "m", [Syntax.FIp4Saddr], [Syntax.FThDport])) ] Verdict.Continue;
    rule_b [ Syntax.BStmt (Syntax.SMetaSet (Packet.MKmark, Syntax.VMap ([Syntax.FIp4Saddr], [], "m"))) ] Verdict.Continue;
    rule_b [ Syntax.BMatch (meq Syntax.FMetaMark [0; 22]) ] Verdict.Accept;
  ] in
  let mdprog = Compile.compile_chain mapdyn_chain in
  Stdlib.List.iter (fun (name, p) ->
    let dsl_mut   = Semantics.eval_chain_mut mapdyn_chain p in
    let vm_mut    = Semantics.run_chain_mut  mdprog mapdyn_chain.Syntax.c_policy p in
    let dsl_nomut = Semantics.eval_chain mapdyn_chain p in
    let ok = dsl_mut = vm_mut in
    Printf.printf "  %-26s mut: DSL=%-7s VM=%-7s | verdict-only DSL=%-7s %s\n"
      name (string_of_verdict dsl_mut) (string_of_verdict vm_mut) (string_of_verdict dsl_nomut)
      (if ok then "ok" else "MISMATCH");
    if not ok then incr fails;
    if dsl_mut = dsl_nomut then
      Printf.printf "    (warning: map-dynset feedback made no difference for this packet)\n")
    [ "saddr->dport learned in @m", mk_pkt ~nh:(nh ~saddr:[10;0;0;1] ~daddr:[8;8;8;8]) ~th:(th ~dport:[0;22]) () ];
  Printf.printf "\n";
  (* (5d) CROSS-PACKET persistence (compile_seq_mut_correct): a learning set that
     accumulates ACROSS packets.  Rule 1 accepts if the source is already in @seen;
     rule 2 learns it.  So the FIRST packet from a source is dropped (not yet seen)
     and a LATER packet from the same source is accepted — the env a packet leaves
     seeds the next.  The compiled VM reproduces the DSL sequence exactly. *)
  Printf.printf "=== ip saddr @seen accept; add @seen {ip saddr}  (across a 2-packet sequence) ===\n";
  let seen_chain = chain Verdict.Drop [
    rule_b [ Syntax.BMatch (Syntax.MConcatSet ([Syntax.FIp4Saddr], false, "seen")) ] Verdict.Accept;
    rule_b [ Syntax.BStmt (Syntax.SDynset ("add", "seen", [Syntax.FIp4Saddr], [])) ] Verdict.Continue;
  ] in
  let sprog = Compile.compile_chain seen_chain in
  let spol  = seen_chain.Syntax.c_policy in
  let one   = mk_pkt ~nh:(nh ~saddr:[10;0;0;1] ~daddr:[8;8;8;8]) () in
  let pkts  = [ one; one ] in    (* two packets from the same source *)
  let dsl_seq = Semantics.seq_eval_env
    (fun e p -> Semantics.eval_chain_mut_env seen_chain (Semantics.set_env p e)) empty_env pkts in
  let vm_seq  = Semantics.seq_eval_env
    (fun e p -> Semantics.run_chain_mut_env sprog spol (Semantics.set_env p e)) empty_env pkts in
  let pp s = "[" ^ Stdlib.String.concat "; " (Stdlib.List.map string_of_verdict s) ^ "]" in
  let ok = dsl_seq = vm_seq in
  Printf.printf "  same source x2          DSL=%-18s VM=%-18s %s\n"
    (pp dsl_seq) (pp vm_seq) (if ok then "ok" else "MISMATCH");
  if not ok then incr fails;
  (match dsl_seq with
   | [ a; b ] when a <> b -> ()   (* first dropped, second accepted: cross-packet learning *)
   | _ -> Printf.printf "    (warning: no cross-packet difference observed)\n");
  Printf.printf "\n";
  (* (6) nft -o CONSOLIDATION passes (Optimize_Merge).  Two batteries:
       (6a) the contiguous-range VALUE-MERGE certificate (eval_rules_range_value_merge):
            `ip protocol 6` + `ip protocol 7` (single-byte field) accept
            =>  `ip protocol 6-7 accept`.  The hand-merged chain must agree with the
            two-rule chain on every single-byte-protocol packet.
       (6b) the consecutive-duplicate-rule pass (optimize_chain2 = optimize_chain
            then dedup_adj): an adjacent duplicate rule is removed (length shrinks)
            and the verdict is preserved on every packet. *)
  Printf.printf "=== (6a) nft -o value-merge: ip protocol {6,7} -> 6-7 (range, single byte) ===\n";
  let ipproto = Syntax.FMetaL4proto in   (* a single-byte selector *)
  let two_rule = chain Verdict.Drop [
    rule [ Syntax.MRange (ipproto, false, [6], [6]) ] Verdict.Accept;
    rule [ Syntax.MRange (ipproto, false, [7], [7]) ] Verdict.Accept;
  ] in
  let merged = chain Verdict.Drop [
    rule [ Syntax.MRange (ipproto, false, [6], [7]) ] Verdict.Accept;
  ] in
  Stdlib.List.iter (fun (_name, proto) ->
    let p = mk_pkt ~l4proto:[proto] () in
    let a = Semantics.eval_chain two_rule p in
    let b = Semantics.eval_chain merged  p in
    let ok = a = b in
    Printf.printf "  proto=%-3d  two-rule=%-7s merged=%-7s %s\n"
      proto (string_of_verdict a) (string_of_verdict b) (if ok then "ok" else "MISMATCH");
    if not ok then incr fails)
    [ "5", 5; "6", 6; "7", 7; "8", 8 ];
  Printf.printf "\n";
  Printf.printf "=== (6b) nft -o dedup: adjacent duplicate rule removed (dedup_adj) ===\n";
  (* [dedup_adj]/[optimize_chain2] (verified in Optimize_Merge.v, axiom-free) are
     kept OUT of the extracted library: their [rule_eq_dec] (a bottom-up
     [decide equality] hierarchy) extracts to a multi-megabyte OCaml term.  We
     re-create the SAME pass here with OCaml's structural equality on the extracted
     [rule] type — the verified [eval_rules_dedup_adj] guarantees this drop is
     verdict-preserving; this witness just exercises it on concrete packets. *)
  let rec dedup_adj : Syntax.rule list -> Syntax.rule list = function
    | r1 :: (r2 :: _ as rest) -> if r1 = r2 then dedup_adj rest else r1 :: dedup_adj rest
    | rs -> rs in
  let optimize_chain2 (c : Syntax.chain) : Syntax.chain =
    let c1 = Optimize.optimize_chain c in
    { c1 with Syntax.c_rules = dedup_adj c1.Syntax.c_rules } in
  let dup_chain = chain Verdict.Drop [
    rule [ l4_tcp; meq Syntax.FThDport [0; 22] ] Verdict.Accept;
    rule [ l4_tcp; meq Syntax.FThDport [0; 22] ] Verdict.Accept;   (* exact duplicate *)
    rule [ meq Syntax.FIp4Saddr [10; 0; 0; 1] ] Verdict.Drop;
  ] in
  let dup_opt = optimize_chain2 dup_chain in
  let len_before = Stdlib.List.length dup_chain.Syntax.c_rules in
  let len_after  = Stdlib.List.length dup_opt.Syntax.c_rules in
  Printf.printf "  rules: %d -> %d (%s)\n" len_before len_after
    (if len_after < len_before then "shrunk: duplicate removed" else "NOT shrunk");
  if not (len_after < len_before) then incr fails;
  Stdlib.List.iter (fun (name, p) ->
    let a = Semantics.eval_chain dup_chain p in
    let b = Semantics.eval_chain dup_opt  p in
    let ok = a = b in
    Printf.printf "  %-22s orig=%-7s opt2=%-7s %s\n"
      name (string_of_verdict a) (string_of_verdict b) (if ok then "ok" else "MISMATCH");
    if not ok then incr fails)
    [ "tcp dport 22",       mk_pkt ~th:(th ~dport:[0; 22]) ();
      "tcp dport 80",       mk_pkt ~th:(th ~dport:[0; 80]) ();
      "saddr 10.0.0.1",     mk_pkt ~nh:(nh ~saddr:[10;0;0;1] ~daddr:[8;8;8;8]) () ];
  Printf.printf "\n";
  (* (6c) THE HEADLINE nft -o pass — value -> anonymous SET (Optimize_Merge.v
     `optimize_rules_sets` / `optimize_chain_sets_correct`, axiom-free).  The
     verified pass mints a fresh `__setN`, emits its (v1,v1)/(v2,v2) declaration,
     and rewrites the adjacent pair into one `MConcatSet [f] false __setN` rule.
     We re-create the SAME rewrite in OCaml (the verified term's `rule_eq_dec`
     extracts to a multi-MB OCaml value, so — exactly as (6b) — we mirror it with
     structural equality; `optimize_rules_sets_correct` guarantees the rewrite is
     verdict-preserving WITH the synthesised set in scope).

       INPUT  (nft -o oracle: `tcp dport 22 accept` + `tcp dport 80 accept`):
         => OUTPUT  `tcp dport { 22, 80 } accept`  (anonymous set __set0={22,80}).

     The witness shows it FIRES (2 rules -> 1, a set declaration is synthesised)
     and that `eval_chain` of the rewritten rule UNDER the synthesised set agrees
     with the two-rule original on every packet. *)
  Printf.printf "=== (6c) nft -o value->SET: tcp dport {22,80} (anonymous set, the headline pass) ===\n";
  let counter = ref 0 in
  let setname () = let n = !counter in incr counter; Printf.sprintf "__set%d" n in
  (* the verified `value_merge_pair`/`optimize_rules_sets` rewrite, mirrored: on an
     adjacent pair `MCmp f CEq v1 :: rest` / `MCmp f CEq v2 :: rest` (same field,
     same rest, same end-fields, v1<>v2, f a fixed-width payload field), mint a set
     and rewrite the pair to one `MConcatSet [f] false name`. *)
  let head_value (r : Syntax.rule) =
    match r.Syntax.r_body with
    | Syntax.BMatch (Syntax.MCmp (f, Bytecode.CEq, v)) :: rest -> Some (f, v, rest)
    | _ -> None in
  let fixed_len (f : Syntax.field) =
    match Syntax.field_load f with
    | Syntax.LPayload (_, _, len) -> Some len | _ -> None in
  let merge_pair (r1 : Syntax.rule) (r2 : Syntax.rule) =
    match head_value r1, head_value r2 with
    | Some (f1, v1, rest1), Some (f2, v2, rest2) ->
        if f1 = f2 && rest1 = rest2 && v1 <> v2
           && fixed_len f1 = Some (Stdlib.List.length v1)
           && fixed_len f1 = Some (Stdlib.List.length v2)
           && { r1 with Syntax.r_body = Syntax.BMatch (Syntax.MCmp (f1, Bytecode.CEq, v1)) :: rest1 }
            = { r2 with Syntax.r_body = Syntax.BMatch (Syntax.MCmp (f1, Bytecode.CEq, v1)) :: rest1 }
        then Some (f1, v1, v2, rest1) else None
    | _ -> None in
  let rec opt_rules sets (rs : Syntax.rule list) =
    match rs with
    | r1 :: (r2 :: rest) ->
        (match merge_pair r1 r2 with
         | Some (f, v1, v2, body) ->
             let name = setname () in
             let sets' = (name, [ (v1, v1); (v2, v2) ]) :: sets in
             let merged = { r1 with Syntax.r_body =
                              Syntax.BMatch (Syntax.MConcatSet ([f], false, name)) :: body } in
             let (sets'', rest') = opt_rules sets' rest in
             (sets'', merged :: rest')
         | None -> let (sets'', rest') = opt_rules sets (r2 :: rest) in (sets'', r1 :: rest'))
    | _ -> (sets, rs) in
  let rs_in = [
    rule [ mcmp Syntax.FThDport Bytecode.CEq [0; 22] ] Verdict.Accept;
    rule [ mcmp Syntax.FThDport Bytecode.CEq [0; 80] ] Verdict.Accept;
  ] in
  let (sets_out, rs_out) = opt_rules [] rs_in in
  let len_in = Stdlib.List.length rs_in and len_out = Stdlib.List.length rs_out in
  Printf.printf "  rules: %d -> %d (%s)\n" len_in len_out
    (if len_out < len_in then "shrunk: value-merge fired" else "NOT shrunk");
  if not (len_out < len_in) then incr fails;
  Stdlib.List.iter (fun (nm, els) ->
    Printf.printf "  synthesised set %s = { %s }\n" nm
      (Stdlib.String.concat ", "
         (Stdlib.List.map (fun (lo, _hi) ->
            string_of_int (Stdlib.List.fold_left (fun a b -> a*256+b) 0 lo)) els)))
    sets_out;
  if sets_out = [] then (Printf.printf "  NO set synthesised\n"; incr fails);
  (* verdict equivalence: original two-rule chain (policy drop) vs the rewritten
     ONE-rule chain evaluated WITH the synthesised set declared in scope. *)
  let decls : Semantics.set_decls =
    { Semantics.sd_sets = sets_out; sd_vmaps = []; sd_maps = [] } in
  let env_out = Semantics.env_with_sets empty_env decls in
  let c_in  = chain Verdict.Drop rs_in in
  let c_out = chain Verdict.Drop rs_out in
  Stdlib.List.iter (fun (name, dport) ->
    let p_in  = mk_pkt ~th:(th ~dport) () in
    let p_out = mk_pkt ~env:env_out ~th:(th ~dport) () in
    let a = Semantics.eval_chain c_in  p_in in
    let b = Semantics.eval_chain c_out p_out in
    let ok = a = b in
    Printf.printf "  %-26s two-rule=%-7s set-merged=%-7s %s\n"
      name (string_of_verdict a) (string_of_verdict b) (if ok then "ok" else "MISMATCH");
    if not ok then incr fails)
    [ "tcp dport 22 (in set)",  [0; 22];
      "tcp dport 80 (in set)",  [0; 80];
      "tcp dport 443 (not in)", [1; 187];
      "tcp dport 1   (not in)", [0; 1] ];
  Printf.printf "\n";
  Printf.printf "%s: compile & optimize preserve the DSL verdict on every packet\n"
    (if !fails = 0 then "PASS" else Printf.sprintf "FAIL (%d mismatches)" !fails);
  if !fails > 0 then exit 1
