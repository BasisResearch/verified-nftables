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
    r_outcome = (match v with Verdict.Continue -> Syntax.ONone | _ -> Syntax.OVerdict v);
    r_after = [] }
let chain pol rs : Syntax.chain = { Syntax.c_policy = pol; c_rules = rs }
(* a rule with an explicit body (matches AND statements interleaved) *)
let rule_b body v : Syntax.rule =
  { Syntax.r_body = body;
    r_outcome = (match v with Verdict.Continue -> Syntax.ONone | _ -> Syntax.OVerdict v);
    r_after = [] }

(* ---- the runtime environment (named set/map state the lookups read) ---- *)
let empty_env : Packet.env =
  { Packet.e_set = (fun _ -> []); e_vmap = (fun _ -> []); e_map = (fun _ -> []);
    e_routes = []; e_rt = (fun _ -> []); e_ifaddrs = (fun _ -> []); e_ifaddrs6 = (fun _ -> []);
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
(* a test packet-in-context: the shared env PLUS one skb, as the (env, packet)
   pair every evaluator now takes as two separate arguments *)
let mk_pkt ?(env = empty_env) ?(l4proto = [6]) ?(nh = []) ?(th = []) ?(fibkey = (fun _ -> []))
           ?(iifname = []) () : Packet.env * Packet.packet =
  (env,
  { Packet.pkt_meta = (fun k -> match k with
                         | Packet.MKl4proto -> l4proto | Packet.MKiifname -> iifname | _ -> []);
    pkt_sock = dummy0;
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
    pkt_ctdir_orig = true; pkt_ct_present = true })

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
  Stdlib.List.iter (fun (name, (e, p)) ->
    let dsl  = Semantics.eval_chain c e p in            (* what the DSL says *)
    let dslo = Semantics.eval_chain copt e p in         (* optimizer preserves it *)
    let vm   = Semantics.run_chain prog  pol e p in     (* compiled bytecode VM *)
    let vmo  = Semantics.run_chain progo pol e p in     (* optimized + compiled *)
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
  let vm = { Syntax.vm_fields = [f]; vm_keyf = Some (f, []);
             vm_name = "portmap" } in
  { Syntax.r_body = [ Syntax.BMatch (meq Syntax.FMetaL4proto [6]) ];
    r_outcome = (match nat with
                 | Some ns -> Syntax.OVmapNat (vm, ns)
                 | None -> Syntax.OVmap vm);
    r_after = [] }

let redirect : Syntax.nat_spec option =
  Some { Syntax.nat_addr_imm = None; nat_field = None; nat_map = None; nat_src = None;
         nat_kind = Bytecode.NKredir; nat_family = Bytecode.NFip4;
         nat_extra = Syntax.NXnone; nat_flags = 0 }

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
  Stdlib.List.iter (fun (name, (e, p)) ->
    let dsl = Semantics.eval_table fuel cenv base e p in
    let vm  = Semantics.run_table  fuel cprog bprog base.Syntax.c_policy e p in
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
  Stdlib.List.iter (fun (name, (e, p)) ->
    let dsl = Semantics.eval_ruleset fuel bases e p in
    let vm  = Semantics.run_ruleset  fuel cbases e p in
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
  let ev_dsl e p = Semantics.eval_chain lim_chain e p in
  let ev_vm  e p = Semantics.run_chain lim_prog lim_chain.Syntax.c_policy e p in
  let pkts = [ snd (mk_pkt ~th:(th ~dport:[0; 22]) ()); snd (mk_pkt ~th:(th ~dport:[0; 22]) ());
               snd (mk_pkt ~th:(th ~dport:[0; 22]) ()) ] in
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
  Stdlib.List.iter (fun (name, (e, p)) ->
    let dsl_mut   = Semantics.eval_chain_mut mut_chain e p in
    let vm_mut    = Semantics.run_chain_mut  mprog mut_chain.Syntax.c_policy e p in
    let dsl_nomut = Semantics.eval_chain mut_chain e p in
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
    rule_b [ Syntax.BStmt (Syntax.SDynset (Bytecode.SOadd, "learn", [Syntax.FIp4Saddr], [])) ] Verdict.Continue;
    rule_b [ Syntax.BMatch (Syntax.MConcatSet ([Syntax.FIp4Saddr], false, "learn")) ] Verdict.Accept;
  ] in
  let dprog = Compile.compile_chain dyn_chain in
  Stdlib.List.iter (fun (name, (e, p)) ->
    let dsl_mut   = Semantics.eval_chain_mut dyn_chain e p in
    let vm_mut    = Semantics.run_chain_mut  dprog dyn_chain.Syntax.c_policy e p in
    let dsl_nomut = Semantics.eval_chain dyn_chain e p in
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
    rule_b [ Syntax.BStmt (Syntax.SDynset (Bytecode.SOadd, "m", [Syntax.FIp4Saddr], [Syntax.FThDport])) ] Verdict.Continue;
    rule_b [ Syntax.BStmt (Syntax.SMetaSet (Packet.MKmark, Syntax.VMap ([Syntax.FIp4Saddr], [], "m"))) ] Verdict.Continue;
    rule_b [ Syntax.BMatch (meq Syntax.FMetaMark [0; 22]) ] Verdict.Accept;
  ] in
  let mdprog = Compile.compile_chain mapdyn_chain in
  Stdlib.List.iter (fun (name, (e, p)) ->
    let dsl_mut   = Semantics.eval_chain_mut mapdyn_chain e p in
    let vm_mut    = Semantics.run_chain_mut  mdprog mapdyn_chain.Syntax.c_policy e p in
    let dsl_nomut = Semantics.eval_chain mapdyn_chain e p in
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
    rule_b [ Syntax.BStmt (Syntax.SDynset (Bytecode.SOadd, "seen", [Syntax.FIp4Saddr], [])) ] Verdict.Continue;
  ] in
  let sprog = Compile.compile_chain seen_chain in
  let spol  = seen_chain.Syntax.c_policy in
  let one   = snd (mk_pkt ~nh:(nh ~saddr:[10;0;0;1] ~daddr:[8;8;8;8]) ()) in
  let pkts  = [ one; one ] in    (* two packets from the same source *)
  let dsl_seq = Semantics.seq_eval_env
    (fun e p -> Semantics.eval_chain_mut_env seen_chain e p) empty_env pkts in
  let vm_seq  = Semantics.seq_eval_env
    (fun e p -> Semantics.run_chain_mut_env sprog spol e p) empty_env pkts in
  let pp s = "[" ^ Stdlib.String.concat "; " (Stdlib.List.map string_of_verdict s) ^ "]" in
  let ok = dsl_seq = vm_seq in
  Printf.printf "  same source x2          DSL=%-18s VM=%-18s %s\n"
    (pp dsl_seq) (pp vm_seq) (if ok then "ok" else "MISMATCH");
  if not ok then incr fails;
  (match dsl_seq with
   | [ a; b ] when a <> b -> ()   (* first dropped, second accepted: cross-packet learning *)
   | _ -> Printf.printf "    (warning: no cross-packet difference observed)\n");
  Printf.printf "\n";
  (* (6) nft -o CONSOLIDATION passes (Optimize_ValueSet).  Two batteries:
       (6a) the contiguous-RANGE value-merge CERTIFICATE
            (eval_rules_range_value_merge): two adjacent point matches over a
            CONTIGUOUS pair `ip protocol 6` + `ip protocol 7` are verdict-equivalent
            to ONE `ip protocol 6-7` range rule.  NOTE: this is a soundness
            certificate for the RANGE form, NOT the shape `nft -o` actually emits —
            `nft -o` consolidates `{6,7}` into a DISCRETE anonymous SET
            `ip protocol { 6, 7 }`, which is the VERIFIED extracted pass exercised in
            (6c) below.  This battery only witnesses that the range merge (when it is
            applicable, i.e. the values happen to be contiguous) preserves verdicts.
       (6b) the consecutive-duplicate-rule pass (optimize_chain2 = optimize_chain
            then dedup_adj): an adjacent duplicate rule is removed (length shrinks)
            and the verdict is preserved on every packet. *)
  Printf.printf "=== (6a) range-merge certificate (NOT nft -o's shape): ip protocol 6 + 7 == 6-7 ===\n";
  let ipproto = Syntax.FMetaL4proto in   (* a single-byte selector *)
  let two_rule = chain Verdict.Drop [
    rule [ Syntax.MRange (ipproto, false, [6], [6]) ] Verdict.Accept;
    rule [ Syntax.MRange (ipproto, false, [7], [7]) ] Verdict.Accept;
  ] in
  let merged = chain Verdict.Drop [
    rule [ Syntax.MRange (ipproto, false, [6], [7]) ] Verdict.Accept;
  ] in
  Stdlib.List.iter (fun (_name, proto) ->
    let (e, p) = mk_pkt ~l4proto:[proto] () in
    let a = Semantics.eval_chain two_rule e p in
    let b = Semantics.eval_chain merged  e p in
    let ok = a = b in
    Printf.printf "  proto=%-3d  two-rule=%-7s merged=%-7s %s\n"
      proto (string_of_verdict a) (string_of_verdict b) (if ok then "ok" else "MISMATCH");
    if not ok then incr fails)
    [ "5", 5; "6", 6; "7", 7; "8", 8 ];
  Printf.printf "\n";
  Printf.printf "=== (6b) nft -o dedup: adjacent duplicate rule removed (dedup_adj) ===\n";
  (* [dedup_adj]/[optimize_chain2] (verified in Optimize_ValueSet.v, axiom-free) are
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
  Stdlib.List.iter (fun (name, (e, p)) ->
    let a = Semantics.eval_chain dup_chain e p in
    let b = Semantics.eval_chain dup_opt  e p in
    let ok = a = b in
    Printf.printf "  %-22s orig=%-7s opt2=%-7s %s\n"
      name (string_of_verdict a) (string_of_verdict b) (if ok then "ok" else "MISMATCH");
    if not ok then incr fails)
    [ "tcp dport 22",       mk_pkt ~th:(th ~dport:[0; 22]) ();
      "tcp dport 80",       mk_pkt ~th:(th ~dport:[0; 80]) ();
      "saddr 10.0.0.1",     mk_pkt ~nh:(nh ~saddr:[10;0;0;1] ~daddr:[8;8;8;8]) () ];
  Printf.printf "\n";
  (* (6c) THE HEADLINE nft -o pass — value -> anonymous SET, now run as the ACTUAL
     extracted VERIFIED term (Optimize_Uncond.optimize_table_uncond, composing base
     dedup/DCE then the N-WAY value->anonymous-SET consolidation
     optimize_chain_valueset).  Previously this was a hand-OCaml mirror because the
     verified term's rule_eq_dec extracted to a multi-MB OCaml value; that bloat is
     now eliminated (compact boolean rule_end_eqb), so the verified term extracts to
     a few KB and runs directly below.

       INPUT  (nft -o oracle): `tcp dport 22|80|443 accept` (three adjacent rules)
         => OUTPUT  `tcp dport { 22, 80, 443 } accept`  (one anonymous-set rule).

     The witness shows it FIRES (3 rules -> 1, the N-element set is synthesised)
     and that `eval_chain` of the rewritten rule UNDER the synthesised set agrees
     with the original on every packet. *)
  Printf.printf "=== (6c) nft -o value->SET: tcp dport {22,80,443} (anonymous set, the headline pass) ===\n";
  (* This now runs the ACTUAL extracted VERIFIED term — the composed optimizer
     [Optimize_Uncond.optimize_table_uncond] (base dedup/DCE then the N-WAY
     value->anonymous-SET consolidation [optimize_chain_valueset]).  Its whole-pipeline
     correctness is the axiom-free [optimize_table_uncond_correct]; the per-pass
     [optimize_chain_valueset_correct] proves verdict-preservation with the synthesised
     N-element set in scope.  No hand-OCaml mirror: the [rule_eq_dec] extraction
     bloat was eliminated by the compact boolean [rule_end_eqb] (see Optimize_ValueSet.v),
     so the verified term extracts to a few KB and runs here directly. *)
  let rs_in = [
    rule [ mcmp Syntax.FThDport Bytecode.CEq [0; 22] ] Verdict.Accept;
    rule [ mcmp Syntax.FThDport Bytecode.CEq [0; 80] ] Verdict.Accept;
    rule [ mcmp Syntax.FThDport Bytecode.CEq [1; 187] ] Verdict.Accept;
  ] in
  let empty_decls : Semantics.set_decls =
    { Semantics.sd_sets = []; sd_vmaps = []; sd_maps = [] } in
  let ((_n_out, decls_out), c_out_v) =
    Optimize_Uncond.optimize_table_uncond (chain Verdict.Drop rs_in) in
  let sets_out = decls_out.Semantics.sd_sets in
  let rs_out = c_out_v.Syntax.c_rules in
  let len_in = Stdlib.List.length rs_in and len_out = Stdlib.List.length rs_out in
  Printf.printf "  rules: %d -> %d (%s)\n" len_in len_out
    (if len_out < len_in then "shrunk: N-way value-merge fired" else "NOT shrunk");
  if not (len_out < len_in) then incr fails;
  Stdlib.List.iter (fun (nm, els) ->
    Printf.printf "  synthesised set %s = { %s }\n" nm
      (Stdlib.String.concat ", "
         (Stdlib.List.map (fun (lo, _hi) ->
            string_of_int (Stdlib.List.fold_left (fun a b -> a*256+b) 0 lo)) els)))
    sets_out;
  if sets_out = [] then (Printf.printf "  NO set synthesised\n"; incr fails);
  (* must consolidate the WHOLE 3-rule run into ONE rule with a 3-element set
     (nft -o oracle: `tcp dport { 22, 80, 443 } accept`), NOT a 2-element set with a
     leftover. *)
  if len_out <> 1 then
    (Printf.printf "  EXPECTED 1 merged rule (N-way), got %d\n" len_out; incr fails);
  (match sets_out with
   | [ (_, els) ] when Stdlib.List.length els = 3 -> ()
   | _ -> Printf.printf "  EXPECTED ONE 3-element set (N-way consolidation)\n"; incr fails);
  (* verdict equivalence: original three-rule chain (policy drop) vs the rewritten
     ONE-rule chain evaluated WITH the synthesised 3-element set declared in scope. *)
  let decls : Semantics.set_decls =
    { Semantics.sd_sets = sets_out; sd_vmaps = []; sd_maps = [] } in
  let env_out = Semantics.env_with_sets empty_env decls in
  let c_in  = chain Verdict.Drop rs_in in
  let c_out = chain Verdict.Drop rs_out in
  Stdlib.List.iter (fun (name, dport) ->
    let (e_in, p_in)  = mk_pkt ~th:(th ~dport) () in
    let (e_o, p_o) = mk_pkt ~env:env_out ~th:(th ~dport) () in
    let a = Semantics.eval_chain c_in  e_in p_in in
    let b = Semantics.eval_chain c_out e_o p_o in
    let ok = a = b in
    Printf.printf "  %-26s three-rule=%-7s set-merged=%-7s %s\n"
      name (string_of_verdict a) (string_of_verdict b) (if ok then "ok" else "MISMATCH");
    if not ok then incr fails)
    [ "tcp dport 22  (in set)", [0; 22];
      "tcp dport 80  (in set)", [0; 80];
      "tcp dport 443 (in set)", [1; 187];
      "tcp dport 1   (not in)", [0; 1];
      "tcp dport 8080(not in)", [31; 144] ];
  Printf.printf "\n";
  (* (6c-N) THE N-DIMENSIONAL CONCAT pass — N(>=3)-field value tuples -> ONE concat
     SET (Optimize_ConcatMulti.v `optimize_chain_concatmulti`, composed into the verified
     `optimize_table_uncond`).  nft -o folds adjacent rules that differ in THREE OR
     MORE selector values into one rule keyed on a concatenation set.  Run here as
     the ACTUAL extracted verified term.

       INPUT (nft -o oracle):
         `ip saddr 10.0.0.1 ip daddr 10.0.0.2 ip protocol 6  accept`
         `ip saddr 10.0.0.3 ip daddr 10.0.0.4 ip protocol 17 accept`
       => OUTPUT `ip saddr . ip daddr . ip protocol { 1.2.6 , 3.4.17 } accept`.

     Witness: it FIRES (2 rules -> 1, a 2-element 3-field concat set is synthesised)
     AND `eval_chain` of the rewritten rule UNDER the synthesised set agrees with the
     original on every packet.  (All three fields are fixed-width PAYLOAD fields, as
     the merge gate `field_fixed_len = Some` requires.) *)
  Printf.printf "=== (6c-N) nft -o N-field CONCAT: ip saddr . ip daddr . ip protocol ===\n";
  (* network header with protocol byte at offset 9, saddr at 12, daddr at 16 *)
  let nh3 ~saddr ~daddr ~proto =
    (Stdlib.List.init 9 (fun _ -> 0)) @ [proto] @ [0; 0] @ saddr @ daddr in
  let row f1 f2 f3 = [
    mcmp Syntax.FIp4Saddr    Bytecode.CEq f1;
    mcmp Syntax.FIp4Daddr    Bytecode.CEq f2;
    mcmp Syntax.FIp4Protocol Bytecode.CEq f3 ] in
  let rsk_in = [
    rule (row [10;0;0;1] [10;0;0;2] [6])  Verdict.Accept;
    rule (row [10;0;0;3] [10;0;0;4] [17]) Verdict.Accept ] in
  let ((_nk, declsk), ck_v) =
    Optimize_Uncond.optimize_table_uncond (chain Verdict.Drop rsk_in) in
  let setsk = declsk.Semantics.sd_sets in
  let rsk_out = ck_v.Syntax.c_rules in
  let lk_in = Stdlib.List.length rsk_in and lk_out = Stdlib.List.length rsk_out in
  Printf.printf "  rules: %d -> %d (%s)\n" lk_in lk_out
    (if lk_out < lk_in then "shrunk: N-field concat-merge fired" else "NOT shrunk");
  if lk_out <> 1 then (Printf.printf "  EXPECTED 1 merged rule, got %d\n" lk_out; incr fails);
  (match setsk with
   | [ (nm, els) ] when Stdlib.List.length els = 2 ->
       Printf.printf "  synthesised concat set %s (%d 3-field tuples)\n" nm (Stdlib.List.length els)
   | _ -> Printf.printf "  EXPECTED ONE 2-element concat set\n"; incr fails);
  let declsk' : Semantics.set_decls =
    { Semantics.sd_sets = setsk; sd_vmaps = []; sd_maps = [] } in
  let envk = Semantics.env_with_sets empty_env declsk' in
  let ck_in  = chain Verdict.Drop rsk_in in
  let ck_out = chain Verdict.Drop rsk_out in
  Stdlib.List.iter (fun (name, sa, da, pr) ->
    let (e_in, p_in)  = mk_pkt ~nh:(nh3 ~saddr:sa ~daddr:da ~proto:pr) () in
    let (e_o, p_o) = mk_pkt ~env:envk ~nh:(nh3 ~saddr:sa ~daddr:da ~proto:pr) () in
    let a = Semantics.eval_chain ck_in  e_in p_in in
    let b = Semantics.eval_chain ck_out e_o p_o in
    let ok = a = b in
    Printf.printf "  %-32s two-rule=%-7s concat-merged=%-7s %s\n"
      name (string_of_verdict a) (string_of_verdict b) (if ok then "ok" else "MISMATCH");
    if not ok then incr fails)
    [ "1.0.0.1 . 1.0.0.2 . 6  (tuple1)",  [10;0;0;1], [10;0;0;2], 6;
      "3.0.0.3 . 3.0.0.4 . 17 (tuple2)",  [10;0;0;3], [10;0;0;4], 17;
      "1.0.0.1 . 1.0.0.2 . 17 (proto miss)", [10;0;0;1], [10;0;0;2], 17;
      "9.9.9.9 . 1.0.0.2 . 6  (saddr miss)", [9;9;9;9], [10;0;0;2], 6 ];
  Printf.printf "\n";
  (* (6d) THE VMAP nft -o pass — value+verdict -> VERDICT MAP (Optimize_Vmap.v
     `optimize_rules_vmap2` / `optimize_chain_vmap2_correct`, axiom-free).  The
     verified pass mints a fresh `__vmapN`, emits its (v1,v1,w1)/(v2,v2,w2)
     declaration, and rewrites the adjacent pair (same field, DIFFERING verdicts)
     into ONE rule whose terminal is a vmap keyed on `f` against `__vmapN`.  We
     re-create the SAME rewrite in OCaml (as in 6c); `optimize_rules_vmap2_correct`
     guarantees it is verdict-preserving WITH the synthesised vmap in scope.

       INPUT  (nft -o oracle: `tcp dport 22 accept` + `tcp dport 80 drop`):
         => OUTPUT  `tcp dport vmap { 22 : accept, 80 : drop }`  (vmap __vmap0).

     The witness shows it FIRES (2 rules -> 1, a vmap declaration is synthesised)
     and that `eval_chain` of the rewritten rule UNDER the synthesised vmap agrees
     with the two-rule original on every packet (dport 22 -> accept, 80 -> drop,
     miss -> policy). *)
  Printf.printf "=== (6d) nft -o value+verdict->VMAP: tcp dport vmap { 22:accept, 80:drop } ===\n";
  (* Runs the ACTUAL extracted VERIFIED term [Optimize_Vmap.optimize_chain_vmap]
     (the N-WAY value+verdict->VERDICT-MAP consolidation), whose correctness is the
     axiom-free [optimize_chain_vmap_correct].  No hand-OCaml mirror — the verified
     term now extracts compactly (the [rule_eq_dec] bloat was replaced by the boolean
     [rule_end_eqb], see Optimize_Vmap.v / Optimize_ValueSet.v). *)
  let vrs_in = [
    rule [ mcmp Syntax.FThDport Bytecode.CEq [0; 22] ] Verdict.Accept;
    rule [ mcmp Syntax.FThDport Bytecode.CEq [0; 80] ] Verdict.Drop;
    rule [ mcmp Syntax.FThDport Bytecode.CEq [1; 187] ] Verdict.Accept;
  ] in
  let vempty_decls : Semantics.set_decls =
    { Semantics.sd_sets = []; sd_vmaps = []; sd_maps = [] } in
  let ((_vn, vdecls_out), vc_out_v) =
    Optimize_Vmap.optimize_chain_vmap 0 vempty_decls (chain Verdict.Drop vrs_in) in
  let vmaps_out = vdecls_out.Semantics.sd_vmaps in
  let vrs_out = vc_out_v.Syntax.c_rules in
  let vlen_in = Stdlib.List.length vrs_in and vlen_out = Stdlib.List.length vrs_out in
  Printf.printf "  rules: %d -> %d (%s)\n" vlen_in vlen_out
    (if vlen_out < vlen_in then "shrunk: N-way vmap-merge fired" else "NOT shrunk");
  if vlen_out <> 1 then
    (Printf.printf "  EXPECTED 1 merged rule (N-way), got %d\n" vlen_out; incr fails);
  (match vmaps_out with
   | [ (_, ents) ] when Stdlib.List.length ents = 3 -> ()
   | _ -> Printf.printf "  EXPECTED ONE 3-entry vmap (N-way consolidation)\n"; incr fails);
  if not (vlen_out < vlen_in) then incr fails;
  Stdlib.List.iter (fun (nm, ents) ->
    Printf.printf "  synthesised vmap %s = { %s }\n" nm
      (Stdlib.String.concat ", "
         (Stdlib.List.map (fun ((lo, _hi), w) ->
            Printf.sprintf "%d : %s"
              (Stdlib.List.fold_left (fun a b -> a*256+b) 0 lo)
              (string_of_verdict w)) ents)))
    vmaps_out;
  if vmaps_out = [] then (Printf.printf "  NO vmap synthesised\n"; incr fails);
  (* verdict equivalence: original two-rule chain (policy continue->drop fallthrough
     modelled as policy Drop) vs the rewritten ONE-rule chain WITH the synthesised
     vmap declared in scope. *)
  let vdecls : Semantics.set_decls =
    { Semantics.sd_sets = []; sd_vmaps = vmaps_out; sd_maps = [] } in
  let venv_out = Semantics.env_with_sets empty_env vdecls in
  let vc_in  = chain Verdict.Drop vrs_in in
  let vc_out = chain Verdict.Drop vrs_out in
  Stdlib.List.iter (fun (name, dport) ->
    let (e_in, p_in)  = mk_pkt ~th:(th ~dport) () in
    let (e_o, p_o) = mk_pkt ~env:venv_out ~th:(th ~dport) () in
    let a = Semantics.eval_chain vc_in  e_in p_in in
    let b = Semantics.eval_chain vc_out e_o p_o in
    let ok = a = b in
    Printf.printf "  %-28s two-rule=%-7s vmap-merged=%-7s %s\n"
      name (string_of_verdict a) (string_of_verdict b) (if ok then "ok" else "MISMATCH");
    if not ok then incr fails)
    [ "tcp dport 22 -> accept",  [0; 22];
      "tcp dport 80 -> drop",    [0; 80];
      "tcp dport 443 -> accept", [1; 187];
      "tcp dport 1   -> policy", [0; 1] ];
  Printf.printf "\n";
  (* (6e) THE CONCAT nft -o pass — two selectors -> CONCATENATION SET
     (Optimize_Concat.v `optimize_rules_concat2` / `optimize_chain_concat2_correct`,
     axiom-free).  The verified pass mints a fresh `__setN`, emits its packed
     two-field point tuples (each field in its 4-byte register slot, last field
     taking the remainder), and rewrites the adjacent pair (differing in BOTH
     selectors, same verdict) into ONE `MConcatSet [f1;f2] false __setN` rule.  We
     re-create the SAME rewrite in OCaml (as in 6c/6d); `optimize_rules_concat2_correct`
     guarantees it is verdict-preserving WITH the synthesised concat set in scope.

       INPUT  (nft -o oracle, ran via `unshare -rn nft -o -f`):
         ip saddr 1.1.1.1 tcp dport 22 accept
         ip saddr 2.2.2.2 tcp dport 80 accept
       => OUTPUT
         ip saddr . tcp dport { 1.1.1.1 . 22, 2.2.2.2 . 80 } accept

     The witness shows it FIRES (2 rules -> 1, a concat set is synthesised) and that
     `eval_chain` of the rewritten rule UNDER the synthesised set agrees with the
     two-rule original on the matching tuples and on a miss (-> policy). *)
  Printf.printf "=== (6e) nft -o concat->SET: ip saddr . tcp dport { 1.1.1.1 . 22, 2.2.2.2 . 80 } accept ===\n";
  (* Runs the ACTUAL extracted VERIFIED term [Optimize_Concat.optimize_chain_concat]
     (the N-WAY two-selector->CONCATENATION-SET consolidation), whose correctness is
     the axiom-free [optimize_chain_concat_correct].  No hand-OCaml mirror — the
     verified term now extracts compactly. *)
  let crule a b w : Syntax.rule =
    rule [ mcmp Syntax.FIp4Saddr Bytecode.CEq a;
           mcmp Syntax.FThDport Bytecode.CEq b ] w in
  let crs_in = [ crule [1;1;1;1] [0;22] Verdict.Accept;
                 crule [2;2;2;2] [0;80] Verdict.Accept;
                 crule [3;3;3;3] [1;187] Verdict.Accept ] in
  let cempty_decls : Semantics.set_decls =
    { Semantics.sd_sets = []; sd_vmaps = []; sd_maps = [] } in
  let ((_cn, cdecls_out), cc_out_v) =
    Optimize_Concat.optimize_chain_concat 0 cempty_decls (chain Verdict.Drop crs_in) in
  let csets_out = cdecls_out.Semantics.sd_sets in
  let crs_out = cc_out_v.Syntax.c_rules in
  let clen_in = Stdlib.List.length crs_in and clen_out = Stdlib.List.length crs_out in
  Printf.printf "  rules: %d -> %d (%s)\n" clen_in clen_out
    (if clen_out < clen_in then "shrunk: N-way concat-merge fired" else "NOT shrunk");
  if clen_out <> 1 then
    (Printf.printf "  EXPECTED 1 merged rule (N-way), got %d\n" clen_out; incr fails);
  (match csets_out with
   | [ (_, els) ] when Stdlib.List.length els = 3 -> ()
   | _ -> Printf.printf "  EXPECTED ONE 3-tuple concat set (N-way)\n"; incr fails);
  if not (clen_out < clen_in) then incr fails;
  Stdlib.List.iter (fun (nm, els) ->
    Printf.printf "  synthesised concat set %s = { %s }\n" nm
      (Stdlib.String.concat ", "
         (Stdlib.List.map (fun (lo, _hi) ->
            Stdlib.String.concat "." (Stdlib.List.map string_of_int lo)) els)))
    csets_out;
  if csets_out = [] then (Printf.printf "  NO concat set synthesised\n"; incr fails);
  let cdecls : Semantics.set_decls =
    { Semantics.sd_sets = csets_out; sd_vmaps = []; sd_maps = [] } in
  let cenv_out = Semantics.env_with_sets empty_env cdecls in
  let cc_in  = chain Verdict.Drop crs_in in
  let cc_out = chain Verdict.Drop crs_out in
  Stdlib.List.iter (fun (name, saddr, dport) ->
    let (e_in, p_in)  = mk_pkt ~nh:(nh ~saddr ~daddr:[8;8;8;8]) ~th:(th ~dport) () in
    let (e_o, p_o) = mk_pkt ~env:cenv_out ~nh:(nh ~saddr ~daddr:[8;8;8;8]) ~th:(th ~dport) () in
    let a = Semantics.eval_chain cc_in  e_in p_in in
    let b = Semantics.eval_chain cc_out e_o p_o in
    let ok = a = b in
    Printf.printf "  %-40s two-rule=%-7s concat-merged=%-7s %s\n"
      name (string_of_verdict a) (string_of_verdict b) (if ok then "ok" else "MISMATCH");
    if not ok then incr fails)
    [ "1.1.1.1 . 22  (in set -> accept)", [1;1;1;1], [0;22];
      "2.2.2.2 . 80  (in set -> accept)", [2;2;2;2], [0;80];
      "3.3.3.3 . 443 (in set -> accept)", [3;3;3;3], [1;187];
      "1.1.1.1 . 80  (cross miss -> policy)", [1;1;1;1], [0;80];
      "9.9.9.9 . 22  (saddr miss -> policy)", [9;9;9;9], [0;22] ];
  Printf.printf "\n";

  (* === (6f) DATA-VALUE-MAP consolidation: `meta mark set ... map` (TODO 1a) ===

       INPUT (the two rules our pass folds):
         ip saddr 1.1.1.1 meta mark set 0x0a
         ip saddr 2.2.2.2 meta mark set 0x14
       => OUTPUT (our verified pass):
         ip saddr { 1.1.1.1, 2.2.2.2 } meta mark set ip saddr map { 1.1.1.1 : 0x0a, 2.2.2.2 : 0x14 }

     NOTE ON FIDELITY: this is NOT `nft -o`'s output.  `nft -o` (v1.1.6) does not
     merge `meta mark set` at all, and for the maps it DOES emit (dnat/snat) it emits
     a BARE map with no head set guard.  We emit the head-set-GUARDED form, which is
     valid, equivalent nftables and is required for soundness in our model (whose
     statement value-map semantics load the map default on a miss rather than
     NFT_BREAK; see the Optimize_DataMap.v header).  What this witnesses is a SOUND
     state-preserving data-map consolidation, not nft -o byte-fidelity.

     Unlike 6c-6e (which consolidate the VERDICT, checked against verdict-only
     [eval_chain]), this folds the differing STATEMENT VALUE (the mark) into a data
     MAP.  The merge is verdict-neutral, so it is invisible to [eval_chain]; the real
     content is the META STATE.  We therefore run the extracted STATE-threading
     semantics [Semantics.dsl_step] and read the resulting [MKmark] — the witness of
     [Optimize_DataMap.dsl_step_map_merge] / the [optimize_table_uncond_correct] chain.

     Runs the ACTUAL extracted VERIFIED term [Optimize_DataMap.optimize_chain_datamap]; this
     pass is the FIRST to synthesise an [sd_maps] entry alongside the head [sd_sets]. *)
  Printf.printf "=== (6f) data-map consolidation: ip saddr { .. } meta mark set ip saddr map { .. } ===\n";
  let omap_rule v m : Syntax.rule =
    rule_b [ Syntax.BMatch (Syntax.MCmp (Syntax.FIp4Saddr, Bytecode.CEq, v));
             Syntax.BStmt (Syntax.SMetaSet (Packet.MKmark, Syntax.VImm m)) ]
           Verdict.Continue in
  let mv1 = [1;1;1;1] and mv2 = [2;2;2;2] in
  let mark1 = [0;0;0;10] and mark2 = [0;0;0;20] in
  let mrs_in = [ omap_rule mv1 mark1; omap_rule mv2 mark2 ] in
  let mempty_decls : Semantics.set_decls =
    { Semantics.sd_sets = []; sd_vmaps = []; sd_maps = [] } in
  let ((_mn, mdecls_out), mc_out_v) =
    Optimize_DataMap.optimize_chain_datamap 0 mempty_decls (chain Verdict.Drop mrs_in) in
  let mrs_out = mc_out_v.Syntax.c_rules in
  let mlen_in = Stdlib.List.length mrs_in and mlen_out = Stdlib.List.length mrs_out in
  Printf.printf "  rules: %d -> %d (%s)\n" mlen_in mlen_out
    (if mlen_out < mlen_in then "shrunk: data-map merge fired" else "NOT shrunk");
  if mlen_out <> 1 then
    (Printf.printf "  EXPECTED 1 merged rule, got %d\n" mlen_out; incr fails);
  (match mdecls_out.Semantics.sd_sets with
   | [ (snm, els) ] when Stdlib.List.length els = 2 ->
       Printf.printf "  synthesised head SET %s = { 1.1.1.1, 2.2.2.2 }\n" snm
   | _ -> Printf.printf "  EXPECTED ONE 2-element head set\n"; incr fails);
  (match mdecls_out.Semantics.sd_maps with
   | [ (mnm, els) ] when Stdlib.List.length els = 2 ->
       Printf.printf "  synthesised data MAP %s = { 1.1.1.1:0x0a, 2.2.2.2:0x14 }  (FIRST sd_maps writer)\n" mnm
   | _ -> Printf.printf "  EXPECTED ONE 2-entry data map (sd_maps)\n"; incr fails);
  let menv = Semantics.env_with_sets empty_env mdecls_out in
  let merged = (match mrs_out with [ r ] -> r | _ -> Stdlib.List.hd mrs_in) in
  let orig1 = omap_rule mv1 mark1 and orig2 = omap_rule mv2 mark2 in
  let hexm m = "0x" ^ Stdlib.String.concat "" (Stdlib.List.map (Printf.sprintf "%02x") m) in
  Stdlib.List.iter (fun (name, saddr) ->
    let (e, p) = mk_pkt ~env:menv ~nh:(nh ~saddr ~daddr:[8;8;8;8]) () in
    (* the merged rule's mark write vs the two originals composed *)
    let (_, p_merged) = Semantics.dsl_step merged e p in
    let p_orig   = (let (e1, p1) = Semantics.dsl_step orig1 e p in
                    snd (Semantics.dsl_step orig2 e1 p1)) in
    let mark_merged = p_merged.Packet.pkt_meta Packet.MKmark in
    let mark_orig   = p_orig.Packet.pkt_meta Packet.MKmark in
    let ok = mark_merged = mark_orig in
    Printf.printf "  %-34s two-rule mark=%-10s map-merged mark=%-10s %s\n"
      name (hexm mark_orig) (hexm mark_merged) (if ok then "ok" else "MISMATCH");
    if not ok then incr fails)
    [ "1.1.1.1 (key -> mark 0x0a)", [1;1;1;1];
      "2.2.2.2 (key -> mark 0x14)", [2;2;2;2];
      "9.9.9.9 (miss -> mark unchanged)", [9;9;9;9] ];
  Printf.printf "\n";

  Printf.printf "%s: compile & optimize preserve the DSL verdict AND meta-state on every packet\n"
    (if !fails = 0 then "PASS" else Printf.sprintf "FAIL (%d mismatches)" !fails);
  if !fails > 0 then exit 1
