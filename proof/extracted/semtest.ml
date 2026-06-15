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
    e_fib = (fun _ _ -> []); e_rt = (fun _ -> []) }
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
let mk_pkt ?(env = empty_env) ?(l4proto = [6]) ?(nh = []) ?(th = []) () : Packet.packet =
  { Packet.pkt_env = env;
    pkt_meta = (fun k -> match k with Packet.MKl4proto -> l4proto | _ -> []);
    pkt_ct = dummy0; pkt_sock = dummy0;
    pkt_eh = (fun _ _ _ _ _ -> []);
    pkt_lh = []; pkt_nh = nh; pkt_th = th; pkt_ih = []; pkt_tnl = [];
    pkt_limit = (fun _ -> true); pkt_quota = (fun _ -> true);
    pkt_connlimit = (fun _ -> true);
    pkt_numgen = dummy0; pkt_osf = [];
    pkt_tunnel = (fun _ -> []);
    pkt_symhash = (fun _ _ -> []); pkt_xfrm = (fun _ _ _ -> []);
    pkt_ctdir = (fun _ _ -> []); pkt_inner = (fun _ _ _ _ -> []) }

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
  let vm_env = env_vmap "portmap" [ ([0; 22], Verdict.Drop); ([0; 80], Verdict.Accept) ] in
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
  (* (5) Phase B: in-traversal mutation.  Rule 1 sets meta mark; rule 2 matches
     it.  Under the mutation-aware semantics (eval/run_chain_mut) the second rule
     observes the write and the packet is ACCEPTED; the old verdict-only eval_chain
     no-ops the set so it reads the original mark and falls through to DROP.  The
     witness shows (a) the compiler preserves the mutated verdict (DSL_mut = VM_mut)
     and (b) mutation actually changes the result (mut != no-mut). *)
  Printf.printf "=== meta mark set 0x1 ; meta mark 0x1 accept (Phase B: mutation visible later) ===\n";
  let mut_chain = chain Verdict.Drop [
    rule_b [ Syntax.BStmt (Syntax.SMetaSet (Packet.MKmark, Syntax.VImm [1])) ] Verdict.Continue;
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
  Printf.printf "%s: compile & optimize preserve the DSL verdict on every packet\n"
    (if !fails = 0 then "PASS" else Printf.sprintf "FAIL (%d mismatches)" !fails);
  if !fails > 0 then exit 1
