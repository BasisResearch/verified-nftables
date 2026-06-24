(* Untrusted glue around the *verified* extracted compiler/optimizer.

   Responsibilities (all untrusted, all small and testable):
     - build concrete DSL chains;
     - render a compiled [Bytecode.program] in the exact textual format of
       `nft --debug=netlink`, so the two can be diffed (differential testing);
     - a tiny demo [main] used by ../difftest.sh.

   The trusted core (compile_chain / optimize_chain and their correctness) lives
   in the extracted modules; nothing here is trusted for the correctness theorem. *)

(* ---- DSL builders (just record/constructor sugar) ---- *)

let meq f v   : Syntax.matchcond = Syntax.MEq (f, v)
(* `field == value` lowered as an ordered comparison (what the value->set merge
   recognises as a mergeable head, via [Optimize_Merge.head_value]). *)
let mcmpeq f v : Syntax.matchcond = Syntax.MCmp (f, Bytecode.CEq, v)
let mrange f lo hi : Syntax.matchcond = Syntax.MRange (f, false, lo, hi)
let rule ms v : Syntax.rule =
  { Syntax.r_body = Stdlib.List.map (fun m -> Syntax.BMatch m) ms;
    r_verdict = v; r_vmap = None; r_nat = None; r_tproxy = None; r_fwd = None;
    r_queue = None; r_after = [] }
let chain pol rs : Syntax.chain = { Syntax.c_policy = pol; Syntax.c_rules = rs }

(* l4proto dependency nft auto-inserts before an L4 (tcp/udp) match. *)
let dep_tcp = meq Syntax.FMetaL4proto [6]

(* ---- rendering: program -> nft --debug=netlink text ---- *)

let base_name = function
  | Packet.PNetwork   -> "network"
  | Packet.PTransport -> "transport"

let meta_name = function
  | Packet.MKl4proto -> "l4proto"

let cmpop_name = function
  | Bytecode.CEq -> "eq"
  | Bytecode.CNe -> "neq"
  | Bytecode.CLt -> "lt"
  | Bytecode.CGt -> "gt"
  | Bytecode.CLe -> "lte"
  | Bytecode.CGe -> "gte"

let verdict_name = function
  | Verdict.Accept   -> "accept"
  | Verdict.Drop     -> "drop"
  | Verdict.Continue -> "continue"

(* nft dumps a register value as little-endian 32-bit words, zero-padded to a
   4-byte boundary, each printed as 0x%08x and space-separated. *)
let render_data (d : Bytes.data) : string =
  let a = Stdlib.Array.of_list d in
  let n = Stdlib.Array.length a in
  let words = (n + 3) / 4 in
  let buf = Buffer.create 16 in
  for w = 0 to words - 1 do
    if w > 0 then Buffer.add_char buf ' ';
    let v = ref 0 in
    for k = 0 to 3 do
      let idx = w * 4 + k in
      let b = if idx < n then a.(idx) else 0 in
      v := !v lor (b lsl (8 * k))
    done;
    Buffer.add_string buf (Printf.sprintf "0x%08x" !v)
  done;
  Buffer.contents buf

let render_instr (i : Bytecode.instr) : string =
  match i with
  | Bytecode.IMetaLoad (k, dst) ->
      Printf.sprintf "  [ meta load %s => reg %d ]" (meta_name k) dst
  | Bytecode.IPayloadLoad (b, off, len, dst) ->
      Printf.sprintf "  [ payload load %db @ %s header + %d => reg %d ]"
        len (base_name b) off dst
  | Bytecode.ICmp (op, src, v) ->
      Printf.sprintf "  [ cmp %s reg %d %s ]" (cmpop_name op) src (render_data v)
  | Bytecode.IRange (op, src, lo, hi) ->
      Printf.sprintf "  [ range %s reg %d %s %s ]"
        (cmpop_name op) src (render_data lo) (render_data hi)
  | Bytecode.IImmediate v ->
      Printf.sprintf "  [ immediate reg 0 %s ]" (verdict_name v)
  | Bytecode.ILookup (srcs, name, inv) ->
      let regs = Stdlib.String.concat " "
                   (Stdlib.List.map (fun r -> Printf.sprintf "reg %d" r) srcs) in
      Printf.sprintf "  [ lookup %s set %s%s ]" regs name
        (if inv then " inv" else "")
  | _ -> "  [ <instr> ]"

(* family/table/chain header line nft prints before each rule's expressions. *)
let render_program ?(hdr = "ip filter input") (prog : Bytecode.program) : string =
  let buf = Buffer.create 256 in
  Stdlib.List.iter
    (fun rp ->
      Buffer.add_string buf hdr; Buffer.add_char buf '\n';
      Stdlib.List.iter
        (fun ins -> Buffer.add_string buf (render_instr ins); Buffer.add_char buf '\n')
        rp)
    prog;
  Buffer.contents buf

let print_compiled ?hdr c =
  print_string (render_program ?hdr (Compile.compile_chain c))

(* ---- demo ---- *)

let () =
  let mode = if Stdlib.Array.length Sys.argv > 1 then Sys.argv.(1) else "compile" in
  (* Mirrors proof/difftest.sh's nft input, in nft's expression-emission order. *)
  let c =
    chain Verdict.Drop [
      rule [ dep_tcp; meq Syntax.FThDport [0; 22] ] Verdict.Accept;
      rule [ meq Syntax.FIp4Saddr [10; 1; 2; 3] ] Verdict.Drop;
      rule [ dep_tcp; meq Syntax.FThSport [0; 80] ] Verdict.Accept;
      rule [ meq Syntax.FIp4Daddr [192; 168; 1; 1];
             dep_tcp; meq Syntax.FThDport [1; 187] ] Verdict.Accept;
    ]
  in
  (* empty table declarations to seed the verified composed optimizer *)
  let empty_decls : Semantics.set_decls =
    { Semantics.sd_sets = []; sd_vmaps = []; sd_maps = [] } in
  (* render the synthesised set declarations the verified pass minted *)
  let render_decls (d : Semantics.set_decls) : string =
    let buf = Buffer.create 64 in
    Stdlib.List.iter
      (fun (nm, elems) ->
        let pts = Stdlib.String.concat ", "
            (Stdlib.List.map (fun (lo, _hi) -> render_data lo) elems) in
        Buffer.add_string buf (Printf.sprintf "  set %s = { %s }\n" nm pts))
      d.Semantics.sd_sets;
    Buffer.contents buf
  in
  match mode with
  | "optimize" ->
      (* Run the VERIFIED composed optimizer [optimize_table_sets] (base dedup/DCE
         then the N-WAY value->anonymous-SET consolidation), whose whole-pipeline
         correctness is the axiom-free [optimize_table_sets_correct]. *)
      let (_, c') = Optimize_Table.optimize_table_sets 0 empty_decls c in
      print_compiled c'
  | "optsets" ->
      (* A realistic multi-rule ruleset where three adjacent rules differ ONLY in
         the [tcp dport] value and share the [accept] verdict — exactly what
         `nft -o` folds into ONE `tcp dport { 22, 80, 443 } accept` (a value->set
         consolidation), here performed by the VERIFIED extracted term. *)
      let d =
        chain Verdict.Accept [
          (* three adjacent `ip saddr <a>` rules sharing the `drop` verdict and
             differing ONLY in the address value -> ONE `ip saddr { .. } drop` *)
          rule [ mcmpeq Syntax.FIp4Saddr [10; 0; 0; 1] ] Verdict.Drop;
          rule [ mcmpeq Syntax.FIp4Saddr [10; 0; 0; 2] ] Verdict.Drop;
          rule [ mcmpeq Syntax.FIp4Saddr [10; 0; 0; 3] ] Verdict.Drop;
          rule [ dep_tcp; meq Syntax.FThDport [0; 22] ]  Verdict.Accept;
        ]
      in
      let ((_, decls'), d') =
        Optimize_Table.optimize_table_sets 0 empty_decls d in
      print_string "--- before (verified optimize_table_sets) ---\n";
      print_compiled d;
      print_string "--- after (verified optimize_table_sets) ---\n";
      print_compiled d';
      print_string "--- synthesised set declarations ---\n";
      print_string (render_decls decls')
  | "optdemo" ->
      (* A chain exercising both optimizations:
         - rule 1 has a duplicate `tcp dport 22` match (dedup removes it);
         - rule 2 matches everything and is terminal (accept-all) -> rules 3,4
           below it are dead (DCE drops them). *)
      let d =
        chain Verdict.Drop [
          rule [ dep_tcp; meq Syntax.FThDport [0; 22];
                 dep_tcp; meq Syntax.FThDport [0; 22] ] Verdict.Accept;
          (* singleton range 22..22 -> simplify_match rewrites it to `cmp eq` *)
          rule [ dep_tcp; mrange Syntax.FThDport [0; 22] [0; 22] ] Verdict.Accept;
          rule [] Verdict.Accept;                       (* accept-all, terminal *)
          rule [ meq Syntax.FIp4Saddr [10; 1; 2; 3] ] Verdict.Drop;   (* dead *)
          rule [ meq Syntax.FIp4Daddr [192; 168; 1; 1] ] Verdict.Drop (* dead *)
        ]
      in
      print_string "--- before optimization ---\n";
      print_compiled d;
      print_string "--- after optimization ---\n";
      print_compiled (Optimize.optimize_chain d)
  | _          -> print_compiled c
