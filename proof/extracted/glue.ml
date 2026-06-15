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
let rule ms v : Syntax.rule =
  { Syntax.r_matches = ms; r_stmts = []; r_verdict = v }
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
  | Bytecode.IImmediate v ->
      Printf.sprintf "  [ immediate reg 0 %s ]" (verdict_name v)

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
  match mode with
  | "optimize" -> print_compiled (Optimize.optimize_chain c)
  | "optdemo" ->
      (* A chain exercising both optimizations:
         - rule 1 has a duplicate `tcp dport 22` match (dedup removes it);
         - rule 2 matches everything and is terminal (accept-all) -> rules 3,4
           below it are dead (DCE drops them). *)
      let d =
        chain Verdict.Drop [
          rule [ dep_tcp; meq Syntax.FThDport [0; 22];
                 dep_tcp; meq Syntax.FThDport [0; 22] ] Verdict.Accept;
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
