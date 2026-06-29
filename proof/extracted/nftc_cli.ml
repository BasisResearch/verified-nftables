(* nftc — the verified nftables optimizer/compiler as a first-class CLI.

   Usage:
     nftc compile  [FILE.nft | -]      parse -> compile_chain -> netlink text
     nftc optimize [FILE.nft | -]      parse -> optimize_table_uncond -> compile -> netlink text
     nftc send     [FILE.nft | -]      parse -> (optimize ->) compile -> SEND to the kernel
                                       (requires --commit; mutates kernel state; see Nl_send)

   Options:
     --table T        restrict to table T (default: all parsed tables)
     --chain C        restrict to base chain C (default: all base chains)
     --no-optimize    for `send`: compile the parsed chain WITHOUT the optimizer
     --commit         for `send`: actually transmit (otherwise a dry run that
                      prints the netlink batch it WOULD send)
     -h | --help      this message

   The compile/optimize core is the EXTRACTED VERIFIED term: `optimize` bottoms
   out in [Optimize_Uncond.optimize_table_uncond] (whole-pipeline verdict
   preservation, axiom-free) and `compile` in [Compile.compile_chain]
   (compile_chain_correct). The parser, renderer (Codec) and sender (Nl_send) are
   untrusted glue, validated differentially against live `nft` — never the TCB. *)

module L = Stdlib.List
module String = Stdlib.String

let prog = "nftc"

let usage () =
  prerr_string
    ("usage: " ^ prog ^ " {compile|optimize|send} [FILE.nft | -] \
      [--table T] [--chain C] [--no-optimize] [--commit]\n");
  exit 2

(* read the whole ruleset text from a file path, or stdin for "-"/absent *)
let read_input = function
  | Some "-" | None ->
      let buf = Buffer.create 4096 in
      (try while true do Buffer.add_channel buf stdin 4096 done with End_of_file -> ());
      Buffer.contents buf
  | Some path ->
      let ic = open_in_bin path in
      let n = in_channel_length ic in
      let s = really_input_string ic n in
      close_in ic; s

(* run the FULL verified consolidation pipeline (Optimize_Uncond.optimize_table_uncond),
   returning the synthesised set/map declarations + the rewritten chain *)
let optimize_table (c : Syntax.chain) : Semantics.set_decls * Syntax.chain =
  let (nd, c') = Optimize_Uncond.optimize_table_uncond c in
  (snd nd, c')

(* the base chains (table, chain-name, chain) of a parsed ruleset, optionally
   filtered by --table / --chain.  A chain is a BASE chain iff it is registered
   with a hook in p_hooks (a jump-target-only chain has no hook). *)
let selected_chains (p : Nft_lower.parsed) ~table ~chain
  : (string * string * Syntax.chain) list =
  let want_table t = match table with None -> true | Some t' -> t = t' in
  let want_chain c = match chain with None -> true | Some c' -> c = c' in
  L.concat_map
    (fun (_fam, tname, chains) ->
      if not (want_table tname) then []
      else
        let hooks =
          match L.find_opt (fun (_f, n, _h) -> n = tname) p.Nft_lower.p_hooks with
          | Some (_f, _n, hs) -> hs | None -> [] in
        let is_base cn = L.exists (fun (n, _hook, _prio) -> n = cn) hooks in
        L.filter_map
          (fun (cn, c) ->
            if is_base cn && want_chain cn then Some (tname, cn, c) else None)
          chains)
    p.Nft_lower.p_tables

(* render a compiled program with a table/chain header line *)
let render_chain ~table ~chain (program : Bytecode.program) : string =
  let hdr = Printf.sprintf "%s %s" table chain in
  let buf = Buffer.create 256 in
  L.iter
    (fun rp ->
      Buffer.add_string buf hdr; Buffer.add_char buf '\n';
      Buffer.add_string buf (Codec.render_rule rp); Buffer.add_char buf '\n')
    program;
  Buffer.contents buf

(* render the anonymous set/map declarations the optimizer minted *)
let render_decls (d : Semantics.set_decls) : string =
  let buf = Buffer.create 64 in
  L.iter
    (fun (nm, elems) ->
      let pts = String.concat ", "
          (L.map (fun (lo, _hi) -> Codec.render_value lo) elems) in
      Buffer.add_string buf (Printf.sprintf "  set %s = { %s }\n" nm pts))
    d.Semantics.sd_sets;
  L.iter
    (fun (nm, _entries) ->
      Buffer.add_string buf (Printf.sprintf "  map %s = { ... }\n" nm))
    d.Semantics.sd_vmaps;
  Buffer.contents buf

let () =
  let args = Stdlib.Array.to_list Sys.argv in
  match args with
  | _ :: ("-h" | "--help") :: _ | [_] -> usage ()
  | _ :: cmd :: rest ->
      let file = ref None and table = ref None and chain = ref None in
      let no_opt = ref false and commit = ref false in
      let rec go = function
        | [] -> ()
        | "--table" :: t :: r -> table := Some t; go r
        | "--chain" :: c :: r -> chain := Some c; go r
        | "--no-optimize" :: r -> no_opt := true; go r
        | "--commit" :: r -> commit := true; go r
        | ("-h" | "--help") :: _ -> usage ()
        | x :: _ when String.length x > 0 && x.[0] = '-' && x <> "-" ->
            prerr_string (prog ^ ": unknown option " ^ x ^ "\n"); usage ()
        | x :: r -> (match !file with None -> file := Some x | Some _ -> usage ()); go r
      in
      go rest;
      let text = read_input !file in
      let parsed =
        try Nft_parse.parse_string text
        with
        | Nft_parse.Parse_error msg ->
            prerr_string (prog ^ ": parse error: " ^ msg ^ "\n"); exit 1
        | Nft_lower.Unsupported msg ->
            prerr_string (prog ^ ": unsupported construct: " ^ msg ^ "\n"); exit 1
      in
      let chains = selected_chains parsed ~table:!table ~chain:!chain in
      if chains = [] then (prerr_string (prog ^ ": no matching base chain\n"); exit 1);
      (match cmd with
       | "compile" ->
           L.iter
             (fun (t, cn, c) ->
               print_string (render_chain ~table:t ~chain:cn (Compile.compile_chain c)))
             chains
       | "optimize" ->
           L.iter
             (fun (t, cn, c) ->
               let (decls, c') = optimize_table c in
               print_string (render_chain ~table:t ~chain:cn (Compile.compile_chain c'));
               let ds = render_decls decls in
               if String.length ds > 0 then
                 (print_string "  # synthesised by the verified optimizer:\n";
                  print_string ds))
             chains
       | "send" ->
           (try
              L.iter
                (fun (t, cn, c) ->
                  let c' = if !no_opt then c else snd (optimize_table c) in
                  let program = Compile.compile_chain c' in
                  Nl_send.send_chain ~table:t ~chain:cn ~commit:!commit program)
                chains
            with Nl_send.Unsupported msg ->
              prerr_string (prog ^ ": cannot encode for netlink: " ^ msg ^ "\n"); exit 4)
       | _ -> usage ())
  | _ -> usage ()
