(* nftc — the verified nftables optimizer/compiler as a first-class CLI.

   Usage:
     nftc compile  [FILE.nft | -]      parse -> compile_chain -> netlink text
     nftc optimize [FILE.nft | -]      parse -> optimize_table_uncond -> compile -> netlink text
     nftc send     [FILE.nft | -]      parse -> (optimize ->) compile -> SEND to the kernel
                                       (requires --commit; mutates kernel state; see Nl_send)

   `send` builds ONE atomic nfnetlink batch for the whole selected ruleset —
   NEWTABLE, NEWCHAIN (every chain, so jump targets exist), NEWSET + NEWSETELEM
   (each set/map a rule references), then NEWRULE per rule — so a ruleset is
   stood up from scratch with no preparatory `nft add`.  Exit codes:
     0 ok ; 1 parse/usage ; 4 an instruction can't be encoded for netlink ;
     5 the kernel rejected the batch ; 6 committed but no kernel ack (timeout).

   Options:
     --table T        restrict to table T (default: all parsed tables)
     --chain C        restrict rule emission to chain C (default: all chains)
     --family F       override the nfgen address family (ip|ip6|inet|arp|bridge|
                      netdev) used for `send` (default: the parsed table family)
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

let usage_line =
  "usage: " ^ prog ^ " {compile|optimize|send} [FILE.nft | -] \
   [--table T] [--chain C] [--family F] [--no-optimize] [--commit]\n"

(* a USAGE ERROR: goes to stderr, exit 2 (the conventional "misuse" code). *)
let usage () = prerr_string usage_line; exit 2

(* an EXPLICIT --help request: success, so print the full help to stdout and
   exit 0 (a caller that asked for help got what it asked for). *)
let help () =
  print_string usage_line;
  print_string
    "\ncommands:\n\
    \  compile   parse -> compile_chain -> netlink-style bytecode text\n\
    \  optimize  parse -> optimize_table_uncond -> compile -> bytecode text\n\
    \  send      parse -> (optimize ->) compile -> netlink batch to the kernel\n\
    \            (dry run unless --commit is given)\n\
     \noptions:\n\
    \  --table T       restrict to table T\n\
    \  --chain C       restrict rule emission to chain C\n\
    \  --family F      override nfgen family (ip|ip6|inet|arp|bridge|netdev)\n\
    \  --no-optimize   for send: compile without the optimizer\n\
    \  --commit        for send: actually transmit (default is a dry run)\n\
    \  -h, --help      this message\n\
     \nexit codes: 0 ok; 1 parse/usage/IO; 2 CLI misuse; 4 unencodable for\n\
     netlink; 5 kernel rejected the batch; 6 committed but no kernel ack.\n";
  exit 0

(* read the whole ruleset text from a file path, or stdin for "-"/absent.
   Any filesystem error (missing file, a directory, a permission problem, a
   read error) is reported cleanly and exits 1 — never an uncaught Sys_error
   stack trace (which would look like a compiler crash to the caller). *)
let read_input arg =
  match arg with
  | Some "-" | None ->
      let buf = Buffer.create 4096 in
      (try while true do Buffer.add_channel buf stdin 4096 done with End_of_file -> ());
      Buffer.contents buf
  | Some path ->
      (* reject a directory up front: open_in_bin on a dir succeeds on Linux but
         in_channel_length/really_input_string then raise a confusing
         Sys_error("Invalid argument"). *)
      (if (try Sys.is_directory path with Sys_error _ -> false) then
         (prerr_string (prog ^ ": " ^ path ^ ": is a directory\n"); exit 1));
      let ic =
        try open_in_bin path
        with Sys_error msg -> prerr_string (prog ^ ": " ^ msg ^ "\n"); exit 1 in
      (try
         let n = in_channel_length ic in
         let s = really_input_string ic n in
         close_in ic; s
       with Sys_error msg ->
         (try close_in_noerr ic with _ -> ());
         prerr_string (prog ^ ": " ^ msg ^ "\n"); exit 1)

(* run the FULL verified consolidation pipeline (Optimize_Uncond.optimize_table_uncond),
   returning the synthesised set/map declarations + the rewritten chain *)
let optimize_table (c : Syntax.chain) : Semantics.set_decls * Syntax.chain =
  let (nd, c') = Optimize_Uncond.optimize_table_uncond c in
  (snd nd, c')

(* base-chain policy verdict -> NFTA_CHAIN_POLICY (NF_ACCEPT=1 / NF_DROP=0) *)
let policy_code = function Verdict.Drop -> 0 | _ -> 1

(* the named sets/maps/vmaps a compiled program references, in lookup order *)
let referenced_sets (prog : Bytecode.program) : string list =
  L.concat_map
    (fun rp ->
      L.filter_map
        (function
          | Bytecode.ILookup (_, n, _) | Bytecode.IVmap (_, n)
          | Bytecode.ILookupVal (_, n, _) | Bytecode.ILookupValBr (_, n, _) -> Some n
          | _ -> None)
        rp)
    prog

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
        let is_base cn = L.exists (fun (n, _ctype, _hook, _prio) -> n = cn) hooks in
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
      (* a genuine interval element (lo<>hi, e.g. a merged range/prefix) is shown as
         `lo-hi`; a point element (lo=hi) as just `lo` — mirroring nft's dump of an
         NFT_SET_INTERVAL anonymous set. *)
      let pts = String.concat ", "
          (L.map (fun (lo, hi) ->
             if lo = hi then Codec.render_value lo
             else Codec.render_value lo ^ "-" ^ Codec.render_value hi) elems) in
      Buffer.add_string buf (Printf.sprintf "  set %s = { %s }\n" nm pts))
    d.Semantics.sd_sets;
  let render_vd = function
    | Verdict.Accept -> "accept" | Verdict.Drop -> "drop"
    | Verdict.Continue -> "continue" | Verdict.Reject _ -> "reject"
    | Verdict.Queue _ -> "queue" | Verdict.Return -> "return"
    | Verdict.Jump n -> "jump " ^ n | Verdict.Goto n -> "goto " ^ n in
  L.iter
    (fun (nm, entries) ->
      let pts = String.concat ", "
          (L.map (fun ((lo, hi), w) ->
             let k = if lo = hi then Codec.render_value lo
                     else Codec.render_value lo ^ "-" ^ Codec.render_value hi in
             k ^ " : " ^ render_vd w) entries) in
      Buffer.add_string buf (Printf.sprintf "  map %s = { %s }\n" nm pts))
    d.Semantics.sd_vmaps;
  Buffer.contents buf

let () =
  let args = Stdlib.Array.to_list Sys.argv in
  match args with
  | _ :: ("-h" | "--help") :: _ -> help ()
  | [_] -> usage ()
  | _ :: cmd :: rest ->
      let file = ref None and table = ref None and chain = ref None in
      let no_opt = ref false and commit = ref false and family = ref None in
      let rec go = function
        | [] -> ()
        | "--table" :: t :: r -> table := Some t; go r
        | "--chain" :: c :: r -> chain := Some c; go r
        | "--family" :: f :: r -> family := Some f; go r
        | "--no-optimize" :: r -> no_opt := true; go r
        | "--commit" :: r -> commit := true; go r
        | ("-h" | "--help") :: _ -> help ()
        (* a value-taking option given as the LAST token has no argument: report
           that specifically rather than the misleading "unknown option". *)
        | (("--table" | "--chain" | "--family") as opt) :: [] ->
            prerr_string (prog ^ ": option " ^ opt ^ " requires an argument\n"); usage ()
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
      let need_chains () =
        if chains = [] then (prerr_string (prog ^ ": no matching base chain\n"); exit 1) in
      (match cmd with
       | "compile" ->
           need_chains ();
           L.iter
             (fun (t, cn, c) ->
               print_string (render_chain ~table:t ~chain:cn (Compile.compile_chain c)))
             chains
       | "optimize" ->
           need_chains ();
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
           (* Build ONE atomic NFNL batch for the whole (selected) ruleset:
              NEWTABLE, NEWCHAIN (every chain, so jump targets exist), NEWSET +
              NEWSETELEM (each set/map a rule references), then NEWRULE per rule.
              The rule expressions are the verified Compile.compile_chain output;
              the table/chain/set framing is the parsed/optimizer structure. *)
           let want_table tn = match !table with None -> true | Some t -> t = tn in
           let want_chain cn = match !chain with None -> true | Some c -> c = cn in
           let sel_tables =
             L.filter (fun (_f, tn, _) -> want_table tn) parsed.Nft_lower.p_tables in
           if sel_tables = [] then
             (prerr_string (prog ^ ": no matching table\n"); exit 1);
           let next_id = let c = ref 0 in fun () -> incr c; !c in
           let msgs = ref [] in
           let add m = msgs := m :: !msgs in
           (try
              L.iter
                (fun (fam_str, tname, tchains) ->
                  let fam = match !family with
                    | Some f -> Nl_send.nfproto_of_family f
                    | None -> Nl_send.nfproto_of_family fam_str in
                  add (Nl_send.msg_table ~family:fam ~table:tname);
                  let hooks =
                    match L.find_opt (fun (_f, n, _h) -> n = tname) parsed.Nft_lower.p_hooks with
                    | Some (_f, _n, hs) -> hs | None -> [] in
                  let base_of cn =
                    match L.find_opt (fun (n, _c, _h, _p) -> n = cn) hooks with
                    | Some (_n, ctype, hook, prio) ->
                        Some (ctype, Nl_send.hooknum_of_name hook, prio)
                    | None -> None in
                  (* every chain is created (jump targets included) *)
                  L.iter
                    (fun (cn, ch) ->
                      let base = base_of cn in
                      let policy = match base with
                        | Some _ -> Some (policy_code ch.Syntax.c_policy) | None -> None in
                      add (Nl_send.msg_chain ~family:fam ~table:tname ~name:cn ~base ~policy))
                    tchains;
                  (* set/map declarations: parsed named ones + optimizer-synthesised *)
                  let synth_sets = ref [] and synth_vmaps = ref [] in
                  let seen = Hashtbl.create 16 in
                  (* the optimizer's synthesised sets are named `__mapN` / `__setN`;
                     those are anonymous+constant (nft renders them folded inline
                     into the rule, and — unlike a plain named set — decodes string
                     key types like `ifname` for display).  A user-declared named
                     set keeps its name and is neither. *)
                  let anon_flags name =
                    if String.length name >= 2 && name.[0] = '_' && name.[1] = '_'
                    then Nl_send.nft_set_anonymous lor Nl_send.nft_set_constant else 0 in
                  let emit_set ~key_fields name =
                    if not (Hashtbl.mem seen name) then begin
                      Hashtbl.add seen name ();
                      let find l1 l2 = match L.assoc_opt name l1 with
                        | Some x -> Some x | None -> L.assoc_opt name l2 in
                      match find !synth_vmaps parsed.Nft_lower.p_vmaps with
                      | Some entries ->
                          let elems = L.map
                            (fun ((lo, _hi), v) ->
                              { Nl_send.ek = Nl_send.pad_concat_key key_fields lo;
                                ed = Some (Nl_send.EVerdict v) })
                            entries in
                          let klen = match elems with e :: _ -> L.length e.Nl_send.ek | [] -> 0 in
                          let concat = L.length key_fields > 1 in
                          let flags = Nl_send.nft_set_map lor anon_flags name
                                      lor (if concat then Nl_send.nft_set_concat else 0) in
                          let id = next_id () in
                          add (Nl_send.msg_set ~family:fam ~table:tname ~name ~set_id:id
                                 ~flags ~klen ~key_fields
                                 ~dtype:(Some Nl_send.nft_data_verdict) ~dlen:None);
                          if elems <> [] then
                            add (Nl_send.msg_setelems ~family:fam ~table:tname ~set:name ~set_id:id ~key_fields elems)
                      | None ->
                          (match find !synth_sets parsed.Nft_lower.p_sets with
                           | Some els ->
                               let elems = L.map
                                 (fun (lo, hi) ->
                                   if lo <> hi then
                                     raise (Nl_send.Unsupported
                                       ("interval element in set " ^ name ^
                                        " (range/prefix set elements not yet encoded)"));
                                   { Nl_send.ek = Nl_send.pad_concat_key key_fields lo; ed = None })
                                 els in
                               let klen = match elems with e :: _ -> L.length e.Nl_send.ek | [] -> 0 in
                               let flags = anon_flags name
                                           lor (if L.length key_fields > 1 then Nl_send.nft_set_concat else 0) in
                               let id = next_id () in
                               add (Nl_send.msg_set ~family:fam ~table:tname ~name ~set_id:id
                                      ~flags ~klen ~key_fields ~dtype:None ~dlen:None);
                               if elems <> [] then
                                 add (Nl_send.msg_setelems ~family:fam ~table:tname ~set:name ~set_id:id ~key_fields elems)
                           | None ->
                               raise (Nl_send.Unsupported ("set/map referenced but not declared: " ^ name)))
                    end in
                  L.iter
                    (fun (cn, ch) ->
                      if want_chain cn then begin
                        let ch' = if !no_opt then ch
                          else (let (d, c') = optimize_table ch in
                                synth_sets := !synth_sets @ d.Semantics.sd_sets;
                                synth_vmaps := !synth_vmaps @ d.Semantics.sd_vmaps;
                                c') in
                        let prog = Compile.compile_chain ch' in
                        let kf = Nl_send.set_key_fields prog in
                        L.iter
                          (fun n ->
                            let key_fields = match L.assoc_opt n kf with Some f -> f | None -> [] in
                            emit_set ~key_fields n)
                          (referenced_sets prog);
                        L.iter (fun rp -> add (Nl_send.msg_rule ~family:fam ~table:tname ~chain:cn rp)) prog
                      end)
                    tchains)
                sel_tables;
              let desc =
                Printf.sprintf "%d table(s), %d message(s)"
                  (L.length sel_tables) (L.length !msgs) in
              Nl_send.send_batch ~commit:!commit ~desc (L.rev !msgs)
            with Nl_send.Unsupported msg ->
              prerr_string (prog ^ ": cannot encode for netlink: " ^ msg ^ "\n"); exit 4)
       | _ -> usage ())
  | _ -> usage ()
