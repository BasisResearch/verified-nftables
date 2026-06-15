(* Differential test against the upstream nftables corpus (tests/py/*.t.payload).
   For each rule-block of bytecode in the corpus we:
     1. parse the `[ ... ]` expression lines into our Bytecode AST;
     2. if every instruction is in our supported subset and every load maps to a
        named DSL field, reconstruct the DSL rule, recompile it through the
        *verified* compiler (Compile.compile_rule), re-render, and check the
        output is byte-identical to the corpus;
     3. otherwise classify *why* it is out of scope (unsupported instruction,
        unmodelled field, non-eq/neq cmp, reg!=1, non-accept/drop verdict, ...).
   A MISMATCH (supported but re-render differs) would expose a real bug in our
   bytecode model or compiler; coverage = supported-and-identical / total. *)

module List = Stdlib.List       (* shadow the extracted List unit *)
module String = Stdlib.String   (* shadow the extracted (empty) String unit *)

(* ---------- name tables (untrusted; checked by the round-trip) ---------- *)

let metas = [
  "l4proto", Packet.MKl4proto; "nfproto", Packet.MKnfproto;
  "protocol", Packet.MKprotocol; "mark", Packet.MKmark;
  "iif", Packet.MKiif; "oif", Packet.MKoif;
  "iiftype", Packet.MKiiftype; "oiftype", Packet.MKoiftype;
  "iifname", Packet.MKiifname; "oifname", Packet.MKoifname;
  "len", Packet.MKlen; "pkttype", Packet.MKpkttype; "cpu", Packet.MKcpu;
  "skuid", Packet.MKskuid; "skgid", Packet.MKskgid; "priority", Packet.MKpriority;
]
let meta_of_name n = try Some (List.assoc n metas) with Not_found -> None
let name_of_meta k =
  let r = ref "?" in List.iter (fun (n,k') -> if k'=k then r:=n) metas; !r

let cts = [
  "state", Packet.CKstate; "status", Packet.CKstatus; "mark", Packet.CKmark;
  "direction", Packet.CKdirection; "expiration", Packet.CKexpiration;
  "id", Packet.CKid;
]
let ct_of_name n = try Some (List.assoc n cts) with Not_found -> None
let name_of_ct k =
  let r = ref "?" in List.iter (fun (n,k') -> if k'=k then r:=n) cts; !r

let ehproto_of_name = function
  | "ipv6" -> Some Packet.EPipv6 | "tcpopt" -> Some Packet.EPtcpopt | _ -> None
let name_of_ehproto = function
  | Packet.EPipv6 -> "ipv6" | Packet.EPtcpopt -> "tcpopt"

let base_of_name = function
  | "link" -> Some Packet.PLink | "network" -> Some Packet.PNetwork
  | "transport" -> Some Packet.PTransport
  | "inner" -> Some Packet.PInner | "tunnel" -> Some Packet.PTunnel | _ -> None
let name_of_base = function
  | Packet.PLink -> "link" | Packet.PNetwork -> "network"
  | Packet.PTransport -> "transport"
  | Packet.PInner -> "inner" | Packet.PTunnel -> "tunnel"

(* descriptor (loaddesc) -> a string key, for the reverse map and equality *)
let key_of_load (ld : Syntax.loaddesc) = match ld with
  | Syntax.LMeta k -> "m:" ^ name_of_meta k
  | Syntax.LCt k -> "c:" ^ name_of_ct k
  | Syntax.LExthdr (ep,h,o,l) ->
      Printf.sprintf "x:%s:%d:%d:%d" (name_of_ehproto ep) h o l
  | Syntax.LPayload (b,o,l) -> Printf.sprintf "p:%s:%d:%d" (name_of_base b) o l

(* reverse map: descriptor key -> field, built from the verified field table *)
let field_of_key : (string, Syntax.field) Hashtbl.t = Hashtbl.create 64
let () = List.iter
  (fun f -> Hashtbl.replace field_of_key (key_of_load (Syntax.field_load f)) f)
  Syntax.all_fields

(* resolve a descriptor key to a DSL field: parametric exthdr keys are built
   directly; everything else is a fixed named field from the reverse map. *)
let field_of_key_str key : Syntax.field option =
  match String.split_on_char ':' key with
  | ["x"; proto; h; o; l] ->
      (match ehproto_of_name proto with
       | Some ep -> Some (Syntax.FExthdr (ep, int_of_string h,
                                          int_of_string o, int_of_string l))
       | None -> None)
  | ["p"; base; o; l] ->
      (match base_of_name base with
       | Some b -> Some (Syntax.FPayload (b, int_of_string o, int_of_string l))
       | None -> None)
  | _ -> (try Some (Hashtbl.find field_of_key key) with Not_found -> None)

(* ---------- corpus value <-> bytes ---------- *)

(* "0x000f540c 0x1104" -> byte list [0x00;0x0f;0x54;0x0c;0x11;0x04] (big-endian
   per space-separated word). *)
let bytes_of_hexwords (words : string list) : int list =
  List.concat_map (fun w ->
    let h = if String.length w >= 2 && w.[0]='0' && w.[1]='x'
            then String.sub w 2 (String.length w - 2) else w in
    let nb = String.length h / 2 in
    List.init nb (fun i -> int_of_string ("0x" ^ String.sub h (2*i) 2))
  ) words

(* byte list -> corpus rendering: 4-byte big-endian chunks, last may be short *)
let render_value (d : int list) : string =
  let a = Array.of_list d in let n = Array.length a in
  let buf = Buffer.create 16 in let i = ref 0 in
  while !i < n do
    let len = min 4 (n - !i) in
    let v = ref 0 in
    for k = 0 to len-1 do v := (!v lsl 8) lor a.(!i+k) done;
    if !i > 0 then Buffer.add_char buf ' ';
    Buffer.add_string buf (Printf.sprintf "0x%0*x" (2*len) !v);
    i := !i + len
  done;
  Buffer.contents buf

(* ---------- render our compiled instrs back to corpus text ---------- *)
let render_instr (i : Bytecode.instr) : string = match i with
  | Bytecode.IMetaLoad (k,r) ->
      Printf.sprintf "[ meta load %s => reg %d ]" (name_of_meta k) r
  | Bytecode.ICtLoad (k,r) ->
      Printf.sprintf "[ ct load %s => reg %d ]" (name_of_ct k) r
  | Bytecode.IExthdrLoad (ep,h,o,l,r) ->
      Printf.sprintf "[ exthdr load %s %db @ %d + %d => reg %d ]"
        (name_of_ehproto ep) l h o r
  | Bytecode.IPayloadLoad (b,o,l,r) ->
      Printf.sprintf "[ payload load %db @ %s header + %d => reg %d ]"
        l (name_of_base b) o r
  | Bytecode.ICmp (op,r,v) ->
      let opn = (match op with Bytecode.CEq -> "eq" | Bytecode.CNe -> "neq") in
      Printf.sprintf "[ cmp %s reg %d %s ]" opn r (render_value v)
  | Bytecode.IRange (op,r,lo,hi) ->
      let opn = (match op with Bytecode.CEq -> "eq" | Bytecode.CNe -> "neq") in
      Printf.sprintf "[ range %s reg %d %s %s ]" opn r (render_value lo) (render_value hi)
  | Bytecode.IBitwise (d,s,mask,xor) ->
      Printf.sprintf "[ bitwise reg %d = ( reg %d & %s ) ^ %s ]"
        d s (render_value mask) (render_value xor)
  | Bytecode.ILookup (s,name,neg,_) ->
      if neg then Printf.sprintf "[ lookup reg %d set %s 0x1 ]" s name
      else Printf.sprintf "[ lookup reg %d set %s ]" s name
  | Bytecode.ICounter (p,b) -> Printf.sprintf "[ counter pkts %d bytes %d ]" p b
  | Bytecode.INotrack -> "[ notrack ]"
  | Bytecode.ILog lv ->
      (match lv with None -> "[ log ]" | Some n -> Printf.sprintf "[ log level %d ]" n)
  | Bytecode.IReject (t,c) -> Printf.sprintf "[ reject type %d code %d ]" t c
  | Bytecode.IQueue (lo,hi,byp,fan) ->
      let nums = if lo=hi then string_of_int lo else Printf.sprintf "%d-%d" lo hi in
      "[ queue num " ^ nums ^ (if byp then " bypass" else "")
        ^ (if fan then " fanout" else "") ^ " ]"
  | Bytecode.IImmediate v ->
      let vn = (match v with Verdict.Accept->"accept"|Verdict.Drop->"drop"
                            |Verdict.Continue->"continue"|Verdict.Reject _->"reject") in
      Printf.sprintf "[ immediate reg 0 %s ]" vn

(* ---------- parse one corpus expression line ---------- *)
(* result of trying to interpret a block: either a reconstructed DSL rule, or a
   classification of why it is unsupported. *)
exception Unsupported of string

let toks_of_line line =
  (* strip, drop leading "[ " and trailing " ]" *)
  let s = String.trim line in
  let s = if String.length s>=2 && String.sub s 0 2 = "[ "
          then String.sub s 2 (String.length s - 2) else s in
  let s = if String.length s>=2 && String.sub s (String.length s-2) 2 = " ]"
          then String.sub s 0 (String.length s - 2) else s in
  String.split_on_char ' ' (String.trim s)
  |> List.filter (fun t -> t <> "")

(* a parsed instruction: a load (descriptor key, reg), a cmp, an immediate, or
   raise Unsupported "<reason>". *)
type pinst =
  | PLoad    of string * int                 (* descriptor key, dst reg *)
  | PCmp     of bool * int * int list         (* is_eq, src reg, value bytes *)
  | PRange   of bool * int * string list      (* is_eq, src reg, lo++hi hexwords *)
  | PBitwise of int * int * int list * int list  (* dst, src, mask, xor *)
  | PLookup  of int * string * bool              (* src reg, set name, inverted *)
  | PCounter of int * int
  | PNotrack
  | PLog     of int option
  | PImm     of Verdict.verdict

let rec take_until tok = function
  | [] -> ([], [])
  | x :: xs -> if x = tok then ([], xs)
               else let (a,b) = take_until tok xs in (x::a, b)

let parse_line line : pinst =
  match toks_of_line line with
  | "payload"::"load"::lb::"@"::base::"header"::"+"::off::"=>"::"reg"::r::[] ->
      let len = int_of_string (String.sub lb 0 (String.length lb - 1)) in
      let b = match base_of_name base with Some b -> b
              | None -> raise (Unsupported ("base:"^base)) in
      PLoad (key_of_load (Syntax.LPayload (b, int_of_string off, len)),
             int_of_string r)
  | "meta"::"load"::name::"=>"::"reg"::r::[] ->
      (match meta_of_name name with
       | Some k -> PLoad (key_of_load (Syntax.LMeta k), int_of_string r)
       | None -> raise (Unsupported ("meta:"^name)))
  | "ct"::"load"::name::"=>"::"reg"::r::[] ->
      (match ct_of_name name with
       | Some k -> PLoad (key_of_load (Syntax.LCt k), int_of_string r)
       | None -> raise (Unsupported ("ct:"^name)))
  | "exthdr"::"load"::proto::lb::"@"::htype::"+"::off::"=>"::"reg"::r::[] ->
      let len = int_of_string (String.sub lb 0 (String.length lb - 1)) in
      (match ehproto_of_name proto with
       | Some _ -> PLoad (Printf.sprintf "x:%s:%s:%s:%d" proto htype off len,
                          int_of_string r)
       | None -> raise (Unsupported ("exthdrproto:"^proto)))
  | "cmp"::op::"reg"::r::rest ->
      let iseq = match op with "eq"->true | "neq"->false
                 | _ -> raise (Unsupported ("cmpop:"^op)) in
      PCmp (iseq, int_of_string r, bytes_of_hexwords rest)
  | "range"::op::"reg"::r::rest ->
      let iseq = match op with "eq"->true | "neq"->false
                 | _ -> raise (Unsupported ("rangeop:"^op)) in
      PRange (iseq, int_of_string r, rest)
  | "bitwise"::"reg"::dst::"="::"("::"reg"::src::"&"::rest ->
      let (mask_w, after) = take_until ")" rest in
      let xor_w = (match after with "^"::xs -> xs
                   | _ -> raise (Unsupported "bitwise:noxor")) in
      PBitwise (int_of_string dst, int_of_string src,
                bytes_of_hexwords mask_w, bytes_of_hexwords xor_w)
  | "bitwise"::_ -> raise (Unsupported "bitwise:form")
  | "lookup"::"reg"::r::"set"::name::rest ->
      (match rest with
       | [] -> PLookup (int_of_string r, name, false)
       | "dreg"::_ -> raise (Unsupported "lookup:map")
       | [h] when String.length h >= 2 && String.sub h 0 2 = "0x" ->
           PLookup (int_of_string r, name, true)
       | _ -> raise (Unsupported "lookup:flags"))
  | "immediate"::"reg"::r::rest ->
      if r <> "0" then raise (Unsupported "imm:datareg");
      (match rest with
       | ["accept"] -> PImm Verdict.Accept
       | ["drop"]   -> PImm Verdict.Drop
       | v::_       -> raise (Unsupported ("verdict:"^v))
       | []         -> raise (Unsupported "verdict:empty"))
  | ["counter"; "pkts"; p; "bytes"; b] -> PCounter (int_of_string p, int_of_string b)
  | ["notrack"] -> PNotrack
  | "log"::rest ->
      (match rest with
       | [] -> PLog None
       | ["level"; n] -> PLog (Some (int_of_string n))
       | _ -> raise (Unsupported "log:opts"))
  | ["reject"; "type"; t; "code"; c] ->
      PImm (Verdict.Reject (int_of_string t, int_of_string c))
  | "queue"::"num"::spec::flags ->
      let (lo,hi) = (match String.split_on_char '-' spec with
        | [a] -> (int_of_string a, int_of_string a)
        | [a;b] -> (int_of_string a, int_of_string b)
        | _ -> raise (Unsupported "queue:spec")) in
      if List.for_all (fun f -> f="bypass" || f="fanout") flags then
        PImm (Verdict.Queue (lo, hi, List.mem "bypass" flags, List.mem "fanout" flags))
      else raise (Unsupported "queue:flags")
  | "queue"::_ -> raise (Unsupported "queue:sreg")
  | tok::_ -> raise (Unsupported ("instr:"^tok))
  | [] -> raise (Unsupported "empty")

(* fold a block into a DSL rule: (load;test)* then verdict-neutral statements
   then a verdict. *)
let rule_of_block (lines : string list) : Syntax.rule =
  let mk matches stmts v : Syntax.rule =
    { Syntax.r_matches = List.rev matches; r_stmts = List.rev stmts; r_verdict = v } in
  let rec go matches stmts = function
    | [] -> mk matches stmts Verdict.Continue   (* match-only rule: falls through *)
    | l1 :: rest ->
      (match parse_line l1 with
       | PImm v ->
           if rest <> [] then raise (Unsupported "trailing-after-verdict");
           mk matches stmts v
       | PCounter (p,b) -> go matches (Syntax.SCounter (p,b) :: stmts) rest
       | PNotrack -> go matches (Syntax.SNotrack :: stmts) rest
       | PLog l -> go matches (Syntax.SLog l :: stmts) rest
       | PLoad (key, lreg) ->
           if stmts <> [] then raise (Unsupported "load-after-stmt");
           if lreg <> 1 then raise (Unsupported "reg!=1");
           let field_of key =
             match field_of_key_str key with Some f -> f
             | None -> raise (Unsupported ("field:"^key)) in
           let acc = matches in
           (match rest with
            | l2 :: rest2 ->
              (match parse_line l2 with
               | PCmp (iseq, creg, v) ->
                   if creg <> 1 then raise (Unsupported "reg!=1");
                   let f = field_of key in
                   let m = if iseq then Syntax.MEq (f, v) else Syntax.MNeq (f, v) in
                   go (m :: acc) stmts rest2
               | PRange (iseq, creg, words) ->
                   if creg <> 1 then raise (Unsupported "reg!=1");
                   let n = List.length words in
                   if n land 1 <> 0 then raise (Unsupported "range-odd-words");
                   let lo = bytes_of_hexwords (List.filteri (fun i _ -> i < n/2) words)
                   and hi = bytes_of_hexwords (List.filteri (fun i _ -> i >= n/2) words) in
                   let f = field_of key in
                   go (Syntax.MRange (f, not iseq, lo, hi) :: acc) stmts rest2
               | PBitwise (bd, bs, mask, xor) ->
                   if bd <> 1 || bs <> 1 then raise (Unsupported "reg!=1");
                   (match rest2 with
                    | l3 :: rest3 ->
                      (match parse_line l3 with
                       | PCmp (iseq, creg, v) ->
                           if creg <> 1 then raise (Unsupported "reg!=1");
                           let f = field_of key in
                           go (Syntax.MMasked (f, not iseq, mask, xor, v) :: acc) stmts rest3
                       | _ -> raise (Unsupported "bitwise-not-followed-by-cmp"))
                    | [] -> raise (Unsupported "dangling-bitwise"))
               | PLookup (lr, name, neg) ->
                   if lr <> 1 then raise (Unsupported "reg!=1");
                   let f = field_of key in
                   go (Syntax.MSet (f, neg, name, []) :: acc) stmts rest2
               | _ -> raise (Unsupported "load-not-followed-by-cmp"))
            | [] -> raise (Unsupported "dangling-load"))
       | _ -> raise (Unsupported "test-without-load"))
  in go [] [] lines

(* ---------- block extraction: maximal runs of `[ ... ]` lines ---------- *)
let blocks_of_file path : string list list =
  let ic = open_in path in
  let blocks = ref [] and cur = ref [] in
  let flush () = if !cur <> [] then (blocks := List.rev !cur :: !blocks; cur := []) in
  (try while true do
     let line = input_line ic in
     if String.length (String.trim line) >= 1 && (String.trim line).[0] = '['
     then cur := line :: !cur
     else flush ()
   done with End_of_file -> ());
  flush (); close_in ic; List.rev !blocks

(* ---------- main ---------- *)
let () =
  let files = Array.to_list Sys.argv |> List.tl in
  let total = ref 0 and pass = ref 0 in
  let cats : (string,int) Hashtbl.t = Hashtbl.create 64 in
  let bump c = Hashtbl.replace cats c (1 + (try Hashtbl.find cats c with Not_found -> 0)) in
  let mismatches = ref [] in
  List.iter (fun path ->
    List.iter (fun block ->
      incr total;
      match (try `R (rule_of_block block) with Unsupported r -> `U r) with
      | `U reason -> bump ("unsupported:" ^ reason)
      | `R rule ->
          let compiled = Compile.compile_rule rule in
          let ours = List.map render_instr compiled in
          let theirs = List.map (fun l -> String.concat " " (toks_of_line l)
                                          |> fun s -> "[ " ^ s ^ " ]") block in
          if ours = theirs then incr pass
          else (bump "MISMATCH";
                if List.length !mismatches < 8 then
                  mismatches := (theirs, ours) :: !mismatches)
    ) (blocks_of_file path)
  ) files;
  Printf.printf "\n=== nftables corpus round-trip (verified compiler) ===\n";
  Printf.printf "rule-blocks: %d   round-tripped: %d   (%.1f%%)\n\n"
    !total !pass (100. *. float !pass /. float (max 1 !total));
  let lst = Hashtbl.fold (fun k v a -> (k,v)::a) cats [] in
  let lst = List.sort (fun (_,a) (_,b) -> compare b a) lst in
  Printf.printf "out-of-scope / failure breakdown:\n";
  List.iter (fun (k,v) -> Printf.printf "  %6d  %s\n" v k) lst;
  List.iter (fun (t,o) ->
    Printf.printf "\nMISMATCH:\n  corpus: %s\n  ours:   %s\n"
      (String.concat " | " t) (String.concat " | " o)) !mismatches;
  (* A mismatch means our verified compiler disagreed with upstream on a rule we
     claim to support: a real bug. Fail the build. *)
  let mm = try Hashtbl.find cats "MISMATCH" with Not_found -> 0 in
  if mm > 0 then (Printf.printf "\nFAIL: %d mismatch(es)\n" mm; exit 1)
  else Printf.printf "\nOK: %d/%d round-tripped, 0 mismatches\n" !pass !total
