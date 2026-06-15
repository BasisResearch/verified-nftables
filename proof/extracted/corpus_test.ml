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
  "cgroup", Packet.MKcgroup; "day", Packet.MKday; "hour", Packet.MKhour;
  "iifgroup", Packet.MKiifgroup; "oifgroup", Packet.MKoifgroup;
  "prandom", Packet.MKprandom; "rtclassid", Packet.MKrtclassid;
  "sdif", Packet.MKsdif; "sdifname", Packet.MKsdifname; "secpath", Packet.MKsecpath;
  "time", Packet.MKtime; "bri_iifname", Packet.MKbri_iifname;
  "bri_oifname", Packet.MKbri_oifname; "bri_iifpvid", Packet.MKbri_iifpvid;
  "bri_iifvproto", Packet.MKbri_iifvproto; "ibrhwaddr", Packet.MKibrhwaddr;
]
let meta_of_name n = try Some (List.assoc n metas) with Not_found -> None
let name_of_meta k =
  let r = ref "?" in List.iter (fun (n,k') -> if k'=k then r:=n) metas; !r

let rts = [
  "classid", Packet.RKclassid; "nexthop4", Packet.RKnexthop4;
  "nexthop6", Packet.RKnexthop6; "tcpmss", Packet.RKtcpmss;
  "mtu", Packet.RKmtu; "ipsec", Packet.RKipsec;
]
let rt_of_name n = try Some (List.assoc n rts) with Not_found -> None
let name_of_rt k = let r = ref "?" in List.iter (fun (n,k') -> if k'=k then r:=n) rts; !r

let socks = [
  "transparent", Packet.SKtransparent; "mark", Packet.SKmark;
  "wildcard", Packet.SKwildcard; "cgroupv2", Packet.SKcgroupv2;
]
let sock_of_name n = try Some (List.assoc n socks) with Not_found -> None
let name_of_sock k = let r = ref "?" in List.iter (fun (n,k') -> if k'=k then r:=n) socks; !r

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
  | Syntax.LRt k -> "r:" ^ name_of_rt k
  | Syntax.LSocket k -> "s:" ^ name_of_sock k
  | Syntax.LExthdr (ep,h,o,l) ->
      Printf.sprintf "x:%s:%d:%d:%d" (name_of_ehproto ep) h o l
  | Syntax.LNumgen s ->
      Printf.sprintf "ng:%b:%d:%d" s.Packet.ng_random s.Packet.ng_mod s.Packet.ng_offset
  | Syntax.LOsf -> "osf:"
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
  | ["m"; n] -> (match meta_of_name n with Some k -> Some (Syntax.FMetaGen k) | None -> None)
  | ["r"; n] -> (match rt_of_name n with Some k -> Some (Syntax.FRtGen k) | None -> None)
  | ["s"; n] -> (match sock_of_name n with Some k -> Some (Syntax.FSocketGen k) | None -> None)
  | ["ng"; rnd; m; off] ->
      Some (Syntax.FNumgen { Packet.ng_random = bool_of_string rnd;
                             ng_mod = int_of_string m; ng_offset = int_of_string off })
  | ["osf"; ""] -> Some Syntax.FOsf
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
  | Bytecode.IRtLoad (k,r) ->
      Printf.sprintf "[ rt load %s => reg %d ]" (name_of_rt k) r
  | Bytecode.ISocketLoad (k,r) ->
      Printf.sprintf "[ socket load %s => reg %d ]" (name_of_sock k) r
  | Bytecode.IExthdrLoad (ep,h,o,l,r) ->
      Printf.sprintf "[ exthdr load %s %db @ %d + %d => reg %d ]"
        (name_of_ehproto ep) l h o r
  | Bytecode.INumgen (s,r) ->
      let off = if s.Packet.ng_offset > 0 then Printf.sprintf " offset %d" s.Packet.ng_offset else "" in
      Printf.sprintf "[ numgen reg %d = %s mod %d%s ]"
        r (if s.Packet.ng_random then "random" else "inc") s.Packet.ng_mod off
  | Bytecode.IOsf r -> Printf.sprintf "[ osf dreg %d ]" r
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
  | Bytecode.IBitShift (d,s,shl,amt) ->
      Printf.sprintf "[ bitwise reg %d = ( reg %d %s 0x%08x ) ]"
        d s (if shl then "<<" else ">>") amt
  | Bytecode.IByteorder (d,s,hton,sz,len) ->
      Printf.sprintf "[ byteorder reg %d = %s(reg %d, %d, %d) ]"
        d (if hton then "hton" else "ntoh") s sz len
  | Bytecode.ILookup (s,name,neg,_) ->
      if neg then Printf.sprintf "[ lookup reg %d set %s 0x1 ]" s name
      else Printf.sprintf "[ lookup reg %d set %s ]" s name
  | Bytecode.ILimit s ->
      let u = (match s.Packet.ls_unit with
               | 0->"second" | 1->"minute" | 2->"hour" | 3->"day" | _->"week") in
      Printf.sprintf "[ limit rate %d/%s burst %d type %s flags 0x%x ]"
        s.Packet.ls_rate u s.Packet.ls_burst
        (if s.Packet.ls_bytes then "bytes" else "packets") s.Packet.ls_flags
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
  | PShift   of int * int * bool * int            (* dst, src, is_left, amount *)
  | PByteorder of int * int * bool * int * int    (* dst, src, hton, size, len *)
  | PLookup  of int * string * bool              (* src reg, set name, inverted *)
  | PCounter of int * int
  | PNotrack
  | PLimit   of Packet.limit_spec
  | PLog     of int option
  | PImm     of Verdict.verdict

let rec take_until tok = function
  | [] -> ([], [])
  | x :: xs -> if x = tok then ([], xs)
               else let (a,b) = take_until tok xs in (x::a, b)

(* int from a token possibly carrying stray punctuation, e.g. "2," or "1)" *)
let only_digits s =
  let b = Buffer.create 8 in
  String.iter (fun c -> if c >= '0' && c <= '9' then Buffer.add_char b c) s;
  int_of_string (Buffer.contents b)

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
  | "rt"::"load"::name::"=>"::"reg"::r::[] ->
      (match rt_of_name name with
       | Some k -> PLoad (key_of_load (Syntax.LRt k), int_of_string r)
       | None -> raise (Unsupported ("rt:"^name)))
  | "socket"::"load"::name::"=>"::"reg"::r::[] ->
      (match sock_of_name name with
       | Some k -> PLoad (key_of_load (Syntax.LSocket k), int_of_string r)
       | None -> raise (Unsupported ("socket:"^name)))
  | "numgen"::"reg"::n::"="::mode::"mod"::m::rest ->
      let off = (match rest with [] -> 0 | ["offset"; o] -> int_of_string o
                 | _ -> raise (Unsupported "numgen:opts")) in
      PLoad (key_of_load (Syntax.LNumgen
        { Packet.ng_random = (mode = "random"); ng_mod = int_of_string m;
          ng_offset = off }), int_of_string n)
  | "osf"::"dreg"::n::[] -> PLoad (key_of_load Syntax.LOsf, int_of_string n)
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
  | "bitwise"::"reg"::dst::"="::"("::"reg"::src::op::amt::")"::[]
    when op = ">>" || op = "<<" ->
      PShift (int_of_string dst, int_of_string src, op = "<<", int_of_string amt)
  | "bitwise"::_ -> raise (Unsupported "bitwise:form")
  | "byteorder"::"reg"::dst::"="::ftok::src::size::len::[] ->
      let hton = String.length ftok >= 4 && String.sub ftok 0 4 = "hton" in
      PByteorder (int_of_string dst, only_digits src, hton,
                  only_digits size, only_digits len)
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
  | ["limit"; "rate"; ru; "burst"; b; "type"; t; "flags"; fl] ->
      let (r,u) = (match String.split_on_char '/' ru with
        | [a;b] -> (int_of_string a, b) | _ -> raise (Unsupported "limit:rate")) in
      let unit_code = (match u with
        | "second"->0 | "minute"->1 | "hour"->2 | "day"->3 | "week"->4
        | _ -> raise (Unsupported ("limit:unit:"^u))) in
      PLimit { Packet.ls_rate = r; ls_unit = unit_code; ls_burst = int_of_string b;
               ls_bytes = (t = "bytes"); ls_flags = int_of_string fl }
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
       | PLimit spec ->
           if stmts <> [] then raise (Unsupported "limit-after-stmt");
           go (Syntax.MLimit spec :: matches) stmts rest
       | PLoad (key, lreg) ->
           if stmts <> [] then raise (Unsupported "load-after-stmt");
           if lreg <> 1 then raise (Unsupported "reg!=1");
           let f = (match field_of_key_str key with Some f -> f
                    | None -> raise (Unsupported ("field:"^key))) in
           (* collect a chain of register transforms, then a tester *)
           let rec collect ts = function
             | l :: more ->
               (match parse_line l with
                | PBitwise (1,1,mask,xor) -> collect (Syntax.TBitAnd (mask,xor) :: ts) more
                | PShift (1,1,shl,amt) -> collect (Syntax.TShift (shl,amt) :: ts) more
                | PByteorder (1,1,h,sz,ln) -> collect (Syntax.TByteorder (h,sz,ln) :: ts) more
                | PCmp (iseq, 1, v) ->
                    let tl = List.rev ts in
                    let m = (match tl with
                      | [] -> if iseq then Syntax.MEq (f,v) else Syntax.MNeq (f,v)
                      | _ -> Syntax.MTransform (f, tl, not iseq, v)) in
                    go (m :: matches) stmts more
                | PRange (iseq, 1, words) when ts = [] ->
                    let n = List.length words in
                    if n land 1 <> 0 then raise (Unsupported "range-odd-words");
                    let lo = bytes_of_hexwords (List.filteri (fun i _ -> i < n/2) words)
                    and hi = bytes_of_hexwords (List.filteri (fun i _ -> i >= n/2) words) in
                    go (Syntax.MRange (f, not iseq, lo, hi) :: matches) stmts more
                | PLookup (1, name, neg) when ts = [] ->
                    go (Syntax.MSet (f, neg, name, []) :: matches) stmts more
                | PRange _ -> raise (Unsupported "transform-then-range")
                | PLookup _ -> raise (Unsupported "transform-then-lookup")
                | PBitwise _ | PShift _ | PByteorder _ | PCmp _ ->
                    raise (Unsupported "reg!=1")
                | _ -> raise (Unsupported "load-not-followed-by-test"))
             | [] -> raise (Unsupported "dangling-load")
           in collect [] rest
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

(* ---------- independent validation of field_load against LIVE nft ----------
   The corpus round-trip cannot validate the name tables or named-field offsets
   (parse and render share them). Here we use live `nft --debug=netlink` as an
   INDEPENDENT oracle: for each named field we emit the corresponding nft rule,
   let the real nft lower it, and check that our field_load descriptor appears
   among the loads nft emitted. A wrong offset/name in field_load fails this. *)
let run_nft input =
  let tf = Filename.temp_file "nftv" ".nft" in
  let oc = open_out tf in output_string oc input; close_out oc;
  let ic = Unix.open_process_in
    (Printf.sprintf "unshare -rn nft --debug=netlink -f %s 2>/dev/null" (Filename.quote tf)) in
  let acc = ref [] in
  (try while true do acc := input_line ic :: !acc done with End_of_file -> ());
  ignore (Unix.close_process_in ic); (try Sys.remove tf with _ -> ());
  List.rev !acc

let load_keys_of lines =
  List.filter_map (fun l ->
    let t = String.trim l in
    if String.length t >= 1 && t.[0] = '[' then
      (try (match parse_line l with PLoad (key,_) -> Some key | _ -> None) with _ -> None)
    else None) lines

(* (family, nft match text, expected field) — exercises field_load offsets/names *)
let validate_pairs : (string * string * Syntax.field) list = [
  "ip",  "ip saddr 1.2.3.4",       Syntax.FIp4Saddr;
  "ip",  "ip daddr 1.2.3.4",       Syntax.FIp4Daddr;
  "ip",  "ip protocol tcp",        Syntax.FIp4Protocol;
  "ip",  "ip ttl 1",               Syntax.FIp4Ttl;
  "ip",  "ip length 100",          Syntax.FIp4Totlen;
  "ip",  "ip id 1",                Syntax.FIp4Id;
  "ip",  "tcp sport 80",           Syntax.FThSport;
  "ip",  "tcp dport 80",           Syntax.FThDport;
  "ip",  "tcp sequence 1",         Syntax.FTcpSeq;
  "ip",  "tcp flags syn",          Syntax.FTcpFlags;
  "ip",  "udp length 8",           Syntax.FUdpLen;
  "ip",  "icmp type echo-request", Syntax.FIcmpType;
  "ip",  "icmp code 0",            Syntax.FIcmpCode;
  "ip6", "ip6 saddr ::1",          Syntax.FIp6Saddr;
  "ip6", "ip6 daddr ::1",          Syntax.FIp6Daddr;
  "ip",  "meta mark 1",            Syntax.FMetaGen Packet.MKmark;
  "ip",  "meta l4proto tcp",       Syntax.FMetaGen Packet.MKl4proto;
  "inet", "meta nfproto ipv4",     Syntax.FMetaGen Packet.MKnfproto;
  "ip",  "meta length 100",        Syntax.FMetaGen Packet.MKlen;
  "ip",  "meta skuid 0",           Syntax.FMetaGen Packet.MKskuid;
  "ip",  "meta priority 0",        Syntax.FMetaGen Packet.MKpriority;
  "ip",  "ct state new",           Syntax.FCtState;
  "ip",  "ct mark 1",              Syntax.FCtMark;
]

let run_validation () =
  let pass = ref 0 and fail = ref 0 in
  List.iter (fun (fam, text, field) ->
    let input = Printf.sprintf
      "table %s validate {\n chain c {\n type filter hook input priority 0;\n %s\n }\n}\n"
      fam text in
    let keys = load_keys_of (run_nft input) in
    let want = key_of_load (Syntax.field_load field) in
    if List.mem want keys then incr pass
    else (incr fail;
      Printf.printf "FAIL: %-26s want %-16s got [%s]\n" text want (String.concat "; " keys)))
    validate_pairs;
  Printf.printf "\n=== field_load vs live nft: %d/%d validated ===\n"
    !pass (!pass + !fail);
  if !fail > 0 then exit 1 else exit 0

(* ---------- main ---------- *)
let run_corpus () =
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

let () =
  match Array.to_list Sys.argv with
  | _ :: "validate" :: _ -> run_validation ()
  | _ -> run_corpus ()
