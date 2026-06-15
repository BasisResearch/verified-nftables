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

open Codec


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
  | POrdCmp  of Bytecode.cmpop * int * int list  (* ordered cmp lt/gt/lte/gte *)
  | PRange   of bool * int * string list      (* is_eq, src reg, lo++hi hexwords *)
  | PBitwise of int * int * int list * int list  (* dst, src, mask, xor *)
  | PShift   of int * int * bool * int            (* dst, src, is_left, amount *)
  | PByteorder of int * int * bool * int * int    (* dst, src, hton, size, len *)
  | PJhash   of int * int * int * int * int * int (* dst, src, len, seed, mod, offset *)
  | PLookup  of int * string * bool              (* src reg, set name, inverted *)
  | PVmap    of int * string                     (* verdict map: lookup .. dreg 0 *)
  | PCounter of int * int
  | PNotrack
  | PLimit   of Packet.limit_spec
  | PQuota   of Packet.quota_spec
  | PConnlimit of Packet.connlimit_spec
  | PLog     of string
  | PImmData of int * int list                    (* immediate into a data register *)
  | PWrite   of int * Packet.pbase * int * int * int * int * int
                            (* payload write: src reg, base, off, len, ctype, coff, cflags *)
  | PMetaSet of Packet.meta_key * int
  | PCtSet   of Packet.ct_key * int
  | PCtSetDir of string * string * int             (* key, dir, src reg *)
  | PMapVal  of int * string * int               (* key reg, map name, dreg *)
  | PNat     of string * string * int option * int option * int option * int option * int
                            (* kind, family, amin, amax, pmin, pmax, flags *)
  | PTproxy  of string * int option * int option   (* family, addr reg, port reg *)
  | PObjref  of int * string                       (* object type, object name *)
  | PObjrefMap of int * string                     (* sreg, object-map name *)
  | PSynproxy of int * int                         (* mss, wscale *)
  | PLast    of string                             (* `last` info (count or "never") *)
  | PDynset  of string * string * int * int option (* op, set name, key reg, data reg *)
  | PExthdrReset of string * int                   (* proto, htype *)
  | PExthdrWrite of string * int * int * int * int (* proto, src reg, htype, off, len *)
  | PDup     of int option * int option            (* dev reg, addr reg *)
  | PFwd     of int option * int option * int option (* dev reg, addr reg, nfproto *)
  | PQueue   of int * bool * bool                  (* sreg, bypass, fanout *)
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
  | "ct"::"load"::key::"=>"::"reg"::r::","::"dir"::dir::[] ->
      (* directional conntrack load (original/reply tuple field) *)
      PLoad (Printf.sprintf "ctd:%s:%s" key dir, int_of_string r)
  | "xfrm"::"load"::dir::sp::key::"=>"::"reg"::r::[] ->
      PLoad (Printf.sprintf "xf:%s:%s:%s" dir sp key, int_of_string r)
  | "tunnel"::"load"::key::"=>"::"reg"::r::[] ->
      PLoad (Printf.sprintf "tun:%s" key, int_of_string r)
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
  | "inner"::"type"::t::"hdrsize"::h::"flags"::fl::"["::rest ->
      let (inner_toks, _) = take_until "]" rest in
      let (desc_toks, after) = take_until "=>" inner_toks in
      let r = (match after with ["reg"; n] -> int_of_string n
               | _ -> raise (Unsupported "inner:form")) in
      let width = (match desc_toks with
        | "meta"::_ -> 4
        | "payload"::"load"::lb::_ ->
            int_of_string (String.sub lb 0 (String.length lb - 1))
        | _ -> raise (Unsupported "inner:innerload")) in
      let desc = String.concat " " desc_toks in
      PLoad (Printf.sprintf "inner:%d:%d:%d:%d:%s"
               (int_of_string t) (int_of_string h)
               (int_of_string ("0x"^fl)) width desc, r)
  | "fib"::rest ->
      let (lhs, after) = take_until "=>" rest in
      let r = (match after with ["reg"; n] -> int_of_string n
               | _ -> raise (Unsupported "fib:form")) in
      (match List.rev lhs with
       | res :: sel_rev when fibres_of_name res <> None ->
           let sel = String.concat " " (List.rev sel_rev) in
           PLoad (Printf.sprintf "fib:%s:%s" sel res, r)
       | _ -> raise (Unsupported "fib:result"))
  | "exthdr"::"load"::proto::lb::"@"::htype::"+"::off::rest
    when ehproto_of_name proto <> None ->
      let len = int_of_string (String.sub lb 0 (String.length lb - 1)) in
      let (present, rest2) = (match rest with
        | "present" :: r -> (true, r) | r -> (false, r)) in
      (match rest2 with
       | "=>"::"reg"::r::[] ->
           PLoad (Printf.sprintf "x:%s:%s:%s:%d:%b" proto htype off len present,
                  int_of_string r)
       | _ -> raise (Unsupported "exthdr:form"))
  | "exthdr"::"load"::lb::"@"::htype::"+"::off::rest
    when String.length lb >= 1 && lb.[String.length lb - 1] = 'b' ->
      (* sctp-chunk exthdr: no protocol word *)
      let len = int_of_string (String.sub lb 0 (String.length lb - 1)) in
      let (present, rest2) = (match rest with
        | "present" :: r -> (true, r) | r -> (false, r)) in
      (match rest2 with
       | "=>"::"reg"::r::[] ->
           PLoad (Printf.sprintf "x:sctp:%s:%s:%d:%b" htype off len present,
                  int_of_string r)
       | _ -> raise (Unsupported "exthdr:form"))
  | "cmp"::op::"reg"::r::rest ->
      let v = bytes_of_hexwords rest in
      (match op with
       | "eq"  -> PCmp (true,  int_of_string r, v)
       | "neq" -> PCmp (false, int_of_string r, v)
       | "lt"  -> POrdCmp (Bytecode.CLt, int_of_string r, v)
       | "gt"  -> POrdCmp (Bytecode.CGt, int_of_string r, v)
       | "lte" -> POrdCmp (Bytecode.CLe, int_of_string r, v)
       | "gte" -> POrdCmp (Bytecode.CGe, int_of_string r, v)
       | _ -> raise (Unsupported ("cmpop:"^op)))
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
  | "hash"::"reg"::d::"="::"symhash()"::"%"::"mod"::m::rest ->
      let off = (match rest with [] -> 0 | ["offset"; o] -> int_of_string o
                 | _ -> raise (Unsupported "hash:opts")) in
      PLoad (Printf.sprintf "sym:%s:%d" m off, int_of_string d)
  | "hash"::"reg"::d::"="::jr::s::len::seed::"%"::"mod"::m::rest
    when String.length jr >= 5 && String.sub jr 0 5 = "jhash" ->
      let off = (match rest with [] -> 0 | ["offset"; o] -> int_of_string o
                 | _ -> raise (Unsupported "hash:opts")) in
      let strip_paren x =
        if String.length x > 0 && x.[String.length x - 1] = ')'
        then String.sub x 0 (String.length x - 1) else x in
      PJhash (int_of_string d, only_digits s, only_digits len,
              int_of_string (strip_paren seed), int_of_string m, off)
  | "lookup"::"reg"::r::"set"::name::rest ->
      (match rest with
       | [] -> PLookup (int_of_string r, name, false)
       | ["dreg"; "0"] -> PVmap (int_of_string r, name)
       | ["dreg"; d] -> PMapVal (int_of_string r, name, int_of_string d)
       | "dreg"::_ -> raise (Unsupported "lookup:map")
       | [h] when String.length h >= 2 && String.sub h 0 2 = "0x" ->
           PLookup (int_of_string r, name, true)
       | _ -> raise (Unsupported "lookup:flags"))
  | "immediate"::"reg"::"0"::rest ->
      (match rest with
       | ["accept"] -> PImm Verdict.Accept
       | ["drop"]   -> PImm Verdict.Drop
       | v::_       -> raise (Unsupported ("verdict:"^v))
       | []         -> raise (Unsupported "verdict:empty"))
  | "immediate"::"reg"::r::rest ->  (* immediate into a data register (NAT/mangle operand) *)
      PImmData (int_of_string r, bytes_of_hexwords rest)
  | "payload"::"write"::"reg"::r::"=>"::lb::"@"::base::"header"::"+"::off::rest ->
      (match base_of_name base, rest with
       | Some b, ["csum_type"; ct; "csum_off"; co; "csum_flags"; cf] ->
           let len = int_of_string (String.sub lb 0 (String.length lb - 1)) in
           PWrite (int_of_string r, b, int_of_string off, len,
                   int_of_string ct, int_of_string co, int_of_string cf)
       | _ -> raise (Unsupported "payload:write:form"))
  | "meta"::"set"::name::"with"::"reg"::r::[] ->
      (match meta_of_name name with
       | Some k -> PMetaSet (k, int_of_string r)
       | None -> raise (Unsupported ("metaset:"^name)))
  | "ct"::"set"::key::"with"::"reg"::r::","::"dir"::dir::[] ->
      PCtSetDir (key, dir, int_of_string r)
  | "ct"::"set"::name::"with"::"reg"::r::[] ->
      (match ct_of_name name with
       | Some k -> PCtSet (k, int_of_string r)
       | None -> raise (Unsupported ("ctset:"^name)))
  | "nat"::kind::family::rest when kind = "snat" || kind = "dnat" ->
      let rec fields amin amax pmin pmax flags = function
        | "addr_min"::"reg"::a::r -> fields (Some (int_of_string a)) amax pmin pmax flags r
        | "addr_max"::"reg"::a::r -> fields amin (Some (int_of_string a)) pmin pmax flags r
        | "proto_min"::"reg"::a::r -> fields amin amax (Some (int_of_string a)) pmax flags r
        | "proto_max"::"reg"::a::r -> fields amin amax pmin (Some (int_of_string a)) flags r
        | "flags"::f::r -> fields amin amax pmin pmax (int_of_string f) r
        | [] -> (amin, amax, pmin, pmax, flags)
        | _ -> raise (Unsupported "nat:field") in
      let (amin,amax,pmin,pmax,flags) = fields None None None None 0 rest in
      PNat (kind, family, amin, amax, pmin, pmax, flags)
  | kind::rest when kind = "masq" || kind = "redir" ->
      let rec fields pmin pmax flags = function
        | "proto_min"::"reg"::a::r -> fields (Some (int_of_string a)) pmax flags r
        | "proto_max"::"reg"::a::r -> fields pmin (Some (int_of_string a)) flags r
        | "flags"::f::r -> fields pmin pmax (int_of_string f) r
        | [] -> (pmin, pmax, flags)
        | _ -> raise (Unsupported "natlike:field") in
      let (pmin,pmax,flags) = fields None None 0 rest in
      PNat (kind, "", None, None, pmin, pmax, flags)
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
  | ["quota"; "bytes"; b; "consumed"; c; "flags"; fl] ->
      PQuota { Packet.q_bytes = int_of_string b; q_consumed = int_of_string c;
               q_flags = int_of_string fl }
  | ["connlimit"; "count"; c; "flags"; fl] ->
      PConnlimit { Packet.cl_count = int_of_string c; cl_flags = int_of_string fl }
  | "log"::rest -> PLog (String.concat " " rest)
  | ["objref"; "type"; t; "name"; n] -> PObjref (int_of_string t, n)
  | ["objref"; "sreg"; r; "set"; name] -> PObjrefMap (int_of_string r, name)
  | ["synproxy"; "mss"; m; "wscale"; w] -> PSynproxy (int_of_string m, int_of_string w)
  | ["last"; info] -> PLast info
  | ["dynset"; op; "reg_key"; k; "set"; name] ->
      PDynset (op, name, int_of_string k, None)
  | ["dynset"; op; "reg_key"; k; "set"; name; "sreg_data"; d] ->
      PDynset (op, name, int_of_string k, Some (int_of_string d))
  | ["exthdr"; "reset"; proto; h] -> PExthdrReset (proto, int_of_string h)
  | "exthdr"::"write"::proto::"reg"::r::"=>"::lb::"@"::htype::"+"::off::[] ->
      let len = int_of_string (String.sub lb 0 (String.length lb - 1)) in
      PExthdrWrite (proto, int_of_string r, int_of_string htype, int_of_string off, len)
  | "dup"::rest ->
      let rec p dev addr = function
        | "sreg_dev"::r::t -> p (Some (int_of_string r)) addr t
        | "sreg_addr"::r::t -> p dev (Some (int_of_string r)) t
        | [] -> (dev, addr)
        | _ -> raise (Unsupported "dup:form") in
      let (dev, addr) = p None None rest in
      PDup (dev, addr)
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
  | "tproxy"::rest ->
      let (family, rest) = (match rest with
        | ("ip" | "ip6" as f) :: r -> (f, r) | r -> ("", r)) in
      let rec p areg preg = function
        | "addr"::"reg"::n::r -> p (Some (int_of_string n)) preg r
        | "port"::"reg"::n::r -> p areg (Some (int_of_string n)) r
        | [] -> (areg, preg)
        | _ -> raise (Unsupported "tproxy:form") in
      let (areg, preg) = p None None rest in
      PTproxy (family, areg, preg)
  | "fwd"::rest ->
      let rec p dev addr nfp = function
        | "sreg_dev"::n::r -> p (Some (int_of_string n)) addr nfp r
        | "sreg_addr"::n::r -> p dev (Some (int_of_string n)) nfp r
        | "nfproto"::n::r -> p dev addr (Some (int_of_string n)) r
        | [] -> (dev, addr, nfp)
        | _ -> raise (Unsupported "fwd:form") in
      let (dev, addr, nfp) = p None None None rest in
      PFwd (dev, addr, nfp)
  | "queue"::"sreg_qnum"::n::flags ->
      PQueue (int_of_string n, List.mem "bypass" flags, List.mem "fanout" flags)
  | "queue"::_ -> raise (Unsupported "queue:form")
  | tok::_ -> raise (Unsupported ("instr:"^tok))
  | [] -> raise (Unsupported "empty")

(* fold a block into a DSL rule: (load;test)* then verdict-neutral statements
   then a verdict. *)
let rule_of_block (lines : string list) : Syntax.rule =
  let mk ?(vmap=None) ?(nat=None) ?(tproxy=None) ?(fwd=None) ?(queue=None) ?(after=[]) body v : Syntax.rule =
    { Syntax.r_body = List.rev body;
      r_verdict = v; r_vmap = vmap; r_nat = nat; r_tproxy = tproxy;
      r_fwd = fwd; r_queue = queue; r_after = after } in
  let mk_fwd ?(src=None) body imms (dev,addr,nfp) =
    mk ~fwd:(Some { Syntax.fwd_imms = imms; fwd_src = src; fwd_devreg = dev;
                    fwd_addrreg = addr; fwd_nfproto = nfp }) body Verdict.Continue in
  let mk_queue ?(src=None) body imms (sreg,bypass,fanout) =
    mk ~queue:(Some { Syntax.q_imms = imms; q_src = src; q_sreg = sreg;
                      q_bypass = bypass; q_fanout = fanout }) body Verdict.Continue in
  let bm body m = Syntax.BMatch m :: body in      (* prepend a match in order *)
  let bs body s = Syntax.BStmt s :: body in       (* prepend a statement in order *)
  (* verdict-neutral statements emitted after a terminal outcome (e.g. a counter
     after a verdict map); anything else there is genuinely unsupported *)
  let rec parse_after = function
    | [] -> []
    | l :: more ->
      (match parse_line l with
       | PCounter (pk,b) -> Syntax.SCounter (pk,b) :: parse_after more
       | PNotrack -> Syntax.SNotrack :: parse_after more
       | PLog s -> Syntax.SLog s :: parse_after more
       | PObjref (t,n) -> Syntax.SObjref (t,n) :: parse_after more
       | _ -> raise (Unsupported "trailing-after-vmap")) in
  let mk_vmap ?(after=[]) body fields name =
    mk ~after ~vmap:(Some { Syntax.vm_fields = fields; vm_keyf = None;
                     vm_name = name; vm_entries = [] }) body Verdict.Continue in
  let mk_vmap_t ?(after=[]) body f ts name =
    mk ~after ~vmap:(Some { Syntax.vm_fields = [f]; vm_keyf = Some (f, ts);
                     vm_name = name; vm_entries = [] }) body Verdict.Continue in
  let mk_nat body imms (kind,family,amin,amax,pmin,pmax,flags) =
    mk ~nat:(Some { Syntax.nat_imms = imms; nat_field = None; nat_map = None;
                    nat_kind = kind; nat_family = family;
                    nat_amin = amin; nat_amax = amax; nat_pmin = pmin;
                    nat_pmax = pmax; nat_flags = flags }) body Verdict.Continue in
  let mk_nat_map body (fields,ts,name) (kind,family,amin,amax,pmin,pmax,flags) =
    mk ~nat:(Some { Syntax.nat_imms = []; nat_field = None; nat_map = Some ((fields, ts), name);
                    nat_kind = kind; nat_family = family;
                    nat_amin = amin; nat_amax = amax; nat_pmin = pmin;
                    nat_pmax = pmax; nat_flags = flags }) body Verdict.Continue in
  let mk_nat_field body (f,ts) (kind,family,amin,amax,pmin,pmax,flags) =
    mk ~nat:(Some { Syntax.nat_imms = []; nat_field = Some (f, ts); nat_map = None;
                    nat_kind = kind; nat_family = family;
                    nat_amin = amin; nat_amax = amax; nat_pmin = pmin;
                    nat_pmax = pmax; nat_flags = flags }) body Verdict.Continue in
  let mk_tproxy body imms (family,areg,preg) =
    mk ~tproxy:(Some { Syntax.tp_imms = imms; tp_family = family;
                       tp_areg = areg; tp_preg = preg }) body Verdict.Continue in
  (* fold a block into a rule body, preserving the source order of matches and
     verdict-neutral statements (nft interleaves them; our [r_body] is ordered). *)
  let rec go body = function
    | [] -> mk body Verdict.Continue   (* match-only rule: falls through *)
    | l1 :: rest ->
      (match parse_line l1 with
       | PImm v ->
           if rest <> [] then raise (Unsupported "trailing-after-verdict");
           mk body v
       | PNat (k,f,a,ax,pm,px,fl) ->
           if rest <> [] then raise (Unsupported "trailing-after-nat");
           mk_nat body [] (k,f,a,ax,pm,px,fl)
       | PImmData (r, v) ->
           let is_set l = (try (match parse_line l with
                                | PWrite _ | PMetaSet _ | PCtSet _ | PCtSetDir _
                                | PExthdrWrite _ -> true | _ -> false)
                           with _ -> false) in
           (match rest with
            | l2 :: more2 when r = 1 && is_set l2 ->   (* immediate + a set/write = mangle *)
                (match parse_line l2 with
                 | PWrite (1, b, off, len, ct, co, cf) ->
                     go (bs body (Syntax.SMangle (Syntax.VImm v, b, off, len, ct, co, cf))) more2
                 | PMetaSet (k, 1) -> go (bs body (Syntax.SMetaSet (k, Syntax.VImm v))) more2
                 | PCtSet (k, 1) -> go (bs body (Syntax.SCtSet (k, Syntax.VImm v))) more2
                 | PCtSetDir (key, dir, 1) -> go (bs body (Syntax.SCtSetDir (key, dir, Syntax.VImm v))) more2
                 | PExthdrWrite (proto, 1, htype, off, len) ->
                     go (bs body (Syntax.SExthdrWrite (Syntax.VImm v, proto, htype, off, len))) more2
                 | _ -> raise (Unsupported "set:reg"))
            | _ ->
                (* otherwise: gather operand immediates, then a nat/tproxy/dup *)
                let rec gnat imms = function
                  | l :: more ->
                    (match parse_line l with
                     | PImmData (r2, v2) -> gnat ((r2, v2) :: imms) more
                     | PNat (k,f,a,ax,pm,px,fl) ->
                         if more <> [] then raise (Unsupported "trailing-after-nat");
                         mk_nat body (List.rev imms) (k,f,a,ax,pm,px,fl)
                     | PTproxy (fam,ar,pr) ->
                         if more <> [] then raise (Unsupported "trailing-after-tproxy");
                         mk_tproxy body (List.rev imms) (fam,ar,pr)
                     | PDup (dev,addr) ->
                         go (bs body (Syntax.SDup (List.rev imms, dev, addr))) more
                     | PFwd (dev,addr,nfp) ->
                         if more <> [] then raise (Unsupported "trailing-after-fwd");
                         mk_fwd body (List.rev imms) (dev,addr,nfp)
                     | PQueue (sreg,bypass,fanout) ->
                         if more <> [] then raise (Unsupported "trailing-after-queue");
                         mk_queue body (List.rev imms) (sreg,bypass,fanout)
                     | _ -> raise (Unsupported "imm-not-nat"))
                  | [] -> raise (Unsupported "imm-dangling")
                in gnat [(r, v)] rest)
       | PCounter (p,b) -> go (bs body (Syntax.SCounter (p,b))) rest
       | PNotrack -> go (bs body Syntax.SNotrack) rest
       | PLog l -> go (bs body (Syntax.SLog l)) rest
       | PObjref (t,n) -> go (bs body (Syntax.SObjref (t,n))) rest
       | PSynproxy (m,w) -> go (bs body (Syntax.SSynproxy (m,w))) rest
       | PLast info -> go (bs body (Syntax.SLast info)) rest
       | PExthdrReset (p,h) -> go (bs body (Syntax.SExthdrReset (p,h))) rest
       | PLimit spec -> go (bm body (Syntax.MLimit spec)) rest
       | PQuota spec -> go (bm body (Syntax.MQuota spec)) rest
       | PConnlimit spec -> go (bm body (Syntax.MConnlimit spec)) rest
       | PLoad (key, lreg) ->
           let field_of k = (match field_of_key_str k with Some f -> f
                             | None -> raise (Unsupported ("field:"^k))) in
           let f = field_of key in
           let is_load l = (try (match parse_line l with PLoad _ -> true | _ -> false)
                            with _ -> false) in
           (match rest with
            | l2 :: _ when is_load l2 ->
                (* concatenation key: gather consecutive loads, then a lookup/use *)
                let rec gather facc = function
                  | l :: more ->
                    (match parse_line l with
                     | PLoad (k, _) -> gather (field_of k :: facc) more
                     | PLookup (_, name, neg) ->
                         go (bm body (Syntax.MConcatSet (List.rev facc, neg, name, []))) more
                     | PVmap (_, name) ->
                         mk_vmap ~after:(parse_after more) body (List.rev facc) name
                     | PDynset (op, name, _, dopt) ->
                         let fields = List.rev facc in
                         let (keys, data) = (match dopt with
                           | None -> (fields, [])
                           | Some _ ->
                               let n = List.length fields in
                               (List.filteri (fun i _ -> i < n-1) fields,
                                List.filteri (fun i _ -> i = n-1) fields)) in
                         go (bs body (Syntax.SDynset (op, name, keys, data))) more
                     | PObjrefMap (_, name) ->
                         go (bs body (Syntax.SObjrefMap (List.rev facc, name))) more
                     (* dynset whose map data is immediate constants: the concat
                        key is loaded, then the data words are [immediate]'d into
                        their own registers, then a dynset references them. *)
                     | PImmData (r, v) ->
                         let keyfs = List.rev facc in
                         let rec gimm iacc = function
                           | l3 :: more3 ->
                             (match parse_line l3 with
                              | PImmData (r2, v2) -> gimm ((r2, v2) :: iacc) more3
                              | PDynset (op, name, _, Some dreg) ->
                                  go (bs body (Syntax.SDynsetImm
                                        (op, name, keyfs, List.rev iacc, dreg))) more3
                              | _ -> raise (Unsupported "dynset-imm-not-dynset"))
                           | [] -> raise (Unsupported "dynset-imm-dangling")
                         in gimm [(r, v)] more
                     (* jhash of the concatenation, feeding a set = a hashed value *)
                     | PJhash (_, _, len, seed, m, o) ->
                         let fields = List.rev facc in
                         (match more with
                          | l3 :: more3 ->
                            (match parse_line l3 with
                             | PMetaSet (k, 1) ->
                                 go (bs body (Syntax.SMetaSet (k, Syntax.VHash (fields, len, seed, m, o)))) more3
                             | PCtSet (k, 1) ->
                                 go (bs body (Syntax.SCtSet (k, Syntax.VHash (fields, len, seed, m, o)))) more3
                             | PQueue (sreg, bypass, fanout) ->
                                 if more3 <> [] then raise (Unsupported "trailing-after-queue");
                                 mk_queue ~src:(Some (Syntax.VHash (fields, len, seed, m, o))) body []
                                   (sreg, bypass, fanout)
                             | _ -> raise (Unsupported "hash-not-set"))
                          | [] -> raise (Unsupported "hash-dangling"))
                     | PMapVal (_, name, 1) ->
                         let fields = List.rev facc in
                         (match more with
                          | l3 :: more3 ->
                            (match parse_line l3 with
                             | PMetaSet (k, 1) ->
                                 go (bs body (Syntax.SMetaSet (k, Syntax.VMap (fields, [], name, [])))) more3
                             | PCtSet (k, 1) ->
                                 go (bs body (Syntax.SCtSet (k, Syntax.VMap (fields, [], name, [])))) more3
                             | PNat (kind,fam,a,ax,pm,px,fl) ->
                                 if more3 <> [] then raise (Unsupported "trailing-after-nat");
                                 mk_nat_map body (fields, [], name) (kind,fam,a,ax,pm,px,fl)
                             | _ -> raise (Unsupported "map-not-set"))
                          | [] -> raise (Unsupported "map-dangling"))
                     | _ -> raise (Unsupported "concat-not-lookup"))
                  | [] -> raise (Unsupported "concat-dangling")
                in gather [f] rest
            | _ ->
                if lreg <> 1 then raise (Unsupported "reg!=1");
                (* single field: collect a transform chain, then a tester *)
                let rec collect ts = function
                  | l :: more ->
                    (match parse_line l with
                     | PBitwise (1,1,mask,xor) -> collect (Syntax.TBitAnd (mask,xor) :: ts) more
                     | PShift (1,1,shl,amt) -> collect (Syntax.TShift (shl,amt) :: ts) more
                     | PByteorder (1,1,h,sz,ln) -> collect (Syntax.TByteorder (h,sz,ln) :: ts) more
                     | PJhash (1,1,len,seed,m,o) -> collect (Syntax.TJhash (len,seed,m,o) :: ts) more
                     | PCmp (iseq, 1, v) ->
                         let tl = List.rev ts in
                         let m = (match tl with
                           | [] -> if iseq then Syntax.MEq (f,v) else Syntax.MNeq (f,v)
                           | _ -> Syntax.MTransform (f, tl, (if iseq then Bytecode.CEq else Bytecode.CNe), v)) in
                         go (bm body m) more
                     | POrdCmp (op, 1, v) ->
                         let m = (match List.rev ts with
                           | [] -> Syntax.MCmp (f, op, v)
                           | tl -> Syntax.MTransform (f, tl, op, v)) in
                         go (bm body m) more
                     | PRange (iseq, 1, words) ->
                         let n = List.length words in
                         if n land 1 <> 0 then raise (Unsupported "range-odd-words");
                         let lo = bytes_of_hexwords (List.filteri (fun i _ -> i < n/2) words)
                         and hi = bytes_of_hexwords (List.filteri (fun i _ -> i >= n/2) words) in
                         let m = (match List.rev ts with
                           | [] -> Syntax.MRange (f, not iseq, lo, hi)
                           | tl -> Syntax.MRangeT (f, tl, not iseq, lo, hi)) in
                         go (bm body m) more
                     | PLookup (1, name, neg) ->
                         let m = (match List.rev ts with
                           | [] -> Syntax.MConcatSet ([f], neg, name, [])
                           | tl -> Syntax.MSetT (f, tl, neg, name, [])) in
                         go (bm body m) more
                     | PVmap (1, name) ->
                         let after = parse_after more in
                         (match List.rev ts with
                          | [] -> mk_vmap ~after body [f] name
                          | tl -> mk_vmap_t ~after body f tl name)
                     | PMapVal (1, name, 1) ->
                         (match more with
                          | l3 :: more3 ->
                            (match parse_line l3 with
                             | PMetaSet (k, 1) ->
                                 go (bs body (Syntax.SMetaSet (k, Syntax.VMap ([f], List.rev ts, name, [])))) more3
                             | PCtSet (k, 1) ->
                                 go (bs body (Syntax.SCtSet (k, Syntax.VMap ([f], List.rev ts, name, [])))) more3
                             | PNat (kind,fam,a,ax,pm,px,fl) ->
                                 if more3 <> [] then raise (Unsupported "trailing-after-nat");
                                 mk_nat_map body ([f], List.rev ts, name) (kind,fam,a,ax,pm,px,fl)
                             (* map value feeding a terminal fwd device *)
                             | PFwd (dev,addr,nfp) ->
                                 if more3 <> [] then raise (Unsupported "trailing-after-fwd");
                                 mk_fwd ~src:(Some (Syntax.VMap ([f], List.rev ts, name, [])))
                                   body [] (dev,addr,nfp)
                             (* map value feeding a terminal queue number *)
                             | PQueue (sreg, bypass, fanout) ->
                                 if more3 <> [] then raise (Unsupported "trailing-after-queue");
                                 mk_queue ~src:(Some (Syntax.VMap ([f], List.rev ts, name, [])))
                                   body [] (sreg, bypass, fanout)
                             (* map value (in reg 1) feeding a dup device/address *)
                             | PDup (dev, addr) ->
                                 go (bs body (Syntax.SDupSrc
                                       (Syntax.VMap ([f], List.rev ts, name, []),
                                        [], dev, addr))) more3
                             (* map value + an immediate operand feeding a dup *)
                             | PImmData (r, v) ->
                                 (match more3 with
                                  | l4 :: more4 ->
                                    (match parse_line l4 with
                                     | PDup (dev, addr) ->
                                         go (bs body (Syntax.SDupSrc
                                               (Syntax.VMap ([f], List.rev ts, name, []),
                                                [(r, v)], dev, addr))) more4
                                     | _ -> raise (Unsupported "map-imm-not-dup"))
                                  | [] -> raise (Unsupported "map-imm-dangling"))
                             | _ -> raise (Unsupported "map-not-set"))
                          | [] -> raise (Unsupported "map-dangling"))
                     | PDynset (op, name, 1, None) when ts = [] ->
                         go (bs body (Syntax.SDynset (op, name, [f], []))) more
                     | PObjrefMap (1, name) when ts = [] ->
                         go (bs body (Syntax.SObjrefMap ([f], name))) more
                     | PQueue (sreg, bypass, fanout) ->
                         if more <> [] then raise (Unsupported "trailing-after-queue");
                         mk_queue ~src:(Some (Syntax.VField (f, List.rev ts))) body []
                           (sreg, bypass, fanout)
                     | PNat (kind,fam,a,ax,pm,px,fl) ->
                         if more <> [] then raise (Unsupported "trailing-after-nat");
                         mk_nat_field body (f, List.rev ts) (kind,fam,a,ax,pm,px,fl)
                     | PMetaSet (k, 1) ->
                         go (bs body (Syntax.SMetaSet (k, Syntax.VField (f, List.rev ts)))) more
                     | PCtSet (k, 1) ->
                         go (bs body (Syntax.SCtSet (k, Syntax.VField (f, List.rev ts)))) more
                     | PCtSetDir (key, dir, 1) ->
                         go (bs body (Syntax.SCtSetDir (key, dir, Syntax.VField (f, List.rev ts)))) more
                     | PWrite (1, b, off, len, ct, co, cf) ->
                         go (bs body (Syntax.SMangle (Syntax.VField (f, List.rev ts), b, off, len, ct, co, cf))) more
                     | PRange _ -> raise (Unsupported "range:reg")
                     | PLookup _ -> raise (Unsupported "lookup:reg")
                     | PBitwise _ | PShift _ | PByteorder _ | PJhash _ | PCmp _ ->
                         raise (Unsupported "reg!=1")
                     | _ -> raise (Unsupported "load-not-followed-by-test"))
                  | [] -> raise (Unsupported "dangling-load")
                in collect [] rest)
       | _ -> raise (Unsupported "test-without-load"))
  in go [] lines

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
  (* fib: independently confirm the selector/result tokenization against live nft
     (the round-trip alone can't, since fib's sel string is free-form). *)
  "inet", "fib daddr . iif type local",   Syntax.FFib ("daddr . iif", Packet.FRtype);
  "inet", "fib saddr . iif oifname \"lo\"", Syntax.FFib ("saddr . iif", Packet.FRoifname);
  "inet", "fib saddr . iif oif != 0",     Syntax.FFib ("saddr . iif", Packet.FRoif);
  (* directional conntrack: confirm the field-name/direction tokenization vs nft *)
  "ip", "ct original ip saddr 1.2.3.4",   Syntax.FCtDir ("src_ip", "original");
  "ip", "ct reply ip daddr 1.2.3.4",      Syntax.FCtDir ("dst_ip", "reply");
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
      | `U reason ->
          bump ("unsupported:" ^ reason);
          (match Sys.getenv_opt "DUMP" with
           | Some pat when pat = "" || pat = reason ->
               Printf.eprintf "--- [%s] %s\n%s\n" reason path
                 (String.concat "\n" block)
           | _ -> ())
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
