(* Codec: name tables + bytecode<->nft-text rendering, shared by the corpus
   differential test and the public Nftc library. Untrusted glue, but the
   render direction is checked byte-identical against the upstream corpus. *)

module List = Stdlib.List
module String = Stdlib.String

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
  "avgpkt", Packet.CKavgpkt; "bytes", Packet.CKbytes; "helper", Packet.CKhelper;
  "l3protocol", Packet.CKl3proto; "label", Packet.CKlabel; "packets", Packet.CKpackets;
  "protocol", Packet.CKproto; "zone", Packet.CKzone; "event", Packet.CKevent;
]
let ct_of_name n = try Some (List.assoc n cts) with Not_found -> None
let name_of_ct k =
  let r = ref "?" in List.iter (fun (n,k') -> if k'=k then r:=n) cts; !r

let ehproto_of_name = function
  | "ipv6" -> Some Packet.EPipv6 | "tcpopt" -> Some Packet.EPtcpopt
  | "sctp" -> Some Packet.EPsctp | _ -> None
let name_of_ehproto = function
  | Packet.EPipv6 -> "ipv6" | Packet.EPtcpopt -> "tcpopt"
  | Packet.EPsctp -> "sctp"

let base_of_name = function
  | "link" -> Some Packet.PLink | "network" -> Some Packet.PNetwork
  | "transport" -> Some Packet.PTransport
  | "inner" -> Some Packet.PInner | "tunnel" -> Some Packet.PTunnel | _ -> None
let name_of_base = function
  | Packet.PLink -> "link" | Packet.PNetwork -> "network"
  | Packet.PTransport -> "transport"
  | Packet.PInner -> "inner" | Packet.PTunnel -> "tunnel"

let name_of_fibres = function
  | Packet.FRoif -> "oif" | Packet.FRoifname -> "oifname"
  | Packet.FRtype -> "type" | Packet.FRpresent -> "present"
let fibres_of_name = function
  | "oif" -> Some Packet.FRoif | "oifname" -> Some Packet.FRoifname
  | "type" -> Some Packet.FRtype | "present" -> Some Packet.FRpresent
  | _ -> None

(* descriptor (loaddesc) -> a string key, for the reverse map and equality *)
let key_of_load (ld : Syntax.loaddesc) = match ld with
  | Syntax.LMeta k -> "m:" ^ name_of_meta k
  | Syntax.LCt k -> "c:" ^ name_of_ct k
  | Syntax.LRt k -> "r:" ^ name_of_rt k
  | Syntax.LSocket k -> "s:" ^ name_of_sock k
  | Syntax.LExthdr (ep,h,o,l,pr) ->
      Printf.sprintf "x:%s:%d:%d:%d:%b" (name_of_ehproto ep) h o l pr
  | Syntax.LNumgen s ->
      Printf.sprintf "ng:%b:%d:%d" s.Packet.ng_random s.Packet.ng_mod s.Packet.ng_offset
  | Syntax.LOsf -> "osf:"
  | Syntax.LFib (sel,res) -> Printf.sprintf "fib:%s:%s" sel (name_of_fibres res)
  | Syntax.LCtDir (key,dir) -> Printf.sprintf "ctd:%s:%s" key dir
  | Syntax.LXfrm (dir,sp,key) -> Printf.sprintf "xf:%s:%d:%s" dir sp key
  | Syntax.LInner (t,h,fl,desc,w) -> Printf.sprintf "inner:%d:%d:%d:%d:%s" t h fl w desc
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
  | ["x"; proto; h; o; l; pr] ->
      (match ehproto_of_name proto with
       | Some ep -> Some (Syntax.FExthdr (ep, int_of_string h, int_of_string o,
                                          int_of_string l, bool_of_string pr))
       | None -> None)
  | ["p"; base; o; l] ->
      (match base_of_name base with
       | Some b -> Some (Syntax.FPayload (b, int_of_string o, int_of_string l))
       | None -> None)
  | ["m"; n] -> (match meta_of_name n with Some k -> Some (Syntax.FMetaGen k) | None -> None)
  | ["c"; n] -> (match ct_of_name n with Some k -> Some (Syntax.FCtGen k) | None -> None)
  | ["r"; n] -> (match rt_of_name n with Some k -> Some (Syntax.FRtGen k) | None -> None)
  | ["s"; n] -> (match sock_of_name n with Some k -> Some (Syntax.FSocketGen k) | None -> None)
  | ["ng"; rnd; m; off] ->
      Some (Syntax.FNumgen { Packet.ng_random = bool_of_string rnd;
                             ng_mod = int_of_string m; ng_offset = int_of_string off })
  | ["osf"; ""] -> Some Syntax.FOsf
  | ["fib"; sel; res] ->
      (match fibres_of_name res with
       | Some r -> Some (Syntax.FFib (sel, r))
       | None -> None)
  | ["ctd"; key; dir] -> Some (Syntax.FCtDir (key, dir))
  | ["xf"; dir; sp; key] -> Some (Syntax.FXfrm (dir, int_of_string sp, key))
  | ["inner"; t; h; fl; w; desc] ->
      Some (Syntax.FInner (int_of_string t, int_of_string h, int_of_string fl,
                           desc, int_of_string w))
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

(* The verified compiler allocates concatenation registers monotonically (slot 0
   -> 1, slot s>0 -> 8+s), which is provably collision-free. nft's debug output
   instead displays a 16-byte-aligned slot using the 128-bit register alias
   (reg 1..4) rather than the 32-bit number. This presentation map (untrusted,
   validated byte-identically by the corpus) translates our register to nft's
   displayed number. slot of our reg r: r<=1 -> r itself (slot 0); else r-8.
   This is injective on nft's valid domain (slots < 16, i.e. <= 64-byte keys);
   nft itself BUG()s on larger keys, so the collisions past slot 32 are
   unreachable and cannot hide a divergence. *)
let nreg r =
  if r <= 1 then r
  else let slot = r - 8 in
       if slot mod 4 = 0 then slot / 4 + 1 else slot + 8

let cmpop_name = function
  | Bytecode.CEq -> "eq" | Bytecode.CNe -> "neq"
  | Bytecode.CLt -> "lt" | Bytecode.CGt -> "gt"
  | Bytecode.CLe -> "lte" | Bytecode.CGe -> "gte"

(* ---------- render our compiled instrs back to corpus text ---------- *)
let render_instr (i : Bytecode.instr) : string = match i with
  | Bytecode.IMetaLoad (k,r) ->
      Printf.sprintf "[ meta load %s => reg %d ]" (name_of_meta k) (nreg r)
  | Bytecode.ICtLoad (k,r) ->
      Printf.sprintf "[ ct load %s => reg %d ]" (name_of_ct k) (nreg r)
  | Bytecode.IRtLoad (k,r) ->
      Printf.sprintf "[ rt load %s => reg %d ]" (name_of_rt k) (nreg r)
  | Bytecode.ISocketLoad (k,r) ->
      Printf.sprintf "[ socket load %s => reg %d ]" (name_of_sock k) (nreg r)
  | Bytecode.IExthdrLoad (Packet.EPsctp,h,o,l,pr,r) ->
      (* sctp-chunk exthdr: nft prints no protocol word *)
      Printf.sprintf "[ exthdr load %db @ %d + %d%s => reg %d ]"
        l h o (if pr then " present" else "") (nreg r)
  | Bytecode.IExthdrLoad (ep,h,o,l,pr,r) ->
      Printf.sprintf "[ exthdr load %s %db @ %d + %d%s => reg %d ]"
        (name_of_ehproto ep) l h o (if pr then " present" else "") (nreg r)
  | Bytecode.IFibLoad (sel,res,r) ->
      Printf.sprintf "[ fib %s %s => reg %d ]" sel (name_of_fibres res) (nreg r)
  | Bytecode.ICtDirLoad (key,dir,r) ->
      Printf.sprintf "[ ct load %s => reg %d , dir %s ]" key (nreg r) dir
  | Bytecode.IXfrmLoad (dir,sp,key,r) ->
      Printf.sprintf "[ xfrm load %s %d %s => reg %d ]" dir sp key (nreg r)
  | Bytecode.IInnerLoad (t,h,fl,desc,_,r) ->
      Printf.sprintf "[ inner type %d hdrsize %d flags %x [ %s => reg %d ] ]"
        t h fl desc (nreg r)
  | Bytecode.INumgen (s,r) ->
      (* mirror upstream nft: it omits "offset" when 0, never emits "offset 0" *)
      let off = if s.Packet.ng_offset > 0 then Printf.sprintf " offset %d" s.Packet.ng_offset else "" in
      Printf.sprintf "[ numgen reg %d = %s mod %d%s ]"
        (nreg r) (if s.Packet.ng_random then "random" else "inc") s.Packet.ng_mod off
  | Bytecode.IOsf r -> Printf.sprintf "[ osf dreg %d ]" (nreg r)
  | Bytecode.IPayloadLoad (b,o,l,r) ->
      Printf.sprintf "[ payload load %db @ %s header + %d => reg %d ]"
        l (name_of_base b) o (nreg r)
  | Bytecode.ICmp (op,r,v) ->
      Printf.sprintf "[ cmp %s reg %d %s ]" (cmpop_name op) r (render_value v)
  | Bytecode.IRange (op,r,lo,hi) ->
      Printf.sprintf "[ range %s reg %d %s %s ]" (cmpop_name op) r (render_value lo) (render_value hi)
  | Bytecode.IBitwise (d,s,mask,xor) ->
      Printf.sprintf "[ bitwise reg %d = ( reg %d & %s ) ^ %s ]"
        d s (render_value mask) (render_value xor)
  | Bytecode.IBitShift (d,s,shl,amt) ->
      Printf.sprintf "[ bitwise reg %d = ( reg %d %s 0x%08x ) ]"
        d s (if shl then "<<" else ">>") amt
  | Bytecode.IByteorder (d,s,hton,sz,len) ->
      Printf.sprintf "[ byteorder reg %d = %s(reg %d, %d, %d) ]"
        d (if hton then "hton" else "ntoh") s sz len
  | Bytecode.IJhash (d,s,len,seed,m,o) ->
      let off = if o > 0 then Printf.sprintf " offset %d" o else "" in
      Printf.sprintf "[ hash reg %d = jhash(reg %d, %d, 0x%x) %% mod %d%s ]"
        d s len seed m off
  | Bytecode.ILookup (srcs,name,neg,_) ->
      let r = nreg (match srcs with x :: _ -> x | [] -> 1) in
      if neg then Printf.sprintf "[ lookup reg %d set %s 0x1 ]" r name
      else Printf.sprintf "[ lookup reg %d set %s ]" r name
  | Bytecode.IVmap (srcs,name,_) ->
      (* entries live in NEWSET, not the rule bytecode; render from the base reg *)
      let r = nreg (match srcs with x :: _ -> x | [] -> 1) in
      Printf.sprintf "[ lookup reg %d set %s dreg 0 ]" r name
  | Bytecode.ILimit s ->
      let u = (match s.Packet.ls_unit with
               | 0->"second" | 1->"minute" | 2->"hour" | 3->"day" | _->"week") in
      Printf.sprintf "[ limit rate %d/%s burst %d type %s flags 0x%x ]"
        s.Packet.ls_rate u s.Packet.ls_burst
        (if s.Packet.ls_bytes then "bytes" else "packets") s.Packet.ls_flags
  | Bytecode.IQuota s ->
      Printf.sprintf "[ quota bytes %d consumed %d flags %d ]"
        s.Packet.q_bytes s.Packet.q_consumed s.Packet.q_flags
  | Bytecode.IObjref (t,n) -> Printf.sprintf "[ objref type %d name %s ]" t n
  | Bytecode.ISynproxy (m,w) -> Printf.sprintf "[ synproxy mss %d wscale %d ]" m w
  | Bytecode.ILast info -> Printf.sprintf "[ last %s ]" info
  | Bytecode.IExthdrReset (proto,h) ->
      Printf.sprintf "[ exthdr reset %s %d ]" proto h
  | Bytecode.IDup (dev,addr) ->
      let opt label = function Some r -> Printf.sprintf " %s %d" label r | None -> "" in
      Printf.sprintf "[ dup%s%s ]" (opt "sreg_addr" addr) (opt "sreg_dev" dev)
  | Bytecode.IDynset (op,name,krs,dreg) ->
      let r = nreg (match krs with x :: _ -> x | [] -> 1) in
      let dat = (match dreg with Some d -> Printf.sprintf " sreg_data %d" (nreg d) | None -> "") in
      Printf.sprintf "[ dynset %s reg_key %d set %s%s ]" op r name dat
  | Bytecode.ICounter (p,b) -> Printf.sprintf "[ counter pkts %d bytes %d ]" p b
  | Bytecode.INotrack -> "[ notrack ]"
  | Bytecode.ILog opts ->
      if opts = "" then "[ log ]" else Printf.sprintf "[ log %s ]" opts
  | Bytecode.IReject (t,c) -> Printf.sprintf "[ reject type %d code %d ]" t c
  | Bytecode.IQueue (lo,hi,byp,fan) ->
      let nums = if lo=hi then string_of_int lo else Printf.sprintf "%d-%d" lo hi in
      "[ queue num " ^ nums ^ (if byp then " bypass" else "")
        ^ (if fan then " fanout" else "") ^ " ]"
  | Bytecode.IImmediate v ->
      let vn = (match v with Verdict.Accept->"accept"|Verdict.Drop->"drop"
                            |Verdict.Continue->"continue"|Verdict.Reject _->"reject") in
      Printf.sprintf "[ immediate reg 0 %s ]" vn
  | Bytecode.IImmediateData (dst,v) ->
      (* NAT operand registers (1..4) are raw nft numbers, not slot regs *)
      Printf.sprintf "[ immediate reg %d %s ]" dst (render_value v)
  | Bytecode.IPayloadWrite (src,b,off,len,ct,co,cf) ->
      Printf.sprintf
        "[ payload write reg %d => %db @ %s header + %d csum_type %d csum_off %d csum_flags 0x%x ]"
        src len (name_of_base b) off ct co cf
  | Bytecode.ILookupVal (keys,name,dreg,_) ->
      let r = nreg (match keys with x :: _ -> x | [] -> 1) in
      Printf.sprintf "[ lookup reg %d set %s dreg %d ]" r name dreg
  | Bytecode.ITproxy (family,areg,preg) ->
      let opt label = function Some r -> Printf.sprintf " %s reg %d" label r | None -> "" in
      let fam = if family = "" then "" else " " ^ family in
      Printf.sprintf "[ tproxy%s%s%s ]" fam (opt "addr" areg) (opt "port" preg)
  | Bytecode.IMetaSet (k,src) ->
      Printf.sprintf "[ meta set %s with reg %d ]" (name_of_meta k) src
  | Bytecode.ICtSet (k,src) ->
      Printf.sprintf "[ ct set %s with reg %d ]" (name_of_ct k) src
  | Bytecode.INat (kind,family,amin,amax,pmin,pmax,flags) ->
      let opt label = function Some r -> Printf.sprintf " %s reg %d" label r | None -> "" in
      let fl = if flags > 0 then Printf.sprintf " flags 0x%x" flags else "" in
      (match kind with
       | "snat" | "dnat" ->
           (* the verified compiler always supplies addr_min for snat/dnat; the
              [None] arm is unreachable from [compile] but kept total for safety *)
           let a = (match amin with Some r -> Printf.sprintf " reg %d" r | None -> "") in
           Printf.sprintf "[ nat %s %s addr_min%s%s%s%s%s ]"
             kind family a (opt "addr_max" amax) (opt "proto_min" pmin)
             (opt "proto_max" pmax) fl
       | _ ->  (* masq / redir: no address/family *)
           Printf.sprintf "[ %s%s%s%s ]" kind (opt "proto_min" pmin)
             (opt "proto_max" pmax) fl)

(* ---------- program rendering (library output) ---------- *)
(* Render one rule's instructions, one per line (no family/table/chain header;
   that framing is the caller's concern). *)
let render_rule (rp : Bytecode.instr list) : string =
  String.concat "\n" (List.map render_instr rp)

(* Render a whole base-chain program: each per-rule instruction block, blank-line
   separated, matching the layout of `nft --debug=netlink`. *)
let render_program (prog : Bytecode.program) : string =
  String.concat "\n" (List.map render_rule prog)
