(* Nft_lower: surface AST (Nft_ast) -> trusted Syntax AST + Packet.env.

   This is where all of nft's frontend behaviour lives, in untrusted code:
     - expanding `define` references (`$lan`);
     - resolving symbolic constants (`established`, `https`, `arp`, `ipv6-icmp`);
     - encoding literals to the byte width of their field / declared set type;
     - inserting the implicit `meta l4proto <proto>` dependency nft puts before an
       L4 (tcp/udp/icmp/...) match;
     - turning named-set/map *declarations* (and inline anonymous `{...}` sets and
       `vmap {...}` maps) into NAMED entries in the evaluation environment, which
       the model looks set/map contents up by name (NOT inlined into the rule).

   Everything here is checked downstream (against the Coq proofs' verdicts and
   live `nft`); nothing here is in the proof TCB.  Any construct outside the
   supported subset raises [Unsupported] — we never guess.  See TODO 9 in
   ../DEVELOPMENT.md. *)

module L = Stdlib.List
module S = Stdlib.String

exception Unsupported of string

(* ---------- byte helpers ---------- *)

let bytes_of_int (width : int) (n : int) : Bytes.data =
  if n < 0 then raise (Unsupported "negative numeric literal");
  L.init width (fun i -> (n lsr (8 * (width - 1 - i))) land 0xff)

let ascii (s : string) : Bytes.data =
  L.init (S.length s) (fun i -> Char.code (S.get s i))

(* nft renders a trailing-`*` wildcard ifname as a cmp of just the prefix bytes,
   which the model's prefix-aware MEq matches; drop the star. *)
let ifname_bytes (s : string) : Bytes.data =
  let s = if S.length s > 0 && S.get s (S.length s - 1) = '*'
          then S.sub s 0 (S.length s - 1) else s in
  ascii s

(* ---------- symbolic-constant tables ---------- *)

let sym_ethertype = [
  "ip",[8;0]; "ip4",[8;0]; "ipv4",[8;0]; "arp",[8;6];
  "ip6",[0x86;0xdd]; "ipv6",[0x86;0xdd]; "vlan",[0x81;0x00];
  "8021q",[0x81;0x00]; "8021ad",[0x88;0xa8];
]
let sym_l4proto = [
  "icmp",[1]; "igmp",[2]; "tcp",[6]; "udp",[17]; "udplite",[136];
  "dccp",[33]; "gre",[47]; "esp",[50]; "ah",[51]; "icmpv6",[58];
  "ipv6-icmp",[58]; "comp",[108]; "sctp",[132];
]
let sym_ctstate = [
  "invalid",[0;0;0;1]; "established",[0;0;0;2]; "related",[0;0;0;4];
  "new",[0;0;0;8]; "untracked",[0;0;0;64];
]
let sym_icmp = [
  "echo-reply",[0]; "destination-unreachable",[3]; "redirect",[5];
  "echo-request",[8]; "router-advertisement",[9]; "router-solicitation",[10];
  "time-exceeded",[11]; "parameter-problem",[12]; "timestamp-request",[13];
  "timestamp-reply",[14];
]
let sym_icmpv6 = [
  "destination-unreachable",[1]; "packet-too-big",[2]; "time-exceeded",[3];
  "parameter-problem",[4]; "echo-request",[128]; "echo-reply",[129];
  "mld-listener-query",[130]; "mld-listener-report",[131];
  "nd-router-solicit",[133]; "nd-router-advert",[134];
  "nd-neighbor-solicit",[135]; "nd-neighbor-advert",[136]; "nd-redirect",[137];
]
let sym_pkttype = [ "host",[0]; "unicast",[0]; "broadcast",[1]; "multicast",[2];
                    "other",[3]; "otherhost",[3]; ]
(* /etc/services subset (extend as corpora demand). *)
let sym_service = [
  "ftp-data",20; "ftp",21; "ssh",22; "telnet",23; "smtp",25; "domain",53;
  "bootps",67; "bootpc",68; "tftp",69; "http",80; "www",80; "pop3",110;
  "ntp",123; "imap",143; "snmp",161; "bgp",179; "https",443; "submission",587;
  "imaps",993; "pop3s",995; "mysql",3306; "rdp",3389; "nfs",2049;
  "syncthing",22000; "wireguard",51820; "openvpn",1194;
]

let lookup ctx tbl s =
  match L.assoc_opt s tbl with
  | Some b -> b
  | None -> raise (Unsupported (Printf.sprintf "symbolic constant %S (%s)" s ctx))

(* ---------- field kinds: how a value is encoded for a given selector ---------- *)

type kind =
  | KIfname | KIp4 | KIp6 | KPort | KL4proto | KEthertype
  | KCtstate | KMark | KIcmp | KIcmpv6 | KPkttype | KFibType | KNum of int

(* fib route-type symbols (the RTN_ route types), as 4-byte words *)
let sym_fibtype = [
  "unspec",[0;0;0;0]; "unicast",[0;0;0;1]; "local",[0;0;0;2];
  "broadcast",[0;0;0;3]; "anycast",[0;0;0;6]; "multicast",[0;0;0;5];
  "blackhole",[0;0;0;6]; "unreachable",[0;0;0;7]; "prohibit",[0;0;0;8];
]

(* encode a single (non-range, non-prefix, non-concat) value for a field kind *)
let enc_atom (k : kind) (v : Nft_ast.value) : Bytes.data =
  match k, v with
  | KIfname, (Nft_ast.Vsym s | Nft_ast.Vstr s) -> ifname_bytes s
  | KIp4, Nft_ast.Vip4 b -> b
  | KIp6, Nft_ast.Vip4 b -> b           (* a v4-mapped literal in a v6 context *)
  | KPort, Nft_ast.Vnum n -> bytes_of_int 2 n
  | KPort, Nft_ast.Vsym s -> bytes_of_int 2 (L.assoc_opt s sym_service
        |> function Some p -> p | None -> raise (Unsupported ("service " ^ s)))
  | KL4proto, Nft_ast.Vnum n -> [n land 0xff]
  | KL4proto, Nft_ast.Vsym s -> lookup "l4proto" sym_l4proto s
  | KEthertype, Nft_ast.Vnum n -> bytes_of_int 2 n
  | KEthertype, Nft_ast.Vsym s -> lookup "ethertype" sym_ethertype s
  | KCtstate, Nft_ast.Vsym s -> lookup "ct state" sym_ctstate s
  | KCtstate, Nft_ast.Vnum n -> bytes_of_int 4 n
  | KMark, Nft_ast.Vnum n -> bytes_of_int 4 n
  | KIcmp, Nft_ast.Vnum n -> [n land 0xff]
  | KIcmp, Nft_ast.Vsym s -> lookup "icmp type" sym_icmp s
  | KIcmpv6, Nft_ast.Vnum n -> [n land 0xff]
  | KIcmpv6, Nft_ast.Vsym s -> lookup "icmpv6 type" sym_icmpv6 s
  | KPkttype, Nft_ast.Vsym s -> lookup "pkttype" sym_pkttype s
  | KPkttype, Nft_ast.Vnum n -> [n land 0xff]
  | KFibType, Nft_ast.Vsym s -> lookup "fib type" sym_fibtype s
  | KFibType, Nft_ast.Vnum n -> bytes_of_int 4 n
  | KNum w, Nft_ast.Vnum n -> bytes_of_int w n
  | _, Nft_ast.Vvar n -> raise (Unsupported ("unresolved $" ^ n))
  | _ -> raise (Unsupported "value/selector type mismatch")

(* the byte width a kind compares at (for building a prefix mask) *)
let width_of_kind = function
  | KIp4 -> 4 | KIp6 -> 16 | KPort | KEthertype -> 2
  | KCtstate | KMark -> 4 | KNum w -> w | _ -> 1

(* ---------- selector resolution: keypath -> (field, kind, l4proto-dep) ---------- *)

let dep_l4 = function
  | "tcp" -> Some [6] | "udp" -> Some [17]
  | "icmp" -> Some [1] | "icmpv6" -> Some [58] | _ -> None

let key_field (kp : Nft_ast.keypath) : Syntax.field * kind * Bytes.data option =
  let none = None in
  match kp with
  | ["tcp"; "dport"] | ["udp"; "dport"] | ["th"; "dport"] ->
      (Syntax.FThDport, KPort, dep_l4 (L.hd kp))
  | ["tcp"; "sport"] | ["udp"; "sport"] | ["th"; "sport"] ->
      (Syntax.FThSport, KPort, dep_l4 (L.hd kp))
  | ["ip"; "saddr"]    -> (Syntax.FIp4Saddr, KIp4, none)
  | ["ip"; "daddr"]    -> (Syntax.FIp4Daddr, KIp4, none)
  | ["ip"; "protocol"] -> (Syntax.FIp4Protocol, KL4proto, none)
  | ["ip6"; "saddr"]   -> (Syntax.FIp6Saddr, KIp6, none)
  | ["ip6"; "daddr"]   -> (Syntax.FIp6Daddr, KIp6, none)
  | ["icmp"; "type"]   -> (Syntax.FIcmpType, KIcmp, dep_l4 "icmp")
  | ["icmpv6"; "type"] -> (Syntax.FIcmpType, KIcmpv6, dep_l4 "icmpv6")
  | ["ether"; "type"]  -> (Syntax.FEtherType, KEthertype, none)
  | ["ether"; "saddr"] -> (Syntax.FEtherSaddr, KNum 6, none)
  | ["ether"; "daddr"] -> (Syntax.FEtherDaddr, KNum 6, none)
  | ["meta"; "l4proto"]  -> (Syntax.FMetaL4proto, KL4proto, none)
  | ["meta"; "nfproto"]  -> (Syntax.FMetaNfproto, KL4proto, none)
  | ["meta"; "protocol"] -> (Syntax.FMetaProtocol, KEthertype, none)
  | ["meta"; "mark"]     -> (Syntax.FMetaMark, KMark, none)
  | ["meta"; "iifname"]  -> (Syntax.FMetaIifname, KIfname, none)
  | ["meta"; "oifname"]  -> (Syntax.FMetaOifname, KIfname, none)
  | ["meta"; "iif"]      -> (Syntax.FMetaIif, KIfname, none)
  | ["meta"; "oif"]      -> (Syntax.FMetaOif, KIfname, none)
  | ["meta"; "obrname"]  -> (Syntax.FMetaGen Packet.MKbri_oifname, KIfname, none)
  | ["meta"; "ibrname"]  -> (Syntax.FMetaGen Packet.MKbri_iifname, KIfname, none)
  | ["meta"; "pkttype"]  -> (Syntax.FMetaPkttype, KPkttype, none)
  | ["mark"]             -> (Syntax.FMetaMark, KMark, none)
  | ["pkttype"]          -> (Syntax.FMetaPkttype, KPkttype, none)
  | ["iifname"]          -> (Syntax.FMetaIifname, KIfname, none)
  | ["oifname"]          -> (Syntax.FMetaOifname, KIfname, none)
  | ["iif"]              -> (Syntax.FMetaIif, KIfname, none)
  | ["oif"]              -> (Syntax.FMetaOif, KIfname, none)
  | ["fib"; sel; "type"]    -> (Syntax.FFib (sel, Packet.FRtype), KFibType, none)
  | ["fib"; sel; "oifname"] -> (Syntax.FFib (sel, Packet.FRoifname), KIfname, none)
  | ["fib"; sel; "oif"]     -> (Syntax.FFib (sel, Packet.FRoif), KNum 4, none)
  | ["ct"; "state"]      -> (Syntax.FCtState, KCtstate, none)
  | ["ct"; "mark"]       -> (Syntax.FCtMark, KMark, none)
  | _ -> raise (Unsupported ("selector: " ^ S.concat " " kp))

(* ---------- prefix mask ---------- *)

let prefix_mask (width : int) (len : int) : Bytes.data =
  L.init width (fun i ->
    let bit_lo = 8 * i and bit_hi = 8 * (i + 1) in
    let m = ref 0 in
    for b = bit_lo to bit_hi - 1 do
      if b < len then m := !m lor (0x80 lsr (b - bit_lo))
    done; !m)
let band a b = L.map2 (land) a b

(* ---------- mutable lowering state ---------- *)

type state = {
  defines : (string, Nft_ast.value) Hashtbl.t;
  mutable sets  : (string * (Bytes.data * Bytes.data) list) list;
  mutable vmaps : (string * (Bytes.data * Verdict.verdict) list) list;
  mutable maps  : (string * (Bytes.data * Bytes.data) list) list;
  mutable counter : int;
}
let fresh st pfx = let n = st.counter in st.counter <- n + 1; Printf.sprintf "%s%d" pfx n

(* expand `$name` to its define (recursively), leave other values as-is *)
let rec resolve_var st (v : Nft_ast.value) : Nft_ast.value =
  match v with
  | Nft_ast.Vvar n ->
      (match Hashtbl.find_opt st.defines n with
       | Some v' -> resolve_var st v'
       | None -> raise (Unsupported ("undefined variable $" ^ n)))
  | Nft_ast.Vprefix (v', l) -> Nft_ast.Vprefix (resolve_var st v', l)
  | Nft_ast.Vrange (a, b) -> Nft_ast.Vrange (resolve_var st a, resolve_var st b)
  | Nft_ast.Vconcat vs -> Nft_ast.Vconcat (L.map (resolve_var st) vs)
  | Nft_ast.Vset vs -> Nft_ast.Vset (L.map (resolve_var st) vs)
  | _ -> v

let lower_verdict : Nft_ast.verdict -> Verdict.verdict = function
  | Nft_ast.SVaccept -> Verdict.Accept
  | Nft_ast.SVdrop -> Verdict.Drop
  | Nft_ast.SVcontinue -> Verdict.Continue
  | Nft_ast.SVreturn -> Verdict.Return
  | Nft_ast.SVjump n -> Verdict.Jump n
  | Nft_ast.SVgoto n -> Verdict.Goto n
  | Nft_ast.SVqueue -> Verdict.Queue (0, 0, false, false)
  | Nft_ast.SVreject _ -> Verdict.Reject (0, 0)

(* ---------- element encoding (single field & declared concat type) ---------- *)

(* encode a value into one interval [lo,hi] for a single-field set *)
let interval_of_value st (k : kind) (v : Nft_ast.value) : Bytes.data * Bytes.data =
  match resolve_var st v with
  | Nft_ast.Vrange (a, b) -> (enc_atom k a, enc_atom k b)
  | Nft_ast.Vprefix (Nft_ast.Vip4 b, len) ->
      let w = width_of_kind k in let mask = prefix_mask w len in
      let net = band b mask in
      let bcast = L.map2 (fun n m -> n lor (m lxor 0xff)) net mask in
      (net, bcast)
  | v' -> let b = enc_atom k v' in (b, b)

(* byte width / encoder for a declared set TYPE atom (e.g. `ipv4_addr . ifname`) *)
let bytes_of_typeatom st (atom : string) (v : Nft_ast.value) : Bytes.data =
  let v = resolve_var st v in
  match atom with
  | "ipv4_addr"    -> enc_atom KIp4 v
  | "ipv6_addr"    -> enc_atom KIp6 v
  | "ifname" | "iface_index" -> enc_atom KIfname v
  | "inet_service" -> enc_atom KPort v
  | "inet_proto"   -> enc_atom KL4proto v
  | "ether_addr"   -> enc_atom (KNum 6) v
  | "mark"         -> enc_atom KMark v
  | _ -> raise (Unsupported ("set element type: " ^ atom))

(* encode one declared-set element (possibly a concatenation) to an interval *)
let interval_of_decl_elem st (types : string list) (v : Nft_ast.value)
    : Bytes.data * Bytes.data =
  match types, resolve_var st v with
  | [t], v' ->
      (* single-typed: allow range / prefix on ipv4 *)
      (match v' with
       | Nft_ast.Vrange (a, b) -> (bytes_of_typeatom st t a, bytes_of_typeatom st t b)
       | Nft_ast.Vprefix _ when t = "ipv4_addr" -> interval_of_value st KIp4 v'
       | _ -> let b = bytes_of_typeatom st t v' in (b, b))
  | _, Nft_ast.Vconcat vs when L.length vs = L.length types ->
      let b = L.concat (L.map2 (bytes_of_typeatom st) types vs) in (b, b)
  | _ -> raise (Unsupported "set element arity does not match declared type")

(* ---------- match lowering ---------- *)

(* build the anonymous-set env entry for an inline `{...}` set over a single
   field kind, returning its fresh name *)
let intern_anon_set st (k : kind) (elems : Nft_ast.value list) : string =
  let name = fresh st "__set" in
  st.sets <- (name, L.map (interval_of_value st k) elems) :: st.sets;
  name

(* build the anonymous-set env entry for a CONCATENATED inline set, where each
   element is a Vconcat matched against [kinds] *)
let intern_anon_concat st (kinds : kind list) (elems : Nft_ast.value list) : string =
  let name = fresh st "__set" in
  let enc1 v = match resolve_var st v with
    | Nft_ast.Vconcat vs when L.length vs = L.length kinds ->
        let b = L.concat (L.map2 enc_atom kinds vs) in (b, b)
    | _ -> raise (Unsupported "concatenated set element arity mismatch") in
  st.sets <- (name, L.map enc1 elems) :: st.sets;
  name

(* lower a single match clause into body items (the l4proto dep is handled by the
   caller via the returned dep) *)
let lower_match st (m : Nft_ast.smatch) : Bytes.data option * Syntax.matchcond =
  let neg = m.Nft_ast.m_rhs.Nft_ast.neg in
  match m.Nft_ast.m_keys with
  | [kp] ->
      let (f, k, dep) = key_field kp in
      let mc = match m.Nft_ast.m_rhs.Nft_ast.payload with
        | Nft_ast.SEref name -> Syntax.MConcatSet ([f], neg, name)
        | Nft_ast.SEset elems -> Syntax.MConcatSet ([f], neg, intern_anon_set st k elems)
        | Nft_ast.SEvalue v ->
            (match resolve_var st v with
             | Nft_ast.Vrange (a, b) -> Syntax.MRange (f, neg, enc_atom k a, enc_atom k b)
             | Nft_ast.Vprefix (Nft_ast.Vip4 bs, len) ->
                 let w = width_of_kind k in let mask = prefix_mask w len in
                 Syntax.MMasked (f, neg, mask, L.init w (fun _ -> 0), band bs mask)
             | Nft_ast.Vset elems ->        (* a `$var` that expands to a set *)
                 Syntax.MConcatSet ([f], neg, intern_anon_set st k elems)
             | v' -> if neg then Syntax.MNeq (f, enc_atom k v')
                     else Syntax.MEq (f, enc_atom k v'))
      in (dep, mc)
  | kps ->
      (* concatenation: ip daddr . oifname [!=] @set / {set} *)
      let triples = L.map key_field kps in
      let fields = L.map (fun (f,_,_) -> f) triples in
      let kinds  = L.map (fun (_,k,_) -> k) triples in
      let dep = L.fold_left (fun acc (_,_,d) -> match acc with Some _ -> acc | None -> d)
                  None triples in
      let name = match m.Nft_ast.m_rhs.Nft_ast.payload with
        | Nft_ast.SEref nm -> nm
        | Nft_ast.SEset elems -> intern_anon_concat st kinds elems
        | Nft_ast.SEvalue (Nft_ast.Vconcat _ as v) -> intern_anon_concat st kinds [v]
        | Nft_ast.SEvalue _ -> raise (Unsupported "concatenated match needs a set/ref rhs")
      in (dep, Syntax.MConcatSet (fields, neg, name))

(* meta/ct key from a name (reuses the codec name tables) *)
let meta_key n = match Codec.meta_of_name n with
  | Some k -> k | None -> raise (Unsupported ("meta key: " ^ n))
let ct_key n = match Codec.ct_of_name n with
  | Some k -> k | None -> raise (Unsupported ("ct key: " ^ n))

let lower_stmt st (s : Nft_ast.sstmt) : Syntax.stmt option =
  match s with
  | Nft_ast.StComment _ -> None              (* metadata; no verdict/bytecode effect *)
  | Nft_ast.StCounter -> Some (Syntax.SCounter (0, 0))
  | Nft_ast.StLog opts -> Some (Syntax.SLog opts)
  | Nft_ast.StLimit _ ->
      (* `limit` is a matchcond (MLimit), not a statement; lower_rule intercepts
         StLimit before reaching here, so this is unreachable. *)
      raise (Unsupported "limit handled as a match, not a statement")
  | Nft_ast.StMasquerade | Nft_ast.StSnat _ | Nft_ast.StDnat _ ->
      (* terminal NAT: the single-packet model treats it as a terminal Accept *)
      None
  | Nft_ast.StMetaSet (k, v) ->
      Some (Syntax.SMetaSet (meta_key k, Syntax.VImm (enc_atom KMark (resolve_var st v))))
  | Nft_ast.StCtSet (k, v) ->
      Some (Syntax.SCtSet (ct_key k, Syntax.VImm (enc_atom KMark (resolve_var st v))))

(* does a statement force a terminal Accept (NAT)? *)
let stmt_is_terminal_accept = function
  | Nft_ast.StMasquerade | Nft_ast.StSnat _ | Nft_ast.StDnat _ -> true | _ -> false

let limit_spec rate unit_ : Packet.limit_spec =
  let u = match unit_ with
    | "second"->0 | "minute"->1 | "hour"->2 | "day"->3 | "week"->4
    | _ -> raise (Unsupported ("limit unit " ^ unit_)) in
  { Packet.ls_rate = rate; ls_unit = u; ls_burst = 5; ls_bytes = false; ls_flags = 0 }

(* a `masquerade` NAT spec: source-NAT to the exit interface's address *)
let masq_spec : Syntax.nat_spec =
  { Syntax.nat_imms = []; nat_field = None; nat_map = None; nat_src = None;
    nat_kind = "masq"; nat_family = ""; nat_amin = None; nat_amax = None;
    nat_pmin = None; nat_pmax = None; nat_flags = 0 }

(* an `snat to <ip>` / `dnat to <ip>` NAT spec: the target address goes into
   register 1 (= NFTNL_EXPR_NAT_REG_ADDR_MIN), which the kernel nft_nat applies
   as NF_NAT_MANIP_SRC / NF_NAT_MANIP_DST.  Only an explicit IPv4 literal target
   is modelled here; anything else (map/field/port-only) stays a bare terminal
   Accept (nat = None) as before. *)
let addr_nat_spec st kind (v : Nft_ast.value) : Syntax.nat_spec option =
  match (try resolve_var st v with Unsupported _ -> v) with
  | Nft_ast.Vip4 b ->
      Some { Syntax.nat_imms = [(1, b)]; nat_field = None; nat_map = None;
             nat_src = None; nat_kind = kind; nat_family = "ip";
             nat_amin = None; nat_amax = None; nat_pmin = None; nat_pmax = None;
             nat_flags = 0 }
  | _ -> None   (* unresolvable / non-literal target: stay a bare terminal Accept *)

let lower_rule st (clauses : Nft_ast.clause list) : Syntax.rule =
  let body = ref [] in
  let deps = ref [] in
  let verdict = ref Verdict.Continue in
  let vmap = ref None in
  let nat = ref None in   (* set for `masquerade` (a source-NAT terminal) *)
  let push bi = body := bi :: !body in
  let ensure_dep = function
    | None -> ()
    | Some pv -> if not (L.mem pv !deps) then
        (push (Syntax.BMatch (Syntax.MEq (Syntax.FMetaL4proto, pv))); deps := pv :: !deps)
  in
  L.iter (fun (cl : Nft_ast.clause) ->
    match cl with
    | Nft_ast.CVerdict v -> verdict := lower_verdict v
    | Nft_ast.CMatch m ->
        let (dep, mc) = lower_match st m in
        ensure_dep dep; push (Syntax.BMatch mc)
    | Nft_ast.CVmap (kp, entries) ->
        if !vmap <> None then raise (Unsupported "more than one verdict map in a rule");
        let (f, k, dep) = key_field kp in ensure_dep dep;
        let name = fresh st "__map" in
        let ents = L.map (fun (v, sv) ->
          (enc_atom k (resolve_var st v), lower_verdict sv)) entries in
        st.vmaps <- (name, ents) :: st.vmaps;
        vmap := Some { Syntax.vm_fields = []; vm_keyf = Some (f, []); vm_name = name }
    | Nft_ast.CVmapRef (kp, name) ->
        (* `<key> vmap @name`: entries come from the named map declared in the env *)
        if !vmap <> None then raise (Unsupported "more than one verdict map in a rule");
        let (f, _, dep) = key_field kp in ensure_dep dep;
        vmap := Some { Syntax.vm_fields = []; vm_keyf = Some (f, []); vm_name = name }
    | Nft_ast.CStmt (Nft_ast.StLimit (r, u)) ->
        push (Syntax.BMatch (Syntax.MLimit (limit_spec r u)))
    | Nft_ast.CStmt s ->
        if stmt_is_terminal_accept s then verdict := Verdict.Accept;
        (match s with
         | Nft_ast.StMasquerade -> nat := Some masq_spec
         | Nft_ast.StSnat (Some v) -> nat := addr_nat_spec st "snat" v
         | Nft_ast.StDnat (Some v) -> nat := addr_nat_spec st "dnat" v
         | _ -> ());
        (match lower_stmt st s with Some st' -> push (Syntax.BStmt st') | None -> ()))
    clauses;
  { Syntax.r_body = L.rev !body; r_verdict = !verdict; r_vmap = !vmap;
    r_nat = !nat; r_tproxy = None; r_fwd = None; r_queue = None; r_after = [] }

(* ---------- declarations ---------- *)

let lower_setdecl st (sd : Nft_ast.setdecl) : unit =
  if sd.Nft_ast.sd_is_map then begin
    (* a verdict map if its elements carry verdict data; an empty declaration is
       registered as an empty value map (its contents arrive at runtime) *)
    let is_vmap = L.exists (fun (_, d) -> match d with
      | Some _ -> true | None -> false) sd.Nft_ast.sd_elements in
    if is_vmap then
      let ents = L.map (fun (key, d) ->
        let (lo, _) = interval_of_decl_elem st sd.Nft_ast.sd_type key in
        (lo, match d with Some v -> lower_verdict v | None -> Verdict.Continue))
        sd.Nft_ast.sd_elements in
      st.vmaps <- (sd.Nft_ast.sd_name, ents) :: st.vmaps
    else if sd.Nft_ast.sd_elements = [] then
      st.maps <- (sd.Nft_ast.sd_name, []) :: st.maps
    else raise (Unsupported "value maps (non-verdict map data) not yet lowered")
  end else begin
    let elems = L.map (fun (v, _) -> interval_of_decl_elem st sd.Nft_ast.sd_type v)
                  sd.Nft_ast.sd_elements in
    st.sets <- (sd.Nft_ast.sd_name, elems) :: st.sets
  end

let lower_chain st (sc : Nft_ast.schain) : string * Syntax.chain =
  let is_base = L.exists (function Nft_ast.ITypeHook _ -> true | _ -> false)
                  sc.Nft_ast.sc_items in
  let policy = ref None and rules = ref [] in
  L.iter (function
    | Nft_ast.ITypeHook _ -> ()
    | Nft_ast.IPolicy v -> policy := Some (lower_verdict v)
    | Nft_ast.IRule cls -> rules := lower_rule st cls :: !rules)
    sc.Nft_ast.sc_items;
  let c_policy = match !policy with
    | Some v -> v | None -> if is_base then Verdict.Accept else Verdict.Continue in
  (sc.Nft_ast.sc_name, { Syntax.c_policy; c_rules = L.rev !rules })

(* ---------- top level ---------- *)

type parsed = {
  p_tables : (string * string * (string * Syntax.chain) list) list;
  p_env    : Packet.env;
  (* the raw declared/anonymous set & map contents, so a Coq emitter can
     serialise them as a [set_decls] record (the env is then [env_with_sets]) *)
  p_sets   : (string * (Bytes.data * Bytes.data) list) list;
  p_vmaps  : (string * (Bytes.data * Verdict.verdict) list) list;
  p_maps   : (string * (Bytes.data * Bytes.data) list) list;
}

let build_env st : Packet.env =
  let sets = st.sets and vmaps = st.vmaps and maps = st.maps in
  { Packet.e_set  = (fun n -> match L.assoc_opt n sets  with Some e -> e | None -> []);
    e_vmap        = (fun n -> match L.assoc_opt n vmaps with Some e -> e | None -> []);
    e_map         = (fun n -> match L.assoc_opt n maps  with Some e -> e | None -> []);
    e_routes = []; e_rt = (fun _ -> []); e_ifaddr = (fun _ -> []);
    e_limit = (fun _ -> 1); e_quota = (fun _ -> 1); e_connlimit = (fun _ -> 1) }

let lower (f : Nft_ast.sfile) : parsed =
  let st = { defines = Hashtbl.create 16; sets = []; vmaps = []; maps = [];
             counter = 0 } in
  (* pass 1: collect defines *)
  L.iter (function Nft_ast.TopDefine (n, v) -> Hashtbl.replace st.defines n v | _ -> ()) f;
  (* pass 2: declarations (sets/maps) must exist before chains reference them *)
  L.iter (function
    | Nft_ast.TopTable t ->
        L.iter (function Nft_ast.TSet sd -> lower_setdecl st sd | _ -> ()) t.Nft_ast.st_items
    | _ -> ()) f;
  (* pass 3: chains *)
  let tables = L.filter_map (function
    | Nft_ast.TopTable t ->
        let chains = L.filter_map (function
          | Nft_ast.TChain sc -> Some (lower_chain st sc)
          | Nft_ast.TSet _ | Nft_ast.TObj _ -> None) t.Nft_ast.st_items in
        Some (t.Nft_ast.st_family, t.Nft_ast.st_name, chains)
    | _ -> None) f
  in
  { p_tables = tables; p_env = build_env st;
    p_sets = L.rev st.sets; p_vmaps = L.rev st.vmaps; p_maps = L.rev st.maps }

(* ---------- lookups ---------- *)

let find_table p name = L.find_opt (fun (_, n, _) -> n = name) p.p_tables
let chains_of p ~table = match find_table p table with
  | Some (_, _, chains) -> chains
  | None -> raise (Unsupported ("no such table: " ^ table))
let find_chain p ~table ~chain = match L.assoc_opt chain (chains_of p ~table) with
  | Some c -> c
  | None -> raise (Unsupported (Printf.sprintf "no chain %s in table %s" chain table))
