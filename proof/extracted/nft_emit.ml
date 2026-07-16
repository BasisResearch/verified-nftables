(* Nft_emit: serialise a parsed ruleset (Nft_inject.parsed) back into Coq source.

   This is the bridge that makes the parser *useful for proving*: instead of
   hand-translating a `.nft` file into the Syntax AST inside a `.v` file (which
   would leave "the AST mirrors the text" eyeballed and untrusted), the parser
   EMITS the AST as Coq `Definition`s, and the proof `Require Import`s the
   generated file and proves properties about *that* term.  So the thing proved
   IS the parser's output — there is no hand step between text and theorem.

   The emitter is untrusted glue (like the renderer); the generated `.v` is
   checked by the Rocq kernel, and every property proved of it transports to the
   installed bytecode via compile_table_correct.  Constructors the lowering never
   produces raise [Unsupported] rather than emitting something unchecked.
   See TODO 9 in ../DEVELOPMENT.md. *)

module L = Stdlib.List
module S = Stdlib.String
let spf = Printf.sprintf
exception Unsupported of string

(* ---------- leaves ---------- *)

let bool b = if b then "true" else "false"

let data (d : Bytes.data) : string =
  "[" ^ S.concat "; " (L.map string_of_int d) ^ "]"

let qstring (s : string) : string =
  let b = Buffer.create (S.length s + 2) in
  Buffer.add_char b '"';
  S.iter (fun c -> if c = '"' || c = '\\' then Buffer.add_char b '\\';
                   Buffer.add_char b c) s;
  Buffer.add_char b '"'; Buffer.contents b

let verdict (v : Verdict.verdict) : string =
  match v with
  | Verdict.Accept -> "Accept" | Verdict.Drop -> "Drop"
  | Verdict.Continue -> "Continue" | Verdict.Return -> "Return"
  | Verdict.Reject (t, c) -> spf "(Reject %d %d)" t c
  | Verdict.Queue (lo, hi, byp, fan) -> spf "(Queue %d %d %s %s)" lo hi (bool byp) (bool fan)
  | Verdict.Jump n -> spf "(Jump %s)" (qstring n)
  | Verdict.Goto n -> spf "(Goto %s)" (qstring n)

(* meta/ct keys: emit the Coq constructor name (= the extracted OCaml one) *)
let meta_key (k : Packet.meta_key) : string = match k with
  | Packet.MKl4proto->"MKl4proto" | Packet.MKnfproto->"MKnfproto"
  | Packet.MKprotocol->"MKprotocol" | Packet.MKmark->"MKmark"
  | Packet.MKiif->"MKiif" | Packet.MKoif->"MKoif"
  | Packet.MKiiftype->"MKiiftype" | Packet.MKoiftype->"MKoiftype"
  | Packet.MKiifname->"MKiifname" | Packet.MKoifname->"MKoifname"
  | Packet.MKlen->"MKlen" | Packet.MKpkttype->"MKpkttype" | Packet.MKcpu->"MKcpu"
  | Packet.MKskuid->"MKskuid" | Packet.MKskgid->"MKskgid"
  | Packet.MKpriority->"MKpriority" | Packet.MKcgroup->"MKcgroup"
  | Packet.MKday->"MKday" | Packet.MKhour->"MKhour"
  | Packet.MKiifgroup->"MKiifgroup" | Packet.MKoifgroup->"MKoifgroup"
  | Packet.MKprandom->"MKprandom" | Packet.MKrtclassid->"MKrtclassid"
  | Packet.MKsdif->"MKsdif" | Packet.MKsdifname->"MKsdifname"
  | Packet.MKsecpath->"MKsecpath" | Packet.MKtime->"MKtime"
  | Packet.MKbri_iifname->"MKbri_iifname" | Packet.MKbri_oifname->"MKbri_oifname"
  | Packet.MKbri_iifpvid->"MKbri_iifpvid" | Packet.MKbri_iifvproto->"MKbri_iifvproto"
  | Packet.MKibrhwaddr->"MKibrhwaddr" | Packet.MKbroute->"MKbroute"

let ct_key (k : Packet.ct_key) : string = match k with
  | Packet.CKstate->"CKstate" | Packet.CKstatus->"CKstatus" | Packet.CKmark->"CKmark"
  | Packet.CKdirection->"CKdirection" | Packet.CKexpiration->"CKexpiration"
  | Packet.CKid->"CKid" | Packet.CKavgpkt->"CKavgpkt" | Packet.CKbytes->"CKbytes"
  | Packet.CKhelper->"CKhelper" | Packet.CKl3proto->"CKl3proto" | Packet.CKlabel->"CKlabel"
  | Packet.CKpackets->"CKpackets" | Packet.CKproto->"CKproto" | Packet.CKzone->"CKzone"
  | Packet.CKevent->"CKevent"

let rec field (f : Syntax.field) : string = match f with
  | Syntax.FMetaL4proto->"FMetaL4proto" | Syntax.FMetaNfproto->"FMetaNfproto"
  | Syntax.FMetaProtocol->"FMetaProtocol" | Syntax.FMetaMark->"FMetaMark"
  | Syntax.FMetaIif->"FMetaIif" | Syntax.FMetaOif->"FMetaOif"
  | Syntax.FMetaIiftype->"FMetaIiftype" | Syntax.FMetaOiftype->"FMetaOiftype"
  | Syntax.FMetaIifname->"FMetaIifname" | Syntax.FMetaOifname->"FMetaOifname"
  | Syntax.FMetaLen->"FMetaLen" | Syntax.FMetaPkttype->"FMetaPkttype"
  | Syntax.FMetaCpu->"FMetaCpu" | Syntax.FMetaSkuid->"FMetaSkuid"
  | Syntax.FMetaSkgid->"FMetaSkgid" | Syntax.FMetaPriority->"FMetaPriority"
  | Syntax.FCtState->"FCtState" | Syntax.FCtStatus->"FCtStatus"
  | Syntax.FCtMark->"FCtMark" | Syntax.FCtDirection->"FCtDirection"
  | Syntax.FCtExpiration->"FCtExpiration" | Syntax.FCtId->"FCtId"
  | Syntax.FEtherDaddr->"FEtherDaddr" | Syntax.FEtherSaddr->"FEtherSaddr"
  | Syntax.FEtherType->"FEtherType" | Syntax.FLinkVlan->"FLinkVlan"
  | Syntax.FIp4VerHdrlen->"FIp4VerHdrlen" | Syntax.FIp4Word0->"FIp4Word0"
  | Syntax.FIp4Tos->"FIp4Tos" | Syntax.FIp4Totlen->"FIp4Totlen"
  | Syntax.FIp4Id->"FIp4Id" | Syntax.FIp4FragOff->"FIp4FragOff"
  | Syntax.FIp4Ttl->"FIp4Ttl" | Syntax.FIp4Protocol->"FIp4Protocol"
  | Syntax.FIp4Csum->"FIp4Csum" | Syntax.FIp4Saddr->"FIp4Saddr"
  | Syntax.FIp4Daddr->"FIp4Daddr" | Syntax.FIp6Saddr->"FIp6Saddr"
  | Syntax.FIp6Daddr->"FIp6Daddr" | Syntax.FThSport->"FThSport"
  | Syntax.FThDport->"FThDport" | Syntax.FTcpSeq->"FTcpSeq" | Syntax.FTcpAck->"FTcpAck"
  | Syntax.FTcpFlags->"FTcpFlags" | Syntax.FUdpLen->"FUdpLen" | Syntax.FUdpCsum->"FUdpCsum"
  | Syntax.FIcmpType->"FIcmpType" | Syntax.FIcmpCode->"FIcmpCode"
  | Syntax.FMetaGen k -> spf "(FMetaGen %s)" (meta_key k)
  | Syntax.FCtGen k -> spf "(FCtGen %s)" (ct_key k)
  | Syntax.FFib (sel, res) -> spf "(FFib %s %s)" (qstring sel) (fib_result res)
  (* raw payload slice: byte-aligned address prefixes (`ip saddr a.b.c.0/24`
     -> FPayload PNetwork 12 3) and the ip6/tcp/igmp raw header fields *)
  | Syntax.FPayload (b, off, len) -> spf "(FPayload %s %d %d)" (pbase b) off len
  | _ -> raise (Unsupported "field constructor not emittable (extend nft_emit.field)")

and pbase (b : Packet.pbase) : string = match b with
  | Packet.PLink -> "PLink" | Packet.PNetwork -> "PNetwork"
  | Packet.PTransport -> "PTransport"

and fib_result (r : Packet.fib_result) : string = match r with
  | Packet.FRoif -> "FRoif" | Packet.FRoifname -> "FRoifname"
  | Packet.FRtype -> "FRtype" | Packet.FRpresent -> "FRpresent"

let field_list (fs : Syntax.field list) : string =
  "[" ^ S.concat "; " (L.map field fs) ^ "]"

let transform (t : Syntax.transform) : string = match t with
  | Syntax.TBitAnd (m, x) -> spf "(TBitAnd %s %s)" (data m) (data x)
  | Syntax.TShift (shl, n) -> spf "(TShift %s %d)" (bool shl) n
  | Syntax.TByteorder (h, s, l) -> spf "(TByteorder %s %d %d)" (bool h) s l
  | Syntax.TJhash (l, s, m, o) -> spf "(TJhash %d %d %d %d)" l s m o
let transform_list ts = "[" ^ S.concat "; " (L.map transform ts) ^ "]"

let vsrc (v : Syntax.vsrc) : string = match v with
  | Syntax.VImm d -> spf "(VImm %s)" (data d)
  | _ -> raise (Unsupported "vsrc constructor not emittable (extend nft_emit.vsrc)")

let limit_spec (s : Packet.limit_spec) : string =
  spf "{| ls_rate := %d; ls_unit := %d; ls_burst := %d; ls_bytes := %s; ls_flags := %d |}"
    s.Packet.ls_rate s.Packet.ls_unit s.Packet.ls_burst (bool s.Packet.ls_bytes)
    s.Packet.ls_flags

(* ---------- typed values / typed matches (the Elab layer) ---------- *)

let n_int (n : BinNums.coq_N) : int = BinNat.N.to_nat n

let printable (c : int) = c >= 0x20 && c < 0x7f && c <> Char.code '"' && c <> Char.code '\\'

let nftval (v : Nftval.nftval) : string = match v with
  | Nftval.VInteger (w, n) -> spf "(VInteger %d %d)" w (n_int n)
  | Nftval.VIpv4 [a;b;c;d] -> spf "(ip4 %d %d %d %d)" a b c d
  | Nftval.VIpv4 b -> spf "(VIpv4 %s)" (data b)
  | Nftval.VIpv6 b -> spf "(VIpv6 %s)" (data b)
  | Nftval.VIfname s when
      (* a full 16-byte NUL-padded printable name prints via the smart ctor *)
      L.length s = 16 &&
      (let rec split acc = function
         | 0 :: rest -> L.for_all (fun c -> c = 0) rest && acc <> []
         | c :: rest -> printable c && split (c :: acc) rest
         | [] -> false
       in split [] s) ->
      let name = S.init (L.length (L.filter (fun c -> c <> 0) s))
                   (fun i -> Char.chr (L.nth s i)) in
      spf "(ifname %s)" (qstring name)
  | Nftval.VIfname s -> spf "(VIfname %s)" (data s)
  | Nftval.VPort n -> spf "(VPort %d)" (n_int n)
  | Nftval.VEther b -> spf "(VEther %s)" (data b)
  | Nftval.VVerdict n -> spf "(VVerdict %d)" (n_int n)
  | Nftval.VCtState n -> spf "(VCtState %d)" (n_int n)
  | Nftval.VFibType n -> spf "(VFibType %d)" (n_int n)
  | Nftval.VHostInt (w, n) -> spf "(VHostInt %d %d)" w (n_int n)

let cmpop (op : Bytecode.cmpop) : string = match op with
  | Bytecode.CEq -> "CEq" | Bytecode.CNe -> "CNe" | Bytecode.CLt -> "CLt"
  | Bytecode.CGt -> "CGt" | Bytecode.CLe -> "CLe" | Bytecode.CGe -> "CGe"

let matchcond (m : Syntax.matchcond) : string = match m with
  | Syntax.MEq (f, v) -> spf "(MEq %s %s)" (field f) (data v)
  | Syntax.MNeq (f, v) -> spf "(MNeq %s %s)" (field f) (data v)
  | Syntax.MRange (f, neg, lo, hi) ->
      spf "(MRange %s %s %s %s)" (field f) (bool neg) (data lo) (data hi)
  (* the implicit-bitmask idiom prints as its derived form [MFlagsSet]:
     (field & bits) <> 0 with an all-zero xor/cmp operand of the mask's width *)
  | Syntax.MMasked (f, Bytecode.CNe, mask, xor, v)
    when xor = Stdlib.List.init (Stdlib.List.length mask) (fun _ -> 0)
      && v = xor ->
      spf "(MFlagsSet %s %s)" (field f) (data mask)
  | Syntax.MMasked (f, op, mask, xor, v) ->
      spf "(MMasked %s %s %s %s %s)" (field f) (cmpop op) (data mask) (data xor) (data v)
  | Syntax.MConcatSet (fs, neg, name) ->
      spf "(MConcatSet %s %s %s)" (field_list fs) (bool neg) (qstring name)
  | Syntax.MSetT (f, ts, neg, name) ->
      spf "(MSetT %s %s %s %s)" (field f) (transform_list ts) (bool neg) (qstring name)
  | Syntax.MRangeT (f, ts, neg, lo, hi) ->
      spf "(MRangeT %s %s %s %s %s)"
        (field f) (transform_list ts) (bool neg) (data lo) (data hi)
  | Syntax.MLimit s -> spf "(MLimit %s)" (limit_spec s)
  | _ -> raise (Unsupported "matchcond constructor not emittable (extend nft_emit.matchcond)")

let stmt (s : Syntax.stmt) : string = match s with
  | Syntax.SCounter (p, b) -> spf "(SCounter %d %d)" p b
  | Syntax.SLog opts -> spf "(SLog %s)" (qstring opts)
  | Syntax.SMetaSet (k, vs) -> spf "(SMetaSet %s %s)" (meta_key k) (vsrc vs)
  | Syntax.SCtSet (k, vs) -> spf "(SCtSet %s %s)" (ct_key k) (vsrc vs)
  | _ -> raise (Unsupported "stmt constructor not emittable (extend nft_emit.stmt)")

let tmatch (tm : Elab.tmatch) : string = match tm with
  | Elab.TMEq (f, v) -> spf "TMEq %s %s" (field f) (nftval v)
  | Elab.TMNeq (f, v) -> spf "TMNeq %s %s" (field f) (nftval v)
  | Elab.MPrefix (f, op, v, plen) ->
      spf "MPrefix %s %s %s %d" (field f) (cmpop op) (nftval v) plen
  | Elab.MWildcard (f, prefix) -> spf "MWildcard %s %s" (field f) (data prefix)

(* a typed-representable match prints as its typed source under the VERIFIED
   elaboration [elab_m]; a synthesized protocol-dependency guard is tagged
   [BDep] (a definitional alias of [BMatch]) *)
let match_str (m : Syntax.matchcond) : string =
  match Nft_inject.typed_of m with
  | Some tm -> spf "(elab_m (%s))" (tmatch tm)
  | None -> matchcond m

let body_item (b : Syntax.body_item) : string = match b with
  | Syntax.BMatch m ->
      spf "(%s %s)" (if Nft_inject.is_dep m then "BDep" else "BMatch") (match_str m)
  | Syntax.BStmt s -> spf "(BStmt %s)" (stmt s)

let vmap_spec (vm : Syntax.vmap_spec) : string =
  let keyf = match vm.Syntax.vm_keyf with
    | None -> "None"
    | Some (f, ts) -> spf "(Some (%s, %s))" (field f) (transform_list ts) in
  spf "{| vm_fields := %s; vm_keyf := %s; vm_name := %s |}"
    (field_list vm.Syntax.vm_fields) keyf (qstring vm.Syntax.vm_name)

let opt_int = function None -> "None" | Some n -> spf "(Some %d)" n

let nat_2nd_str (e : Syntax.nat_2nd) : string =
  match e with
  | Syntax.NXnone -> "NXnone"
  | Syntax.NXimm (amax, pmin, pmax) ->
      let od = function Some v -> spf "(Some %s)" (data v) | None -> "None" in
      spf "(NXimm %s %s %s)" (od amax) (od pmin) (od pmax)
  | Syntax.NXmap_addr_max -> "NXmap_addr_max"
  | Syntax.NXmap_port -> "NXmap_port"
  | Syntax.NXmap_full -> "NXmap_full"

let nat_op (k : Bytecode.nat_op) : string = match k with
  | Bytecode.NKsnat -> "NKsnat" | Bytecode.NKdnat -> "NKdnat"
  | Bytecode.NKmasq -> "NKmasq" | Bytecode.NKredir -> "NKredir"
let nat_af (f : Bytecode.nat_af) : string = match f with
  | Bytecode.NFip4 -> "NFip4" | Bytecode.NFip6 -> "NFip6" | Bytecode.NFinet -> "NFinet"

let nat_spec (ns : Syntax.nat_spec) : string =
  (* the lowering produces `masquerade` (no operand) and immediate-address/port
     `snat`/`dnat to <ipv4>[:<port>]` (register-free: nat_addr_imm / nat_extra).
     Field/map/src-sourced NAT operands are not produced by the lowering. *)
  (match ns.Syntax.nat_field, ns.Syntax.nat_map, ns.Syntax.nat_src with
   | None, None, None -> ()
   | _ -> raise (Unsupported "nat operand emission (extend nft_emit.nat_spec)"));
  ignore opt_int;
  spf "{| nat_addr_imm := %s; nat_field := None; nat_map := None; nat_src := None; nat_extra := %s; nat_kind := %s; nat_family := %s; nat_flags := %d |}"
    (match ns.Syntax.nat_addr_imm with Some v -> spf "(Some %s)" (data v) | None -> "None")
    (nat_2nd_str ns.Syntax.nat_extra)
    (nat_op ns.Syntax.nat_kind) (nat_af ns.Syntax.nat_family) ns.Syntax.nat_flags

let outcome (o : Syntax.outcome) : string = match o with
  | Syntax.OVerdict v ->
      let vs = verdict v in
      spf "OVerdict %s" (if S.contains vs ' ' && not (S.get vs 0 = '(') then "(" ^ vs ^ ")" else vs)
  | Syntax.ONone -> "ONone"
  | Syntax.OVmap vm -> spf "OVmap %s" (vmap_spec vm)
  | Syntax.OVmapNat (vm, ns) -> spf "OVmapNat %s %s" (vmap_spec vm) (nat_spec ns)
  | Syntax.ONat ns -> spf "ONat %s" (nat_spec ns)
  | Syntax.OTproxy _ | Syntax.OFwd _ | Syntax.OQueue _ ->
      raise (Unsupported "outcome constructor not emittable (extend nft_emit.outcome)")

let rule (r : Syntax.rule) : string =
  let body = "[" ^ S.concat ";\n             " (L.map body_item r.Syntax.r_body) ^ "]" in
  spf "{| r_body := %s;\n     r_outcome := %s; r_after := [] |}"
    body (outcome r.Syntax.r_outcome)

let chain (c : Syntax.chain) : string =
  let rules = "[" ^ S.concat ";\n\n   " (L.map rule c.Syntax.c_rules) ^ "]" in
  spf "{| c_policy := %s;\n   c_rules := %s |}" (verdict c.Syntax.c_policy) rules

(* ---------- set/map declarations -> a set_decls record ---------- *)

(* a set element prints as its source view: a point via [SEl], an interval via
   [SRange] (both definitional aliases of the stored pair, Elab.v) *)
let iv (lo, hi) =
  if lo = hi then spf "(SEl %s)" (data lo)
  else spf "(SRange %s %s)" (data lo) (data hi)
(* a verdict-map entry is an interval KEY [lo,hi] paired with its verdict
   (NFT_SET_INTERVAL | NFT_SET_MAP); emit the Coq triple [(lo, hi, v)] which
   parses as [((lo,hi),v) : data * data * verdict]. *)
let kv ((lo, hi), v) = spf "(%s, %s, %s)" (data lo) (data hi) (verdict v)

let assoc_ivs (l : (string * (Bytes.data * Bytes.data) list) list) : string =
  "[" ^ S.concat ";\n   "
    (L.map (fun (n, ivs) ->
       spf "(%s, [%s])" (qstring n) (S.concat "; " (L.map iv ivs))) l) ^ "]"
let assoc_kvs (l : (string * ((Bytes.data * Bytes.data) * Verdict.verdict) list) list) : string =
  "[" ^ S.concat ";\n   "
    (L.map (fun (n, kvs) ->
       spf "(%s, [%s])" (qstring n) (S.concat "; " (L.map kv kvs))) l) ^ "]"

(* ---------- hook registration ---------- *)

(* map an nftables hook name to the Coq [hook_id] constructor.  Fail loudly on an
   unknown hook so a base chain is never silently dropped from dispatch. *)
let hook_id (h : string) : string = match S.lowercase_ascii h with
  | "prerouting"  -> "Hprerouting"
  | "input"       -> "Hinput"
  | "forward"     -> "Hforward"
  | "output"      -> "Houtput"
  | "postrouting" -> "Hpostrouting"
  | "ingress"     -> "Hingress"
  | other -> raise (Unsupported ("unknown netfilter hook: " ^ other))

(* ---------- whole-file emission ---------- *)

let sanitize (s : string) : string =
  S.map (fun c -> if (c>='a'&&c<='z')||(c>='A'&&c<='Z')||(c>='0'&&c<='9') then c
                  else '_') s

let emit (src_path : string) (p : Nft_inject.parsed) : string =
  let b = Buffer.create 4096 in
  let pr fmt = Printf.ksprintf (Buffer.add_string b) fmt in
  pr "(* AUTO-GENERATED from %s by nft2coq (extracted/nft_emit.ml). DO NOT EDIT.\n" src_path;
  pr "   This is the parser's output as Coq terms: the chains and the set/map\n";
  pr "   declarations their lookups read.  Properties proved about these terms\n";
  pr "   are properties of the parsed ruleset (and, via compile_table_correct, of\n";
  pr "   the installed bytecode). *)\n\n";
  pr "From Stdlib Require Import List String ZArith.\n";
  pr "From Nft Require Import Bytes Verdict Packet Bytecode Syntax Semantics Nftval Elab.\n";
  pr "Import ListNotations.\nOpen Scope string_scope.\n\n";
  (* the declared/anonymous sets & maps *)
  pr "Definition decls : set_decls :=\n  {| sd_sets := %s;\n   sd_vmaps := %s;\n   sd_maps := %s |}.\n\n"
    (assoc_ivs p.Nft_inject.p_sets) (assoc_kvs p.Nft_inject.p_vmaps) (assoc_ivs p.Nft_inject.p_maps);
  pr "Definition base_env : env :=\n";
  pr "  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];\n";
  pr "     e_routes := []; e_rt := fun _ => [];\n";
  pr "     e_ifaddrs := (fun _ => []); e_ifaddrs6 := (fun _ => []);\n";
  pr "     e_limit := fun _ => 0; e_quota := fun _ => 0; e_connlimit := fun _ => [];\n";
  pr "     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.\n\n";
  pr "Definition gen_env : env := env_with_sets base_env decls.\n\n";
  (* each table's chains, then the per-table chain environment *)
  L.iter (fun (fam, tname, chains) ->
    let pfx = sanitize tname in
    pr "(* ===== table %s %s ===== *)\n\n" fam tname;
    L.iter (fun (cname, c) ->
      pr "Definition %s_%s : chain :=\n  %s.\n\n" pfx (sanitize cname) (chain c)) chains;
    pr "Definition %s_chains : list (string * chain) :=\n  [%s].\n\n" pfx
      (S.concat ";\n   "
         (L.map (fun (cname, _) ->
            spf "(%s, %s_%s)" (qstring cname) pfx (sanitize cname)) chains));
    (* hook registration for this table's base chains: emit a [hooked_chain] per
       `type _ hook H priority P` declaration, so dispatch (eval_hook/select_hook)
       runs the PARSER-chosen chain at each hook — not a chain the prover named. *)
    let hooks = match L.find_opt (fun (_, n, _) -> n = tname) p.Nft_inject.p_hooks with
      | Some (_, _, hs) -> hs | None -> [] in
    pr "Definition %s_hooks : list hooked_chain :=\n  [%s].\n\n" pfx
      (S.concat ";\n   "
         (L.map (fun (cname, _ctype, hook, prio) ->
            spf "{| hc_hook := %s; hc_prio := (%d)%%Z; hc_env := %s_chains; hc_base := %s_%s |}"
              (hook_id hook) prio pfx pfx (sanitize cname)) hooks)))
    p.Nft_inject.p_tables;
  Buffer.contents b
