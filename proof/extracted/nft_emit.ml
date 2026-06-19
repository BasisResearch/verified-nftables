(* Nft_emit: serialise a parsed ruleset (Nft_lower.parsed) back into Coq source.

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
  | _ -> raise (Unsupported "field constructor not emittable (extend nft_emit.field)")

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

let matchcond (m : Syntax.matchcond) : string = match m with
  | Syntax.MEq (f, v) -> spf "(MEq %s %s)" (field f) (data v)
  | Syntax.MNeq (f, v) -> spf "(MNeq %s %s)" (field f) (data v)
  | Syntax.MRange (f, neg, lo, hi) ->
      spf "(MRange %s %s %s %s)" (field f) (bool neg) (data lo) (data hi)
  | Syntax.MMasked (f, neg, mask, xor, v) ->
      spf "(MMasked %s %s %s %s %s)" (field f) (bool neg) (data mask) (data xor) (data v)
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

let body_item (b : Syntax.body_item) : string = match b with
  | Syntax.BMatch m -> spf "(BMatch %s)" (matchcond m)
  | Syntax.BStmt s -> spf "(BStmt %s)" (stmt s)

let vmap_spec (vm : Syntax.vmap_spec) : string =
  let keyf = match vm.Syntax.vm_keyf with
    | None -> "None"
    | Some (f, ts) -> spf "(Some (%s, %s))" (field f) (transform_list ts) in
  spf "{| vm_fields := %s; vm_keyf := %s; vm_name := %s |}"
    (field_list vm.Syntax.vm_fields) keyf (qstring vm.Syntax.vm_name)

let opt_int = function None -> "None" | Some n -> spf "(Some %d)" n

let nat_spec (ns : Syntax.nat_spec) : string =
  (* the lowering only produces `masquerade` (no explicit operand); fail loudly if
     a richer NAT operand (snat/dnat address/map/field) ever needs emitting *)
  (match ns.Syntax.nat_field, ns.Syntax.nat_map, ns.Syntax.nat_src, ns.Syntax.nat_imms with
   | None, None, None, [] -> ()
   | _ -> raise (Unsupported "nat operand emission (extend nft_emit.nat_spec)"));
  spf "{| nat_imms := []; nat_field := None; nat_map := None; nat_src := None; nat_kind := %s; nat_family := %s; nat_amin := %s; nat_amax := %s; nat_pmin := %s; nat_pmax := %s; nat_flags := %d |}"
    (qstring ns.Syntax.nat_kind) (qstring ns.Syntax.nat_family)
    (opt_int ns.Syntax.nat_amin) (opt_int ns.Syntax.nat_amax)
    (opt_int ns.Syntax.nat_pmin) (opt_int ns.Syntax.nat_pmax) ns.Syntax.nat_flags

let rule (r : Syntax.rule) : string =
  let vmap = match r.Syntax.r_vmap with
    | None -> "None" | Some vm -> spf "(Some %s)" (vmap_spec vm) in
  let nat = match r.Syntax.r_nat with
    | None -> "None" | Some ns -> spf "(Some %s)" (nat_spec ns) in
  let body = "[" ^ S.concat ";\n             " (L.map body_item r.Syntax.r_body) ^ "]" in
  spf "{| r_body := %s;\n     r_verdict := %s; r_vmap := %s;\n     r_nat := %s; r_tproxy := None; r_fwd := None; r_queue := None; r_after := [] |}"
    body (verdict r.Syntax.r_verdict) vmap nat

let chain (c : Syntax.chain) : string =
  let rules = "[" ^ S.concat ";\n\n   " (L.map rule c.Syntax.c_rules) ^ "]" in
  spf "{| c_policy := %s;\n   c_rules := %s |}" (verdict c.Syntax.c_policy) rules

(* ---------- set/map declarations -> a set_decls record ---------- *)

let iv (lo, hi) = spf "(%s, %s)" (data lo) (data hi)
let kv (k, v) = spf "(%s, %s)" (data k) (verdict v)

let assoc_ivs (l : (string * (Bytes.data * Bytes.data) list) list) : string =
  "[" ^ S.concat ";\n   "
    (L.map (fun (n, ivs) ->
       spf "(%s, [%s])" (qstring n) (S.concat "; " (L.map iv ivs))) l) ^ "]"
let assoc_kvs (l : (string * (Bytes.data * Verdict.verdict) list) list) : string =
  "[" ^ S.concat ";\n   "
    (L.map (fun (n, kvs) ->
       spf "(%s, [%s])" (qstring n) (S.concat "; " (L.map kv kvs))) l) ^ "]"

(* ---------- whole-file emission ---------- *)

let sanitize (s : string) : string =
  S.map (fun c -> if (c>='a'&&c<='z')||(c>='A'&&c<='Z')||(c>='0'&&c<='9') then c
                  else '_') s

let emit (src_path : string) (p : Nft_lower.parsed) : string =
  let b = Buffer.create 4096 in
  let pr fmt = Printf.ksprintf (Buffer.add_string b) fmt in
  pr "(* AUTO-GENERATED from %s by nft2coq (extracted/nft_emit.ml). DO NOT EDIT.\n" src_path;
  pr "   This is the parser's output as Coq terms: the chains and the set/map\n";
  pr "   declarations their lookups read.  Properties proved about these terms\n";
  pr "   are properties of the parsed ruleset (and, via compile_table_correct, of\n";
  pr "   the installed bytecode). *)\n\n";
  pr "From Stdlib Require Import List String.\n";
  pr "From Nft Require Import Bytes Verdict Packet Syntax Semantics.\n";
  pr "Import ListNotations.\nOpen Scope string_scope.\n\n";
  (* the declared/anonymous sets & maps *)
  pr "Definition decls : set_decls :=\n  {| sd_sets := %s;\n   sd_vmaps := %s;\n   sd_maps := %s |}.\n\n"
    (assoc_ivs p.Nft_lower.p_sets) (assoc_kvs p.Nft_lower.p_vmaps) (assoc_ivs p.Nft_lower.p_maps);
  pr "Definition base_env : env :=\n";
  pr "  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];\n";
  pr "     e_routes := []; e_rt := fun _ => [];\n";
  pr "     e_ifaddr := (fun _ => []); e_ifaddr6 := (fun _ => []);\n";
  pr "     e_limit := fun _ => 0; e_quota := fun _ => 0; e_connlimit := fun _ => 0;\n";
  pr "     e_ct := fun _ _ => []; e_nat := fun _ => None |}.\n\n";
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
            spf "(%s, %s_%s)" (qstring cname) pfx (sanitize cname)) chains)))
    p.Nft_lower.p_tables;
  Buffer.contents b
