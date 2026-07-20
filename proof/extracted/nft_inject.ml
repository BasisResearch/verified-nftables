(* Nft_inject: Nft_ast (the Menhir parser's surface tree) -> Ast (the extracted
   Coq surface tree, theories/Surface/Ast.v), PURE STRUCTURAL INJECTION.

   This is the ONLY translation site between the OCaml frontend and the
   verified typed layer, and it is deliberately trivial: constructor ->
   constructor, string -> string (ExtrOcamlNativeString), int -> nat
   (ExtrOcamlNatInt).  NO byte encoding, NO symbol resolution, NO width or
   byteorder decision happens here — those are Coq definitions
   (Surface.Datatype / Surface.Symbols / Surface.Typecheck).

   The two guards are the EXTRACTION SEAM (not typing):
     - negative literals never become a [nat] (the extracted nat is a native
       int whose arithmetic the proofs know nothing about below 0);
     - literals >= 2^40 are rejected, the same bound the `limit` guard
       enforces (see theories/Compiler/Extract.v's ExtrOcamlNatInt note), so
       no extracted nat ARITHMETIC can reach the 63-bit wrap.
   Note the wrap bound is NOT the whole story for a large-but-in-bounds
   literal: a value like `meta mark 0x80000000` (2^31) is well under 2^40 yet
   would overflow the OCaml stack in Coq's O(n) [N.of_nat]/[Pos.of_succ_nat]
   when the verified lowering builds its register value.  [N.of_nat] is
   therefore realised in log(n) at the extraction seam (Extract.v), so every
   literal the parser admits (< 2^40) compiles without a stack overflow.
   A negative base-chain priority (`priority -100`) crosses in SIGN-MAGNITUDE
   form (Ast.ITypeHook's prio_neg flag), so no negative number meets nat. *)

module L = Stdlib.List

exception Inject_error of string

(* the ExtrOcamlNatInt seam bound (= the parser's limit_value bound) *)
let max_nat = 1 lsl 40

let nat (n : int) : int =
  if n < 0 then raise (Inject_error "negative literal at the nat seam");
  if n >= max_nat then
    raise (Inject_error "literal exceeds the extracted-int-safe bound 2^40 \
                         (see theories/Compiler/Extract.v)");
  n

let byte_list (b : int list) : int list = L.map nat b

(* IPv6 literal groups: pure structural injection of the lexer's UN-expanded
   groups onto the Coq [Ast.ip6grp] constructors (int -> nat, octet grouping).
   The big-endian 16-bit split and `::` zero-fill are done in verified Coq
   ([Ast.sip6_bytes], reached from [Lower]); nothing here decides a byte. *)
let ip6grp : Nft_ast.ip6grp -> Ast.ip6grp = function
  | Nft_ast.Ip6_g16 n  -> Ast.G16 (nat n)
  | Nft_ast.Ip6_g4 os  -> Ast.G4 (byte_list os)

let ip6grps (gs : Nft_ast.ip6grp list) : Ast.ip6grp list = L.map ip6grp gs

let rec value : Nft_ast.value -> Ast.svalue = function
  | Nft_ast.Vnum n -> Ast.SVNum (nat n)
  | Nft_ast.Vsym s -> Ast.SVSym s
  | Nft_ast.Vstr s -> Ast.SVStr s
  | Nft_ast.Vip4 b -> Ast.SVIp4 (byte_list b)
  | Nft_ast.Vip6 lit -> Ast.SVIp6 (ip6grps lit.Nft_ast.il_left,
                                   Option.map ip6grps lit.Nft_ast.il_right)
  | Nft_ast.Vmac b -> Ast.SVMac (byte_list b)
  | Nft_ast.Vvar s -> Ast.SVVar s
  | Nft_ast.Vprefix (v, l) -> Ast.SVPrefix (value v, nat l)
  | Nft_ast.Vrange (a, b) -> Ast.SVRange (value a, value b)
  | Nft_ast.Vconcat vs -> Ast.SVConcat (L.map value vs)
  | Nft_ast.Vset vs -> Ast.SVSet (L.map value vs)
  | Nft_ast.Vor vs -> Ast.SVOr (L.map value vs)

let sobjkind : Nft_ast.sobjkind -> Ast.sobjkind = function
  | Nft_ast.OKcounter -> Ast.OKcounter | Nft_ast.OKquota -> Ast.OKquota
  | Nft_ast.OKlimit -> Ast.OKlimit | Nft_ast.OKcthelper -> Ast.OKcthelper
  | Nft_ast.OKcttimeout -> Ast.OKcttimeout | Nft_ast.OKctexpect -> Ast.OKctexpect
  | Nft_ast.OKsecmark -> Ast.OKsecmark | Nft_ast.OKsynproxy -> Ast.OKsynproxy

let verdict : Nft_ast.verdict -> Ast.sverdict = function
  | Nft_ast.SVaccept -> Ast.SVaccept
  | Nft_ast.SVdrop -> Ast.SVdrop
  | Nft_ast.SVcontinue -> Ast.SVcontinue
  | Nft_ast.SVreturn -> Ast.SVreturn
  | Nft_ast.SVjump c -> Ast.SVjump c
  | Nft_ast.SVgoto c -> Ast.SVgoto c
  | Nft_ast.SVqueue (lo, hi, byp, fan) -> Ast.SVqueue (nat lo, nat hi, byp, fan)
  | Nft_ast.SVreject opts -> Ast.SVreject opts

let setexpr : Nft_ast.setexpr -> Ast.ssetexpr = function
  | Nft_ast.SEvalue v -> Ast.SSEvalue (value v)
  | Nft_ast.SEset vs -> Ast.SSEset (L.map value vs)
  | Nft_ast.SElist vs -> Ast.SSElist (L.map value vs)
  | Nft_ast.SEref n -> Ast.SSEref n

let relop : Nft_ast.relop -> Ast.srelop = function
  | Nft_ast.Op_implicit -> Ast.SOpImplicit
  | Nft_ast.Op_eq -> Ast.SOpEq
  | Nft_ast.Op_ne -> Ast.SOpNe
  | Nft_ast.Op_bang -> Ast.SOpBang

let rhs (r : Nft_ast.rhs) : Ast.srhs =
  { Ast.sr_op = relop r.Nft_ast.op;
    sr_neg = r.Nft_ast.neg;
    sr_payload = setexpr r.Nft_ast.payload }

let smatch (m : Nft_ast.smatch) : Ast.smatch =
  { Ast.sm_keys = m.Nft_ast.m_keys; sm_rhs = rhs m.Nft_ast.m_rhs }

let opt_nat : int option -> int option = function
  | None -> None
  | Some n -> Some (nat n)

let stmt : Nft_ast.sstmt -> Ast.sstmt = function
  | Nft_ast.StComment c -> Ast.StComment c
  | Nft_ast.StCounter (p, b) -> Ast.StCounter (nat p, nat b)
  | Nft_ast.StObjref (k, n) -> Ast.StObjref (sobjkind k, n)
  | Nft_ast.StLog opts -> Ast.StLog opts
  | Nft_ast.StLimit (rate, unit_, over, burst, bytes) ->
      Ast.StLimit (nat rate, unit_, over, nat burst, bytes)
  | Nft_ast.StMasquerade fs -> Ast.StMasquerade fs
  | Nft_ast.StSnat (a, p, fs) ->
      Ast.StSnat (Option.map value a, opt_nat p, fs)
  | Nft_ast.StDnat (a, p, fs) ->
      Ast.StDnat (Option.map value a, opt_nat p, fs)
  | Nft_ast.StRedirect (p, fs) -> Ast.StRedirect (opt_nat p, fs)
  | Nft_ast.StTproxy (fam, a, p) ->
      Ast.StTproxy (fam, Option.map value a, opt_nat p)
  | Nft_ast.StMetaSet (k, v) -> Ast.StMetaSet (k, value v)
  | Nft_ast.StCtSet (k, v) -> Ast.StCtSet (k, value v)
  | Nft_ast.StNotrack -> Ast.StNotrack

let clause : Nft_ast.clause -> Ast.sclause = function
  | Nft_ast.CMatch m -> Ast.CMatch (smatch m)
  | Nft_ast.CVmap (keys, entries) ->
      Ast.CVmap (keys, L.map (fun (v, sv) -> (value v, verdict sv)) entries)
  | Nft_ast.CVmapRef (keys, name) -> Ast.CVmapRef (keys, name)
  | Nft_ast.CVerdict v -> Ast.CVerdict (verdict v)
  | Nft_ast.CStmt s -> Ast.CStmt (stmt s)
  | Nft_ast.CObjrefMap (k, keys, entries) ->
      Ast.CObjrefMap (sobjkind k, keys, L.map (fun (v, n) -> (value v, n)) entries)
  | Nft_ast.CBitmatch (kp, op, mask, r) ->
      Ast.CBitmatch (kp, op, value mask, rhs r)

let setdecl (sd : Nft_ast.setdecl) : Ast.ssetdecl =
  { Ast.sd_name = sd.Nft_ast.sd_name;
    sd_is_map = sd.Nft_ast.sd_is_map;
    sd_type = sd.Nft_ast.sd_type;
    sd_flags = sd.Nft_ast.sd_flags;
    sd_elements =
      L.map (fun (v, d) -> (value v, Option.map verdict d))
        sd.Nft_ast.sd_elements }

let chain_item : Nft_ast.chain_item -> Ast.schain_item = function
  | Nft_ast.ITypeHook { ct_type; hook; priority } ->
      (* sign-magnitude across the nat seam: -100 -> (true, 100) *)
      if priority < 0 then Ast.ITypeHook (ct_type, hook, true, nat (- priority))
      else Ast.ITypeHook (ct_type, hook, false, nat priority)
  | Nft_ast.IPolicy v -> Ast.IPolicy (verdict v)
  | Nft_ast.IRule r -> Ast.IRule (L.map clause r)

let chain (sc : Nft_ast.schain) : Ast.schain =
  { Ast.sc_name = sc.Nft_ast.sc_name;
    sc_items = L.map chain_item sc.Nft_ast.sc_items }

let table_item : Nft_ast.table_item -> Ast.stable_item = function
  | Nft_ast.TChain c -> Ast.TChain (chain c)
  | Nft_ast.TSet sd -> Ast.TSet (setdecl sd)
  | Nft_ast.TObj (n, k) -> Ast.TObj (n, sobjkind k)

let table (t : Nft_ast.stable) : Ast.stable =
  { Ast.st_family = t.Nft_ast.st_family;
    st_name = t.Nft_ast.st_name;
    st_items = L.map table_item t.Nft_ast.st_items }

let toplevel : Nft_ast.toplevel -> Ast.stoplevel = function
  | Nft_ast.TopDefine (n, v) -> Ast.TopDefine (n, value v)
  | Nft_ast.TopTable t -> Ast.TopTable (table t)
  | Nft_ast.TopInclude p -> Ast.TopInclude p
  | Nft_ast.TopOp _ ->
      (* config-management ops are applied by the driver (Nft_config) BEFORE
         injection; none should survive to here. *)
      raise (Inject_error "internal: unapplied config op reached injection")

(* a whole (include-expanded) surface file *)
let file (f : Nft_ast.sfile) : Ast.sruleset = L.map toplevel f

(* ================================================================== *)
(* M4: the driver glue.  [Nft_inject] is now the ONLY untrusted OCaml
   between the parser and the proofs: pure structural injection (above) +
   the ifindex oracle + a call to the VERIFIED whole-ruleset lowering
   [Lower.lower_ruleset], whose result is unpacked into the [parsed] record
   the emitter / semantic tests consume.  NO byte is composed here. *)

(* ---------- the ifindex oracle (the single host-dependent residue) ----------
   Real nft resolves an interface NAME to a numeric index at LOAD time via
   nft_if_nametoindex() against the live host.  The one kernel invariant known
   without the live table is "lo" = 1 (the first device registered); any other
   name has no faithful static answer, so the oracle DECLINES it and the
   verified lowering then refuses (fail-loud).  This finite map is the sole
   value the OCaml frontend hands the verified lowering; it composes no byte.
   This is the kernel's `nametoindex` lookup, restricted to the one static
   invariant. *)
let ifindex_oracle (s : string) : int option =
  match s with "lo" -> Some 1 | _ -> None

(* the typed-view side channel: which produced matchconds have a typed source
   term ([Typed.txmatch]) and which are synthesized protocol-dependency
   guards.  Both come straight from the verified [lower_ruleset] output —
   this file decides neither. *)
let g_typed : (Syntax.matchcond * Typed.txmatch) list ref = ref []
let g_deps : Syntax.matchcond list ref = ref []
let typed_of (mc : Syntax.matchcond) : Typed.txmatch option = L.assoc_opt mc !g_typed
let is_dep (mc : Syntax.matchcond) : bool = L.mem mc !g_deps

exception Lower_error of string

type parsed = {
  p_tables : (string * string * (string * Syntax.chain) list) list;
  p_hooks  : (string * string * (string * string * string * int) list) list;
  p_env    : Packet.env;
  p_sets   : (string * (Bytes.data * Bytes.data) list) list;
  p_vmaps  : (string * ((Bytes.data * Bytes.data) * Verdict.verdict) list) list;
  p_maps   : (string * (Bytes.data * Bytes.data) list) list;
}

(* the evaluation environment the model looks set/map contents up by name (the
   contents themselves are the verified [lower_ruleset] interning output) *)
let build_env sets vmaps maps : Packet.env =
  { Packet.e_set  = (fun n -> match L.assoc_opt n sets  with Some e -> e | None -> []);
    e_vmap        = (fun n -> match L.assoc_opt n vmaps with Some e -> e | None -> []);
    e_map         = (fun n -> match L.assoc_opt n maps  with Some e -> e | None -> []);
    e_routes = []; e_rt = (fun _ -> []); e_ifaddrs = (fun _ -> []); e_ifaddrs6 = (fun _ -> []);
    e_limit = (fun _ -> 1); e_quota = (fun _ -> 1); e_connlimit = (fun _ -> []);
    e_ct = (fun _ _ -> []); e_nat = (fun _ -> None); e_numgen = (fun _ -> 0) }

(* ---------- the verified surface typecheck, on the SHIPPED path ----------
   T3 residue (claim honesty): the extracted Coq typechecker
   (theories/Surface/Typecheck.v, [typecheck_ruleset]) used to run only in the
   parse-test / sweep GATES, so `nftc compile` on a config whose rule said
   `counter name "undeclared"` (no declaration, or one of the wrong kind)
   silently lowered — an objref to a nonexistent object.  Now EVERY frontend
   consumer of [lower] (nftc compile/optimize/send, parse_test's CLI mode,
   semtest, e2e) runs the same verified check before the verified lowering.
   No typing logic lives here: this function only calls the EXTRACTED
   per-table/per-chain checkers again to NAME the failing spot for the error
   message; accept/reject is decided by [Typecheck.typecheck_ruleset] alone. *)
let typecheck_error (surface : Ast.sruleset) : string =
  let defs = Typecheck.defines_of surface in
  let where =
    L.find_map
      (function
        | Ast.TopTable t when not (Typecheck.typecheck_table defs t) ->
            let decls = Typecheck.decls_of_table t in
            let objs = Typecheck.objs_of_table t in
            let item =
              L.find_map
                (function
                  | Ast.TChain c
                    when not (Typecheck.typecheck_chain defs decls objs c) ->
                      Some (", chain " ^ c.Ast.sc_name)
                  | Ast.TSet sd when not (Typecheck.tc_setdecl defs sd) ->
                      Some (", set " ^ sd.Ast.sd_name)
                  | _ -> None)
                t.Ast.st_items in
            Some (Printf.sprintf " (table %s %s%s)" t.Ast.st_family t.Ast.st_name
                    (match item with Some i -> i | None -> ""))
        | _ -> None)
      surface in
  "ill-typed ruleset rejected by the verified surface typecheck \
   (Surface/Typecheck.v)"
  ^ (match where with Some w -> w | None -> "")
  ^ ": e.g. a named-object reference (counter/quota/... name) with no \
     declaration or a declaration of another kind, an unknown symbol, or a \
     cross-type match"

let lower (f : Nft_ast.sfile) : parsed =
  let surface = file f in
  if not (Typecheck.typecheck_ruleset surface) then
    raise (Lower_error (typecheck_error surface));
  match Lower.lower_ruleset ifindex_oracle surface with
  | Lower.LErr e -> raise (Lower_error (Lower.lerr_message e))
  | Lower.LOk lr ->
      g_typed := lr.Lower.lr_typed;
      g_deps  := lr.Lower.lr_deps;
      let p_tables =
        L.map (fun ((fam, name), chains) -> (fam, name, chains)) lr.Lower.lr_tables in
      let p_hooks =
        L.map (fun ((fam, name), hooks) ->
          (fam, name,
           L.map (fun ((((cn, ct), hk), pn), pr) -> (cn, ct, hk, if pn then - pr else pr))
             hooks))
          lr.Lower.lr_hooks in
      { p_tables; p_hooks;
        p_env  = build_env lr.Lower.lr_sets lr.Lower.lr_vmaps lr.Lower.lr_maps;
        p_sets = lr.Lower.lr_sets; p_vmaps = lr.Lower.lr_vmaps; p_maps = lr.Lower.lr_maps }

(* ---------- lookups (pure structural) ---------- *)

let find_table p name = L.find_opt (fun (_, n, _) -> n = name) p.p_tables
let chains_of p ~table = match find_table p table with
  | Some (_, _, chains) -> chains
  | None -> raise (Lower_error ("no such table: " ^ table))
let find_chain p ~table ~chain = match L.assoc_opt chain (chains_of p ~table) with
  | Some c -> c
  | None -> raise (Lower_error (Printf.sprintf "no chain %s in table %s" chain table))
