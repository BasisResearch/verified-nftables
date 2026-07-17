(* Nft_emit: serialise the SURFACE ruleset (the parser's structural injection,
   [Ast.sruleset]) back into a Coq source file.

   This is the bridge that makes the parser useful for proving: instead of
   hand-translating a `.nft` file into an AST inside a `.v` file (which would
   leave "the AST mirrors the text" eyeballed and untrusted), the parser EMITS
   the SURFACE tree as a Coq `Definition <name>_surface : sruleset`, and the Gen
   file then LOWERS it with the VERIFIED Coq `Lower.lower_ruleset` (via
   [lower_or_empty] / the [lr_*] projections).  So every byte the proofs reason
   about — every match operand, set element, NAT target, hook priority — is
   produced by the kernel-checked lowering, NOT written here.  This emitter
   composes NO byte and makes NO datatype/byteorder decision: it prints only the
   untyped surface constructors (IP literals via the [sip4] smart ctor, i.e. as
   decimal octets, so the Gen file carries no raw byte list).

   Fail-loud: a generated `Example <name>_lowers_ok : lower_ok ... = true` breaks
   `make proofs` if the ruleset does not lower — a refused construct can never
   silently fall back to OCaml bytes.  Surface constructors the emitter has no
   spelling for raise [Unsupported] rather than emitting something unchecked.
   See TODO 9 in ../DEVELOPMENT.md. *)

module L = Stdlib.List
module S = Stdlib.String
let spf = Printf.sprintf
exception Unsupported of string

(* ---------- leaves ---------- *)

let bool b = if b then "true" else "false"

let qstring (s : string) : string =
  let b = Buffer.create (S.length s + 2) in
  Buffer.add_char b '"';
  S.iter (fun c -> if c = '"' || c = '\\' then Buffer.add_char b '\\';
                   Buffer.add_char b c) s;
  Buffer.add_char b '"'; Buffer.contents b

let str_list (l : string list) : string =
  "[" ^ S.concat "; " (L.map qstring l) ^ "]"

(* a selector key path [["tcp";"dport"]] and a list of them *)
let keypath (kp : Ast.skeypath) : string = str_list kp
let keypath_list (kps : Ast.skeypath list) : string =
  "[" ^ S.concat "; " (L.map keypath kps) ^ "]"

let opt_nat = function None -> "None" | Some (n : int) -> spf "(Some %d)" n

(* ---------- surface values (mirror of Ast.svalue) ----------
   IP literals print through the [sip4] smart ctor (decimal octets), never a
   raw byte list; the byteorder of those octets is decided only by the Coq
   datatype layer during lowering. *)
let rec svalue (v : Ast.svalue) : string = match v with
  | Ast.SVNum n -> spf "(SVNum %d)" n
  | Ast.SVSym s -> spf "(SVSym %s)" (qstring s)
  | Ast.SVStr s -> spf "(SVStr %s)" (qstring s)
  | Ast.SVIp4 [a; b; c; d] -> spf "(sip4 %d %d %d %d)" a b c d
  | Ast.SVIp4 _ -> raise (Unsupported "IPv4 literal is not 4 octets")
  | Ast.SVIp6 (_, _) -> raise (Unsupported "IPv6 literal emission (add an sip6 smart ctor)")
  | Ast.SVMac _ -> raise (Unsupported "MAC literal emission (add an smac smart ctor)")
  | Ast.SVVar s -> spf "(SVVar %s)" (qstring s)
  | Ast.SVPrefix (v, l) -> spf "(SVPrefix %s %d)" (svalue v) l
  | Ast.SVRange (a, b) -> spf "(SVRange %s %s)" (svalue a) (svalue b)
  | Ast.SVConcat vs -> spf "(SVConcat %s)" (svalue_list vs)
  | Ast.SVSet vs -> spf "(SVSet %s)" (svalue_list vs)
and svalue_list (vs : Ast.svalue list) : string =
  "[" ^ S.concat "; " (L.map svalue vs) ^ "]"

let opt_svalue = function None -> "None" | Some v -> spf "(Some %s)" (svalue v)

let sverdict (v : Ast.sverdict) : string = match v with
  | Ast.SVaccept -> "SVaccept" | Ast.SVdrop -> "SVdrop"
  | Ast.SVcontinue -> "SVcontinue" | Ast.SVreturn -> "SVreturn"
  | Ast.SVjump c -> spf "(SVjump %s)" (qstring c)
  | Ast.SVgoto c -> spf "(SVgoto %s)" (qstring c)
  | Ast.SVqueue (lo, hi, byp, fan) ->
      spf "(SVqueue %d %d %s %s)" lo hi (bool byp) (bool fan)
  | Ast.SVreject opts -> spf "(SVreject %s)" (qstring opts)

let ssetexpr (e : Ast.ssetexpr) : string = match e with
  | Ast.SSEvalue v -> spf "(SSEvalue %s)" (svalue v)
  | Ast.SSEset vs -> spf "(SSEset %s)" (svalue_list vs)
  | Ast.SSElist vs -> spf "(SSElist %s)" (svalue_list vs)
  | Ast.SSEref n -> spf "(SSEref %s)" (qstring n)

let srelop (o : Ast.srelop) : string = match o with
  | Ast.SOpImplicit -> "SOpImplicit" | Ast.SOpEq -> "SOpEq"
  | Ast.SOpNe -> "SOpNe" | Ast.SOpBang -> "SOpBang"

let srhs (r : Ast.srhs) : string =
  spf "{| sr_op := %s; sr_neg := %s; sr_payload := %s |}"
    (srelop r.Ast.sr_op) (bool r.Ast.sr_neg) (ssetexpr r.Ast.sr_payload)

let smatch (m : Ast.smatch) : string =
  spf "{| sm_keys := %s; sm_rhs := %s |}"
    (keypath_list m.Ast.sm_keys) (srhs m.Ast.sm_rhs)

let sstmt (s : Ast.sstmt) : string = match s with
  | Ast.StComment c -> spf "(StComment %s)" (qstring c)
  | Ast.StCounter -> "StCounter"
  | Ast.StLog opts -> spf "(StLog %s)" (qstring opts)
  | Ast.StLimit (rate, unit, over, burst, byte_rate) ->
      spf "(StLimit %d %s %s %d %s)" rate (qstring unit) (bool over) burst (bool byte_rate)
  | Ast.StMasquerade flags -> spf "(StMasquerade %s)" (str_list flags)
  | Ast.StSnat (addr, port, flags) ->
      spf "(StSnat %s %s %s)" (opt_svalue addr) (opt_nat port) (str_list flags)
  | Ast.StDnat (addr, port, flags) ->
      spf "(StDnat %s %s %s)" (opt_svalue addr) (opt_nat port) (str_list flags)
  | Ast.StRedirect (port, flags) ->
      spf "(StRedirect %s %s)" (opt_nat port) (str_list flags)
  | Ast.StTproxy (fam, addr, port) ->
      spf "(StTproxy %s %s %s)" (qstring fam) (opt_svalue addr) (opt_nat port)
  | Ast.StMetaSet (k, v) -> spf "(StMetaSet %s %s)" (qstring k) (svalue v)
  | Ast.StCtSet (k, v) -> spf "(StCtSet %s %s)" (qstring k) (svalue v)
  | Ast.StNotrack -> "StNotrack"

let vmap_entry ((v, sv) : Ast.svalue * Ast.sverdict) : string =
  spf "(%s, %s)" (svalue v) (sverdict sv)

let sclause (c : Ast.sclause) : string = match c with
  | Ast.CMatch m -> spf "(CMatch %s)" (smatch m)
  | Ast.CVmap (keys, entries) ->
      spf "(CVmap %s [%s])" (keypath_list keys)
        (S.concat "; " (L.map vmap_entry entries))
  | Ast.CVmapRef (keys, name) ->
      spf "(CVmapRef %s %s)" (keypath_list keys) (qstring name)
  | Ast.CVerdict v -> spf "(CVerdict %s)" (sverdict v)
  | Ast.CStmt s -> spf "(CStmt %s)" (sstmt s)
  | Ast.CBitmatch (kp, op, mask, r) ->
      spf "(CBitmatch %s %s %s %s)" (keypath kp) (qstring op) (svalue mask) (srhs r)

let srule (r : Ast.srule) : string =
  "[" ^ S.concat ";\n           " (L.map sclause r) ^ "]"

let opt_sverdict = function None -> "None" | Some v -> spf "(Some %s)" (sverdict v)

let setdecl_elem ((v, d) : Ast.svalue * Ast.sverdict option) : string =
  spf "(%s, %s)" (svalue v) (opt_sverdict d)

let ssetdecl (sd : Ast.ssetdecl) : string =
  spf "(TSet {| sd_name := %s; sd_is_map := %s; sd_type := %s; sd_flags := %s;\n            sd_elements := [%s] |})"
    (qstring sd.Ast.sd_name) (bool sd.Ast.sd_is_map)
    (str_list sd.Ast.sd_type) (str_list sd.Ast.sd_flags)
    (S.concat "; " (L.map setdecl_elem sd.Ast.sd_elements))

let schain_item (it : Ast.schain_item) : string = match it with
  | Ast.ITypeHook (ct, hook, pn, prio) ->
      spf "(ITypeHook %s %s %s %d)" (qstring ct) (qstring hook) (bool pn) prio
  | Ast.IPolicy v -> spf "(IPolicy %s)" (sverdict v)
  | Ast.IRule r -> spf "(IRule %s)" (srule r)

let schain (c : Ast.schain) : string =
  spf "(TChain {| sc_name := %s;\n        sc_items := [%s] |})"
    (qstring c.Ast.sc_name)
    (S.concat ";\n         " (L.map schain_item c.Ast.sc_items))

let stable_item (it : Ast.stable_item) : string = match it with
  | Ast.TChain c -> schain c
  | Ast.TSet sd -> ssetdecl sd
  | Ast.TObj n -> spf "(TObj %s)" (qstring n)

let stable (t : Ast.stable) : string =
  spf "(TopTable {| st_family := %s; st_name := %s;\n      st_items := [%s] |})"
    (qstring t.Ast.st_family) (qstring t.Ast.st_name)
    (S.concat ";\n      " (L.map stable_item t.Ast.st_items))

let stoplevel (tl : Ast.stoplevel) : string = match tl with
  | Ast.TopDefine (n, v) -> spf "(TopDefine %s %s)" (qstring n) (svalue v)
  | Ast.TopTable t -> stable t
  | Ast.TopInclude p -> spf "(TopInclude %s)" (qstring p)
  | Ast.TopNop -> "TopNop"

(* ---------- whole-file emission ---------- *)

let sanitize (s : string) : string =
  S.map (fun c -> if (c>='a'&&c<='z')||(c>='A'&&c<='Z')||(c>='0'&&c<='9') then c
                  else '_') s

(* the tables of the surface ruleset, with their chain names (for the
   per-table / per-chain projection definitions the proofs reference) *)
let tables_of (rs : Ast.sruleset) : (string * string * string list) list =
  L.filter_map (function
    | Ast.TopTable t ->
        let chains = L.filter_map (function
          | Ast.TChain c -> Some c.Ast.sc_name
          | _ -> None) t.Ast.st_items in
        Some (t.Ast.st_family, t.Ast.st_name, chains)
    | _ -> None) rs

let emit (src_path : string) (rs : Ast.sruleset) : string =
  let base = sanitize (Filename.remove_extension (Filename.basename src_path)) in
  let b = Buffer.create 8192 in
  let pr fmt = Printf.ksprintf (Buffer.add_string b) fmt in
  pr "(* AUTO-GENERATED from %s by nft2coq (extracted/nft_emit.ml). DO NOT EDIT.\n" src_path;
  pr "   This is the parser's SURFACE output as a Coq [sruleset]; the tables,\n";
  pr "   chains, hooks and set/map declarations the proofs reason about are the\n";
  pr "   VERIFIED lowering [Lower.lower_ruleset] applied to it (no hand-written\n";
  pr "   bytes here).  A refused construct fails [%s_lowers_ok] (fail-loud). *)\n\n" base;
  pr "From Stdlib Require Import List String ZArith.\n";
  pr "From Nft Require Import Bytes Verdict Packet Bytecode Syntax Semantics Nftval.\n";
  pr "From Nft Require Import Surface.Ast Surface.Lower Gen_Support.\n";
  pr "Import ListNotations.\nOpen Scope string_scope.\n\n";
  (* the surface ruleset as written *)
  pr "Definition %s_surface : sruleset :=\n  [%s].\n\n"
    base (S.concat ";\n\n   " (L.map stoplevel rs));
  (* the single host-dependent residue, pinned as a finite map (allowed residue
     (a) — the ifindex oracle; see DEVELOPMENT.md).  `iif "lo"` -> 1; every
     other name declines and the verified lowering fails loud. *)
  pr "Definition ifindex_pins (s : string) : option nat :=\n";
  pr "  if String.eqb s \"lo\" then Some 1%%nat else None.\n\n";
  (* fail-loud: the ruleset lowers, or `make proofs` breaks here *)
  pr "Example %s_lowers_ok : lower_ok ifindex_pins %s_surface = true.\n" base base;
  pr "Proof. vm_compute. reflexivity. Qed.\n\n";
  (* the verified lowering's output, reduced once to a literal *)
  pr "Definition %s_lowered : lowered_ruleset :=\n" base;
  pr "  Eval vm_compute in lower_or_empty ifindex_pins %s_surface.\n\n" base;
  (* the declarations gen_env reads, and the evaluation environment *)
  pr "Definition decls : set_decls := Eval vm_compute in lr_set_decls %s_lowered.\n\n" base;
  pr "Definition base_env : env :=\n";
  pr "  {| e_set := fun _ => []; e_vmap := fun _ => []; e_map := fun _ => [];\n";
  pr "     e_routes := []; e_rt := fun _ => [];\n";
  pr "     e_ifaddrs := (fun _ => []); e_ifaddrs6 := (fun _ => []);\n";
  pr "     e_limit := fun _ => 0; e_quota := fun _ => 0; e_connlimit := fun _ => [];\n";
  pr "     e_ct := fun _ _ => []; e_nat := fun _ => None; e_numgen := fun _ => 0 |}.\n\n";
  pr "Definition gen_env : env := env_with_sets base_env decls.\n\n";
  (* per-table: the chains (individually and as the table's environment) and the
     hook registrations, each carved out of the same verified lowering *)
  L.iter (fun (fam, tname, chains) ->
    let pfx = sanitize tname in
    pr "(* ===== table %s %s ===== *)\n\n" fam tname;
    L.iter (fun cname ->
      pr "Definition %s_%s : chain :=\n  Eval vm_compute in lr_chain_of %s_lowered %s %s.\n\n"
        pfx (sanitize cname) base (qstring tname) (qstring cname)) chains;
    pr "Definition %s_chains : list (string * chain) :=\n  Eval vm_compute in lr_chains_of %s_lowered %s.\n\n"
      pfx base (qstring tname);
    pr "Definition %s_hooks : list hooked_chain :=\n  Eval vm_compute in lr_hooks_of %s_lowered %s.\n\n"
      pfx base (qstring tname))
    (tables_of rs);
  Buffer.contents b
