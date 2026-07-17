(* Nft_config: apply configuration-management operations (delete / destroy /
   flush) to the parsed surface config, in file order, BEFORE the verified
   injection/lowering sees it.

   nft evaluates `delete table`, `destroy table`, `flush chain`, ... as
   imperative edits to the ruleset under construction, not as installed rules —
   so they belong to the UNVERIFIED frontend, exactly like `include` expansion.
   This module is that preprocessing stage: it consumes every [Nft_ast.TopOp]
   and rewrites the remaining tables/chains accordingly, leaving a config with
   NO ops for the injection.  Semantics mirrored from nft:
     - delete  : remove the named entity; ERROR if it does not exist
     - destroy : delete-if-exists (no error on a missing entity)
     - flush   : empty the entity (rules cleared; the table/chain itself stays)

   VERIFIED-MODELING FOLLOW-UP: these edits are applied here, untrusted; a future
   milestone can model a stateful ruleset (a sequence of NEW*/DEL*/FLUSH batch
   messages) inside Coq and prove the frontend's fold agrees with it.  Until
   then this is honest, ledgered, unverified preprocessing. *)

module L = Stdlib.List

exception Config_error of string

let table_name = function
  | Nft_ast.TopTable t -> Some t.Nft_ast.st_name
  | _ -> None

let has_table tls name = L.exists (fun tl -> table_name tl = Some name) tls

(* map the named table's [stable] through [f] (identity elsewhere) *)
let map_table tls name f =
  L.map (function
    | Nft_ast.TopTable t when t.Nft_ast.st_name = name -> Nft_ast.TopTable (f t)
    | tl -> tl) tls

let is_rule = function Nft_ast.IRule _ -> true | _ -> false

let flush_chains_of t names_pred =
  { t with Nft_ast.st_items =
      L.map (function
        | Nft_ast.TChain c when names_pred c.Nft_ast.sc_name ->
            Nft_ast.TChain { c with Nft_ast.sc_items =
              L.filter (fun it -> not (is_rule it)) c.Nft_ast.sc_items }
        | it -> it) t.Nft_ast.st_items }

let has_chain t cname =
  L.exists (function Nft_ast.TChain c -> c.Nft_ast.sc_name = cname | _ -> false)
    t.Nft_ast.st_items

let del_chain_of t cname =
  { t with Nft_ast.st_items =
      L.filter (function Nft_ast.TChain c -> c.Nft_ast.sc_name <> cname | _ -> true)
        t.Nft_ast.st_items }

(* apply one op to the accumulated (ordered) toplevel list *)
let apply_op (acc : Nft_ast.sfile) (op : Nft_ast.config_op) : Nft_ast.sfile =
  let open Nft_ast in
  let require_table verb name =
    if not (has_table acc name) then
      raise (Config_error (Printf.sprintf "%s: table '%s' does not exist" verb name)) in
  let require_chain verb tname cname =
    require_table verb tname;
    let ok = L.exists (function
      | TopTable t when t.st_name = tname -> has_chain t cname
      | _ -> false) acc in
    if not ok then
      raise (Config_error
        (Printf.sprintf "%s: chain '%s' in table '%s' does not exist" verb cname tname)) in
  match op with
  | OpFlush CTruleset ->
      (* keep defines; drop every table *)
      L.filter (function TopTable _ -> false | _ -> true) acc
  | OpFlush (CTtable name) ->
      require_table "flush table" name;
      map_table acc name (fun t -> flush_chains_of t (fun _ -> true))
  | OpFlush (CTchain (tname, cname)) ->
      require_chain "flush chain" tname cname;
      map_table acc tname (fun t -> flush_chains_of t (fun c -> c = cname))
  | OpDelete (CTtable name) ->
      require_table "delete table" name;
      L.filter (fun tl -> table_name tl <> Some name) acc
  | OpDelete (CTchain (tname, cname)) ->
      require_chain "delete chain" tname cname;
      map_table acc tname (fun t -> del_chain_of t cname)
  | OpDestroy (CTtable name) ->
      (* delete-if-exists: no error when absent *)
      L.filter (fun tl -> table_name tl <> Some name) acc
  | OpDestroy (CTchain (tname, cname)) ->
      if has_table acc tname then map_table acc tname (fun t -> del_chain_of t cname)
      else acc

(* fold the file left-to-right, resolving every op against what precedes it *)
let apply (tls : Nft_ast.sfile) : Nft_ast.sfile =
  L.fold_left (fun acc tl ->
    match tl with
    | Nft_ast.TopOp op -> apply_op acc op
    | _ -> acc @ [tl]) [] tls
