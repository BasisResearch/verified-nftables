(* Nft_parse: the public entry point of the .nft frontend.

   parse_string / parse_file turn nftables DSL text into the trusted Syntax AST
   (a [Nft_inject.parsed]: the tables' chains + the [Packet.env] their set/map
   lookups read), via the Menhir parser (Parser/Lexer), `include` expansion, and
   the lowering pass (Nft_inject).  Properties can then be proved about the AST in
   Rocq (theories/*_Gen.v are this parser's output as Coq terms); via
   compile_table_correct they hold of the installed bytecode.  Untrusted glue. *)

exception Parse_error of string

let pos_msg (lexbuf : Lexing.lexbuf) : string =
  let p = lexbuf.Lexing.lex_curr_p in
  Printf.sprintf "line %d, column %d"
    p.Lexing.pos_lnum (p.Lexing.pos_cnum - p.Lexing.pos_bol + 1)

(* parse one file's text into the surface toplevel list (no include expansion) *)
let parse_raw (src : string) : Nft_ast.sfile =
  (* trailing newline so every item is newline-terminated (the grammar relies on it) *)
  let lexbuf = Lexing.from_string (src ^ "\n") in
  try Parser.file Lexer.token lexbuf with
  | Lexer.Lex_error msg ->
      raise (Parse_error (Printf.sprintf "lexical error at %s: %s" (pos_msg lexbuf) msg))
  | Parser.Error ->
      raise (Parse_error (Printf.sprintf "syntax error at %s" (pos_msg lexbuf)))

let read_file (path : string) : string =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic; s

(* expand `include "rel"` directives, resolving paths relative to the including
   file's directory (nft semantics).  [base] is that directory. *)
let rec expand (base : string) (tls : Nft_ast.sfile) : Nft_ast.sfile =
  Stdlib.List.concat_map (function
    | Nft_ast.TopInclude rel ->
        let path = if Filename.is_relative rel then Filename.concat base rel else rel in
        (try expand (Filename.dirname path) (parse_raw (read_file path))
         with Sys_error msg -> raise (Parse_error ("include: " ^ msg)))
    | t -> [t]) tls

let parse_string (src : string) : Nft_inject.parsed =
  (* a string has no file context; a relative include cannot be resolved *)
  Nft_inject.lower (expand (Sys.getcwd ()) (parse_raw src))

let parse_file (path : string) : Nft_inject.parsed =
  Nft_inject.lower (expand (Filename.dirname path) (parse_raw (read_file path)))

(* the include-expanded SURFACE tree (before lowering): what nft2coq emits as a
   Coq [sruleset] for the Gen file to lower with the verified Coq lowering. *)
let parse_file_surface (path : string) : Ast.sruleset =
  Nft_inject.file (expand (Filename.dirname path) (parse_raw (read_file path)))
