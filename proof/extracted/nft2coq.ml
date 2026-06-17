(* nft2coq: parse a .nft ruleset and print its AST as a Coq source file.

   Usage:  dune exec ./nft2coq.exe -- path/to/ruleset.nft  > theories/Gen.v

   The emitted file defines the parsed chains and the set/map declarations their
   lookups read; a proof `Require Import`s it and reasons about the parser's
   actual output (no hand translation).  Untrusted glue; see TODO 9. *)

let () =
  if Stdlib.Array.length Sys.argv < 2 then
    (prerr_endline "usage: nft2coq <file.nft>"; exit 2);
  let path = Sys.argv.(1) in
  let parsed = Nft_parse.parse_file path in
  print_string (Nft_emit.emit path parsed)
