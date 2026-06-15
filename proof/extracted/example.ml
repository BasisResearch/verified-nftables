(* Example consumer of the verified Nftc compiler library.
   Build & run:  dune exec ./example.exe
   Demonstrates the whole public API: build a chain in the DSL, compile it with
   the proof-extracted compiler, and optimize-then-compile. *)

let () =
  let open Nftc in
  (* port/address byte strings are big-endian int lists: 22 = [0;22] *)
  let c =
    chain Verdict.Drop [
      (* tcp dport 22 accept *)
      rule [ eq Syntax.FMetaL4proto [6]; eq Syntax.FThDport [0; 22] ] Verdict.Accept;
      (* tcp dport 80 written as a singleton range -> optimizer rewrites to cmp eq *)
      rule [ eq Syntax.FMetaL4proto [6];
             range Syntax.FThDport [0; 80] [0; 80] ] Verdict.Accept;
      (* tcp dport < 1024, with a counter and a log statement (ordered cmp) *)
      rule ~stmts:[ counter; log "privileged" ]
           [ eq Syntax.FMetaL4proto [6]; cmp Syntax.FThDport Bytecode.CLt [4; 0] ]
           Verdict.Accept;
      (* source in 10.0.0.0/8 via a masked prefix match -> drop *)
      rule [ masked Syntax.FIp4Saddr [255; 0; 0; 0] [0; 0; 0; 0] [10; 0; 0; 0] ]
           Verdict.Drop;
      (* accept-all terminal rule: everything below it is dead (DCE removes it) *)
      rule [] Verdict.Accept;
      rule [ eq Syntax.FIp4Saddr [10; 0; 0; 1] ] Verdict.Drop;   (* dead *)
    ]
  in
  print_endline "=== compile (verified, semantics-preserving) ===";
  print_endline (to_netlink_text (compile c));
  print_endline "";
  print_endline "=== optimize then compile (verified verdict-preserving) ===";
  print_endline (to_netlink_text (compile_optimized c))
