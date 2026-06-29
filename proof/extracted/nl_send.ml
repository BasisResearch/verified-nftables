(* Nl_send — transmit a VERIFIED-compiled chain to the kernel over real netlink.

   The bytes this builds are a 1:1 serialisation of the verified
   [Compile.compile_chain] output (a [Bytecode.program] = list of instruction
   lists): each rule's instruction list is encoded, instruction by instruction,
   into the kernel's NFTA_RULE_EXPRESSIONS nlattr form, with the compiler's
   register numbers sent VERBATIM (the compiler's [reg_of_slot] already matches
   nft's NFT_REG_* / NFT_REG32_* numbering — see Compile.v).  The sender NEVER
   re-derives rules from the DSL; it only encodes what compile_chain produced.

   Untrusted transport: like the renderer, this is glue, validated differentially
   against live `nft` (a netns round-trip), not part of the proof TCB.

   NOTE: this is the STUB — actual nfnetlink encoding + the AF_NETLINK socket land
   in a follow-up.  For now `send_chain` dry-runs (prints the per-instruction
   expression mapping) and refuses `--commit`. *)

module L = Stdlib.List

let send_chain ~table ~chain ~commit (prog : Bytecode.program) : unit =
  if commit then (
    prerr_string "nftc: netlink --commit is not yet wired (stub)\n";
    exit 3);
  Printf.printf "# would send to %s/%s (%d rules) via NETLINK_NETFILTER:\n"
    table chain (L.length prog);
  L.iteri
    (fun i rp ->
      Printf.printf "  rule %d:\n" i;
      L.iter (fun ins -> Printf.printf "    %s\n" (Codec.render_instr ins)) rp)
    prog
