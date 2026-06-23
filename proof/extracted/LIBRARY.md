# `nftc` — a formally-verified nftables compiler, as a library

`nftc` is the proof-extracted nftables DSL → control-plane bytecode compiler,
packaged as a dune library you can depend on. The `compile` and `optimize`
functions are extracted from machine-checked Rocq proofs:

- **`compile`** preserves the rule set's packet → verdict meaning
  (`compile_chain_correct`);
- **`optimize`** never changes any packet's verdict
  (`optimize_chain_correct`).

Only `to_netlink_text` (rendering bytecode to `nft --debug=netlink` text) is
untrusted glue, and it is differentially tested **byte-identical** against the
upstream nftables corpus (2532/2532 rule-blocks, 100%, 0 mismatches) and live `nft`.

## Build

```sh
make lib          # builds the library
make example      # builds + runs the demo below
```

In a dune project, depend on it with `(libraries nftc)`.

## API (`nftc.mli`)

```ocaml
(* DSL builders — byte strings are big-endian int lists, e.g. port 22 = [0;22] *)
val eq    : field -> Bytes.data -> matchcond
val neq   : field -> Bytes.data -> matchcond
val range : ?neg:bool -> field -> Bytes.data -> Bytes.data -> matchcond
val rule  : ?stmts:Syntax.stmt list -> matchcond list -> verdict -> rule
val chain : verdict -> rule list -> chain

(* The verified pipeline *)
val compile           : chain -> program     (* proved semantics-preserving *)
val optimize          : chain -> chain        (* proved verdict-preserving   *)
val compile_optimized : chain -> program

(* Rendering (untrusted, corpus-tested) *)
val to_netlink_text : program -> string
```

The full field/verdict/statement vocabulary lives in the re-exported
`Nftc.Syntax`, `Nftc.Verdict`, `Nftc.Packet`, `Nftc.Bytecode` modules.

## Example

```ocaml
let () =
  let open Nftc in
  let c =
    chain Verdict.Drop [
      rule [ eq Syntax.FMetaL4proto [6]; eq Syntax.FThDport [0; 22] ] Verdict.Accept;
      rule [] Verdict.Accept;                                   (* accept-all *)
      rule [ eq Syntax.FIp4Saddr [10; 0; 0; 1] ] Verdict.Drop;  (* dead       *)
    ]
  in
  print_endline (to_netlink_text (compile_optimized c))
  (* the dead rule is gone; the result is verified to filter identically to `c` *)
```

See `example.ml` for the runnable version.
