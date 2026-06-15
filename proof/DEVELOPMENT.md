# certified-nft — development log & design notes

A formally verified compiler from the declarative **nftables DSL** to the
**nftables control-plane bytecode** (the netlink expressions `nft` emits),
proved semantics-preserving in **Rocq**, plus a verified DSL optimizer.
Extracted to OCaml and **differential-tested against the upstream nftables test
corpus**: the verified compiler reproduces the real tool's bytecode on
**1272 / 2532 (50.2%)** of the corpus's rule-blocks, with **zero mismatches** on
the supported subset.

This implements the *"Goal for now"* in `../instructions.org` (Rocq only, no VST
yet): specify the DSL, specify the control-plane bytecode, write a verified
semantics-preserving compiler, and a verified optimization pass — and validate
the model against a real corpus rather than hand-written examples.

## What exists

| File | Role |
|---|---|
| `theories/Bytes.v` | byte/`data` domain; `data_eqb`, lexicographic order, bitwise op, set membership |
| `theories/Packet.v` | the packet both languages observe: metadata, conntrack, exthdr, header bytes |
| `theories/Verdict.v` | `Accept`/`Drop`/`Continue` |
| `theories/Syntax.v` | **DSL**: 46 named fields + a parametric exthdr field; matches (eq/neq/range/masked/set); rules, chains, tables |
| `theories/Bytecode.v` | **control-plane bytecode**: register VM (`meta/ct/exthdr/payload load`, `cmp`, `range`, `bitwise`, `lookup`, `immediate`) |
| `theories/Semantics.v` | packet→verdict semantics for *both* languages |
| `theories/Compile.v` | the compiler `compile_chain : chain -> program` |
| `theories/Correct.v` | **`compile_chain_correct`** — semantic preservation |
| `theories/Optimize.v` | DSL optimizer (DCE + match-dedup) + **`optimize_chain_correct`** |
| `theories/Extract.v` | extraction to `extracted/*.ml` |
| `extracted/glue.ml` | *untrusted* glue: builds chains, renders nft-format bytecode (forward test) |
| `extracted/corpus_test.ml` | *untrusted* harness: round-trips the upstream corpus through the verified compiler |
| `difftest.sh` | byte-identical forward check vs the local `nft` |
| `corpus.sh` | round-trip the upstream corpus; report coverage; fail on any mismatch |

Build & check proofs: `make proofs`. Forward test: `make difftest`. Corpus
coverage: `make corpus` (clones nftables' `tests/py` once into a cache dir).

## The two theorems (both `Closed under the global context` — no axioms)

```coq
Theorem compile_chain_correct : forall c p,
  run_chain (compile_chain c) (c_policy c) p = eval_chain c p.

Theorem optimize_chain_correct : forall c p,
  eval_chain (optimize_chain c) p = eval_chain c p.
```

`eval_chain` is the declarative meaning of a base chain (first-match evaluation
with a default policy); `run_chain` runs the compiled register-machine bytecode.
The first says the netlink ruleset we would install filters every packet exactly
as the DSL specifies; the second says the optimizer never changes a verdict.

## Differential testing against the upstream corpus

The oracle is nftables' own `tests/py/*.t.payload`: ~2500 rule-blocks, each a
real rule lowered to its expected netlink expressions (the exact level we model).
`corpus_test.ml` parses each block into our `Bytecode` AST, and for every block
in our supported subset it reconstructs the DSL rule, recompiles it through the
**verified** `Compile.compile_rule`, re-renders, and checks the result is
**byte-identical** to the corpus.

Coverage grew as the verified core grew (each step kept both theorems axiom-free):

| step | what was added | round-trip |
|---|---|---|
| baseline | eq/neq on 5 fields, accept/drop | 90 (3.6%) |
| + ranges | `range eq/neq` | 102 (4.0%) |
| + match-only rules | `Continue` compiles to no `immediate` (as nft does) | 594 (23.5%) |
| + prefixes | `bitwise` masked matches (e.g. /24) | 689 (27.2%) |
| + sets | `lookup` set membership (incl. inverted) | 926 (36.6%) |
| + conntrack & fields | `ct load`, 46 named fields | 979 (38.7%) |
| + extension headers | parametric `exthdr load` (IPv6 ext / TCP opts) | **1272 (50.2%)** |

**Zero mismatches throughout** — every block we claim to support compiles to
exactly nft's bytecode. The remaining ~50% is a deliberate plateau: it needs
*new subsystems*, not more match expressions (see below).

## Trust story (TCB)

Trusted: the Rocq kernel; the `.v` *specifications* (`Semantics.v` defines what
"correct" means); Rocq's extraction. **Not** trusted: the compiler/optimizer
(proved); the OCaml glue (`glue.ml`, `corpus_test.ml`), which only builds inputs
and renders/parses text and is itself checked against the corpus and the live
`nft`. The glue is minimal and differentially tested rather than reimplementing
nft logic; the heavy lifting stays in the verified core. Note the bitwise/set
*semantics* are not extracted (the glue never runs the packet semantics), so the
byte-level `Nat.land`/membership functions are trusted only inside the proof.

## Assessment (the instructions' checklist, with numbers)

- **Theorem useful?** Yes — end-to-end: DSL meaning ≡ installed bytecode behaviour.
- **Catches injected bugs?** Yes (mutation-tested: flipping `cmp eq`→`neq` breaks
  `Correct.v`); and the corpus catches *spec*-vs-*reality* drift (a wrong offset
  would mismatch against nft).
- **Measured coverage:** 1272/2532 (50.2%) of upstream corpus blocks, 0 mismatches.
- **Deployable?** `compile_chain`/`optimize_chain` extract to OCaml and already
  emit nft's exact text; the remaining step is a libnftnl netlink emitter shim.

## What's unsupported, and why (the named plateau)

The remaining corpus blocks need subsystems beyond match-expression lowering:

- **statements** (`reject`, `counter`, `limit`, `log`, `nat`/`masq`/`redir`,
  `queue`, …): non-verdict rule statements — needs a statement model.
- **maps / vmaps** (`lookup … dreg N`) and **concatenations** (multi-register
  loads then a combined lookup; `imm:datareg`): multi-register data flow.
- **byteorder** (`ntoh`/`hton`) and a few **parametric payloads** (odd byte
  slots) and **inner/tunnel** headers.

Cheap remaining wins (no proof cost): more meta keys (`hour`, `day`, `time`,
`iifgroup`/`oifgroup`, …) and a handful more byte-slot fields — each a constructor
plus a glue table entry.

## Next steps (toward the broader instructions.org goals)

1. A **statement** subsystem (verdict + non-verdict statements) — unlocks the
   single largest remaining slice.
2. **Maps/concatenation** (multi-register lowering) for `lookup … dreg`.
3. The **netlink emitter** shim (libnftnl) as the last untrusted, differentially
   tested step; round-trip `compile → emit → nft list`.
4. Then the *future* goals: a data-plane bytecode interpreter spec, and VST
   proofs that the C interpreter meets it (CompCert/clightgen enters here).
