# certified-nft — development log & design notes

A formally verified compiler from the declarative **nftables DSL** to the
**nftables control-plane bytecode** (the netlink expressions `nft` emits),
proved semantics-preserving in the **Rocq** prover, plus a verified DSL
optimizer. Extracted to OCaml and differential-tested against the real `nft`.

This implements the *"Goal for now"* in `../instructions.org` (no VST yet, just
Rocq): specify the DSL, specify the control-plane bytecode, write a verified
semantics-preserving compiler, and a verified optimization pass.

## What exists

| File | Role |
|---|---|
| `theories/Bytes.v` | byte/`data` value domain + decidable equality |
| `theories/Packet.v` | the packet both languages observe (metadata + header bytes) |
| `theories/Verdict.v` | `Accept`/`Drop`/`Continue` |
| `theories/Syntax.v` | **DSL**: fields, matches, rules, chains, tables; `field_load` denotation |
| `theories/Bytecode.v` | **control-plane bytecode**: register VM instrs (`meta/payload load`, `cmp`, `immediate`) |
| `theories/Semantics.v` | packet→verdict semantics for *both* languages |
| `theories/Compile.v` | the compiler `compile_chain : chain -> program` |
| `theories/Correct.v` | **`compile_chain_correct`** — semantic preservation |
| `theories/Optimize.v` | DSL optimizer (DCE + match-dedup) + **`optimize_chain_correct`** |
| `theories/Extract.v` | extraction to `extracted/*.ml` |
| `extracted/glue.ml` | *untrusted* OCaml: builds chains, renders nft-format bytecode |
| `difftest.sh` | diffs our bytecode vs `nft --debug=netlink` |

Build & check everything: `make` (proofs + glue). Differential test: `make difftest`.

## The two theorems (both `Closed under the global context` — no axioms)

```coq
Theorem compile_chain_correct : forall c p,
  run_chain (compile_chain c) (c_policy c) p = eval_chain c p.

Theorem optimize_chain_correct : forall c p,
  eval_chain (optimize_chain c) p = eval_chain c p.
```

`eval_chain` is the declarative meaning of a base chain (first-match rule
evaluation with a default policy). `run_chain` runs the compiled register-machine
bytecode. The first theorem says **the netlink ruleset we would install filters
every packet exactly as the DSL specifies**; the second says the optimizer never
changes a packet's verdict.

## Key design decisions

- **One packet model, shared semantics.** Both languages are interpreted over the
  *same* `packet` (metadata function + network/transport header bytes) and the
  *same* observable type (packet→verdict). "Semantics preserving" is therefore a
  literal function equality, not a correspondence between two bespoke models.

- **The bytecode is modelled at exactly nft's level.** Instructions mirror what
  `nft --debug=netlink` prints: `meta load`, `payload load Nb @ base+off`,
  `cmp`, `immediate reg 0 <verdict>`, over a register file with reg 1 reused
  across matches and reg 0 as the verdict register — just as nft does. Netlink
  *serialization* is deliberately out of scope (per the task); we stop at the
  expression list each NEWRULE carries.

- **`field_load` is the single source of truth.** Each high-level field (e.g.
  `tcp dport`) denotes a concrete load (transport header, offset 2, length 2).
  The semantics reads the field through `field_load`; the compiler emits a load
  through the *same* `field_load`. A wrong offset can't pass both the proof and
  differential testing.

- **Faithful, not invented.** The compiler reproduces nft's actual lowering
  (register allocation, l4proto dependency ordering, comparison direction). This
  is why the extracted compiler's output is **byte-identical** to `nft` on the
  test ruleset — see below.

## Trust story (TCB)

Trusted: the Rocq kernel; the two `.v` *specifications* (`Semantics.v` defines
what "correct" means); Rocq's extraction. **Not** trusted: the compiler and
optimizer functions (proved), and the OCaml `glue.ml` (it only builds inputs and
pretty-prints — and it is checked against `nft` by `difftest.sh`). Following the
task's guidance, glue is minimal and testable rather than reimplementing nft
logic; the heavy lifting stays in the verified core.

## Assessment (the instructions' "constantly assess" checklist)

- **Is the theorem useful?** Yes — it's an end-to-end correctness property
  (DSL meaning ≡ installed bytecode behaviour), the exact property a control
  plane should have.
- **Can it catch injected bugs?** Yes — verified by mutation: changing the `MEq`
  compilation from `cmp eq` to `cmp neq` makes `Correct.v` fail to compile (the
  `cmp` case of `run_compile_matches` no longer closes). The theorem is
  non-vacuous.
- **Feature parity plausible?** The architecture grows by adding constructors
  (`field`, `meta_key`, `cmpop`, `verdict`) and clauses; the proofs are by
  structural induction over rule/match lists and are robust to that. Set lookups,
  ranges, bitwise/prefix matches, `jump`/`goto`, and more metadata keys slot in
  without disturbing the chain-sequencing core.
- **Deployable?** Yes — `compile_chain`/`optimize_chain` extract to OCaml; the
  glue already emits nft's exact text. The deployment path is: extracted compiler
  → libnftnl/netlink emitter (the remaining untrusted, testable shim) → kernel.
- **Differential testing** (`make difftest`): the extracted compiler's bytecode
  is **byte-identical** to `nft --debug=netlink` on a 4-rule ruleset spanning
  `tcp dport/sport`, `ip saddr/daddr`, l4proto dependencies, and multi-match
  rules. This is the spec-vs-reality check the upstream tool gives us for free.

## What could be done differently / trade-offs

- The shared `field_load` makes the *per-field load* correct essentially by
  definition; the proof's real content is **rule/chain sequencing, register
  threading, verdict handling, and the optimizer**. An alternative is a fully
  byte-level DSL semantics (no field abstraction) — more "honest" about offsets
  but it just pushes the offset facts into differential testing, which already
  covers them. The current split keeps offsets checkable against `nft` while
  keeping the proof about control flow.
- Modelling a chain's bytecode as a *list of per-rule programs* (one NEWRULE
  each) matches the netlink reality and makes concatenation/sequencing clean.

## Next steps (toward the broader instructions.org goals)

1. More match types: sets/maps (`lookup`), ranges, prefixes/bitwise, more meta &
   payload fields — each is a new constructor + clause.
2. Non-terminal verdicts: `jump`/`goto`/`return` (chain-to-chain control flow);
   generalize `run_program`/`eval_rules` to a chain environment.
3. The netlink emitter shim (libnftnl) as the last untrusted, differentially
   tested step; round-trip `compile → emit → nft list` equality.
4. Then the *future* goals: a data-plane bytecode interpreter spec, and VST
   proofs that the C interpreter meets it — at which point CompCert/clightgen
   enters and the C may need thin shims for unsupported constructs.
