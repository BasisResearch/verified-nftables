# certified-nft — development log & design notes

A formally verified compiler from the declarative **nftables DSL** to the
**nftables control-plane bytecode** (the netlink expressions `nft` emits),
proved semantics-preserving in **Rocq**, plus a verified DSL optimizer.
Extracted to OCaml and **differential-tested against the upstream nftables test
corpus**: the verified compiler reproduces the real tool's bytecode on
**2532 / 2532 (100%)** of the corpus's rule-blocks, with **zero mismatches** on
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
| `theories/Optimize.v` | DSL optimizer (dedup + range-simplify + no-op-prune + DCE) + **`optimize_chain_correct`** |
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

Coverage has since grown well past the table — **2532/2532 (100%)**, still
zero mismatches. Beyond the table: ranges, prefixes, sets, ct/exthdr (incl. the
`present` existence test), transform chains (bitwise shift, byteorder, jhash),
statements (counter/notrack/log), reject/queue verdicts, stateful `limit` via an
oracle, all meta keys, rt/socket/numgen/osf oracle loads, **verified
multi-register concatenation** (a real register-allocation proof: distinct
registers via `NoDup`, non-clobbering loads, concat lookup), **sets/ranges over
transformed values** (`MSetT`/`MRangeT`), and **verified verdict maps** (`vmap`:
the rule's verdict comes from a map lookup; `eval_rules` refactored through a
uniform `outcome`, proven a faithful no-op for static verdicts).

**What the round-trip does and does NOT validate (honest scope).** It validates
the *structural lowering*: that each match becomes the right load + test + the
verdict/statement instructions in the right order, value byte-grouping, range
lo/hi split, set-name pass-through, etc. It does **not** by itself validate the
name tables or `field_load` offsets — its parser and renderer share those tables,
so a self-consistent-but-wrong entry would round-trip cleanly (a code review
proved this: permuting `iif`/`oif`, or corrupting an offset, was invisible).
That gap is closed separately by **`make validate`**, which feeds each named
field / meta-ct key to **live `nft`** (an independent oracle we don't control)
and checks our `field_load` descriptor appears in nft's lowering — 28/28 pass.
A wrong offset or name fails there.

## Trust story (TCB)

Trusted: the Rocq kernel; the `.v` *specifications* (`Semantics.v` defines what
"correct" means); Rocq's extraction. **Not** trusted: the compiler/optimizer
(proved); the OCaml glue (`glue.ml`, `corpus_test.ml`), which only builds inputs
and renders/parses text and is itself checked against the corpus and the live
`nft`. The glue is minimal and differentially tested rather than reimplementing
nft logic; the heavy lifting stays in the verified core.

**Eyeball-trusted, never-differentially-tested semantics.** The corpus checks
*structure*, not the data-plane *meaning* of register operations. The byte-level
functions `data_bitops`, `data_le`, `data_mem`, `data_shift`, `data_byteorder`
are not extracted (the glue never runs the packet semantics) and have no external
oracle; their faithfulness rests on inspection of the `.v` definitions. They are
written to match nft: `data_byteorder` reverses each `len`-byte element (matching
nft's byteorder, not a whole-string `rev` stub); `data_shift` shifts via a
big-endian `N` of the loaded width. A small data-plane differential test for
these is future work.

**Known abstractions** (each faithful or documented, none a silent no-op):
`reject`/`queue` model only their control-flow (stop traversal), not the emitted
ICMP / userspace hand-off; sets carry their elements inside the `lookup`
instruction (the real set lives in a separate NEWSET object; dynamic set mutation
is out of scope); `notrack` is verdict-neutral here (its conntrack side effect is
outside the single-packet model). `nat`/`masq`/`redir` model only their terminal
control-flow (accept + stop traversal); the address/port translation loaded into
registers 1–4 is carried for byte-identical rendering but is outside the
single-packet verdict model — exactly like reject's ICMP emission. Concatenation now uses multiple registers with
a verified distinct-register allocation; nft's debug register *numbering* (the
128-bit alias for 16-byte-aligned slots) is a tested-glue presentation map
(`nreg`), validated byte-identically — the dataflow correctness is verified.
Field count: `all_fields` lists 48 named fields plus the parametric/oracle
constructors. `fib` (route lookup) and `inner` (tunnel-decapsulated header reads)
are modeled as explicit oracles keyed by the rule's request — `pkt_fib selector
result` and `pkt_inner type hdrsize flags innerdesc` — so an inner/fib read can
never produce a *wrong* verdict, only an abstract one; the inner packet is a
distinct packet, hence an independent oracle rather than a function of the outer
headers. The `fib` selector/result tokenization (free-form, so the round-trip
can't self-check it) is confirmed against live `nft` by `make validate`.
Ordered comparisons (`cmp lt/gt/lte/gte`) use `data_le`, a total order on the
equal-width operands nft emits. Map-valued sets (`meta/ct set … map`) verify
verdict-neutrality; the looked-up value, like every set/mangle value, is checked
by the differential corpus, not Rocq.

## Assessment (the instructions' checklist, with numbers)

- **Theorem useful?** Yes — end-to-end: DSL meaning ≡ installed bytecode behaviour.
- **Catches injected bugs?** Yes (mutation-tested: flipping `cmp eq`→`neq` breaks
  `Correct.v`). Spec-vs-reality drift in *offsets/names* is caught by `make
  validate` against live `nft` (not by the corpus round-trip alone — see above).
- **Measured coverage:** 2532/2532 (100%) of upstream corpus blocks, 0 mismatches.
- **Deployable?** `compile_chain`/`optimize_chain` extract to OCaml and already
  emit nft's exact text; the remaining step is a libnftnl netlink emitter shim.

## Reaching 100% (2532/2532, 0 mismatches)

Every rule-block of the upstream `tests/py` corpus now round-trips byte-for-byte.
The climb from 97.7% closed these structured features, each a verified addition
(both theorems stayed axiom-free throughout, reviewed by an adversarial subagent
at every step):

- **`SDynsetImm`** — a dynset whose map data is immediate constants in their own
  registers (`@map { … : 10.0.0.1 . 80 }`).
- **map-/immediate-value consumers** for `fwd`/`queue`/`dup`: a `lookup … dreg 1`
  value (or an immediate) feeding a device/number/address (`fwd_src`, `q_src`,
  the `SDupSrc` statement).
- **transformed concatenation keys** (`MConcatSetT`): each concat element loaded
  into its own slot register and transformed *in place* there, proven via a
  register-readback lemma (`run_load_fields_t`, distinct slots never clobber) —
  value-correct, not merely verdict-neutral.
- **register-OR value sources** (`VOr` + `IBitwiseOr`/`data_or`): a value built by
  OR-ing several (transformed) field sources (`meta mark | meta iif | meta cpu`).
- **`VMapT`** — a value map under a transformed concat key.
- **vmap-then-terminal** (`tcp dport vmap {…} redirect`): the core outcome was
  restructured so a verdict map evaluates first and a miss falls through to the
  terminal (`IVmap` is now continue-on-miss; `outcome = vmap-hit ? v :
  terminal_outcome`; `compile_end = compile_vmap ++ compile_terminal`).
- **`VHashMap`** + `nat_src` — a NAT operand from a jhash-keyed map
  (`dnat to jhash ip saddr mod N map {…}`).
- **`tp_portmap`** — a tproxy port from a symhash-keyed map.

**Done** (verified, byte-identical): all named/parametric loads incl. fib, inner
(tunnel decap), xfrm, directional & full conntrack, sctp exthdr; eq/neq/ordered
ranges & comparisons; bitwise/shift/byteorder/jhash transforms (per-field inside a
concat too); set membership and verdict maps (concatenated, transformed, and
hash-keyed); map-/field-/immediate-/OR-valued set/mangle; NAT/masq/redir and
tproxy terminals (incl. map-sourced operands and vmap fall-through); quota/limit
stateful breaks; counter/notrack/log/objref/synproxy/last/dynset(add,delete,map,
immediate)/exthdr-reset/exthdr-write/dup/fwd statements; reject/queue verdicts.

## The verified optimizer (5 passes)

`optimize_chain` = `dce ∘ prune_noops ∘ (simplify_rule ∘ dedup_rule)*`, all proved
verdict-preserving (`optimize_chain_correct`, axiom-free):
- **dedup_rule** — drop duplicate match conditions (matches commute).
- **simplify_rule** — singleton range `lo..lo` → `cmp eq/neq`, both plain
  (`MRange`) and transformed (`MRangeT` → `MTransform`).
- **prune_noops** — drop rules that match-all-and-fall-through.
- **dce** — drop rules shadowed by an unconditional accept/drop.

## The reusable `Nftc` library

`extracted/nftc.ml{,i}` is a public OCaml facade over the proof-extracted
`compile`/`optimize`: DSL builders (`eq`/`neq`/`range`/`cmp`/`masked`,
`counter`/`notrack`/`log`, `rule`/`chain`), the verified pipeline
(`compile`/`optimize`/`compile_optimized`), and `to_netlink_text`. See
`extracted/example.ml` (`dune exec ./example.exe`) for an end-to-end demo.

## Next steps (toward the broader instructions.org goals)

The DSL → control-plane-bytecode compiler and optimizer are complete and 100%
corpus-faithful. What remains is breadth and depth beyond the round-trip:

1. The **netlink emitter** shim (libnftnl) as the last untrusted, differentially
   tested step; round-trip `compile → emit → nft list` against a live kernel.
2. **More optimization passes** — e.g. consecutive-duplicate-rule elimination
   (needs a `rule_eq_dec`; a monolithic `decide equality` is too costly, so it
   wants a bottom-up `vsrc`/`stmt`/spec eq_dec hierarchy), or rule→vmap/set
   consolidation (the classic nft optimization, harder to verify).
3. The *future* goals: a data-plane bytecode interpreter spec, and VST proofs
   that the C interpreter meets it (CompCert/clightgen enters here).
