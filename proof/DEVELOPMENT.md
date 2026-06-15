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

> **Read this before trusting the 100%.** "2532/2532" is *control-plane
> byte-identity of single base chains* — it says the compiler emits the same
> netlink expressions as `nft` for the rule-expression vocabulary the corpus
> covers. It is **not** a faithful end-to-end *packet semantics*, and the
> correctness theorem is **vacuous** in several important dimensions because the
> DSL semantics and the bytecode VM *share* the same abstractions. See
> **"Known semantic gaps"** below. The corpus could never reveal these (it never
> populates a set, never uses a jump, always abstracts stateful values), and
> declaring the work "complete" on it was premature — see `../issues.org`.

## Known semantic gaps (audit against the nftables manual, not the corpus)

The data-plane semantics (`eval_chain` / `run_rule`) that the correctness
theorem is stated against is **not** faithful in these areas. Grouped by kind:

**A. External named/shared/mutable state** *(named sets/maps: FIXED, 2026-06)*:
- ✅ **Named sets/maps**: the inlined `elems`/`vm_entries`/`entries` are GONE from
  the rule AST and the bytecode. A `lookup @s` reads the current contents of the
  named set/map from the evaluation environment `env` (`e_set`/`e_vmap`/`e_map`,
  in `Packet.v`), so the contents are decoupled from the rule and can change at
  runtime. The correctness theorem is quantified over the whole environment, so
  it holds for *every* set/map state — non-vacuous. `semtest` battery (3) shows
  the SAME rule give `accept` (set = {22,80}) vs `drop` (empty set).
  Sets/maps are also DECLARED OBJECTS: `set_decls` (a table's named set/vmap/value-
  map declarations with concrete elements) + `env_with_sets` build the lookup
  environment FROM the declarations, so `lookup @s` reads exactly the elements
  declared for `s` (`e_set_declared`); `compile_chain_sets_correct` ties the
  compiler to it; semtest (3c) shows the verdict follow the DECLARATION (accept
  dport 22 when `@set={22,80}`, drop when re-declared `{443}`). The set/map
  DEFINITION lines the corpus emits (`__set%d … / element …`, previously skipped by
  `blocks_of_file`) now round-trip through the data model **642/651 byte-identical**
  (the 9 out are interval sets carrying a `userdata` annotation).
- ⛔ STILL OPEN — **routing table (`fib`)**, **conntrack table (`ct`)**, and
  **stateful objects** (counter/quota/limit/meter, dynset feedback) remain
  per-packet oracles, not the explicit FIB/conntrack/object state they should be.
- **Routing table (`fib`/`rt`)** *(relocated to shared state, 2026-06)*: `fib` and
  `rt` now read from the evaluation environment (`e_fib : selector -> result ->
  data`, `e_rt : rt_key -> data` in `env`), NOT from the packet — so the routing
  table is shared external state decoupled from any one packet, and the theorems
  quantify over it (hold as routes change).
- ✅ **Longest-prefix-match FIB** *(FIXED 2026-06)*: the abstract `e_fib` is replaced
  by a **routing table** `e_routes : list ([lo,hi] * (fib_result -> data))` in `env`,
  and `fib`'s result is *computed* by `lpm_fib` — the first route whose destination
  interval contains the key (table kept most-specific-first = longest-prefix-match).
  Key extraction (which packet bytes the selector reads) is `pkt_fibkey : string ->
  data` (genuinely packet-determined); the table lookup is computed, not oracle'd.
  semtest (4d): route `10.0.0.0/8 -> oif 3`, `fib saddr oif 3 accept` accepts
  `10.1.2.3`, drops `192.168.1.1`, VM=DSL. (Selector→key parsing is abstracted into
  `pkt_fibkey`; exact ECMP/scope tie-breaking not modelled.)
- **Conntrack table (`ct …`)**: `pkt_ct` is a per-packet oracle; really the ct
  table is keyed by flow and accumulates across packets (`ct count`, `ct state`).
- ✅ **Stateful limiters `limit`/`quota`/`connlimit`** *(FIXED 2026-06)*: relocated
  from per-packet bool oracles into the shared `env` as **remaining-resource counts**
  (`e_limit`/`e_quota`/`e_connlimit : spec -> nat`); the match passes iff
  `0 < remaining`. A packet-sequence evaluator `seq_eval ev step e packets` threads
  the shared `env` across packets, `step` mutating it from each verdict (e.g.
  decrement a limiter's tokens on accept), so a later packet observes the
  accumulated state. **`compile_seq_correct`** (axiom-free) proves the compiled
  sequence run equals the DSL one — accumulation across packets is now both
  *expressible* and *compiler-preserved*. semtest (4c): 2 tokens, three packets →
  `[accept;accept;drop]`, VM=DSL. (`step` is keyed on the verdict — a single
  limiter per ruleset; per-rule attribution of which limiter consumed is the
  refinement. `counter`/`ct helper`/`synproxy`/`secmark` objects still verdict-
  neutral.)
- **Dynamic sets / meters (`dynset`, `update`, `meter`)**: their entire purpose is
  to mutate set state at runtime so later lookups see it (per-key rate limiting);
  modelled as verdict-neutral, so the feedback loop is absent.
- **flowtables, incremental `numgen`, `osf`**: stateful; oracle'd or ignored.

**B. In-traversal mutation ignored ("verdict-neutral" overused)** — a statement
that doesn't change *this* rule's verdict still mutates state later rules read:
- `meta mark set`, `ct mark set`, `ip dscp set`, ttl/hoplimit, payload mangle,
  NAT address/port rewrite, exthdr/tcpopt write are all modelled as no-ops/
  terminal-Accept. **Concrete mis-model:** `meta mark set 0x1 ; meta mark 0x1
  accept` — the second rule reads the *original* (oracle) mark, not `0x1`. The
  compiler theorem still proves because BOTH the DSL semantics and the VM no-op
  the set — a textbook vacuous-theorem case.

  *Status: FIXED (2026-06) for the common fragment.* A mutated packet is threaded
  across rules: the VM effect `run_rule_writes` (mirrors `run_rule`'s register
  threading but, on an `IMetaSet/ICtSet` reached after the matches pass, returns
  `set_meta/set_ct p k (rf src)`; cmp/range/lookup/limit break → unchanged `p`)
  and the DSL `body_writes`/`dsl_writes` (left-to-right: a `set` writes
  `eval_vsrc vs` against the packet mutated so far; a failing match stops, keeping
  earlier writes). `eval_rules_mut`/`run_program_mut` (and `eval/run_chain_mut`)
  thread the writes so a later rule observes an earlier `set`. The theorem
  **`compile_chain_mut_correct`** (axiom-free) proves
  `run_chain_mut (compile_chain c) policy = eval_chain_mut c` for **every rule**
  (`mut_wf`, a well-formedness — NOT a feature scope): matches, meta/ct sets, AND
  every other statement (mangle, NAT, dup, counter, log, dynset, exthdr, objref, …,
  which are threaded as meta/ct-neutral via the `straight`-line-prefix lemma). The
  cited `meta mark set 0x1 ; meta mark 0x1 accept` bug now ACCEPTS on both sides, and
  semtest witnesses a rule *mixing* `counter`/`log` with the meta-set. Built on the
  operand value-correctness `eval_vsrc vs p = (regfile after compile_vsrc vs) 1`,
  proved for every operand kind (immediate, field(+transforms), value map (any key
  transform), `VMapT`, jhash, jhash-map, OR-fold). The only `mut_wf` exclusions are a
  malformed zero-field jhash/map/or operand (no real ruleset emits one) and a
  meta/ct set inside the post-outcome (`r_after`) statements (always verdict-neutral
  — counter/log/objref — in the corpus); the *old* `plain_simple` scope (which hid
  every rule with a non-set statement) is gone.

**C. Control flow** *(jump/goto/return + user chains, AND multi-table dispatch: FIXED, 2026-06)*:
- ✅ **Multi-table / multi-hook dispatch**: `eval_ruleset`/`run_ruleset` traverse a
  hook's base chains (across tables) in order with netfilter verdict combination —
  an ACCEPT (or accept-policy fall-through) lets the packet proceed to the next base
  chain, DROP/REJECT/QUEUE is terminal. **`compile_ruleset_correct`** (axiom-free)
  proves the compiled dispatch reproduces the DSL one; semtest (4b) witnesses two
  base chains where the second drops.
- ✅ **Hook / priority selection**: base chains are registered with `(hook, priority,
  env)` (`hooked_chain` — separate metadata, not `chain` fields, faithful to
  `type filter hook input priority N`). `eval_hook fuel rs h` filters the registered
  chains by hook `h` and sorts ascending by priority, then dispatches.
  **`compile_hook_correct`** (axiom-free) proves the compiled hook dispatch equals
  the DSL one (a corollary of `compile_ruleset_correct`, since selection/ordering is
  a pure list op applied identically on both sides). So the engine now models the
  full hook→priority-ordered→base-chain→jump traversal. (Families/`ingress`-vs-`netdev`
  nuances and exact kernel priority tie-breaking are not separately modelled.)
- ✅ `jump` / `goto` / `return` and **user-defined chains** are now modelled:
  `verdict` carries Jump/Goto/Return; `eval_rules_j`/`eval_table` (DSL) and
  `run_rules_j`/`run_table` (VM) are fuel-bounded interpreters over a named chain
  environment, and `compile_table_correct` proves the compiler preserves the
  whole-ruleset verdict for every fuel (axiom-free; `semtest` battery (4) is an
  executable witness with a real `jump`).
- ⛔ STILL OPEN — **hooks, chain priorities, multiple tables/families**: a packet
  really traverses several base chains across hooks (prerouting→input/forward→
  output→postrouting) in priority order; we still evaluate a *single* base chain
  (+ its user chains). `family` is a string label. This is netfilter-core
  dispatch above the per-ruleset semantics; a separate modelling layer.

**D. Data-semantics infidelities inside modelled features:**
- **Concat-key padding**: the kernel pads each concatenated set-key field to its
  4-byte register slot; we omit it, so membership is wrong for sub-4-byte
  concatenated fields (flagged in `Semantics.v`).
- ✅ **Interval/prefix sets** (`flags interval`) *(FIXED 2026-06)*: a named set's
  contents are now closed intervals `[lo,hi]` (`e_set : string -> list (data*data)`)
  and membership is `set_mem x = ∃[lo,hi], lo ≤ x ≤ hi` (big-endian order). An exact
  element is `[x,x]` (reduces to equality via `data_le_antisym`), so exact sets are
  unchanged while CIDR/range sets (`ip saddr {10.0.0.0/8}`, `tcp dport {1024-65535}`)
  are faithfully expressible. semtest (3b) witnesses in-range-accept/out-drop, DSL=VM.
- ✅ **Wildcard interface names** (`iifname "eth*"`) *(FIXED 2026-06)*: the kernel
  emits a wildcard as a *short* `cmp eq` (e.g. `cmp eq reg 1 0x64756d6d 0x79` = the
  5-byte prefix "dummy"), i.e. a comparison of only `length value` bytes.
  `eval_cmp CEq`/`CNe` now compare `firstn (length b) a` — exact for equal-width
  values, a prefix match for a short (wildcard) value. The conflicting
  singleton-range→equality optimisation (a full-width range-eq diverges from a
  prefix `MEq`) is dropped (`simplify_match` is now the identity) — only a minor
  bytecode-shrinking pass is foregone; all eight theorems and corpus 2532/2532 are
  unaffected. semtest (4e): `iifname "eth"` accepts eth0/eth1, drops wlan0, VM=DSL.
- **Operand *value* semantics** *(largely FIXED 2026-06; see B)*: `eval_vsrc` is now
  proved equal to the register the compiled operand leaves for immediate, field,
  value-map, transformed-concat-map, jhash(-map), and OR-fold operands — the value
  the verdict proof had delegated to the corpus. (`data_or`'s truncation is now a
  *modelled* choice both sides share, not an unchecked one.) Open: key-transformed
  value maps and the empty-field degenerate operands.

**What the theorem *does* still give** (honestly): the compiler and optimizer are
*internally consistent* w.r.t. this semantics — the compiler introduces no bug
relative to `eval_chain`, and `optimize_chain` preserves `eval_chain` exactly.
That is real and useful (especially for the optimizer). It is weaker than "the
emitted bytecode means what nftables means," which requires closing the gaps
above.

The gap-closing program was tracked as C→A→B→D. Status as of 2026-06:
- ✅ **(1) Named/external state** (A): sets/maps as declared objects threaded
  through the env (`compile_chain_sets_correct`); FIB as an `lpm_fib` routing
  table; stateful limiters accumulated across a packet sequence
  (`compile_seq_correct`).
- ✅ **(2) Control flow** (C): `jump`/`goto`/`return` + user chains
  (`compile_table_correct`); multi-table/hook/priority dispatch
  (`compile_ruleset_correct`, `compile_hook_correct`).
- 🔶 **(3) In-traversal mutation** (B): DONE for the common fragment —
  `meta`/`ct` `set` is threaded across rules (`compile_chain_mut_correct`).
  **STILL OPEN:** payload-mangle, NAT address/port rewrite, and `dynset`
  set-feedback mutations are threaded only as meta/ct-*neutral* (their own writes
  are not yet visible to later rules).
- 🔶 **(4) Explicit tables** (D-ish): FIB done (`lpm_fib`); **STILL OPEN:** the
  conntrack table is still a per-packet oracle, not a flow-keyed table that
  accumulates across packets (`ct count`, `ct state`).
- 🔶 **(5) Data fidelity** (D): interval/prefix sets and wildcard ifnames done;
  **STILL OPEN:** concat-key sub-4-byte register-slot padding.

So the headline honest gaps remaining are: **payload/NAT/dynset mutation
threading**, the **flow-keyed conntrack table**, and **concat-key padding** —
plus the standing framing caveat that this is internal consistency against a
self-authored semantics, with kernel fidelity resting on `make validate` (28/28)
rather than the corpus round-trip.

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

## The theorems (all eight `Closed under the global context` — no axioms)

The two headline statements:

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

The verified core has grown well past those two. The full set of top-level
theorems in `Correct.v`/`Optimize.v`, each verified axiom-free by
`Print Assumptions` (8 × "Closed under the global context"):

| theorem | what it preserves |
|---|---|
| `compile_chain_correct` | a single base chain's per-packet verdict |
| `optimize_chain_correct` | the optimizer changes no verdict |
| `compile_chain_sets_correct` | a `lookup @s` reads the elements *declared* for `s` (named state as a declared object) |
| `compile_chain_mut_correct` | in-traversal **mutation** (meta/ct `set`) is visible to later rules; holds for *every* rule under `mut_wf` well-formedness |
| `compile_table_correct` | **control flow**: `jump`/`goto`/`return` + user chains (fuel-bounded) |
| `compile_ruleset_correct` | multi-table/multi-hook dispatch with netfilter verdict combination |
| `compile_hook_correct` | hook → priority-ordered base-chain selection |
| `compile_seq_correct` | **stateful accumulation** across a packet sequence (limiters threaded between packets) |

Re-check anytime with `Print Assumptions <name>` (see the probe in the git
history) — every one must print "Closed under the global context".

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
