# certified-nft — development log & design notes

A formally verified compiler from the declarative **nftables DSL** to the
**nftables control-plane bytecode** (the netlink expressions `nft` emits),
proved semantics-preserving in **Rocq**, plus a verified DSL optimizer.
Extracted to OCaml and **differential-tested against the upstream nftables test
corpus**: the verified compiler reproduces the real tool's bytecode on
**2532 / 2532 (100%)** of the corpus's rule-blocks, with **zero mismatches** on
the supported subset.

This implements the project's *"Goal for now"* (Rocq only, no VST yet): specify
the DSL, specify the control-plane bytecode, write a verified semantics-preserving
compiler, and a verified optimization pass — and validate the model against a real
corpus rather than hand-written examples.

> **Read this before trusting the 100%.** "2532/2532" is *control-plane
> byte-identity of single base chains* — it says the compiler emits the same
> netlink expressions as `nft` for the rule-expression vocabulary the corpus
> covers. It is **not** a faithful end-to-end *packet semantics*, and the
> correctness theorem is **vacuous** in several important dimensions because the
> DSL semantics and the bytecode VM *share* the same abstractions. See
> **"Known semantic gaps"** below. The corpus could never reveal these (it never
> populates a set, never uses a jump, always abstracts stateful values), so
> declaring the work "complete" on it would be premature — the "Known semantic
> gaps" section and [`../NOTES.md`](../NOTES.md) track what remains.

> **Data-plane fidelity audit (2026-06) — many gaps below are now CLOSED.** After the
> work logged here, the data-plane semantics was hardened by an **adversarial red/blue
> audit** against the linux-6.18.33 kernel source: a red agent substantiates an
> infidelity (kernel C source, or a property the model wrongly proves / cannot prove), a
> blue agent fixes the *specification* keeping every gate green and axiom-free, looping
> until red can find nothing more. It **converged** after **52 fidelity fixes**. Full
> write-up + the complete fix list: [`../adversarial.md`](../adversarial.md). The audit
> closed, among others: the **flow-keyed conntrack table** (TODO 1), **NAT
> address/port rewrite + checksums + reply un-NAT** (the "NAT modelled as accept" gap),
> **concat-key register-slot padding** (TODO 4), **`numgen inc`** (part of TODO 5),
> live **limit/quota/connlimit** token buckets, and many match/encoding/byteorder
> infidelities. The sections below are the *pre-audit* design log; ✅/⛔/🔶 markers and
> TODO statuses have been updated where the audit changed them, but read them together
> with `../adversarial.md`, which is authoritative for current data-plane fidelity.

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
- ✅ **Conntrack table (`ct`)** *(FIXED by the 2026-06 audit)*: the old per-packet
  `pkt_ct` oracle is replaced by a shared, flow-keyed table
  `e_ct : data -> ct_key -> data` in `env`, keyed by the packet's `pkt_flow`.
  Writable keys (mark/label/secmark) persist across a flow's packets (`ct mark
  set V` on packet 1 is read back by a later packet of the same flow); the
  read-only keys (state/status/direction/expiration/…) are flow-derived too;
  `notrack` and `ct … set` follow the kernel's entry-present/absent guards.
  See TODO 1 and `../adversarial.md`.
- ⛔ STILL OPEN — `meter` and immediate-data MAP-dynset feedback remain per-packet
  oracles / verdict-neutral. (SET-dynset feedback, FIB, conntrack, and `numgen inc` are
  now modelled — see B below, the `fib` bullets, and `../adversarial.md`.)
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
- ✅ **Dynamic sets (`add`/`update`/`delete @s {key}`)** *(FIXED 2026-06)*: a `dynset`
  whose target is a SET (no map data) now MUTATES the named-set state in the env
  instead of being verdict-neutral.  `env_set_upd` (in `Semantics.v`)
  inserts the exact element `[key,key]` (add/update — so a later `set_mem` on `key`
  succeeds) or drop it (delete); this is threaded through the mutation machinery
  (`run_rule_writes` on `IDynset _ None`, `body_writes` on `SDynset _ _ _ []`), so a
  LATER rule's `lookup @s` observes the element this rule learned — the dynamic-set
  feedback loop.  It is carried by the SAME axiom-free theorem as meta/ct mutation,
  **`compile_chain_mut_correct`** (dynset is now an `is_mut_stmt`, no longer a
  straight-line no-op), so the compiler is proven to preserve the fed-back verdict.
  semtest (5b): `add @learn {ip saddr}; ip saddr @learn accept` — the source address
  is learned by rule 1 and matched by rule 2, flipping the verdict the old
  verdict-neutral model gave (DROP) to ACCEPT, with VM = DSL.
- ✅ **Map dynsets (`add @m {key : field}`)** *(FIXED 2026-06)*: a dynset whose data
  is a packet FIELD now learns `key -> data` in the value map (`env_map_upd`);
  the compiled `IDynset _ (Some dreg) true` (the `fdata`
  flag marks a field-sourced data register, vs an immediate one) threads the same
  write, so a later `@m`-keyed map lookup observes it.  Also carried by
  `compile_chain_mut_correct`.  semtest (5c): `add @m {ip saddr : tcp dport};
  meta mark set ip saddr map @m; meta mark 22 accept` — the learned key→value is
  read back into the mark and matched, VM = DSL.
- ✅ **Cross-packet persistence** *(FIXED 2026-06)*: the env a chain LEAVES (with its
  learned set/map elements) is exposed by `eval_chain_mut_env`/`run_chain_mut_env`
  and threaded across a packet SEQUENCE by `seq_eval_env`, so a `add @s` on an
  earlier packet is visible to a `lookup @s` on a later one.  **`compile_seq_mut_correct`**
  (axiom-free) proves the compiled VM reproduces the DSL sequence.  semtest (5d):
  `ip saddr @seen accept; add @seen {ip saddr}` over two packets from one source →
  `[drop; accept]` (first unseen, second learned), VM = DSL.
- ⛔ STILL verdict-neutral: an IMMEDIATE-data dynset (`add @m {key : 10.0.0.1}`,
  `SDynsetImm` — the `fdata=false` form) and `meter`/`numgen` increments.
- **flowtables, incremental `numgen`, `osf`**: stateful; oracle'd or ignored.

**B. In-traversal mutation ignored ("verdict-neutral" overused)** *(originally; now
mostly closed — see the per-item markers and TODO 3)* — a statement that doesn't change
*this* rule's verdict still mutates state later rules read:
- *(Originally)* `meta mark set`, `ct mark set`, `ip dscp set`, ttl/hoplimit, payload
  mangle, NAT address/port rewrite, exthdr/tcpopt write were all modelled as no-ops/
  terminal-Accept. **`meta`/`ct` set are now threaded** (Status below); **NAT
  address/port rewrite is now modelled** (2026-06 audit — see TODO 3); payload-mangle and
  exthdr/tcpopt write remain verdict-neutral. **Concrete mis-model (the original bug):**
  `meta mark set 0x1 ; meta mark 0x1
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
  thread the writes so a later rule observes an earlier `set`. A **set-`dynset`**
  (`add`/`update`/`delete @s {key}`) likewise mutates the env's named-set state
  (`run_rule_writes` on `IDynset _ None` → `env_set_upd`; `body_writes` on
  `SDynset _ _ _ []`), so a later `lookup @s` sees the learned element — the
  dynamic-set feedback loop (semtest 5b). The theorem
  **`compile_chain_mut_correct`** (axiom-free) proves
  `run_chain_mut (compile_chain c) policy = eval_chain_mut c` for **every rule**
  (`mut_wf`, a well-formedness — NOT a feature scope): matches, meta/ct sets,
  set-dynsets, AND every other statement (mangle, NAT, dup, counter, log, map-dynset,
  exthdr, objref, …, threaded as state-neutral via the `straight`-line-prefix lemma). The
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
- ⛔ STILL OPEN — **the hook *pipeline* and families**: one hook's dispatch is
  modelled (the two ✅ bullets above), but a packet's traversal of *successive*
  hooks (prerouting→input/forward→output→postrouting) is composed manually via
  `chain_out`, not by a single verified pipeline theorem; `family` is a string
  label, and `ingress`-vs-`netdev` / exact kernel priority tie-breaking are not
  separately modelled.

**D. Data-semantics infidelities inside modelled features:**
- ✅ **Concat-key padding** *(FIXED 2026-06, `13ee781`)*: the kernel pads each
  concatenated set-key field to its 4-byte register slot; stored concat
  elements are now split by 4-byte register slots (ifname = 16) rather than raw
  field widths, so sub-4-byte concatenated fields match the kernel layout (see
  item (5) at the end of this section).
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
  bytecode-shrinking pass is foregone; all theorems and corpus 2532/2532 are
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
  `meta`/`ct` `set`, **set-`dynset`** (`add`/`update`/`delete @s {key}`), AND
  **field-data map-`dynset`** (`add @m {key : field}`) are threaded across rules so
  a later lookup sees the learned element/entry (`compile_chain_mut_correct`); the
  learned env also persists ACROSS packets (`compile_seq_mut_correct`).
  **NAT address/port rewrite is now modelled** by the 2026-06 audit — flow-stateful
  mapping in `e_nat`, L3+L4 checksum updates, reply-direction un-NAT, NF_DROP on
  no-usable-address — observed across hooks by the whole-chain trace evaluator
  (`eval_chain_trace`). **STILL OPEN:** payload-mangle (`SMangle`) and IMMEDIATE-data
  dynsets are threaded only as state-*neutral* (their own writes are not yet visible
  to later rules).
- ✅ **(4) Explicit tables** (D-ish): FIB done (`lpm_fib`); the **conntrack table is
  now flow-keyed** (`e_ct`, keyed by `pkt_flow`) by the 2026-06 audit — `ct
  mark`/`state`/`direction`/`connlimit` accumulate across a flow's packets. (See TODO 1
  and `../adversarial.md`.)
- ✅ **(5) Data fidelity** (D): interval/prefix sets, wildcard ifnames, and **concat-key
  register-slot padding** are done — the 2026-06 audit's `13ee781` splits a stored
  concat element by 4-byte register slots (ifname = 16) rather than raw field widths, so
  sub-4-byte concatenated fields now match the kernel layout (this underpins the
  anti-spoofing proof's `ip daddr . oifname` key).

So the headline honest gaps remaining are: **payload-mangle and immediate-data-dynset
mutation threading**, **`meter`** state, the **netlink emitter shim** (TODO 6), and the
**VST data-plane layer** (TODO 8) — plus the standing framing caveat that this is internal
consistency against a self-authored semantics, with kernel fidelity now resting on the
2026-06 adversarial audit (`../adversarial.md`) and `make validate` (28/28) rather than the
corpus round-trip.

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
| `theories/Optimize.v` | rule-local base optimizer pass (dedup + range-simplify + no-op-prune + DCE) + `optimize_chain_correct`; the shipped 18-stage table-level pipeline is `Optimize_Table.v`/`Optimize_Uncond.v` (see "The verified optimizer" below) |
| `theories/Example_Ruleset.v` | worked example: `../rulesets/ruleset.nft` hand-translated to the AST + 9 axiom-free packet-property proofs (the user-facing use case; the baseline a parser should reproduce — see TODO 9) |
| `theories/Extract.v` | extraction to `extracted/*.ml` |
| `extracted/glue.ml` | *untrusted* glue: builds chains, renders nft-format bytecode (forward test) |
| `extracted/lexer.mll` `parser.mly` `nft_ast.ml` `nft_lower.ml` `nft_parse.ml` | *untrusted* **`.nft` text → `Syntax` AST frontend** (TODO 9): ocamllex+Menhir surface parser → lowering (define/symbol resolution, implicit-l4proto deps, CIDR/range/concat, anonymous-set/vmap → `env`, `include` expansion) → `Nft_parse.parse_file` |
| `extracted/nft_emit.ml` `nft2coq.ml` | *untrusted* **AST → Coq emitter**: serialise the parsed chains + `set_decls`/`env` as Coq `Definition`s (`make gen`), so proofs reason about the parser's real output |
| `theories/Optiplex_Gen.v` `Ruleset_Gen.v` `Router_Gen.v` `Tutorial_Gen.v` | **generated** by `nft2coq` from the matching `../rulesets/*.nft` (`make gen`; the parser's output as Coq terms, kernel-checked). `Tutorial_Gen.v` backs the [`CONFIG_PROOFS.md`](CONFIG_PROOFS.md) tutorial |
| `theories/Optiplex_Antispoof.v` | **anti-spoofing** proofs about the parsed `optiplex.nft` bridge `output` chain (+ legit-traffic-allowed); all axiom-free |
| `theories/Optiplex_Antispoof_Gaps.v` | **adversarial** proofs: the binding is unenforced outside `@vmaddrs` / off br.20 (real bypasses), axiom-free |
| `theories/Optiplex_Mark.v` | **firewall-mark** proofs about the parsed prerouting/postrouting chains: marking RDP traffic, mark-gated masquerade, cross-hook flow; axiom-free |
| `theories/Ruleset_Verified.v` | the 8 `ruleset.nft` packet properties, about the *generated* AST (supersedes the hand copy in `Example_Ruleset.v`) |
| `extracted/parse_test.ml` | *untrusted* harness/CLI: checks parsed-AST verdicts vs the proofs (ruleset.nft 8 props; optiplex anti-spoofing + bypasses); difftest AST equality; live-`nft` round-trip |
| `extracted/corpus_test.ml` | *untrusted* harness: round-trips the upstream corpus through the verified compiler |
| `difftest.sh` | byte-identical forward check vs the local `nft` |
| `corpus.sh` | round-trip the upstream corpus; report coverage; fail on any mismatch |

Build & check proofs: `make proofs`. Forward test: `make difftest`. Corpus
coverage: `make corpus` (clones nftables' `tests/py` once into a cache dir).

## The theorems (every one `Closed under the global context` — no axioms)

**The authoritative map is [`THEOREMS.md`](THEOREMS.md)** — one HEADLINE
theorem per verified axis, the HEADLINE/STAGE/SUPPORTING/SUPERSEDED/DEMO
classification of every `Theorem`/`Corollary`, and the evaluator matrix.
The entry points are restated (with `Print Assumptions`) in
[`theories/Main.v`](theories/Main.v), and `make axioms` re-checks the whole
set. Two of the most-cited statements:

```coq
Theorem compile_chain_correct : forall c e p,
  run_chain (compile_chain c) (c_policy c) e p = eval_chain c e p.

(* whole-pipeline optimizer correctness, for ANY input chain — no rules_clean,
   no caller freshness side-condition (freshness is internal via seed_start): *)
Theorem optimize_table_uncond_correct : forall c base p n' d' c',
  optimize_table_uncond c = (n', d', c') ->
  eval_chain c' (env_with_sets base d') p
  = eval_chain c (env_with_sets base empty_decls) p.

Theorem optimize_table_uncond_compile_correct : ...  (* same, to the COMPILED bytecode *)
```

`eval_chain` is the declarative meaning of a base chain (first-match evaluation
with a default policy); `run_chain` runs the compiled register-machine bytecode.
The first says the netlink ruleset we would install filters every packet exactly
as the DSL specifies; the `optimize_table_uncond` family (in `Optimize_Uncond.v`)
says the *optimized* chain — and its compiled bytecode — preserves every packet's
verdict against the synthesised set/map declarations, for **any** input *chain*
(no `rules_clean` or freshness precondition). The optimizer theorem is
**per-chain**: quantified over a single chain and all environments/packets;
multi-chain/hook preservation is the separate
`compile_ruleset_correct`/`compile_hook_correct` family, **not composed with
the optimizer**. The earlier per-pass `Optimize.optimize_chain_correct` (the
base dedup/simplify pass alone changes no verdict) is subsumed by it
(SUPERSEDED as a standalone result; it survives as the pipeline's base stage).

The verified core also includes the compile/control-flow theorems below, each
verified axiom-free by `Print Assumptions` ("Closed under the global context").
This list is the original compile core; the optimizer pipeline adds the
`optimize_table_uncond*` headline above (and the per-pass `_correct_uncond`
lemmas in `Optimize_Uncond.v`), all likewise axiom-free — re-check any with
`Print Assumptions <name>`:

| theorem | what it preserves |
|---|---|
| `compile_chain_correct` | a single base chain's per-packet verdict |
| `optimize_chain_correct` | the rule-local base pass changes no verdict (SUPERSEDED as a standalone result — the shipped pipeline's theorem is `optimize_table_uncond_compile_correct`) |
| `compile_chain_sets_correct` | a `lookup @s` reads the elements *declared* for `s` (named state as a declared object) |
| `compile_chain_mut_correct` | in-traversal **mutation** (meta/ct `set`, set-`dynset` learning, field-data map-`dynset` learning) is visible to later rules; holds for *every* rule under `mut_wf` well-formedness |
| `compile_chain_mut_env_correct` | the **env a chain leaves** (its dynset-learned sets/maps) is preserved too — basis for cross-packet learning |
| `compile_table_correct` | **control flow**: `jump`/`goto`/`return` + user chains (fuel-bounded) |
| `compile_chain_faithful_jumpfree` | the single-chain `compile_chain` agrees with the faithful jump-aware `eval_table` on jump-free chains (bridges the two engines) |
| `compiled_table_jump_drops` | a `jump` into a chain that drops is honoured end-to-end (jump-aware drop is not lost) |
| `compile_ruleset_correct` | multi-table/multi-hook dispatch with netfilter verdict combination |
| `compile_hook_correct` | hook → priority-ordered base-chain selection |
| `compile_seq_correct` | per-packet **congruence** lifted over a packet sequence under an **arbitrary step** `verdict -> env -> env` (the between-packet env update is caller-supplied, *not* generated by the ruleset — for ruleset-generated evolution see `compile_seq_mut_correct`) |
| `compile_seq_mut_correct` | **cross-packet learning**: dynset-learned env threaded between packets, so an earlier packet's `add @s` is seen by a later packet's `lookup @s` |

Re-check anytime with `Print Assumptions <name>` (or `make axioms`) — every
one must print "Closed under the global context".

**Evaluator matrix** (full version with bridging theorems: `THEOREMS.md` §3).
The nine DSL entry points — `eval_rules`, `eval_rules_mut`,
`eval_rules_mut_env`, `eval_rules_trace`, `eval_rules_j`/`eval_table`,
`eval_ruleset`, `eval_hook`, `seq_eval`, `seq_eval_env` — have near-identical
signatures but **disjoint** feature coverage:

| entry point | threads writes | returns env | jump/goto/return | NAT effect | multi-chain |
|---|---|---|---|---|---|
| `eval_rules` | no | no | no (jump-free domain) | no | no |
| `eval_rules_mut` | yes (`dsl_step`) | no | no | no | no |
| `eval_rules_mut_env` | yes | yes | no | no | no |
| `eval_rules_trace` | yes | (whole packet) | no | yes | no |
| `eval_rules_j` / `eval_table` | no | no | yes | no | user chains |
| `eval_ruleset` | no | no | yes | no | base chains |
| `eval_hook` | no | no | yes | no | hook dispatch |
| `seq_eval` | no (external step) | threaded between packets | yes (with `eval_hook`) | no | yes |
| `seq_eval_env` | yes (with `eval_chain_mut_env`) | threaded between packets | no | no | no |

The mutation strand and the jump strand are disjoint: **mutation × jump/goto
is not jointly verified**.

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
statements (counter/notrack/log), reject/queue verdicts, stateful
`limit`/`quota`/`connlimit` (rendered here; their *semantics* are now live consuming
token buckets, not oracles — 2026-06 audit), all meta keys, rt/socket/osf oracle loads
and `numgen` (whose `inc` form is now a persistent counter in `env`), **verified
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
instruction (the real set lives in a separate NEWSET object; dynamic SET mutation
is verdict-neutral in this single-packet model but IS modelled by the
mutation-aware `run_chain_mut`/`eval_chain_mut` — see "B" above — so a learned
element is visible to later rules); `notrack` now sets the flow's ct state to UNTRACKED
with the kernel's entry-present guard (no-op when an entry exists), observed by later ct
reads (2026-06 audit). `nat`/`masq`/`redir` now **rewrite the packet** — the
address/port translation (flow-stateful in `e_nat`, with L3+L4 checksum fix-up and
reply-direction un-NAT) is applied by the whole-chain trace evaluator and observed by
later hooks, not merely carried for rendering (2026-06 audit; see TODO 3 and
`../adversarial.md`). Concatenation now uses multiple registers with
a verified distinct-register allocation; nft's debug register *numbering* (the
128-bit alias for 16-byte-aligned slots) is a tested-glue presentation map
(`nreg`), validated byte-identically — the dataflow correctness is verified.
Field count: `all_fields` lists 48 named fields plus the parametric/oracle
constructors. `fib` (route lookup) is *computed*, not oracle'd: the env carries
a routing table `e_routes : list ([lo,hi] * (fib_result -> data))` and `lpm_fib`
returns the first route whose destination interval contains the key
(most-specific-first = longest-prefix-match), with key extraction
`pkt_fibkey : string -> data` reading the packet bytes the selector names
(`Fib_Local.v` additionally proves the kernel-faithful host-local type
behaviour). `inner` (tunnel-decapsulated header reads) remains an explicit
oracle keyed by the rule's request — `pkt_inner type hdrsize flags innerdesc` —
because the inner packet is a distinct packet, not a function of the outer
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

## The verified optimizer

Two layers (the shipped entry point is `optimize_table_uncond` in
`Optimize_Uncond.v`, which is what `Extract.v` extracts and the `nftc` CLI
runs).

**Layer 1 — rule-local base pass** (`Optimize.optimize_chain` =
`dce ∘ prune_noops ∘ (simplify_rule ∘ dedup_rule)*`, verdict-preserving,
axiom-free; SUPERSEDED as a standalone headline, it runs as the pipeline's
base stage):
- **dedup_rule** — drop duplicate match conditions (matches commute).
- **simplify_rule** — singleton range `lo..lo` → `cmp eq/neq`, both plain
  (`MRange`) and transformed (`MRangeT` → `MTransform`).
- **prune_noops** — drop rules that match-all-and-fall-through.
- **dce** — drop rules shadowed by an unconditional accept/drop.

**Layer 2 — the table-level `nft -o` consolidation pipeline**
(`Optimize_Table.optimize_table`): after `normalize_chain`
(`Optimize_Normalize.v`, head normalisation so the recognisers fire on parser
output) and the layer-1 base pass, 18 stages run in this composition order,
threading a fresh-name counter and a `set_decls` accumulator:

1. `optimize_chain_absorb` — subsumed-rule absorption
2. `optimize_chain_ctmask` — ct-mark mask folding
3. `optimize_chain_dnat` — dnat runs → one bare dnat map
4. `optimize_chain_snat` — snat runs → one bare snat map
5. `optimize_chain_setsN` — N-way value → anonymous set
6. `optimize_chain_concatK` — K-row two-selector concat set
7. `optimize_chain_mapn` — mark-map merge (labelled sound superset of `nft -o`)
8. `optimize_chain_concatN` — N-way concat set
9. `optimize_chain_concatM` — mixed concat set
10. `optimize_chain_setg` — guarded value set
11. `optimize_chain_ivset` — interval (range) set
12. `optimize_chain_ivsett` — transformed interval set
13. `optimize_chain_dscp` — dscp value runs
14. `optimize_chain_ivsetg` — guarded interval set
15. `optimize_chain_ivmixg` — guarded mixed value/interval set
16. `optimize_chain_vmapNg` — guarded verdict map
17. `optimize_chain_dscpv` — dscp verdict map
18. `optimize_chain_vmapN` — N-way value+verdict → verdict map

**`nft -o` fold-shape ledger.** Each consolidation stage targets a concrete
`nft --optimize` fold shape (differentially confirmed against host `nft`; the
battery cases live under `battery_cases/`). Shapes are referred to by name —
historical branch-local "gap G*n*" numbers were retired because two audit
branches assigned the same numbers to different shapes:

| shape | example fold | pass module | fidelity |
|---|---|---|---|
| snat bare-map | `ip saddr A snat to T` runs → `snat to ip saddr map { A : T, .. }` | `Optimize_Snat` | matches `nft -o` (bare map) |
| dnat bare-map | `ip daddr A dnat to T` runs → `dnat to ip daddr map { .. }` | `Optimize_Dnat` | matches `nft -o` (bare map) |
| value set | `tcp dport P accept` runs → `tcp dport { P1, P2 } accept` | `Optimize_Merge` (setsN) / `Optimize_Setg` | matches `nft -o` |
| interval set | `ip saddr lo-hi accept` runs → `ip saddr { lo1-hi1, .. }` | `Optimize_Ivset`/`_Ivsetg` | matches `nft -o` |
| host-order interval set | `ct mark 10-20 accept` runs → `ct mark { 10-20, .. }` (hton transform) | `Optimize_Ivsett` | matches `nft -o` |
| mixed value/interval | guarded mixed runs → one set | `Optimize_Ivmixg` | matches `nft -o` |
| concat set | `ip saddr A tcp dport P` runs → `ip saddr . tcp dport { A . P, .. }` | `Optimize_Concat*` | matches `nft -o` |
| verdict map | `tcp dport P <verdict>` runs, differing verdicts → `vmap { P : v, .. }` | `Optimize_Vmap`/`_Vmapg` | matches `nft -o` |
| ether-vmap | `ether saddr MAC <verdict>` runs → `ether saddr vmap { .. }` | `Optimize_Vmapg` | matches `nft -o` |
| dscp-masked-vmap | `ip dscp N <verdict>` runs → `ip dscp vmap { .. }` (masked key) | `Optimize_Dscpv` (+ `Optimize_Dscp` for same-verdict) | matches `nft -o` |
| mark-map merge | `ip daddr A meta mark set M` runs → guarded `meta mark set ip daddr map { .. }` | `Optimize_Mapn` | sound superset — `nft -o` does not fold `meta mark set` (see `Optimize_Mapn.v` §D1) |

The seam theorem `optimize_chain_clean` (`Optimize_Table.v`) feeds the base
pass's output into the stage proofs. Whole-pipeline correctness — with **no**
precondition on the input chain — is `optimize_table_uncond_correct`, and its
compiled-bytecode form `optimize_table_uncond_compile_correct` is the
optimizer's HEADLINE theorem (both in `Optimize_Uncond.v`, axiom-free; see
`THEOREMS.md`).

## The reusable `Nftc` library

`extracted/nftc.ml{,i}` is a public OCaml facade over the proof-extracted
`compile`/`optimize`: DSL builders (`eq`/`neq`/`range`/`cmp`/`masked`,
`counter`/`notrack`/`log`, `rule`/`chain`), the verified pipeline
(`compile`/`optimize`/`compile_optimized`), and `to_netlink_text`. See
`extracted/example.ml` (`dune exec ./example.exe`) for an end-to-end demo.

## Proving properties about a concrete ruleset (ergonomics layer)

To STATE and PROVE a security property about a specific `.nft` file, use the
readable predicate / notation / tactic layer in
[`theories/Nft_Tactics.v`](theories/Nft_Tactics.v): write
`my_chain denies p under my_chains budget my_fuel` (definitionally
`eval_table my_fuel my_chains my_chain p = Drop`) with typed hypotheses
`fieldof FThDport p === port 25` (routed through the `Nftval` constructors), and
discharge it with one tactic — **`nft_eval Hpe`** for a packet constrained by
hypotheses, **`nft_decide`** for a fully concrete packet. The step-by-step recipe
(including `make gen` onboarding of a new file) is in
[`CONFIG_PROOFS.md`](CONFIG_PROOFS.md); compiling worked examples are
`theories/Nft_Demo_Symbolic.v` and `theories/Nft_Demo_Concrete.v`. The layer is
additive and sound: every notation is *definitionally* its raw `eval_table` /
`field_value` statement (`nft_*_spec` / `demo_*_def`), `demo_recovers_original`
re-derives the original `Ruleset_Verified`-shaped theorem from the readable one,
and `demo_smtp_not_accepted` / `Fail now nft_decide` witness that the tactics
cannot prove a false property.

## Orientation for a fresh session (read this before picking up a TODO)

**Build & verify (every change must keep ALL of these green):**

| command | gate |
|---|---|
| `make proofs` | all `.v` check; also re-runs `Extract.v` → regenerates `extracted/*.ml{,i}` |
| `make corpus` | upstream `tests/py` round-trip: **2532/2532, 0 mismatches** |
| `make difftest` | compiled bytecode **byte-identical** to live `nft --debug=netlink` |
| `make validate` | `field_load` offsets/names vs live `nft`: **28/28** |
| `make semtest` | executable witnesses: DSL = VM = optimized on packet batteries (incl. the mutation / sequence witnesses) |
| `make parse-test` | `.nft` frontend (TODO 9 M1): parses `../rulesets/ruleset.nft`, checks parsed-AST verdicts vs `Example_Ruleset.v`; difftest ruleset → `glue.ml`'s AST; live-`nft` round-trip |

Axiom-freedom — every headline theorem must print "Closed under the global
context". Re-check the optimizer-pipeline headline (and the compile core) with:
```
cd theories && printf 'From Nft Require Import Correct Optimize_Uncond.\nPrint Assumptions compile_chain_correct.\nPrint Assumptions Optimize_Uncond.optimize_table_uncond_correct.\nPrint Assumptions Optimize_Uncond.optimize_table_uncond_compile_correct.\n' | coqtop -R . Nft | grep -c "Closed under the global context"
```
or run **`make axioms`**, which checks the whole `THEOREMS.md` HEADLINE set +
the `Correct.v` strata in one shot (plus the in-repo `Print Assumptions`
guards across `theories/*.v`, checked on every `make proofs`).
The theorem strata are listed in "The theorems" table above and classified in
`THEOREMS.md`. Any new top-level theorem must also print `Closed under the
global context`.

**Where things live:**
- `theories/Packet.v` — the `packet` and its `env` (the shared mutable state:
  `e_set`/`e_vmap`/`e_map`/`e_routes`/`e_rt`/`e_limit`/`e_quota`/`e_connlimit`).
  `meta_key`, `ct_key`, etc.
- `theories/Syntax.v` — the DSL AST; `field_load : field -> loaddesc` and
  `do_load`/`field_value` (how a field reads the packet/env); `op_delete`.
- `theories/Bytecode.v` — the VM instruction set (`IDynset` has an `fdata` flag,
  see "discriminator pattern" below).
- `theories/Compile.v` — `compile_stmt`/`compile_chain`; register allocation
  `alloc_regs`/`reg_of_slot`/`field_slots`/`load_fields`.
- `theories/Semantics.v` — verdict semantics (`eval_chain`/`run_chain`, jump-aware
  `eval_table`/`run_table`, hook `eval_ruleset`/`eval_hook`); **mutation** machinery
  (`run_rule_writes`/`body_writes`, `eval_chain_mut`/`run_chain_mut`); **cross-packet**
  (`eval_chain_mut_env`/`run_chain_mut_env`/`seq_eval_env`); packet/env mutators
  (`set_meta`/`set_ct`/`env_set_upd`/`env_map_upd`).
- `theories/Correct.v` — all the theorems and their scaffolding.
- `theories/Extract.v` — **add any function you want to call from `semtest.ml` to the
  `Separate Extraction` list** (else "Unbound value Semantics.X").
- `extracted/` — `codec.ml` (renderer), `corpus_test.ml` (parser + DSL
  reconstructor), `glue.ml`, `semtest.ml`, `nftc.ml{,i}` are **hand-written**
  (`proof/.gitignore` ignores `extracted/*.ml{,i}`, so these are force-added with
  `git add -f`); everything else under `extracted/` is generated by `make proofs`.
  In hand-written `.ml`, use `Stdlib.List`/`Stdlib.String` — the extracted `List`/
  `String` modules shadow the stdlib ones.

## Architecture: the state & mutation machinery (reuse these patterns)

**Design rule for state.** State that *accumulates* or is *shared/named* lives in
`env` — an EXPLICIT argument of every evaluator (`eval : … -> env -> packet -> …`;
the mutation evaluators also RETURN the env they leave); a purely per-packet
abstraction is a packet-field oracle (`pkt_meta`, `pkt_sock`, …). The correctness
theorems quantify over the whole `env`, so anything in `env` is automatically
non-vacuous.

**To relocate a per-packet oracle into `env`** (e.g. the conntrack TODO): change
BOTH `Syntax.do_load` (the relevant `L*` case) and the matching VM load case in
`Semantics.run_rule`/`run_rule_writes` so they read the new `env` field; the
`compile_load`-style correctness lemmas realign automatically because both sides
read the *same* env function.

**To add a new in-traversal MUTATION** (a statement whose write a later rule sees):
1. `Semantics.v`: give its compiled instruction an effect in `run_rule_writes`
   (return the mutated packet), and its DSL effect in `body_writes`. Keep the
   *verdict* semantics (`run_rule`/`eval_rules`/`outcome`) neutral — mutation only
   affects *later* rules, which `eval_rules_mut`/`run_program_mut` already thread.
2. `Correct.v`: mark the instruction as a write in `writes_instr` (`true`) and
   non-straight in `straight_instr` (`false`); add the statement to `is_mut_stmt`;
   handle it in `run_compile_body_writes`'s `is_mut_stmt = true` branch with a
   *readback* lemma proving `run_rule_writes (compile …) = body_writes …`. Re-check
   that `run_rule_writes_neutral`, `straight_imp_nw`, `run_rule_writes_straight`
   still discharge the instruction's pattern (they `destruct` the instruction —
   add `option`/`bool` sub-destructs for new argument shapes, as the `IDynset`
   cases already do).
3. Add `mut_wf` well-formedness ONLY to exclude a genuinely malformed sub-case.
4. Witness it in `semtest.ml`: show `DSL_mut = VM_mut` AND that mutation changes the
   verdict vs the verdict-only `eval_chain` (the adversarial check).

**Register readback lemmas** (in `Correct.v`, reuse for any field-loading
statement): `alloc_regs_app`/`slots_of` (split a key++data allocation),
`write_fields_app`, `map_write_fields_app_l` (read the key prefix of a key++data
load), `write_fields_concat_key`/`write_fields_concat_key_app` (concat key = concat
of field values), `write_fields_data_head` (first data register = first data
field's value), `skipn_map_snd_alloc_app` (the data register a dynset compiles to).

**Discriminator pattern (variant without changing rendering).** When two DSL
constructs compile to the *same* rendered instruction but need different semantics
(e.g. `SDynset` field-data vs `SDynsetImm` immediate-data, both `dynset … sreg_data`),
add a flag to the Bytecode instruction that `codec.ml` **ignores** (so corpus
byte-identity is untouched), set it in `compile_stmt`, and branch on it only in the
semantics. `IDynset`'s `fdata : bool` is the worked example.

**Cross-packet preservation.** `eval_chain_mut_env`/`run_chain_mut_env` return
`(verdict, env)`; `seq_eval_env` threads that env into the next packet;
`compile_seq_mut_correct` is the theorem. Per-packet fields (`pkt_meta`/`pkt_sock`/…)
are *not* carried across packets (they are local), only `env` is.

## Remaining work (TODOs for a fresh session)

Each item says what's missing, why it matters, a concrete plan, the risks, and how
to validate. Ordered roughly by value × tractability.

### TODO 1 — Flow-keyed conntrack table  ✅ DONE (2026-06 adversarial audit)
**Status: DONE.** The plan below was executed by the audit (`../adversarial.md`): `env`
now carries `e_ct : data -> ct_key -> data` keyed by `pkt_flow`; `Syntax.do_load`'s `LCt`
and the VM `ICtLoad` read it; `set_ct` writes the flow entry for writable keys
(mark/label/secmark); read-only keys (state/status/direction/expiration) are flow-derived;
`notrack` and `ct … set` follow the kernel's entry-present/absent guards; ct-state INVALID
bit fixed; `connlimit` is a flow-keyed conncount. A `ct mark set` on one packet is read
back by a later packet of the same flow (and reply direction). Kept for the original
problem framing / plan:

**Missing (original).** `ct` was a per-packet oracle: `Syntax.do_load`'s `LCt k => pkt_ct p k`,
and `ct set` mutates the *packet* (`set_ct`, threaded within one packet only). The
real conntrack table is keyed by flow (5-tuple) and accumulates across packets
(`ct count`, `ct state`, `ct mark` learned on packet 1 seen on packet 2 of the same
flow).
**Why it matters.** Stateful firewalling (`ct state established accept`) is the
single most common real nftables idiom; today its cross-packet, per-flow nature is
abstracted away.
**Plan.**
1. `Packet.v`: add a `flow_key` type (model as `data`, the canonicalised 5-tuple)
   and `e_ct : flow_key -> ct_key -> data` to `env`; add `pkt_flowkey : flow_key`
   to `packet` (packet-determined, like `pkt_fibkey`).
2. `Syntax.do_load`: `LCt k => e_ct e (pkt_flowkey p) k`. Mirror in the VM
   `ICtLoad` case in `Semantics.run_rule` AND `run_rule_writes`.
3. Replace `set_ct` (packet mutator) with an `env`-level `env_ct_upd e flow k v`
   (threaded through the `env` half of the evaluators' state).
   `ICtSet`/`SCtSet` then mutate `env` (like the dynset), so a `ct mark set` is
   visible to later rules AND (via `seq_eval_env`) later packets of the same flow.
4. `Correct.v`: the `SCtSet` case in `run_compile_body_writes` moves from the
   `writes_vsrc_simple`/`set_ct` path to an env-write path analogous to the dynset
   set case (reuse `run_vsrc_value`/`writes_vsrc_simple` for the value, then the
   env update). Re-prove `compile_chain_mut_correct`; add a `compile_seq_mut`
   witness for cross-packet `ct mark`.
**Risk.** `do_load`'s `LCt` change ripples into *every* match proof that reads a ct
field (they go through `compile_load_correct`, which should realign since both
sides read `e_ct`, but expect to touch `run_compile_matches_const` ct sub-cases).
Do it incrementally: first relocate the READ (`do_load` + VM load) and re-green
everything, THEN relocate the WRITE (`set_ct` → env). Two separate green commits.
**Validate.** `make proofs` (10 axiom-free), corpus/difftest/validate unchanged
(ct *rendering* is untouched — only the semantics of `LCt`/`ICtSet` change), and a
new semtest: packet 1 `ct mark set 0x1`, packet 2 of the same flow `ct mark 0x1
accept` → `[…; accept]`, with a *different* flow staying at the policy.

### TODO 2 — Immediate-data dynset feedback (`SDynsetImm`, `add @m {key : 10.0.0.1}`)
**Missing.** A dynset whose map data is immediate constants compiles to
`IDynset … (Some dreg) false` and is left env-neutral (the `fdata=false` path). Only
field-data map dynsets (`fdata=true`) are modelled.
**Why it matters.** Completeness of map learning; lower value than TODO 1 (constant
map data is rarer than field/conntrack-derived data).
**Plan.** Make `fdata=false` a write too. The data value is the immediate at `dreg`:
define `imm_at (r) (dimms) := fold_left (fun acc rv => if Nat.eqb (fst rv) r then snd rv else acc) dimms []`
(last write wins, matching `set_reg` order); `body_writes` for `SDynsetImm` uses
`imm_at datareg dimms`. Prove `load_imms`-readback: running the `IImmediateData`
prefix leaves `dreg` holding `imm_at datareg dimms` **when** `datareg ∈ map fst dimms`
(a fold-independence lemma: a matching key overrides the initial register value).
Add that `existsb (fst = datareg) dimms` to `simple_body` as a well-formedness
(true for every corpus rule). Then handle `SDynsetImm` in `run_compile_body_writes`
and add it to `is_mut_stmt`; flip its `IDynset … (Some _) false` to a write in
`writes_instr`/`straight_instr`.
**Risk.** Low–moderate; the only new lemma is fold-independence. **Validate.**
semtest: `add @m {ip saddr : 0x1}; meta mark set ip saddr map @m; meta mark 0x1 accept`.

### TODO 3 — Payload-mangle visible to later rules  🔶 NAT done, payload-mangle open
**NAT: DONE (2026-06 audit).** NAT address/port rewrite is now modelled — flow-stateful
mapping in `e_nat`, L3 (IPv4 header) + L4 (TCP/UDP) checksum updates, zero-UDP-csum
untouched (RFC 768), reply-direction un-NAT of address *and* port, `NF_DROP` on a
no-usable-address interface, ip6-family geometry, inet-table runtime L3 dispatch. Because
NAT is terminal, its rewrite is observed across hooks by the whole-chain trace evaluator
`eval_chain_trace` (see `Optiplex_Mark.v`'s `streaming_flow_whole_ruleset`).
**STILL OPEN — payload-mangle.** `payload set` (mangle), `ip dscp set`, ttl/hoplimit are
still verdict-neutral straight-line statements (`SMangle` is not an `is_mut_stmt`), so a
later rule reading the mangled bytes sees the original.
**Plan.** Add a `set_payload p base off len v` packet mutator (like `set_meta`),
extend `run_rule_writes`/`body_writes` for `SMangle`/`IPayloadWrite` (the value is
already `compile_vsrc`/`eval_vsrc`, reuse `writes_vsrc_simple`). NAT is *terminal*,
so its rewrite is only observable by a *different* hook's chain — model it in the
`eval_ruleset`/`run_ruleset` dispatch (carry the rewritten packet to the next base
chain) rather than within one chain. **Risk.** Moderate; `read_payload`/`slice`
readback after a partial-overwrite needs a small byte-splice lemma. **Validate.**
semtest: `ip daddr set 1.2.3.4 ; ip daddr 1.2.3.4 accept`.

### TODO 4 — Concat-key 4-byte register-slot padding  ✅ DONE (2026-06 audit)
**Status: DONE.** The 2026-06 audit (`13ee781`, with `43202ed`) modelled concat-set
membership as per-field cross-product with each stored element split by its 4-byte
register slot (ifname = 16), not raw field widths — matching the kernel's register layout
for sub-4-byte concatenated fields. This was substantiated against the kernel source
rather than the (set-blind) corpus, and it underpins the anti-spoofing proof's
`ip daddr . oifname @vmantispoof` key. A live data-plane set-membership oracle
(netns + crafted packet) remains desirable as an independent check, but the byte layout is
no longer an unvalidated guess.

### TODO 5 — Meters / `numgen` incremental state  🔶 numgen done, meter open
**`numgen inc`: DONE (2026-06 audit, `ee5193a`).** Modelled as a shared persistent
round-robin counter `e_numgen : numgen_spec -> nat` in `env` (a `numgen` reads
`(e_numgen spec mod ng_mod) + ng_offset`), not a per-packet oracle — so successive
packets advance it. **STILL OPEN — `meter`.** Per-key dynamic rate limiting (a meter =
a dynset with a per-key limiter) is not yet modelled; it composes the now-built flow/env
state (TODO 1) with the dynset feedback. **Validate.** semtest sequence showing the meter
rate-limit per key.

### TODO 6 — Netlink emitter shim (libnftnl), end-to-end to a live kernel
**Missing.** The pipeline stops at byte-identical netlink *text*. Add an untrusted
OCaml shim that emits real netlink via libnftnl, then round-trip
`compile → emit → nft list ruleset` against a live kernel and diff. This closes the
"text matches" → "kernel installs the same ruleset" gap. Untrusted + differentially
tested, like `glue.ml`.

### TODO 7 — More optimization passes (each needs `optimize_chain_correct` extended)
**The `nft -o` / `nft --optimize` consolidation passes are now ported and proved
in `theories/Optimize_Merge.v` (all axiom-free, `Print Assumptions` clean):**
- **Abstract adjacent-rule merge** `eval_rules_merge2`: replacing two adjacent
  rules `r1; r2` by one `r12` preserves `eval_rules` on every packet, given that
  `r12` is loadable / outcomes exactly as each original and **applies iff EITHER
  original applies** (the head selector is the *disjunction* of the two). This is
  the soundness core of every `nft -o` value/vmap merge (`MERGE_BY_VERDICT` in
  upstream `src/optimize.c`).
- **Value-merge from a disjunction certificate** `eval_rules_value_merge`: two
  rules `mk_head m1 rest r1` / `mk_head m2 rest r1` (identical but for the head
  match value) collapse to `mk_head m12 rest r1` when `m12` loads the same field
  and `eval_matchcond m12 = eval_matchcond m1 || eval_matchcond m2` — exactly the
  anonymous-set merge `tcp dport 22 accept` + `tcp dport 80 accept` ⇒
  `tcp dport { 22, 80 } accept`, at the matchcond level.
- **Concrete contiguous-range certificate** `eval_rules_range_value_merge`
  (GUARDED): the value-merge instantiated to a single range —
  `f 6, f 7 ⇒ f 6-7` — discharged via `range_byte_split` for a **single-byte**
  selector (guard: `length (field_value f p) = 1`, since a multi-byte bound is a
  prefix test for which a contiguous two-element set is *not* one range). This is
  the env-free, no-new-constructor instance `nft` itself coalesces a contiguous
  anonymous set into.
- **Consecutive-duplicate-rule elimination** `dedup_adj` / `eval_rules_dedup_adj`:
  a full bottom-up `verdict`/`vsrc`/`stmt`/spec `eq_dec` hierarchy up to
  `rule_eq_dec` is built; dropping the second of two byte-identical adjacent rules
  is the `r1=r2` instance of `eval_rules_merge2`. Folded into the runnable
  top-level `optimize_chain2` (= `optimize_chain` then `dedup_adj`), proved
  verdict-preserving by `optimize_chain2_correct`.
- **Value → anonymous SET, as an EXECUTABLE table-level rewrite** (the headline
  `nft -o` pass) `optimize_rules_sets` / `optimize_chain_sets`, proved
  `optimize_chain_sets_correct` (axiom-free). On an adjacent pair
  `tcp dport 22 accept` / `tcp dport 80 accept` it **mints a fresh `__setN`**,
  **emits its element declaration** `[(22,22);(80,80)]` into `sd_sets`, and rewrites
  the pair into ONE `MConcatSet [dport] false __setN accept` — exactly
  `nft -o`'s `tcp dport { 22, 80 } accept` (the anonymous set interned by name, the
  way the parser's `intern_anon_set` already does it; the corpus round-trips
  `__setN`). Correctness is end-to-end over the *table* semantics WITH the
  synthesised set in scope: `eval_chain c' (set_env p (env_with_sets base d')) =
  eval_chain c (set_env p (env_with_sets base d))`, discharged via the disjunction
  certificate `concat_set_two_points` (`set_mem = existsb data_in_iv` over two point
  intervals = `orb` of the two `MCmp f CEq`) + `eval_rules_merge2`. **Guards** (both
  fire on the real `nft -o` examples): the differing dimension is a single
  `MCmp f CEq` over a **fixed-width payload field** (`field_fixed_len f = Some
  (length v)`, so `MCmp`'s prefix equality coincides with the set's full-width
  membership), the rest of the two rules is syntactically equal, and the minted
  `__setN` names are fresh (`setname_inj` + the prepend-only freshness lemma). A
  `semtest` witness (6c) runs it on the demanded input: `2 → 1` rules, set
  `__set0 = { 22, 80 }` synthesised, verdict preserved on every packet.
  NOTE: this corrects an earlier *infidelity* — `eval_rules_range_value_merge`
  modelled `6,7 ⇒ 6-7` as a RANGE, but `nft -o` emits a discrete SET `{ 6, 7 }`;
  the value→set pass is the faithful consolidation (discrete elements).

- **Value+verdict → VERDICT MAP, as an EXECUTABLE table-level rewrite** (the
  `nft -o` vmap pass) `optimize_rules_vmap` / `optimize_chain_vmap` in
  `theories/Optimize_Vmap.v`, proved `optimize_chain_vmap_correct` (axiom-free).
  On an adjacent pair `tcp dport 22 accept` / `tcp dport 80 drop` (same selector,
  **differing terminal verdicts**) it **mints a fresh `__vmapN`**, **emits its
  key→verdict declaration** `[(22,22,accept);(80,80,drop)]` into `sd_vmaps`, and
  rewrites the pair into ONE rule whose terminal is `r_vmap` keyed on `dport`
  against `__vmapN` (with a `Continue` fall-through so a vmap MISS proceeds to the
  next rule) — exactly `nft -o`'s `tcp dport vmap { 22 : accept, 80 : drop }`.
  Correctness is end-to-end over the table semantics WITH the synthesised vmap in
  scope (`eval_chain c' (set_env p (env_with_sets base d')) = eval_chain c (set_env
  p (env_with_sets base d))`), discharged via the two-point vmap certificate
  `vmap_two_points` (`assoc_verdict` over two point keys = `w1`/`w2`) and the
  dedicated first-match collapse `eval_rules_vmap_merge2` (the merged rule applies
  on more packets, but on the extra ones the vmap MISSES → outcome `None` → treated
  exactly as "did not apply"). **Guards** (both fire on the real `nft -o` example):
  the differing selector is `MCmp f CEq` over a **fixed-width payload field**
  (`field_fixed_len`), the two verdicts are **terminal** and **distinct**, the two
  rules are otherwise the identical pure-terminal `orig_rule` shells, and the
  minted `__vmapN` names are fresh (`vmapname_inj` + the prepend-only stability
  lemma). A `semtest` witness (6d) runs it on the demanded input: `2 → 1` rules,
  vmap `__vmap0 = { 22 : accept, 80 : drop }` synthesised, verdict preserved on
  every packet (22→accept, 80→drop, miss→policy).

- **Two selectors → CONCATENATION SET, as an EXECUTABLE table-level rewrite** (the
  third headline `nft -o` pass) `optimize_rules_concat` / `optimize_chain_concat`
  in `theories/Optimize_Concat.v`, proved `optimize_chain_concat_correct`
  (axiom-free). On an adjacent pair `ip saddr 1.1.1.1 tcp dport 22 accept` /
  `ip saddr 2.2.2.2 tcp dport 80 accept` (differing in **two** selectors, same
  verdict) it **mints a fresh `__setN`**, **emits its packed per-field point
  tuples** `[(pack2 1.1.1.1 22, …);(pack2 2.2.2.2 80, …)]` into `sd_sets` (each
  field in its 4-byte register slot, the last field taking the remainder, exactly
  the kernel's NFT_SET_CONCAT layout), and rewrites the pair into ONE
  `MConcatSet [saddr;dport] false __setN accept` — exactly `nft -o`'s
  `ip saddr . tcp dport { 1.1.1.1 . 22, 2.2.2.2 . 80 } accept` (confirmed by the
  live `unshare -rn nft -o -f` oracle). Correctness is end-to-end over the table
  semantics WITH the synthesised set in scope, discharged via the two-field
  cross-product membership certificate `concat_in_iv_two_points`
  (`concat_in_iv [va;vb] (pack2 a b, pack2 a b) = data_eqb va a && data_eqb vb b`)
  lifted to `concat_two_fields_certificate` (the merged head = `orb` of the two
  per-row conjunctions `f1=a_i AND f2=b_i`) + the two-field merge backbone
  `eval_rules_concat_merge2` (over `eval_rules_merge2`). **Guards** (fire on the
  real `nft -o` example): BOTH differing dimensions are `MCmp f CEq` over
  **fixed-width payload fields** (`field_fixed_len`), the two rules are otherwise
  the identical `orig_rule2` shells, the two tuples are distinct (not a duplicate),
  and the minted `__setN` names are fresh (`setname_inj` + the prepend-only
  stability lemma). A `semtest` witness (6e) runs it on the demanded input:
  `2 → 1` rules, concat set `__set0 = { 1.1.1.1 . 22, 2.2.2.2 . 80 }` synthesised,
  verdict preserved on hits, a cross-miss, and a saddr-miss (→ policy).

NOT yet ported (honest gaps): the value→set / vmap / concat passes on
*variable-width* selectors (guarded out, since a prefix `MCmp` is not full-width
set membership there). The earlier "sets can't be synthesised by a chain pass"
claim was **wrong** and is now retired: anonymous sets, verdict maps, AND
concatenation sets ARE named objects, and the table-level `set_decls` rewrite
synthesises them with no new constructor. All three headline `nft -o` merge
families (value→set, value+verdict→vmap, two-selector→concat-set) are now ported
as runnable, verdict-preserving, axiom-free passes.

### TODO 8 — (future) Data-plane interpreter + VST
A data-plane bytecode *interpreter* spec (what the C engine does to a packet) and
VST proofs that the C interpreter meets it (CompCert/clightgen). This is the
"end-to-end verified implementation" north star beyond the control-plane compiler.

### TODO 9 — Menhir frontend: `.nft` text → DSL AST  (LARGELY DONE 2026-06)
**Status (2026-06): implemented, and — crucially — the proofs are about the
parser's OUTPUT, not a hand copy.** The pipeline:

  `.nft` text → `lexer.mll` (ocamllex) + `parser.mly` (Menhir) → surface tree
  (`nft_ast.ml`) → **`nft_lower.ml`** → trusted `Syntax` AST + `Packet.env`.

`nft_lower` does nft's frontend NAME RESOLUTION, untrusted: expands `define`s
(`$v`), resolves symbolic constants (services like `https`, `ethertype`/
`l4proto`/`ct state`/`icmp` names) to the TYPED value of the selector's
datatype (`typed_atom : kind -> value -> Nftval.nftval`), inserts the implicit
`meta l4proto` dependency (emitted as the `BDep`-tagged conjunct), and turns
named-set/map *declarations* (and inline anonymous `{…}` sets / `vmap {…}`
maps, incl. **concatenated** keys like `ip daddr . oifname`) into named `env`
entries — anonymous sets DEDUPLICATED by contents.  The typed value -> register
bytes step is NOT frontend code: every match immediate is produced by the
VERIFIED `Nftval.encode` / `Elab.elab_m` (`enc_atom` is literally
`encode ∘ typed_atom`), the CIDR byte-alignment split lives in the verified
`Elab.prefix_expand`, and `Elab.elab_matchcond_correct` proves the elaborated
term evaluates exactly as the typed source.  `Nft_parse.parse_file` adds
`include` expansion (relative to the file dir).

**The proof bridge (`nft_emit.ml` + `nft2coq`).** `make gen` runs the parser on a
`.nft` file and EMITS its AST as Coq terms — `theories/Optiplex_Gen.v`,
`theories/Ruleset_Gen.v` define the parsed chains and the `set_decls`/`env` their
lookups read.  The proof files `Require Import` these and prove properties about
the *parser's actual output*, closing the previously-eyeballed "the AST mirrors
the text" link.  `nft2coq` IS the frontend; the emitted `.v` is checked by the
Rocq kernel (untrusted emitter, kernel-checked result — same trust story as the
renderer).

**Proven about the parsed rulesets (all axiom-free):**
  - `Ruleset_Verified.v` — the 8 packet-verdict properties of `../rulesets/ruleset.nft`
    (established/invalid/loopback/ssh/smtp/ipv6-nd/forward), now about the
    *generated* `firewall_inbound` rather than a hand copy.
  - `Optiplex_Antispoof.v` — **anti-spoofing** for `../rulesets/optiplex.nft`'s bridge
    `output` chain: a frame to a protected VM address leaving br.20 on the wrong
    interface is **dropped** (`antispoof_general`; concrete
    `vikunja_cannot_spoof_budget`, `gentoo_cannot_spoof_hass`), while the legit
    bound pair is **accepted** (`budget_legitimate_allowed`).
  - `Optiplex_Antispoof_Gaps.v` — **adversarial** analysis proving the binding is
    UNENFORCED outside its guards: any destination not in `@vmaddrs`
    (`unlisted_daddr_unconstrained`, `spoof_to_unlisted_address`) and any egress
    port other than br.20 (`other_bridge_port_bypasses_binding`) bypass the drop.
    Real findings: the protection covers only the enumerated addresses, only on
    br.20.
  - `Optiplex_Mark.v` — the **firewall mark (0x99)** machinery, end-to-end.  A
    game-streaming packet (dport 48010) is run through the WHOLE prerouting chain
    by `eval_chain_trace` (a packet-returning whole-chain evaluator added to
    `Semantics.v`, proven verdict-identical to the verified `eval_chain_mut` by
    `eval_chain_trace_verdict`): it flows PAST rule 1 (the 3389 rule, which does
    not match — `pre1_streaming_noop`) and is matched by rule 2, which BOTH marks
    the packet (the body) AND destination-NATs it (the terminal `dnat ip to
    $windows` = 192.168.51.186).  The headline `streaming_prerouting_io`
    characterises **what comes out**: `eval_chain_trace filter_prerouting p =
    (Accept, apply_nat … pre2 (set_meta p MKmark 0x99))` — the marked packet with
    the terminal dnat applied; `pre2_apply_dnat` shows the dnat rewrites the
    destination address to the windows box, and `streaming_prerouting_mark` shows
    the mark SURVIVES it.  `streaming_flow_whole_ruleset` then carries that packet
    to the postrouting hook, where the (surviving) mark drives the masquerade rule
    (`masquerade_gated_on_mark`) and the chain accepts; the cross-hook skb mark is
    threaded explicitly (the model evaluates per base chain).  The postrouting
    masquerade is in an `inet` table, so its L3 family is resolved per-packet
    (`nat_addrfamily_pkt = pkt_l3_family`, the audit's inet-runtime-dispatch fix);
    the IPv4-flow masquerade lemmas carry `pkt_l3_family p = "ip"`.  (Parsing these
    rules added `fib daddr type` matches; the live `define windows` makes the dnat
    target a real IPv4 literal — an UNDEFINED `$var` in a NAT target now fails the
    parse loudly, mirroring `nft -f`, rather than being silently dropped.)

**Validation (`make parse-test`, all green):** (A) parsed `ruleset.nft` run
through the extracted `eval_table` reproduces the 8 proven verdicts; (D) parsed
`optiplex.nft` reproduces the anti-spoofing Drop/Accept AND the proven bypasses;
(B) the difftest ruleset lowers structurally equal to `glue.ml`'s known-good AST;
(C) best-effort live `nft --debug=netlink` round-trip is byte-identical.

**Stress test (stock nftables examples + real rulesets).** `/usr/share/nftables/*`
and `/usr/share/doc/nftables/examples/*`: **14/18 fully parse+lower+compile**
(all ipv4/ipv6/inet/arp/bridge/netdev filter·nat·mangle·raw, `all-in-one` via
`include`), plus the two real-world rulesets (`optiplex.nft`, `ruleset.nft`)
which are far richer.  The 4 that fail do so **loudly** (clean `Parse_error`/
`Unsupported`, never a mis-parse) on genuinely advanced features outside the
supported subset: `ct helper … set` assignment-by-map, SELinux `secmark`
value-maps, `dnat to numgen … map` load-balancing, and one exotic value encoding.

**Still open:** value maps with non-verdict (object/address) data; the advanced
NAT/helper-set forms above; matching nft's exact `__setN` anonymous-set numbering
(ours is internally consistent, not byte-compared — sets aren't in the corpus).

**Original framing (kept for the open items).**
There is no parser from nftables DSL *text* to the extracted
`Syntax` AST (`chain`/`table`/`ruleset` + the `env`/`set_decls` the lookups read).
Today a user with a real ruleset must hand-translate it — see
`theories/Example_Ruleset.v`, which encodes `../rulesets/ruleset.nft` by hand and proves
properties against `eval_table`. That manual step is the one *unverified* link:
the proofs check AST→verdict soundness, but "the AST mirrors the `.nft` text" is
eyeballed. A differentially-tested parser closes that gap and lets users prove
properties about their own rulesets directly (the use case in the project brief).

**Why it matters.** It turns the verified core into a usable tool: feed a `.nft`
file, get an AST you can state theorems about (and, via `compile_table_correct`,
have them hold of the installed bytecode). It also makes `Example_Ruleset.v`'s
hand-translation reproducible/checkable instead of trusted.

**Trust story (unchanged TCB).** The parser is **untrusted glue**, like
`glue.ml`/`corpus_test.ml`: it builds inputs out of the trusted `Syntax`
constructors. It earns trust the same way the rest of the glue does — a
**round-trip differential test against live `nft`** (see Validate). Nothing about
the parser enters the proof TCB.

**Architecture decision to make FIRST (do not skip).** Two routes; weigh before
coding:
  - **(A) Surface-syntax parser (what "Menhir" implies).** `ocamllex` + Menhir
    over the nft DSL grammar directly. Most user-friendly (parses the file the
    user already has) but you must **re-implement nft's frontend logic** —
    implicit protocol dependencies, anonymous-set anonymisation, `define`/include
    expansion — in untrusted code, with divergence risk.
  - **(B) Parse `nft --json` / `nft --debug=netlink` output.** Let real `nft` do
    the lowering; parse its *structured* output into the AST. Far less parser
    logic and more faithful (nft is the oracle), at the cost of requiring `nft` at
    parse time. `corpus_test.ml` already parses the netlink `.t.payload` format, so
    there is precedent and reusable code.
  The user asked for Menhir (A); **start there**, but lift the dependency-inference
  and set-anonymisation passes from nft's behaviour and lean hard on the
  differential test. If (A)'s frontend logic balloons, (B) is the escape hatch.

**Plan (incremental, each milestone gated by the round-trip difftest).**
1. **M1 — minimal grammar = the `ruleset.nft` example.** `extracted/lexer.mll` +
   `extracted/parser.mly` for: `table`/`chain` blocks, base-chain metadata
   (`type filter hook input priority N; policy P;` → `hooked_chain`'s
   hook/prio/policy), `accept`/`drop`/`jump`/`goto`/`return`, simple matches
   (`iifname`, `meta protocol`, `ct state`, `tcp dport`), inline sets `{a,b,c}`
   and vmaps `{ k : verdict }`. Build a `chain` + the `env` (sets/vmaps). **Acceptance:
   parse `../rulesets/ruleset.nft` and check the resulting `inbound` AST/verdicts agree with
   the hand-written `Example_Ruleset.v`** (a concrete first oracle, independent of nft).
2. **M2 — anonymous set/map allocation.** Inline `{…}` must become a named
   `MConcatSet … "name"` + an `env`/`set_decls` entry, with names matching what
   `Compile`/`codec.ml` expect (see how `corpus_test.ml` reconstructs `__setN`).
3. **M3 — implicit dependencies (the faithfulness crux).** `tcp dport` inserts
   `meta l4proto tcp`; `udp`/`icmp`/`icmpv6`/`ip`/`ip6` likewise; payload matches
   add their network/transport-header deps. Replicate nft's insertion order
   exactly — this is where surface parsing most easily diverges; the difftest is
   the only real check.
4. **M4 — the corpus match/stmt vocabulary.** Ranges, CIDR prefixes (`/24` →
   `MMasked`/interval), masks, concatenations, transforms (bitwise/shift/
   byteorder/jhash), counters/log/limit, NAT/redirect, named-set/map *declarations*
   (`set s { type … ; elements = … }` → `set_decls`). Grow against the difftest.
5. **M5 — whole-file structure.** Multiple tables, user chains, `define`
   variables, `include`, `flush ruleset`; assemble a `ruleset`/`hooked_chain` list
   (hooks + priorities) for `eval_hook`/`compile_hook`.
6. **M6 — facade + CLI.** `parse_file : string -> ruleset` in `nftc.ml{,i}`; a
   `dune exec` CLI that parses, optimises, and renders. Wire `lexer.mll`/`parser.mly`
   into `dune` (menhir + ocamllex stanzas).

**Risks.** (1) Re-implementing nft's dependency inference / set anonymisation in
untrusted code is the main divergence risk — mitigate with the difftest and by
**failing loudly** on any construct outside the supported subset (never silently
mis-parse; raise `Unsupported "<construct>"`). (2) The surface grammar is large
and partly underspecified — target the corpus subset, error otherwise. (3)
`define`/`include`/arithmetic: decide whether to expand them in the parser or
pre-process with `nft --check` first.

**Validate (reuses existing infrastructure — the key enabler).** The forward
pipeline already renders AST→netlink text and diffs it against live `nft`
(`make difftest`, `difftest.sh`). So a parse is faithful iff
`parse(file) |> compile_optimized |> to_netlink_text` is **byte-identical** to
`nft --debug=netlink -f file`. Add a `make parse-test` target that runs this over
a corpus of real `.nft` files (start with `../rulesets/ruleset.nft`; then nftables'
`files/examples/*.nft` and `doc/` rulesets). Same honest scope as the existing
round-trip: it checks structural lowering, not the byte-level data-plane meaning.

**Files / build notes.** New hand-written `extracted/lexer.mll`,
`extracted/parser.mly`, and a builder `extracted/nft_parse.ml` (text → `Syntax`
AST + `env`); extend `nftc.ml{,i}`. Remember `proof/.gitignore` ignores
`extracted/*.ml{,i}` — hand-written sources are force-added (`git add -f`); add
`.mll`/`.mly` to the ignore-exceptions too. In hand-written `.ml`, qualify
`Stdlib.List`/`Stdlib.String` (the extracted `List`/`String` shadow them). Use
the extracted constructors directly (the same ones `Example_Ruleset.v` uses:
`MEq`/`MConcatSet`/`vmap_spec`/`Jump`/…).
