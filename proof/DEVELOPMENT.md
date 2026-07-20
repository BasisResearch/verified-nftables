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
  (`run_rule_step` on `IDynset _ None`, `body_step` on `SDynset _ _ _ []`), so a
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

  *Status: FIXED — cross-rule (2026-06) AND intra-rule (T1 single-fold).* The
  per-rule semantics is ONE left-to-right fold (`Semantics.rule_step` /
  `Semantics.run_rule_step`), exactly the kernel's expression walk
  (nf_tables_core.c `nft_rule_dp_for_each_expr`): every expression — a match,
  a statement operand, the verdict-map key, a limiter check — sees the writes
  (packet-local `set_meta`/`set_ct` AND dynset `env_set_upd`/`env_map_upd`)
  of the expressions before it in the SAME rule; a failing match or breaking
  load stops the walk keeping the earlier writes; statements after a terminal
  verdict never run; `r_after` statements (writes included) run only on a
  `Continue` fall-through.  `eval_rules_mut`/`run_program_mut` (and
  `eval/run_chain_mut`) thread the state a rule leaves to the next rule, so
  BOTH the cross-rule and the intra-rule `meta mark set 0x1 … meta mark 0x1
  accept` forms now ACCEPT (positive pins:
  `Regression/Setread_IntraRule.v`; intra-rule dynset feedback — `add @s
  {key}` then `@s` lookup in ONE rule — is pinned there too).  The theorem
  **`compile_chain_mut_correct`** (axiom-free) proves
  `run_chain_mut (compile_chain c) policy = eval_chain_mut c` for every
  numgen-free rule — `rule_numgen_free` is the strand's ONLY hypothesis, and
  `Lower_Proofs.lower_ruleset_numgen_free` discharges it for EVERY
  frontend-emitted program (the lowering refuses incremental numgen
  fail-loud, `Lower.LEnumgen`).  Matches, meta/ct sets, set-dynsets, AND
  every other statement (mangle, NAT, dup, counter, log, map-dynset, exthdr,
  objref, …, threaded as state-neutral via the `straight`-line-prefix lemma)
  are in scope; semtest witnesses a rule *mixing* `counter`/`log` with the
  meta-set.  Built on the operand value-correctness `eval_vsrc vs p =
  (regfile after compile_vsrc vs) 1`, proved for EVERY operand kind
  (immediate, field(+transforms), value map (any key transform), `VMapT`,
  jhash, jhash-map, OR-fold — including the degenerate zero-field shapes,
  whose source register the compiler now pins with an `IImmediateData _ []`,
  keeping the bridge unconditional).  The historical `mut_wf` well-formedness
  hypothesis is GONE (see "Known model infidelities" for the flipped entry).

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
- ⛔ STILL OPEN — **shared byte-level primitives with no external oracle**:
  `data_jhash` is a structural abstraction of the kernel's Jenkins hash (a kernel
  differential would fail BY DESIGN), and `data_byteorder` ignores its `hton` and
  `len` parameters (safe only under the producer invariant stated on its docstring
  in `Core/Bytes.v`). Both are shared by the DSL and the VM, so every compile
  theorem is blind to them and **no shipped gate can catch a divergence there** —
  see "Eyeball-trusted, never-differentially-tested semantics" in the Trust story
  below for the full statement and what a closing gate would take.

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
  to later rules); and two *confirmed divergences inside the modelled features*
  (limiter sweep past a failing match, `OVmapNat` vmap-hit trace NAT) are
  ledgered in **"Known model infidelities"** below (the third — intra-rule
  set-then-read — is REPAIRED by the T1 single-fold rule semantics; positive
  pins in `Regression/Setread_IntraRule.v`).
- ✅ **(4) Explicit tables** (D-ish): FIB done (`lpm_fib`); the **conntrack table is
  now flow-keyed** (`e_ct`, keyed by `pkt_flow`) by the 2026-06 audit — `ct
  mark`/`state`/`direction`/`connlimit` accumulate across a flow's packets. (See TODO 1
  and `../adversarial.md`.)
  ⛔ Caveat on the KEY itself: **`pkt_flow` is an opaque packet oracle** — nothing
  ties it to the header bytes' direction-normalised 5-tuple (+ l4proto/zone), the
  same residual `Fib_Local.fibkey_wf` closed for the *fib* key (and closed only for
  the four IPv4 daddr/saddr selectors it pins).  The ct/NAT theorems are congruences over that opaque
  key, so their transfer to a real skb rests on an unverified injective-
  canonicalisation assumption; a `flow_wf` layer analogous to `fibkey_wf` is the
  designated de-oracling step.  Full rationale: the `pkt_flow` comment in
  `theories/Core/Packet.v`; scope note in `THEOREMS.md` §1.
- ✅ **(5) Data fidelity** (D): interval/prefix sets, wildcard ifnames, and **concat-key
  register-slot padding** are done — the 2026-06 audit's `13ee781` splits a stored
  concat element by 4-byte register slots (ifname = 16) rather than raw field widths, so
  sub-4-byte concatenated fields now match the kernel layout (this underpins the
  anti-spoofing proof's `ip daddr . oifname` key).

So the headline honest gaps remaining are: **payload-mangle and immediate-data-dynset
mutation threading**, **`meter`** state, the **un-de-oracled packet keys**
(`pkt_flow` — see the (4) caveat above — plus `pkt_fibkey` beyond the four
`fibkey_wf`-pinned selectors, and `pkt_inner`), the **netlink emitter shim** (TODO 6),
and the **VST data-plane layer** (TODO 8) — plus the standing framing caveat that this is
internal consistency against a self-authored semantics, with kernel fidelity now resting
on the 2026-06 adversarial audit (`../adversarial.md` — see its evidence-class ledger:
most fixes are backed by kernel *source reading* + golden control-plane payloads, few by
kernel-executed packet differentials) and `make validate` (28/28) rather than the
corpus round-trip. Additionally, two **confirmed model-vs-kernel divergences inside
modelled features** are known and deliberately left open — the ledger below.

## Known model infidelities (open, confirmed)

Unlike the ⛔ items above (features not yet modelled), these are behaviours the
model **does** exhibit that are **confirmed wrong against linux-6.18.33** — found
by re-interrogating the semantics after the 2026-06 audit converged (so
`../adversarial.md`'s "red satisfied" is scoped by this list). They are
documented and **pinned** rather than fixed here because each repair is a
*semantics change* (it moves verdicts/effects), which belongs to the
adversarial-semantics-audit track with its own red-verification loop — not to a
documentation/legibility milestone. Every entry is locked in by a `vm_compute`
theorem in [`theories/Regression/Known_Infidelities.v`](theories/Regression/Known_Infidelities.v)
that pins the **model's divergent behaviour**: a future fidelity fix MUST flip
that pin (it becomes unprovable) and update this ledger, so the divergence can
be neither forgotten nor silently half-fixed. The DSL and the VM **agree** on
both (the compiler theorems are honest); the divergence is model-vs-kernel.

**1. The limiter sweep depletes buckets the kernel never evaluates.**
- *Kernel*: a rule's expressions run left-to-right; a failing match sets
  `NFT_BREAK` and ends the rule (nf_tables_core.c `nft_do_chain`'s
  per-expression verdict check), so in `ip saddr 1.2.3.4 limit rate 1/second
  accept` a non-matching packet never reaches `nft_limit_eval` — **no token is
  consumed**.
- *Model*: `dsl_step` applies `limit_sweep_body` (and `vm_rule_step` applies
  `limit_sweep_prog`) **unconditionally over the whole rule body**
  (`Semantics.v`, the sweep definitions + `dsl_step`), draining every
  `limit`/`quota`/`connlimit` the rule *contains* — even past a failing earlier
  match or a breaking load.
- *Repro*: a `meta mark 0x1 limit rate 1/second accept` chain on a
  non-matching packet leaves `e_limit = 0` (kernel: 1); verdict sequences over
  `seq_eval_env` then diverge observably from the kernel.
- *Pin*: `Known_Infidelities.gate_limit_drained` / `vm_gate_limit_drained`.
- *Why open*: the faithful shape folds the CONSUMPTION into the break-aware
  `body_step`/`run_rule_step` fold at the limiter's position (the CHECK already
  evaluates there against the running state; only the depletion remains a
  whole-body sweep at the `dsl_rule_step`/`vm_rule_step` boundary) — a semantics
  change on both sides (audit track).

**2. A vmap HIT on an `OVmapNat` rule still runs the trailing NAT in the trace
evaluator (including a spurious flow-state write).**
- *Kernel*: `… vmap {…} dnat/redirect …` — a vmap hit writes a non-CONTINUE
  verdict register and the rule's remaining expressions never evaluate
  (nf_tables_core.c per-expression verdict check); the trailing NAT runs only
  on a map **miss**. The repo's own verdict/loadability semantics agree
  (`Semantics.end_loadable`: "vmap HIT: terminal/r_after unreachable").
- *Model*: `eval_rules_trace` (`Semantics.v`) dispatches `nat_drops`/`apply_nat`
  on `r_nat r`, which projects the NAT out of `OVmapNat` **regardless of which
  outcome arm produced the terminal verdict** — so on a vmap HIT it still
  rewrites the packet **and stores a flow-keyed `e_nat` mapping**
  (`store_nat_mapping`) that later same-flow packets then reuse.
- *Repro*: a `meta mark vmap { 0x1 : accept } dnat to 10.0.0.1` rule on a
  mark-0x1 packet: trace verdict Accept (correct) but daddr rewritten to
  10.0.0.1 and `e_nat` populated (kernel: packet untouched, no NAT tuple).
- *Pin*: `Known_Infidelities.vmaphit_daddr_rewritten` /
  `vmaphit_stores_nat_mapping`.
- *Why open*: `dsl_rule_step` returns only the verdict, not which outcome arm
  produced it; the fix threads outcome provenance (or re-tests the hit) through
  the trace evaluator — a semantics change (audit track). Plain `ONat` rules
  (the corpus/ruleset-common shape) are unaffected.

**(repaired) 3. Intra-rule set-then-read.**  The historical third entry — the
one-rule `meta mark set 0x1 meta mark 0x1 accept` dropping where the kernel
accepts, an artefact of the retired two-fold verdict/write split — is FIXED by
the T1 single-fold rule semantics (`rule_step`/`run_rule_step` run every
expression against the running state).  Its pins flipped from divergence locks
to POSITIVE witnesses: `Regression/Setread_IntraRule.v`
(`setread_accepted`/`vm_setread_accepted`, the intra-rule dynset-feedback
pins, and the break-keeps-earlier-writes pins).

Cross-references: `THEOREMS.md` §1 scope notes and §3 (evaluator matrix);
`../adversarial.md` "Outcome" (scoping note). The in-source ⚠ KNOWN INFIDELITY
markers sit on `limit_sweep_prog` and `eval_rules_trace` in `Semantics.v`,
and on `OVmapNat` in `IR/Syntax.v`.

## What exists

`theories/` is organised by role — the directory listing answers "what must I
read to trust a theorem":

| Directory | Contents (trust role) |
|---|---|
| `theories/Core/` | the shared object language: bytes, verdicts, the packet record, the bytecode VM — read these to trust any statement |
| `theories/IR/` | the rule IR (`Syntax.v`) and the typed byte-domain view (`Nftval.v`) |
| `theories/Semantics/` | the evaluators (`Semantics.v`) plus the fib and multi-address network-state layers |
| `theories/Compiler/` | `Compile.v`, the correctness strata (`Correct.v`), the machine-checked entry points (`Main.v`), extraction (`Extract.v`) |
| `theories/Optimizer/` | the `nft -o` passes (`Optimize_<Shape>.v`, one file per `optimize_chain_<shape>` stage), pipeline composition (`Optimize_Table.v`, `Optimize_Table_Inv.v`, `Optimize_Uncond.v`) |
| `theories/Optimizer/Witness/` | fires-witnesses: `Optimize_<Shape>[_<Arm>]_Witness.v`, one per pass arm, each `vm_compute`-checked against host `nft --optimize` output |
| `theories/Regression/` | kernel-behaviour regression gates, named after the invariant they pin (e.g. `Numgen_RoundRobin.v`, `Nat_FlowStateful.v`); a model regression makes their theorems unprovable |
| `theories/Examples/` | worked per-configuration proofs (`Router_*`, `Optiplex_*`, `Tutorial_Proofs.v`, `Example_Ruleset.v`, demos) and their shared engine (`Eval_Fw.v`, `Nft_Tactics.v`) |
| `theories/Generated/` | `nft2coq` output (`*_Gen.v`, regenerated by `make gen`, drift-gated by `make gen-check`) — parser-emitted ASTs the Examples reason about |

| File | Role |
|---|---|
| `theories/Core/Bytes.v` | byte/`data` domain; `data_eqb`, lexicographic order, bitwise op, set membership |
| `theories/Core/Packet.v` | the packet both languages observe: metadata, conntrack, exthdr, header bytes |
| `theories/Core/Verdict.v` | `Accept`/`Drop`/`Continue` |
| `theories/IR/Syntax.v` | **DSL**: 46 named fields + a parametric exthdr field; matches (eq/neq/range/masked/set); rules, chains, tables |
| `theories/Core/Bytecode.v` | **control-plane bytecode**: register VM (`meta/ct/exthdr/payload load`, `cmp`, `range`, `bitwise`, `lookup`, `immediate`) |
| `theories/Semantics/Semantics.v` | packet→verdict semantics for *both* languages |
| `theories/Compiler/Compile.v` | the compiler `compile_chain : chain -> program` |
| `theories/Compiler/Correct.v` | **`compile_chain_correct`** — semantic preservation |
| `theories/Optimizer/Optimize.v` | rule-local base optimizer pass (dedup + range-simplify + no-op-prune + DCE) + `optimize_chain_correct`; the shipped 18-stage table-level pipeline is `Optimize_Table.v`/`Optimize_Uncond.v` (see "The verified optimizer" below) |
| `theories/Examples/Example_Ruleset.v` | worked example: `../rulesets/ruleset.nft` hand-translated to the AST + 9 axiom-free packet-property proofs (the user-facing use case; the baseline a parser should reproduce — see TODO 9) |
| `theories/Compiler/Extract.v` | extraction to `extracted/*.ml` |
| `extracted/glue.ml` | *untrusted* glue: builds chains, renders nft-format bytecode (forward test) |
| `extracted/lexer.mll` `parser.mly` `nft_ast.ml` `nft_inject.ml` `nft_parse.ml` | *untrusted* **`.nft` text → surface AST frontend** (TODO 9): ocamllex+Menhir surface parser → **pure structural** `Nft_ast → Ast.*` constructor injection (`nft_inject.ml`) + the single `ifindex` oracle (`nametoindex "lo" → 1`) + the 2^40 extraction-seam guard, then handed VERBATIM to the extracted Coq `Lower.lower_ruleset`. All lowering (define/symbol resolution, implicit-l4proto deps, CIDR/range/concat, anonymous-set/vmap → `env`, `include` expansion) is now the VERIFIED Coq `Lower.lower_ruleset`, **not** OCaml. `Nft_parse.parse_file` orchestrates parse → inject → lower |
| `extracted/nft_emit.ml` `nft2coq.ml` | *untrusted* **surface → Coq emitter** (M6): serialise the injected SURFACE ruleset as a Coq `Definition <name>_surface : sruleset` (only the untyped surface constructors — IP literals via the `sip4` smart ctor, i.e. decimal octets, never a raw byte list), plus the `<name>_lowered := lower_or_empty ifindex_pins <name>_surface` binding and the `lr_*` projections that carve out `decls`/`gen_env`/the per-table chains + hooks. The emitter composes NO byte and makes NO datatype/byteorder decision — every operand/element/target byte is produced by the VERIFIED Coq `Lower.lower_ruleset`, kernel-reduced, not written here |
| `theories/Generated/Gen_Support.v` | the Semantics-level lowering projections the Gen files reduce (`lr_set_decls`, `lr_hooks_of`, `hook_id_of_string`); compiled after `Semantics`, before the four `*_Gen.v`. NOT extracted |
| `theories/Generated/Optiplex_Gen.v` `Ruleset_Gen.v` `Router_Gen.v` `Tutorial_Gen.v` | **generated** by `nft2coq` from the matching `../rulesets/*.nft` (`make gen`, all four incl. router; `make gen-check` fails the gates if any is stale). Each carries `<name>_surface` + a fail-loud `Example <name>_lowers_ok : lower_ok ifindex_pins <name>_surface = true` (a refused construct breaks `make proofs`, never a silent OCaml byte). `Tutorial_Gen.v` backs the [`CONFIG_PROOFS.md`](CONFIG_PROOFS.md) tutorial |
| `theories/Examples/Optiplex_Antispoof.v` | **anti-spoofing** proofs about the parsed `optiplex.nft` bridge `output` chain (+ legit-traffic-allowed); all axiom-free |
| `theories/Examples/Optiplex_Antispoof_Gaps.v` | **adversarial** proofs: the binding is unenforced outside `@vmaddrs` / off br.20 (real bypasses), axiom-free |
| `theories/Examples/Optiplex_Mark.v` | **firewall-mark** proofs about the parsed prerouting/postrouting chains: marking RDP traffic, mark-gated masquerade, cross-hook flow; axiom-free |
| `theories/Examples/Ruleset_Verified.v` | the 8 `ruleset.nft` packet properties, about the *generated* AST (supersedes the hand copy in `Example_Ruleset.v`) |
| `extracted/parse_test.ml` | *untrusted* harness/CLI: checks parsed-AST verdicts vs the proofs (ruleset.nft 8 props; optiplex anti-spoofing + bypasses); difftest AST equality; live-`nft` round-trip |
| `extracted/corpus_test.ml` | *untrusted* harness: round-trips the upstream corpus through the verified compiler |
| `difftest.sh` | byte-identical forward check vs the local `nft` |
| `corpus.sh` | round-trip the upstream corpus; report coverage; fail on any mismatch |

Build & check proofs: `make proofs`. Forward test: `make difftest`. Corpus
coverage: `make corpus` (clones nftables' `tests/py` once into a cache dir).

## The theorems (every one `Closed under the global context` — no axioms)

That axiom-freedom claim is **enforced by `make axioms`** (the build-failing
`Print Assumptions` gate over `AXIOM_GATE_THEOREMS` in the Makefile — the
headline set plus every README-claimed result; see `THEOREMS.md` §4), not by
the in-file `Print Assumptions` lines, which only print to the build log.

**The authoritative map is [`THEOREMS.md`](THEOREMS.md)** — one HEADLINE
theorem per verified axis, the HEADLINE/STAGE/SUPPORTING/SUPERSEDED/DEMO
classification of every `Theorem`/`Corollary`, and the evaluator matrix.
The entry points are restated (with `Print Assumptions`) in
[`theories/Compiler/Main.v`](theories/Compiler/Main.v), and `make axioms` re-checks the whole
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
| `compile_chain_mut_correct` | in-traversal **mutation** (meta/ct `set`, set-`dynset` learning, field-data map-`dynset` learning) is visible to later rules AND to later expressions of the SAME rule (single-fold); holds for every numgen-free rule (`rule_numgen_free`, discharged for all frontend programs by `Lower_Proofs.lower_ruleset_numgen_free`) |
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
and `numgen` (whose `inc` form is now a persistent counter in `env` — advanced by the
**VM-side** mutation evaluators only: the DSL step has no numgen sweep, and the
`rule_numgen_free` hypothesis excludes numgen-inc rules from every mutation-strand
compiler theorem — discharged for all frontend programs by
`Lower_Proofs.lower_ruleset_numgen_free` (the lowering refuses incremental numgen,
`Lower.LEnumgen`) — so the round-robin behaviour `Regression/Numgen_RoundRobin.v` pins is
**not compiler-preserved**; rationale on `Semantics.dsl_rule_step`, cross-referenced in
`THEOREMS.md` §3), **verified
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

**The oracle direction (read before citing 2532/2532).** The name-table example
above is an instance of a *general* property of this gate: `corpus_test.ml`'s
`rule_of_block` reconstructs the DSL rule **from** the corpus netlink block, so
the check is `render(compile_rule(rule_of_block(b))) = b` — a **fixed point of a
payload-level round-trip**, not a differential from the rule's *source text*.
Anything the reconstructor and the compiler systematically agree on — a shared
misunderstanding of how nft lowers a given `.nft` construct, not just a shared
table entry — round-trips cleanly and is invisible to this gate. (The one
documented near-miss was exactly this shape: the compile path's host-order byte
handling was wrong while `make corpus` stayed green, because the round-trip
never runs the source compiler — see "Enforcement model" below and
`../NOTES.md` § "Register byte-order sweep".)

**Why not drive the whole corpus source-side?** Every corpus block carries its
source rule as a `# <src>` header, so the stricter gate — parse `<src>` with our
frontend, compile with the verified compiler, diff the rendered lines against
the block — is *implementable today*, and we measured it (2026-07, this review,
with a throwaway whole-corpus generalisation of `byteorder-gate`'s per-block
loop in `extracted/parse_test.ml`; deliberately NOT wired in as a gate — see
below). Of the **1742** headered blocks the harness can attempt, **1142 (65.6%)** already survive the full compile-from-source
diff; **517** fail to parse/lower (frontend syntax gaps: constructs the Menhir
frontend does not accept, e.g. exotic statements and set forms — loud
`Parse_error`/`Unsupported`, never a mis-parse); **83** parse but render
*differently* from the corpus. The 83 fall into three classes, all in
territory `byteorder-gate` deliberately excludes:
  - **host-order byte-order divergences** on cmp/range/bitwise immediates for
    host-endian keys *outside* the gate's covered set (`meta
    length`/`cpu`/`skuid`/`skgid`, `ct expiration`, the `meta mark and/or/xor`
    mask+xor operands): the corpus renders `0x00000bb8` where we render
    `0xb80b0000` — the display-vs-wire question `../NOTES.md` flags as *still
    to adjudicate against a real kernel* for precisely these keys;
  - **nft constant-folds/merges we don't replicate**: `meta mark xor 0x03 ==
    0x01` → nft folds to a plain `cmp eq 0x02` (we emit `bitwise; cmp`), and
    the adjacent-payload merge `tcp sport 1 tcp dport 2` → one 4-byte load
    (we emit two 2-byte loads — semantically equal, textually not);
  - **render/lowering text differences with no adjudicated wire divergence**:
    dependency-guard synthesis in the vlan/ether/icmpv6 family contexts the
    corpus varies, `reject` default type/code rendering, `log` option
    defaults, `exthdr != exists` compare polarity.
### The 83 source-divergences, adjudicated (T2A)

The 83 compile-from-source text mismatches were adjudicated against two
independent oracles (live `nft` 1.1.6 + the corpus) and kernel source, with
netns packet counters where a wire question needed a behaviour test:
`reports/discrepancy-adjudication.md` (82 rows after two harness-artefact
corrections) and `reports/corpus-divergence-bugs.md`. The verdict: **31 real
wire-level bugs**, **1 upstream nftables bug** (class O below), **50 benign**
(wire-identical or provably same-packets). Corpus-text accounting of the fixes
(correcting the T2A repair commit message's "all 31 leave the divergent set"):
**26** of the 31 fixed blocks leave the divergent set — byte-identical to the
corpus after their fixes — while **5** remain textually divergent yet
wire-correct/packet-equal, a host-endian display residual (not bugs; see the
per-class ledger notes below). Every bug was a decision in the
**frontend's** source→DSL encoding — the Rocq DSL≡bytecode theorems were never
contradicted — and the typed-layer migration ported those decisions verbatim
into the verified Coq lowering, so the fixes are now IN the verified lowering:

- **B (host-endian ordered ranges, 10 blocks) — FIXED.** `Surface.Typed.range_hton`
  is now `dt_byteorder = BoHost`, so EVERY host-endian ordered range
  (meta length/skuid/skgid/cpu/cgroup/iifgroup/oifgroup, ct id/zone, mark/iif/
  oif/fib-type) takes nft's mandatory `byteorder hton` + big-endian-bounds path
  (`range_erasure_host`, unchanged, now covers them).
- **C (`ct expiration` unit+byteorder, 3 blocks) — FIXED.** A new `DTtime`
  datatype scales the SECONDS literal to the kernel's MILLISECONDS register
  (`resolve_num DTtime n = VHostInt 4 (n*1000)`) and rides the class-B hton path.
- **D (`exthdr`/`tcpopt` `!= exists|missing` polarity, 2 blocks + 1 corpus-invisible
  twin) — FIXED.** `Lower.lower_presence` threads the surface `!=` (regression
  pins `lower_exthdr_neq_exists`, `lower_tcpopt_neq_exists`).
- **E (`reject with tcp reset` missing `meta l4proto 6`, 3 blocks) — FIXED
  (packet-identical, wire-order divergent).** `reject_dep` adds `DepL4 6` for
  `tcp reset` (packet-proven: the RST no longer fires on non-TCP). One residual
  divergence, ledgered here: nft hoists the reject's L4 dependency to the FRONT
  of the rule (`meta l4proto 6; meta mark N; reject`), whereas this pipeline
  emits the reject's guard where the reject statement sits (`meta mark N; meta
  l4proto 6; reject`). The two are packet-EQUIVALENT (both guards are pure
  conjuncts that must all hold before the reject fires; kernel readback confirms
  the ICMP-passes / TCP-RST behaviour matches nft) but NOT wire-identical. Making
  it byte-identical means hoisting statement dependencies to rule scope — a
  rule-assembly reordering left to a dedicated milestone rather than rushed under
  this commit's ratchet.
- **F (`ether type`/vlan missing the `meta iiftype == ether` guard, 4 blocks) —
  FIXED.** `Selector` attaches `dep_ether` to `ether type` and the vlan
  bitfields (a no-op in bridge, real in inet/netdev).
- **N (`ct label set K` = bit K, 1 block) — FIXED (wire-verified).**
  `Lower.ct_label_imm` sets bit `K` of the 128-bit bitmap and serialises it
  HOST-endian (`List.rev (N_to_data 16 (2^K))`), matching nft's `mpz_setbit`
  + `mpz_export_data(BYTEORDER_HOST_ENDIAN)` (`src/ct.c ct_label_type_parse`,
  `ct_label_type.byteorder = BYTEORDER_HOST_ENDIAN`): bit `K` lands in byte
  `K/8` at bit `K mod 8`, so `ct label set 127` -> byte 15 = `0x80` (register
  `00..00 80`), which the kernel reads back as `ct label set 127`. `N_to_data`
  is `N` arithmetic so `2^127` does not wrap (the OCaml `lsl`-on-63-bit
  shift-wrap half of the bug died with `nft_lower.ml`). Pinned by
  `lower_ct_label_set_127`/`_0` (the width-128 encode test). VERIFIED against
  live nft by kernel round-trip, NOT by corpus text: the committed golden
  `ct.t.payload` (`immediate 0x80000000 0x0 0x0 0x0`, byte 0 = `0x80`) is
  endian-unportable — it predates / disagrees with live nft v1.1.6, which dumps
  the same rule as `0x00000000 0x00000000 0x00000000 0x80000000`. `make corpus`
  is blind to this: its ct-label block reconstructs the rule from the golden
  bytes through the low-level `Syntax`/`Compile` round-trip, never through the
  surface `ct_label_imm`, so it neither catches nor is broken by this fix.
- **G (L2 in-frame ethertype guard shape, 8 blocks) — FIXED.** In bridge/netdev
  the network-layer ethertype guard is NOT always `meta protocol`. Its SHAPE
  follows nft's protocol context (`src/proto.c` proto_eth / proto_netdev /
  proto_vlan `protocol_key` template + `src/payload.c` `payload_gen_dependency` /
  `payload_gen_special_dependency`):
  - a DIRECT network selector (`ip saddr`/`ip protocol`) in bridge/netdev reaches
    the ethertype through proto_netdev's `meta protocol` — the historical shape,
    still correct and unchanged;
  - a network guard synthesised UNDER the link header by a transport selector
    (`icmp`/`icmpv6`/`igmp type`) uses proto_eth in **bridge** → `payload load 2b
    @ link header + 12`; in **netdev** it stays proto_netdev → `meta protocol`
    (golden `bridge/icmpX.t.payload` vs `any/icmpX.t.netdev.payload`);
  - once a vlan tag (`ether type 0x8100`) has matched, the context is proto_vlan
    and every subsequent in-frame protocol read moves to `payload load 2b @ link
    header + 16`, in BOTH L2 families.
  Implemented as a new `Selector.depspec` `DepNetLL` (the transport-implied
  network dep) plus a vlan-context flag threaded into `Lower.dep_guard` and a
  once-per-network-layer dedup (`Lower.layer_class`) that unifies the three
  interchangeable spellings (`meta protocol`, `payload @ link+12`,
  `payload @ link+16`). No IR field was added — the guard reuses the parametric
  `FPayload PLink off 2`. The `table bridge vmfilter` in `Optiplex_Gen` is
  UNAFFECTED: its `ip daddr` anti-spoofing rules are direct, non-vlan network
  selectors, so they keep the `meta protocol` shape — `Optiplex_Gen.v` is
  byte-identical and the axiom-gated `Optiplex_Antispoof`/`Optiplex_Mark` headline
  proofs are untouched. All 8 blocks are byte-identical to live nft (source-sweep
  pass 1168 → 1176).

Machine-caught now: **`make byteorder-gate`** covers the ORDERED-RANGE class
(its trigger fires on the hton `byteorder` transform, not just the narrow
mark/ct-mark loads), and the new **`make source-sweep-gate`** is a TRACKED-COUNT
RATCHET — the compile-from-source byte-identical count is pinned as a floor in
the Makefile, so a frontend regression that drops a block below the floor turns
the build red while the endian-unportable / benign display classes stay visible
without freezing the gate.

### Class I — the adjacent-payload merge, now a verified optimizer pass (T2B)

Class I ("adjacent-payload merge not replicated", 5 blocks, packet-proven equal)
is closed by a NEW intra-rule optimizer pass, **`Optimize_PayMerge.paymerge_chain`**:
two byte-contiguous full-width payload equalities in the same header fuse into
one wider load+compare, exactly where nft's own `payload_can_merge`
(src/payload.c) does — adjacent, combined width ≤ 16 bytes, and either ≤ 4 bytes
(u32 fast path), a link-layer base, or a side already > u32. The pass is
SELF-GUARDING and its correctness is UNCONDITIONAL (`paymerge_chain_eval`,
axiom-gated): a payload read and its loadability split at any interior offset for
EVERY packet, so no byte-/length-well-formedness hypothesis is needed. It is
applied source-side in the sweep (5 blocks moved from divergent to
byte-identical: `inet/payloadmerge.t.payload:1`, `inet/tcp.t.payload:166/173/182`,
`bridge/vlan.t.payload:279`; **floor 1176 → 1181**) and is exposed by name to the
`nftc -O paymerge` CLI.

Class L ("xor constant-fold not replicated", 4 blocks) gets the companion pass
**`Optimize_XorFold.xorfold_chain`**, which performs nft's `binop_transfer` step
— transferring the pure-xor register operand onto the compare value
(`(reg & 0xff..) ^ C <op> V → ^ 0 <op> V^C`), UNCONDITIONAL by xor's involutivity
(`xorfold_chain_eval`, axiom-gated). Note that class L does NOT move the
source-sweep floor: its blocks are `mark`-based, so they are host-endian
**endian-unportable** in the text corpus (the same reason the whole host-order
family cannot be text-green cross-endian, above), AND nft additionally DROPS the
now-trivial `& 0xff.. ^ 0` binop — a register-byte-width fact this
over-approximating packet model (unbounded `nat` bytes from `pkt_meta`/`e_ct`)
cannot carry soundly. The pass is the maximal fold the model supports soundly;
it is exposed as `nftc -O xorfold`.

Both passes plus the pipeline's chain-level stages are entries in the extracted
pass **registry** (`Optimize_Registry`), and the ONE generic composition theorem
`run_passes_correct` proves that folding any registry pass list preserves
`eval_chain`. `nftc -O p1,p2,...` parses names into a pass list and folds them
left-to-right; `nftc --list-passes` enumerates the registry; `-O default` runs
the whole-table pipeline (`optimize_table_uncond`), byte-identical to `nftc
optimize`. The two intra-rule passes act on disjoint matchcond shapes (payload
equalities vs `MMasked` xor), so they commute at the bytecode level; the CLI
still applies them in the given order and the composition theorem holds for every
order.

### Classes I + L are DEFAULT-ON: the shipped compile pipeline (T3 residue)

nft performs the class-I merge and the class-L fold **unconditionally at
netlink linearization** — no `nft -o` involved — so an opt-in `-O` pass was
not parity: plain `nftc compile` still diverged from plain `nft`. The T3
residue composes both into the DEFAULT pipeline,
**`Optimize_Linearize.compile_chain_default`** = `compile_chain ∘
xorfold_chain ∘ paymerge_chain` (`theories/Optimizer/Optimize_Linearize.v`):

- **`nftc compile`**, **`nftc optimize`** and **`nftc send`** ALL bottom out in
  `compile_chain_default` — linearization sits at the compile boundary,
  mirroring nft (emission-time, after any `-o` consolidation), NOT inside
  `optimize_table_uncond`.
- Composed headlines, axiom-gated: **`compile_chain_default_correct`**
  (`compile_chain_correct` carried through both stages, for every chain/env/
  packet) and **`optimize_table_uncond_compile_correct`** — RESTATED over
  `compile_chain_default`, so the optimizer headline is about the term the CLI
  actually emits. `linearize_chain_eval` is the composed stage theorem.
  Non-vacuity is Compute-pinned in `Optimize_Linearize.v`
  (`default_pipeline_merges_payload_loads`: `tcp sport 1 tcp dport 2`
  default-compiles to ONE 4-byte load; `default_pipeline_folds_xor`).
- The `-O paymerge` / `-O xorfold` registry passes REMAIN (explicit use before
  the default compile is an idempotent second application: both passes rewrite
  only where their syntactic guard still fires).
- The source-sweep and byteorder gates now compile through the SHIPPED
  `compile_chain_default` (no more harness-side ad-hoc pass application). The
  sweep floor HELD at 1196 under the switch — the class-L blocks stay open on
  the host-endian DISPLAY residual and nft's identity-binop elision (above).
  The remaining compile-from-source mismatches are classified block-by-block
  in `reports/default-linearization-audit.md`.

### Class O — `ct id` byte order: WE are kernel-faithful, nft is not

The one upstream bug. `nft` declares `NFT_CT_ID` `BYTEORDER_BIG_ENDIAN`
(`src/ct.c:317`) and emits a big-endian immediate, but the kernel writes the
conntrack id as a native `u32` (`nft_ct.c:174`, `*dest = nf_ct_get_id(ct)`, no
byte-swap), so on little-endian hosts `nft`'s `ct id <n>` can essentially never
match. We type `ct id` host-endian (`Selector`: `DThostint 4`), matching the
kernel register. Draft upstream report with both citations:
`reports/upstream-ct-id.md`. (Source-adjudicated; no packet demo — the id is a
random siphash.)

## T3 — full frontend coverage: named objects, config ops, parser sweep

Three additions closing the parser's silent-drop gaps. The verified core already
carried the object IR (`SObjref`, `SObjrefMap`, `MQuota`, `SCounter`); T3 wires
the surface layer to it and gates the reference forms.

**Named stateful objects (end-to-end).** A table declares objects
(`counter`/`quota`/`limit`/`ct helper`/`ct timeout`/`ct expectation`/`secmark`/
`synproxy`); a rule references one by name. The surface AST carries the object's
`sobjkind` (`Surface/Ast.v`); the typechecker checks a reference for
declared-existence + kind agreement (`objkind_declared`, `tc_objrefmap` in
`Surface/Typecheck.v` — an undeclared or wrong-kind reference is rejected, pinned
by `objref_{declared_accepts,undeclared_rejects,wrong_kind_rejects,...}` and the
`tests/illtyped/objref_*.nft` suite); the lowering emits `SObjref (objkind_otype
k) name` / `SObjrefMap` (`Surface/Lower.v`). The verified typecheck runs on the
SHIPPED frontend path itself (`Nft_inject.lower` calls the extracted
`Typecheck.typecheck_ruleset` before the verified lowering), not only in the
parse-test/sweep gates — so `nftc compile`/`optimize`/`send` loudly reject an
ill-typed config (e.g. `counter name "undeclared"` with no declaration, or one
of another kind) instead of silently lowering it. The corpus sweeps re-inject
the sibling `.t` file's `!set`/`%object` declarations into their synthetic
wrap (`parse_test.ml` `Harness.decls_for_payload`), since a bare recorded rule
is ill-typed without the declaration context it was recorded under. `counter packets N bytes N` now
keeps its initial values (`StCounter pkts bytes` → `SCounter pkts bytes`), no
longer discarded. Object type numbers are the kernel's `NFT_OBJECT_*`
(`include/linux/netfilter/nf_tables.h`), verified against live nft's payload
(`ip/objects.t.payload`: `counter name "cnt2"` → `[ objref type 1 name cnt2 ]`,
`ct helper set "cthelp1"` → `type 3`, `ct timeout set` → `type 7`, `ct
expectation set` → `type 9`, ...).

*Model boundaries (ledgered, not refusals — the reference forms all lower):*
- A **named quota's over-limit drop** is not modelled: `quota name X` lowers to a
  verdict-neutral `SObjref` (the object accounts; the verdict effect of a
  depleted named quota is not threaded). An anonymous inline `quota N bytes`
  statement is not parsed at all: `parser.mly`'s only `QUOTA` productions are the
  objref (`QUOTA IDENT STRING`), the declaration (`QUOTA IDENT LBRACE obj_body
  RBRACE`), and the objref-map clause, so `quota 100 bytes` in a rule is a loud
  parse error — consistent with the "anonymous stateful statements" entry in the
  T3 corpus ok/fail residual below. Only the named-quota objref form lowers, and
  it lowers verdict-neutrally. Follow-up: thread named-quota state through `env`
  like `e_quota` and give `SObjref` of a quota a `MQuota`-style verdict.
- An **objref verdict-map's element→object bindings** (`counter name <key> map {
  443 : "cnt1" }`) are a verdict-neutral side effect not read by the semantics,
  so they are not interned into the verdict `env`; `SObjrefMap` references a
  fresh anonymous map name and compiles to `[ objref sreg 1 set __mapN ]`. The
  netlink `send` path does not yet emit the map's element set. Follow-up: record
  the bindings for `send` emission.
- **Object-body deep validation** (helper protocol modules, ct-timeout policy
  state names, l3proto compatibility) is kernel-module behaviour outside this
  model. Object bodies are parsed *structurally* (a typed `obj_body` grammar,
  not the deleted `junk` catch-all) but only the object's kind is retained. The
  `objects-sweep-gate` therefore scopes to RULE lines; the `%name type ...`
  DECLARATION `;ok`/`;fail` verdicts (which test that body validity) are the
  ledgered residual.

**Config-management ops (unverified preprocessing).** `delete`/`destroy`/`flush`
of a table/chain/ruleset parse to structured `TopOp`s that the UNVERIFIED driver
(`extracted/nft_config.ml`) applies, in file order, to the parsed config before
the verified injection sees a `TopOp`-free config — exactly like `include`
expansion. Semantics mirror nft: `delete` errors on a missing entity, `destroy`
is delete-if-exists, `flush` empties. Zero `TopNop` productions remain
(`parser.mly`); the `.nft` `flush ruleset`/`destroy table` lines that were
silently dropped now visibly edit the compiled output (a CLI test writes
delete/destroy/flush and observes the entity gone/emptied, and a `delete` of a
nonexistent table errors like nft). *Follow-up (verified modelling):* model a
stateful ruleset as a sequence of NEW/DEL/FLUSH batch messages inside Coq and
prove the frontend's fold agrees.

**Parser junk catch-all deleted.** `objdecl`'s `IDENT IDENT LBRACE junk RBRACE`
(which swallowed ANY unknown two-word table item — a flowtable vanished) is gone:
object declarations have real per-kind productions, an unknown table item
(`frobtable x { }`) is a genuine parse error, and a `flowtable` is parsed
structurally then LOUDLY refused (offload is out of model). The `objects-sweep-
gate` ratchet runs every `objects.t` rule line through parse+typecheck+lowering
BIDIRECTIONALLY (`;ok` accepted, `;fail` rejected) — 14/14 within scope.

**Corpus ok/fail sweep (bidirectional ratchet).** Beyond `objects.t`, the
`corpus-okfail-gate` runs EVERY rule line of the model's supported families
(ip, inet, any — 1391 rule lines after non-rule directives are excluded, see
below) through parse + typecheck + verified lowering and checks accept/reject
against the corpus `;ok`/`;fail` verdict. Two counts are pinned
(`corpus-okfail-gate.sh`): `pass >= 1003` (a supported `;ok` line newly rejected,
or a `;fail` line newly accepted, drops pass → red) and `false_accept <= 47`
(a NEW invalid `;fail` line slipping through → red). This gate is the
`;fail`-direction check that `source-sweep-gate` (a one-directional byte-identity
PASS-count ratchet) is *structurally blind to*.

*Harness correctness (the residual list must reflect model coverage, not wrap
artifacts).* Each rule is wrapped in a hardcoded `table ip` / `chain … { type
filter hook input priority 0; … }` base chain — `NF_INET_LOCAL_IN` is a valid
hook for every ip/inet filter chain, so lowering never fails for a *hook* reason.
The wrap deliberately IGNORES the rule's own chain hook recorded on the corpus
`:` line: netdev files end on `hook egress device lo`, an ip-invalid hook that
would fail EVERY rule in those ~30 files and mask false-accepts there. The harness
strips the `- ` list-output continuation prefix; skips `define`/variable lines;
translates the corpus `%name type …` (stateful object), `!name type …` (named
set/map) declaration directives into real declarations and injects the ones that
individually typecheck+lower so `@name` / object-reference rules resolve (a decl
with an unmodelled element datatype is dropped rather than poisoning the whole
wrapped table); and skips `?name elem` set-element directives (not rules). What
remains in the residual is therefore genuine model coverage. (An earlier revision
tracked the chain hook last-wins and hardcoded `table ip`, so it silently failed
every rule in the netdev-hook files and undercounted false-accepts; that ceiling
was unsound and is corrected here.)

Several argument-validations landed with this gate (previously silent accepts):
a `queue num` argument is a 16-bit queue index (kernel nf_queue: `__u16`;
`Typecheck.sverdict_valid` rejects `queue num 65536`); a `tcp option` kind is a
byte with per-option template fields (nft `tcpopt.c`: `Symbols.dt_tcpopt_num`
rejects a raw kind > 255, `tcpopt_field_valid` rejects a field absent from the
option's template such as `tcp option eol left`, since `eol`/`nop` carry only
`kind`); and a `limit`'s data-rate units follow nft's grammar (`parser.mly`
`byte_unit_scale`/`limit_burst`) — the only valid byte units are
`bytes`/`kbytes`/`mbytes` (`src/statement.c` `data_unit[]`, so `1 gbytes/second`
is refused, not silently scaled by 1), and a packet-rate pairs only with a
packet-burst and a byte-rate only with a byte-burst (`src/parser_bison.y`
`limit_args` has no crossed production, so `rate 1023/second burst 10 bytes` and
`rate 512 kbytes/second burst 5 packets` are refused).

*The 47 residual `;fail` lines still accepted (per-case ledger — each is a
validation OUTSIDE the model, not a laziness gap; loud refusal of the valid
reference forms is not acceptable, so these accept the payload and skip the
context check nft performs). The count is the true post-harness-fix figure and
the pinned `false_accept` ceiling:*
- **NAT/tproxy hook-context (22 lines):** `masquerade`/`redirect`/`snat`/`dnat`/
  `tproxy` are legal only in specific hooks (nat postrouting/prerouting, mangle
  prerouting); the corpus places them in a `filter input` chain, where nft
  rejects on hook context. Instances: `masquerade.t` (`tcp dport 22 masquerade
  counter … accept`, `tcp sport 22 masquerade accept`, `ip saddr 10.1.1.1
  masquerade drop`); `redirect.t` (`redirect to :1234`, `tcp dport 22 redirect
  counter … accept`, `tcp sport 22 redirect accept`, `ip saddr 10.1.1.1 redirect
  drop`); `snat.t` (`snat to 192.168.3.2`, `snat to dead::beef`); `dnat.t`
  (`dnat ip6 to 1.2.3.4`, `dnat to 1.2.3.4`, `ip6 daddr dead::beef dnat to
  10.1.2.3`, `meta l4proto { tcp, udp } tcp dport 20 dnat to 1.1.1.1:80`, `ip
  protocol { tcp, udp } tcp dport 20 dnat to 1.1.1.1:80`); `tproxy.t` (`tproxy`,
  `tproxy to 192.0.2.1`, `tproxy to 192.0.2.1:50080`, `tproxy to :50080`, `meta
  l4proto 17 tproxy to 192.0.2.1`, `meta l4proto 6 tproxy to 192.0.2.1:50080`,
  `ip6 nexthdr 6 tproxy ip to 192.0.2.1`). The model has no hook/family context
  threaded into statement typing. Follow-up: carry the chain's hook type into
  `tc_stmt` and reject hook-incompatible statements.
- **`reject` type family/`nfproto` scope (5 lines):** a `reject with` code must
  match the L3 family/`nfproto` — `reject.t` (`reject with icmpv6 no-route` in an
  ip table; `meta nfproto ipv6 reject with icmp host-unreachable`; `meta nfproto
  ipv4 ip protocol icmp reject with icmpv6 no-route`; `meta nfproto ipv6 ip
  protocol icmp reject with icmp host-unreachable`; `meta l4proto udp reject with
  tcp reset`). The model does not cross-check the reject code against a
  runtime `nfproto`/family constraint. Follow-up: a family-context lattice
  checked in `tc_stmt`.
- **`ct` direction address `nfproto` scope (1 line):** a direction-qualified ct
  address must match `nfproto` — `ct.t` (`meta nfproto ipv6 ct original ip saddr
  1.2.3.4`, an IPv4 address under an ipv6 nfproto guard). Same missing
  family-context lattice as above.
- **Bridge-family selectors + empty interface name (6 lines):** `meta
  ibrname`/`obrname` (input/output bridge port name) are bridge-family only —
  `meta.t` (2 lines, in both the ip and inet tables = 4 instances); and `meta
  iifname ""` / `meta oifname ""` name an interface with the empty string, which
  nft refuses (an interface name cannot be empty) — `meta.t` (2 instances). The
  model treats an ifname as a 16-byte buffer (`""` is the all-zero buffer) and
  does not scope a selector to a bridge family or validate string content.
  Follow-up: the family-context lattice, plus a non-empty-string check on
  ifname-typed match values.
- **`log` option mutual-exclusion (8 lines):** nft forbids combining a syslog
  `level`/`level audit` with `group`/`snaplen`/`queue-threshold`/`prefix`/`flags`
  (group selects nfnetlink_log, disjoint from the syslog path) — `log.t` (`log
  level emerg group 2`, `log level alert group 2 prefix "log test2"`, `log level
  audit prefix "foo"`, `log level audit group 42`, `log level audit snaplen 23`,
  `log level audit queue-threshold 1337`, `log level audit flags all`, `log
  flags all group 2`). The model accepts the log-option bag verbatim (`StLog`
  carries the option string; it is verdict-neutral). Follow-up: validate the
  option-set exclusivity in the log-statement typecheck.
- **vmap overlapping-interval detection (2 lines):** `ip.t` (`ip saddr vmap {
  10.0.1.0-10.0.1.255 : accept, 10.0.1.1-10.0.2.255 : drop }` and `ip saddr vmap
  { 3.3.3.3-3.3.3.4 : accept, 1.1.1.1-1.1.1.255 : accept, 1.1.1.0-1.1.2.1 : drop
  }`) — the interval entries overlap, which nft's interval-set builder rejects.
  The model lowers each vmap entry independently and has no interval-overlap
  check. Follow-up: an interval-disjointness check in the vmap/interval-set
  lowering.
- **`ether` payload-dependency (1 line):** `ether type ip vlan id 1` (`ether.t`)
  — accessing `vlan id` requires the ethertype to be `8021q`/`8021ad`, so
  `ether type ip` (IPv4) contradicts the implicit vlan dependency. The model
  loads each payload field without the ethertype-dependency chain. Follow-up:
  model the payload-protocol dependency graph.
- **`fib` key-set validity (1 line):** `fib daddr . oif type local` — the
  `daddr . oif` selector tuple is not a valid fib lookup key for the `type`
  result (`fib.t`). The model resolves fib keys structurally without the
  key/result compatibility table. Follow-up: a fib key-set validity check.
- **icmp field inter-dependency (1 line):** `icmp code != 1 icmp type 2 icmp mtu
  5` (`icmp.t`) — nft rejects the combination because `icmp mtu` carries an
  implicit dependency incompatible with the preceding `icmp code`/`type` in one
  rule. The model loads each icmp field independently without the conflict check.
  Follow-up: model the icmp field dependency graph.

*The `;ok` lines still rejected (`false_reject`, 336) are genuine unsupported-
construct model boundaries — whole feature families rather than laziness gaps in
the supported ones. (Compound flag masks — `tcp flags & (fin | syn | rst | ack)
== syn | ack`, the parenthesized/pipe-joined OR-group idiom, inet/tcp.t:81-85 —
left this residual with T3 residue R2: the group is parsed structurally into
`Ast.SVOr`, the member symbols and the OR-fold resolve in verified Coq
(`Typecheck.resolve_value`), and the existing `CBitmatch` lowering emits nft's
exact `bitwise (reg & m) ^ 0; cmp` shape; the `!`-after-mask form inet/tcp.t:90
pins as `;fail` stays refused.) The major buckets: unsupported L4/tunnel
protocols (`sctp`, `dccp`, `gre`/`gretap`, `geneve`, `vxlan`, `comp`, `osf`,
`rt`, `ipsec`, `socket`, `hash`, `numgen`, `synproxy`, `rawpayload`);
unsupported `meta` selectors (`priority`/tc-handle, `iiftype`/`oiftype`,
`time`/`day`/`hour`, `nftrace`, `rtclassid`, `sdif`/`sdifname`, `ipsec`);
relational `<`/`>` comparisons (parser has `==`/`!=` only — `ct expiration >
…`, `ct bytes > …`, `meta time < …`); sub-byte bitfield set/range matches (`ip
hdrlength`, `ip dscp`, `tcp doff` — the masked set/range lookup shape is not
lowered, see the `tc_bitfield` note in `Surface/Typecheck.v`); tcp-flags
SET-shaped forms (`tcp flags { syn, syn | ack }` brace-set membership and the
masked set lookup `tcp flags & (…) == { … }` — the `LEtcpflagSet` /
bitwise-set-rhs refusals; the lookup-after-bitwise shape is not lowered);
payload set-statement mangling (`ip ttl set …`, `ip dscp set …`, `tcp flags set
…`); anonymous stateful statements (`quota N bytes`, `ct count …`); dynamic
set-add statements (`add @set { … }`); and `typeof`-typed sets/maps and
wildcard (`*`) vmap defaults. Each is a named construct the typed frontend does
not yet cover; none is a regression in a construct it does cover.*

## Trust story (TCB)

Trusted: the Rocq kernel; the `.v` *specifications* (`Semantics.v` defines what
"correct" means); Rocq's extraction. **Not** trusted: the compiler/optimizer
(proved); the OCaml glue (`glue.ml`, `corpus_test.ml`), which only builds inputs
and renders/parses text and is itself checked against the corpus and the live
`nft`. The glue is minimal and differentially tested rather than reimplementing
nft logic; the heavy lifting stays in the verified core.

**The extraction seam (ExtrOcamlNatInt).** Extraction realises Rocq's
unbounded `nat` as OCaml's 63-bit native int, whose arithmetic WRAPS — a
semantics no proof covers.  This is part of the TCB (we trust extraction *plus*
this realisation), and it is sound only while no extracted `nat` computation
can reach 2^62.  The classification (spelled out beside the import in
`theories/Compiler/Extract.v`): bytes are `mod 256` by construction, addresses
and hashes travel as `N`/byte lists, register indices and field widths are
small compiler constants, and the optimizer's fresh-name seed `seed_start` is
a max over set-name *lengths* — all structurally bounded.  The one
user-controlled family is a `limit`'s `ls_rate`/`ls_burst`, which the
semantics multiplies by `lim_window <= 604800` (`lim_cost`/`lim_max`): the
untrusted frontend therefore REJECTS scaled rates/bursts above 2^40
(`limit_value`, `parser.mly`; re-checked in `Lower.limit_spec`), keeping
every extracted product below `604800 * 2^41 < 2^62`, and rejects integer
literals beyond OCaml's `max_int` as a clean lexer error.  `make parse-test`
pins the rejection (`limit rate 9000000000000 mbytes/second` used to wrap
silently into wrong bytecode).  So "is there a gate?" — yes: the guard is
untrusted-frontend code, and the parse-test pins are the gate.

**The interned-name seam (`Lower.nat_dec` → `string_of_int`).** From M3, ALL
set / map / vmap element byte composition — point / range / CIDR (net+broadcast)
intervals, the host-endian interval `byteorder hton` bounds, declared-set type
atoms, concatenated tuples with 4-byte register-slot padding (and the FLAT
unpadded vmap-key asymmetry), and the content-dedup `__setN`/`__mapN` interning —
is the VERIFIED Rocq lowering (`theories/Surface/Lower.v`; the OCaml frontend no
longer composes a single set byte, and `extracted/nft_lower.ml` — which used to
hold `interval_of_value`/`bytes_of_typeatom`/`pad_to_slot`/`prefix_mask`/… — has
been DELETED, its value→byte logic entirely absorbed into `Lower.lower_ruleset`).
The one residue is the *rendering* of the fresh-name suffix: `Lower.nat_dec`
extracts to OCaml `Stdlib.string_of_int` (its Rocq body is a faithful decimal
renderer used only by `vm_compute` witnesses), the same seam class as
`string_of_nat` above — only decimalness/injectivity is relied on, and the golden
corpus / `gen-check` re-check every produced `__setN`/`__mapN` name end-to-end.
The set membership decisions are proved: `set_interval_erasure` (byte interval =
numeric membership), `concat_key_erasure` (slot padding is faithfully invertible
— the historical padding bug), and `cidr_interval_agrees_prefix_expand` (the set
CIDR expansion and `Typed.prefix_expand`'s masked compare decide membership
identically — one Rocq expansion, no parallel OCaml CIDR).

**The ifindex oracle (allowed residue (a): host-dependent lookup).** Interface
selectors that name a device by string (`iif "lo"`, `oif …`) need that host's
*current* ifindex — a value that lives in the running kernel, not in the config
text, so it cannot be a pure function. The one such site is the `ifindex_oracle`
in `extracted/nft_inject.ml`: `nametoindex : string → int option`, threaded into
`Lower.lower_ruleset` as its first parameter. It resolves the loopback name
(`"lo" → 1`) and **declines every other name** (`None`), whereupon the VERIFIED
Coq lowering FAILS LOUD (an `lerr`), never guessing an index. This is the single
host-dependent lookup in the whole frontend (`grep -cw nametoindex nft_inject.ml`
= 1); the oracle-free typecheck path uses the same `"lo" → 1` fallback inside
`Lower.resolve_value` so `make parse-test` stays hermetic.

**Structural injection (allowed residue (b): pure `Nft_ast → Ast.*`).** The only
other untrusted OCaml translation is `nft_inject.ml`'s structural mapping of the
Menhir surface tree (`nft_ast.ml`) onto the extracted surface-AST constructors
(`Ast.*`): character/string/int injection and constructor shuffling only. It
DECODES nothing — no symbol tables, no width/byteorder decisions, no
interval/CIDR/mask arithmetic (the M-C banned-name grep over the frontend is 0).
Everything semantic downstream of it is the verified `Lower.lower_ruleset`. This
is the pure-structural-translation residue class the M-C ledger permits.

**The M-C boundary is now permanent (`make boundary`, M6).** The migration is
no longer a one-time state described in prose — it is a build gate. `make
boundary` (part of `make gates`) enforces, on every build: (1) NO value→byte /
kind / byteorder identifier (`bytes_of_int`, `enc_atom`, `width_of_kind`,
`host_endian_kind`, `prefix_mask`, `interval_of_value`, `pad_to_slot`,
`mask_shift`, `ifname_bytes`, `bitfield_sel`, …) in the OCaml frontend
(`nft_ast`/`nft_inject`/`nft_parse`/`nft_emit`/`nft2coq`); (2) NO symbol table
(`sym_*`, `syslog_level`, `nat_flag_bit`, `key_field`, …) there; (3)
`extracted/nft_lower.ml` stays deleted; (4) `TypedEval.v`'s numeric evaluator
stays independent of the encode path (`grep -cwE
'encode|data_eqb|firstn|eval_matchcond|elab_m'` = 0); (5) `extracted/lexer.mll`
does NO bit-arithmetic (`grep -nwE 'lsl|lsr|land|lor|asr'` = 0) — the lexer may
parse numerals and group dotted octets, but any byteorder split (historically
the IPv6 16-bit-group `lsr 8` split) must live in verified Coq.  The three
residues the ledger permits — (a) the `nametoindex "lo" → 1` ifindex oracle,
(b) the pure `Nft_ast → Ast.*` structural injection, (c) the `ExtrOcamlNatInt`
63-bit seam + its `2^40` guard — are exactly what remains; a regression that
re-introduces lowering logic into OCaml fails the gate, not a code review.

**TCB after M6 — the three residues, enumerated.**
  - (a) *host-dependent ifindex oracle.* `nft_inject.ml`'s `ifindex_oracle`
    (`"lo" → Some 1`, every other name `None`), pinned in each Gen file as the
    finite map `ifindex_pins` so the file is self-contained and the
    host-dependence is visible; the verified lowering fails loud on any declined
    name.
  - (b) *pure structural injection.* `nft_inject.ml`'s `Nft_ast → Ast.*`
    constructor/int/string mapping (`nat` over the seam, `string` over
    `ExtrOcamlNativeString`, IPv4/MAC as the lexer's digit-group lists, IPv6 as
    the lexer's UN-expanded `ip6grp` groups). It decides NO byte order: an IPv4
    octet and a MAC hex pair are each exactly one byte (grouping only), and an
    IPv6 literal's 16-bit-group big-endian split + `::` zero-fill are performed
    by the verified `Surface.Ast.sip6_bytes` (reached from `Lower`), which fails
    loud (`None`) on any literal that cannot form 16 bytes — the injection just
    carries the numerals and octet groups the lexer parsed. Boundary check (5)
    (`make boundary`) forbids bit-arithmetic in the lexer so this cannot regress.
  - (c) *extraction seam.* The `ExtrOcamlNatInt` 63-bit-int representation of
    `nat` and the `2^40` injection guard (`nft_inject.ml` / the `limit` bound in
    `Extract.v`) that keeps every extracted `nat` far below the wrap.
  - (d) *`N.of_nat` realization.* `Extract Constant N.of_nat` in
    `Compiler/Extract.v` replaces Coq's default (`Pos.of_succ_nat`, non-tail
    recursive → OCaml stack overflow at ~2^31) with a log-depth OCaml `N.of_nat`.
    It is extensionally equal to the Coq function (`XH=1`, `XO p=2p`, `XI p=2p+1`,
    so no proof observes the difference — the `.v` proofs use the real `N.of_nat`),
    but it is UNVERIFIED OCaml, hence TCB. Guarded by the parse-test pin
    `check_big_literal_no_overflow` (`meta mark 0x80000000`): a revert re-crashes
    the gate.

**Eyeball-trusted, never-differentially-tested semantics.** The corpus checks
*structure*, not the data-plane *meaning* of register operations. The byte-level
functions `data_bitops`, `data_le`, `data_mem`, `data_shift`, `data_byteorder`,
`data_jhash` **are extracted and executed** — `make semtest` and `make
parse-test` run the extracted DSL semantics and bytecode VM on concrete packets
through them — but the expected outputs in those harnesses are **authored in
this repo**, so they have **no external oracle**: their faithfulness rests on
inspection of the `.v` definitions against the kernel source. They are written
to match the kernel: `data_byteorder` reverses each `size`-byte element
(matching nft_byteorder.c's per-element swap — the very shape fix `ab4c83d` in
`../adversarial.md` records; NOT a whole-`len`-chunk or whole-string reversal;
note its `hton`/`len` parameters are deliberately dead — see the docstring in
`theories/Core/Bytes.v` for the producer invariant that makes that safe);
`data_shift` shifts via a big-endian `N` of the loaded width. `data_jhash`
deserves the strongest caveat: it is a **structural abstraction** of the real
Jenkins hash (deterministic, input/seed-dependent, mod-bounded — but NOT the
kernel's mixing function), so a kernel differential on a jhash-bearing rule
would fail **by design**; jhash-dependent theorems match the kernel only up to
a renaming of hash values. All of these are shared by the DSL semantics AND the
VM, so every compile theorem is *blind* to them — the vacuous-by-shared-
abstraction pattern this document warns about. No shipped gate can catch a
divergence here (e.g. a hypothetical `len < length d` byteorder input, or any
jhash value): these belong on the ⛔ STILL-OPEN list alongside the unmodelled
features, and the only closing move is the data-plane differential below.

**Why no at-scale data-plane differential yet (the fuzz-gate question).**
Control-plane bytes are checked on 2532 blocks; packet *semantics* is checked
only by hand-picked witnesses (`make semtest` batteries, `e2e.sh`'s B6 netns
per-rule-counter probe, `vm-e2e`'s live ping/TCP counter checks). The obvious
gate — random supported rulesets × random packets in a netns, kernel per-rule
counters vs the extracted `eval_chain`/`eval_hook` — is *not* blocked on
missing machinery. The ingredients exist: the evaluators (incl. the sequence
form `seq_eval_env`) are extracted and runnable, `nftc send --commit` installs
a verified-compiled ruleset atomically, `e2e.sh` B6 already reads back per-rule
counters after crafted traffic in an unprivileged netns, and `vm-e2e` boots a
stock kernel rootlessly for the cases netns cannot host. The honest blockers,
in order:
1. **Generator effort** (the bulk of it): a random-ruleset generator that stays
   inside the supported subset, plus a packet generator that *reaches* the
   generated matches (random bytes almost never hit a `ct state established`
   or a specific concat-set element; you need constraint-aware packet
   synthesis per rule) — engineering, not research, but substantial.
2. **Observability of env state**: verdicts are observable per rule (counters),
   but the model's `e_limit`/`e_quota` are *token counts* consumed by a
   verdict-keyed sweep with no per-rule attribution (see infidelity 1 in the
   ledger above), while the kernel's limits are *time-based* (tokens refill);
   ct-entry internals are only partially readable (`conntrack -L`). So for
   stateful rules the kernel exposes less than the model tracks, and the model
   is known-divergent — a naive differential would mostly rediscover ledgered
   infidelities. Scoping the fuzz gate to the stateless fragment first avoids
   this.
3. **Privileges**: netns covers most of it unprivileged; anything needing real
   devices/timers goes through the (slower) `vm-e2e` path.
So the answer to "effort or observability?" is: *effort for the stateless
fragment* (where the gate is well-defined and would catch e.g. a `data_bitops`
divergence), *observability + ledgered known-divergence for the stateful
fragment*. Until it exists, the eyeball-trusted list above is exactly the
data-plane TCB.

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
equal-width operands nft emits. The `jhash` transform is `data_jhash`, a
**structural abstraction** of the kernel's Jenkins hash (see "Eyeball-trusted"
above): "proved equal on both sides" for a jhash-bearing operand means both
sides compute the *same abstracted* hash — the value matches the real kernel
only up to hash-value renaming, and no differential gate can (or is meant to)
close that. Meta/ct `set` operand VALUES (immediate, field,
value-map, jhash, OR-fold) are now Rocq-proved equal on both sides (the
`eval_vsrc` value-correctness underlying `compile_chain_mut_correct`); the
*mangle* (`SMangle` payload-write) value remains checked by the differential
corpus only — its write is not yet threaded (TODO 3).

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
5. `optimize_chain_valueset` — N-way value → anonymous set
6. `optimize_chain_concatmulti` — K-row two-selector concat set
7. `optimize_chain_datamap` — mark-map merge (labelled sound superset of `nft -o`)
8. `optimize_chain_concat` — N-way concat set
9. `optimize_chain_concatguarded` — mixed concat set
10. `optimize_chain_setguarded` — guarded value set
11. `optimize_chain_intervalset` — interval (range) set
12. `optimize_chain_intervalsethostorder` — transformed interval set
13. `optimize_chain_dscp` — dscp value runs
14. `optimize_chain_intervalsetguarded` — guarded interval set
15. `optimize_chain_mixedpointrangeguarded` — guarded mixed value/interval set
16. `optimize_chain_vmapguarded` — guarded verdict map
17. `optimize_chain_dscpvmap` — dscp verdict map
18. `optimize_chain_vmap` — N-way value+verdict → verdict map

**`nft -o` fold-shape ledger.** Each consolidation stage targets a concrete
`nft --optimize` fold shape (differentially confirmed against host `nft`; the
battery cases live under `battery_cases/`). Shapes are referred to by name —
historical branch-local "gap G*n*" numbers were retired because two audit
branches assigned the same numbers to different shapes:

| shape | example fold | pass module | fidelity |
|---|---|---|---|
| snat bare-map | `ip saddr A snat to T` runs → `snat to ip saddr map { A : T, .. }` | `Optimize_Snat` | matches `nft -o` (bare map) |
| dnat bare-map | `ip daddr A dnat to T` runs → `dnat to ip daddr map { .. }` | `Optimize_Dnat` | matches `nft -o` (bare map) |
| value set | `tcp dport P accept` runs → `tcp dport { P1, P2 } accept` | `Optimize_ValueSet` (valueset) / `Optimize_SetGuarded` | matches `nft -o` |
| interval set | `ip saddr lo-hi accept` runs → `ip saddr { lo1-hi1, .. }` | `Optimize_IntervalSet`/`_Ivsetg` | matches `nft -o` |
| host-order interval set | `ct mark 10-20 accept` runs → `ct mark { 10-20, .. }` (hton transform) | `Optimize_IntervalSetHostOrder` | matches `nft -o` |
| mixed value/interval | guarded mixed runs → one set | `Optimize_MixedPointRangeGuarded` | matches `nft -o` |
| concat set | `ip saddr A tcp dport P` runs → `ip saddr . tcp dport { A . P, .. }` | `Optimize_Concat*` | matches `nft -o` |
| verdict map | `tcp dport P <verdict>` runs, differing verdicts → `vmap { P : v, .. }` | `Optimize_Vmap`/`_Vmapg` | matches `nft -o` |
| ether-vmap | `ether saddr MAC <verdict>` runs → `ether saddr vmap { .. }` | `Optimize_VmapGuarded` | matches `nft -o` |
| dscp-masked-vmap | `ip dscp N <verdict>` runs → `ip dscp vmap { .. }` (masked key) | `Optimize_DscpVmap` (+ `Optimize_Dscp` for same-verdict) | matches `nft -o` |
| mark-map merge | `ip daddr A meta mark set M` runs → guarded `meta mark set ip daddr map { .. }` | `Optimize_DataMap` | sound superset — `nft -o` does not fold `meta mark set` (see `Optimize_DataMap.v` §D1) |

The seam theorem `optimize_preserves_rules_clean` (`Optimize_Table.v`) feeds the base
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
[`theories/Examples/Nft_Tactics.v`](theories/Examples/Nft_Tactics.v): write
`my_chain denies p under my_chains budget my_fuel` (definitionally
`eval_table my_fuel my_chains my_chain p = Drop`) with typed hypotheses
`fieldof FThDport p === port 25` (routed through the `Nftval` constructors), and
discharge it with one tactic — **`nft_eval Hpe`** for a packet constrained by
hypotheses, **`nft_decide`** for a fully concrete packet. The step-by-step recipe
(including `make gen` onboarding of a new file) is in
[`CONFIG_PROOFS.md`](CONFIG_PROOFS.md); compiling worked examples are
`theories/Examples/Nft_Demo_Symbolic.v` and `theories/Examples/Nft_Demo_Concrete.v`. The layer is
additive and sound: every notation is *definitionally* its raw `eval_table` /
`field_value` statement (`nft_*_spec` / `demo_*_def`), `demo_recovers_original`
re-derives the original `Ruleset_Verified`-shaped theorem from the readable one,
and `demo_smtp_not_accepted` / `Fail now nft_decide` witness that the tactics
cannot prove a false property.

**Two M4 soundness rules for this workflow** (full rationale in
`CONFIG_PROOFS.md`, machine-checked artifacts cited):

1. **Pin only what the lookups read — never `e = gen_env` next to an
   env-reading field hypothesis.** `gen_env` empties every non-declaration
   component (conntrack, routes, NAT, ifaddrs), so the whole-env pin can make
   the hypothesis set unsatisfiable and the theorem vacuous. Two proved
   instances: `Router_Realistic.ctstate_under_genenv_never_new` (the pin
   contradicts `ct state new`) and
   `Optiplex_Mark.genenv_fib_local_contradiction` (the pin contradicts
   `fib daddr type local`). Relax to the `e_set`/`e_vmap` CONTENTS the chain
   reads (`Router_Realistic.v` is the reference; `Optiplex_Mark.*_real` the
   fib instance; `Optiplex_Antispoof.antispoof_general_any_env` the
   pin-was-inert case), and always add a concrete satisfiability witness.
   Classification of the superseded-vacuous originals: `THEOREMS.md` §5.
2. **Discharge the fuel budget.** `eval_table` maps fuel exhaustion to the
   chain policy (a verdict the kernel can never produce), and naive fuel
   monotonicity is FALSE (`Semantics.eval_rules_j_not_naively_monotone`).
   Above the computable `Semantics.sufficient_fuel` bound, under the
   `chain_ranked` acyclicity witness (one `reflexivity` via
   `chains_no_transfer_ranked` for jump-free environments), the verdict is
   provably fuel-independent (`eval_table_fuel_indep`,
   `Nft_Tactics.nft_*_fuel_indep`; worked instance
   `Tutorial_Proofs.tutorial_blocks_exactly_any_fuel`). Semantics.v § "Fuel
   discipline for the jump strand" carries the design rationale and the
   kernel citations (load-time loop rejection; `NFT_JUMP_STACK_SIZE = 16`).

## Orientation for a fresh session (read this before picking up a TODO)

**Build & verify (every change must keep ALL of these green):**

| command | gate |
|---|---|
| `make proofs` | all `.v` check; also re-runs `Extract.v` → regenerates `extracted/*.ml{,i}` |
| `make corpus` | upstream `tests/py` round-trip: **2532/2532, 0 mismatches** |
| `make difftest` | compiled bytecode **byte-identical** to live `nft --debug=netlink` |
| `make validate` | `field_load` offsets/names vs live `nft`: **28/28** |
| `make semtest` | executable witnesses: DSL = VM = optimized on packet batteries (incl. the mutation / sequence witnesses) |
| `make parse-test` | `.nft` frontend (TODO 9 M1): parses `../rulesets/ruleset.nft`, checks parsed-AST verdicts vs `Example_Ruleset.v`; difftest ruleset → `glue.ml`'s AST; live-`nft` round-trip; `rule_numgen_free` sanity pins (the discharge itself is the theorem `Lower_Proofs.lower_ruleset_numgen_free`); ExtrOcamlNatInt limit-rate rejection pins |
| `make axioms` | build-failing `Print Assumptions` over every claimed theorem (55): all must be "Closed under the global context" |
| `make gen-check` | checked-in `theories/Generated/*_Gen.v` byte-identical to fresh `nft2coq` output (all four rulesets) |
| `make boundary` | **the M-C migration-permanence gate** (M6): the OCaml frontend (`nft_ast`/`nft_inject`/`nft_parse`/`nft_emit`/`nft2coq`) contains NO value→byte identifier and NO symbol table; `extracted/nft_lower.ml` stays deleted; `TypedEval.v` stays independent of the encode path (`grep encode\|data_eqb\|firstn\|eval_matchcond\|elab_m` = 0). Fails the build on any regression |
| `make gates` | the aggregate: `proofs axioms corpus validate parse-test gen-check boundary`, sequentially |

Axiom-freedom — every headline theorem must print "Closed under the global
context". Re-check the optimizer-pipeline headline (and the compile core) with:
```
cd theories && printf 'From Nft Require Import Correct Optimize_Uncond.\nPrint Assumptions compile_chain_correct.\nPrint Assumptions Optimize_Uncond.optimize_table_uncond_correct.\nPrint Assumptions Optimize_Uncond.optimize_table_uncond_compile_correct.\n' | coqtop -R . Nft | grep -c "Closed under the global context"
```
or run **`make axioms`**, which checks the whole `THEOREMS.md` HEADLINE set +
the `Correct.v` strata + every README-claimed config/semantics result
(anti-spoofing, established-accept, masquerade/multi-address, fib host-local,
ct-state, plus the M4 fuel-adequacy and de-vacuized config heads — 55 theorems total) in one shot and FAILS on anything but "Closed
under the global context".  The in-file `Print Assumptions` lines across
`theories/*.v` are informational (build-log only — they cannot fail a build).
The theorem strata are listed in "The theorems" table above and classified in
`THEOREMS.md`. Any new claimed theorem must be added to `AXIOM_GATE_THEOREMS`
in the same commit that adds the claim.

### Enforcement model (what actually stops a red gate from landing)

Be precise about this, because the honest answer is layered:

- **There is no CI.** The repository has no `.github/` (or any other CI
  configuration); no machine runs the gates on push, and no per-commit gate
  status is recorded anywhere.  Whether some historical commit landed with a
  red gate that was only caught later is therefore *unknowable from the repo*
  — the gates prove the present, not the past.
- **The enforcement point is `make gates`** — one command that runs
  `proofs`, `axioms`, `corpus`, `validate`, `parse-test`, `gen-check`
  sequentially and fails on the first red stage.  The documented norm is that
  *every change keeps all of these green* (this section's table); `make
  gates` makes the norm executable instead of a checklist.
- **The agent workflows bind their own runs, not humans.**  The audit
  workflows under `.claude/workflows/` (see `../adversarial.md`, "commit (or
  git-restore and report failure — never leave red)") enforce a
  revert-on-red discipline, but only for changes made through those
  workflows; a manual commit is constrained by nothing but the norm above.
- **The one documented near-miss** is instructive: `make corpus` stayed green
  while the compile path's host-order byte handling was wrong, because the
  corpus round-trip parses and re-renders the same `.payload` and never runs
  the source compiler on those blocks (`../NOTES.md`, "Register byte-order
  sweep").  The fix shipped with a NEW gate (`make byteorder-gate`) covering
  the blind spot — the pattern this project follows: a gap a gate cannot see
  becomes a new gate, not a doc caveat.  (`make byteorder-gate` and the
  live-kernel `e2e`/`nl-send` targets are heavier, environment-dependent
  gates kept out of the default `gates` sequence; run `byteorder-gate`
  whenever the compile path or renderer touches byte handling.)

**Where things live:**
- `theories/Core/Packet.v` — the `packet` and its `env` (the shared mutable state:
  `e_set`/`e_vmap`/`e_map`/`e_routes`/`e_rt`/`e_limit`/`e_quota`/`e_connlimit`).
  `meta_key`, `ct_key`, etc.
- `theories/IR/Syntax.v` — the DSL AST; `field_load : field -> loaddesc` and
  `do_load`/`field_value` (how a field reads the packet/env); `op_delete`.
- `theories/Core/Bytecode.v` — the VM instruction set (`IDynset` has an `fdata` flag,
  see "discriminator pattern" below).
- `theories/Compiler/Compile.v` — `compile_stmt`/`compile_chain`; register allocation
  `alloc_regs`/`reg_of_slot`/`field_slots`/`load_fields`.
- `theories/Semantics/Semantics.v` — verdict semantics (`eval_chain`/`run_chain`, jump-aware
  `eval_table`/`run_table`, hook `eval_ruleset`/`eval_hook`); **mutation** machinery
  (the per-rule folds `body_step`/`run_rule_step` and their step boundary
  `dsl_rule_step`/`vm_rule_step`, `eval_chain_mut`/`run_chain_mut`); **cross-packet**
  (`eval_chain_mut_env`/`run_chain_mut_env`/`seq_eval_env`); packet/env mutators
  (`set_meta`/`set_ct`/`env_set_upd`/`env_map_upd`).
- `theories/Compiler/Correct.v` — all the theorems and their scaffolding.
- `theories/Compiler/Extract.v` — **add any function you want to call from `semtest.ml` to the
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
`Semantics.run_rule`/`run_rule_step` so they read the new `env` field; the
`compile_load`-style correctness lemmas realign automatically because both sides
read the *same* env function.

**To add a new in-traversal MUTATION** (a statement whose write a later rule sees):
1. `Semantics.v`: give its compiled instruction an effect in `run_rule_step`
   (thread the mutated state to the REST of the walk), and its DSL effect in the
   matching `body_step` case. The single fold makes the write visible to later
   matches/operands of the SAME rule as well as to later rules
   (`eval_rules_mut`/`run_program_mut` thread the step state). Add the statement
   to `is_mut_stmt` so the write-free projection (`run_rule`/`eval_rules`/
   `outcome`) and the mut-free coincidence lemmas (`rule_step_mutfree`/
   `run_rule_step_no_writes`) keep excluding it.
2. `Correct.v`: mark the instruction as a write in `writes_instr` (`true`) and
   non-straight in `straight_instr` (`false`);
   handle it in `run_step_compile_body`'s `is_mut_stmt = true` branch (and in
   `step_compile_after` if it may appear post-outcome) with a *readback* lemma
   proving the compiled statement's `run_rule_step` threading equals the
   `body_step`/`after_step` case. Re-check that `run_rule_step_no_writes`,
   `straight_imp_nw`, `run_rule_step_straight` still discharge the
   instruction's pattern (they `destruct` the instruction — add
   `option`/`bool` sub-destructs for new argument shapes, as the `IDynset`
   cases already do).
3. Do NOT add a well-formedness hypothesis for a shape the frontend can emit:
   either prove it correct or make the lowering refuse it fail-loud (the
   `LEnumgen` pattern), with the discharge theorem over `lower_ruleset`.
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
   `ICtLoad` case in `Semantics.run_rule` AND `run_rule_writes` (a since-retired
   evaluator; its successor is `run_rule_step`).
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
**Plan.** Make `fdata=false` a write too — one new case in each per-rule fold:
the DSL write in `body_step`'s `SDynsetImm` case, the VM write in `run_rule_step`'s
`IDynset … (Some dreg) false` case (threaded at the RUNNING state, so the learned
element is visible to later lookups of the SAME rule too). The data value is the
immediate at `dreg`:
define `imm_at (r) (dimms) := fold_left (fun acc rv => if Nat.eqb (fst rv) r then snd rv else acc) dimms []`
(last write wins, matching `set_reg` order); `body_step` for `SDynsetImm` uses
`imm_at datareg dimms`. Prove `load_imms`-readback: running the `IImmediateData`
prefix leaves `dreg` holding `imm_at datareg dimms` **when** `datareg ∈ map fst dimms`
(a fold-independence lemma: a matching key overrides the initial register value).
There is no well-formedness-conjunct route for that side condition (`simple_body`/
`mut_wf` are retired; the bridge takes no such hypotheses): either prove
`datareg ∈ map fst dimms` unconditionally over `compile_stmt` output (the compiler
emits the data immediate itself — the `compile_vsrc` degenerate-operand pinning
pattern), or make the lowering refuse the shape fail-loud (the `Lower.LEnumgen`
pattern, with a discharge theorem over `lower_ruleset`). Then handle `SDynsetImm`
in `run_step_compile_body`'s `is_mut_stmt = true` branch and add it to
`is_mut_stmt`; flip its `IDynset … (Some _) false` to a write in
`writes_instr`/`straight_instr`.
**Risk.** Low–moderate; the only new lemma is fold-independence. **Validate.**
semtest: `add @m {ip saddr : 0x1}; meta mark set ip saddr map @m; meta mark 0x1 accept`.

### TODO 3 — Payload-mangle visible to later rules  🔶 NAT done, payload-mangle open
**NAT: DONE (2026-06 audit).** NAT address/port rewrite is now modelled — flow-stateful
mapping in `e_nat`, L3 (IPv4 header) + L4 (TCP/UDP) checksum updates, zero-UDP-csum
untouched (RFC 768), reply-direction un-NAT of address *and* port, `NF_DROP` on a
no-usable-address interface, ip6-family geometry, inet-table runtime L3 dispatch. Because
NAT is terminal, its rewrite is observed across hooks by the whole-chain trace evaluator
`eval_chain_trace` (see `Optiplex_Mark.v`'s `streaming_flow_whole_ruleset_real`).
**STILL OPEN — payload-mangle.** `payload set` (mangle), `ip dscp set`, ttl/hoplimit are
still verdict-neutral straight-line statements (`SMangle` is not an `is_mut_stmt`), so a
later rule reading the mangled bytes sees the original.
**Plan.** Add a `set_payload p base off len v` packet mutator (like `set_meta`),
extend `body_step`/`run_rule_step` for `SMangle`/`IPayloadWrite` (the value is
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
in `theories/Optimizer/Optimize_ValueSet.v` (all axiom-free, `Print Assumptions` clean):**
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
  `nft -o` vmap pass) `optimize_rules_vmap2` / `optimize_chain_vmap2` in
  `theories/Optimizer/Optimize_Vmap.v`, proved `optimize_chain_vmap2_correct` (axiom-free).
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
  third headline `nft -o` pass) `optimize_rules_concat2` / `optimize_chain_concat2`
  in `theories/Optimizer/Optimize_Concat.v`, proved `optimize_chain_concat2_correct`
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
  (`nft_ast.ml`) → **`nft_inject.ml`** (pure structural `Nft_ast → Ast.*`
  injection + `ifindex` oracle) → extracted **`Lower.lower_ruleset`** (VERIFIED)
  → trusted `Syntax` AST (`table` + `set_decls`) + `Packet.env`.

**As of M4, all name resolution / value→byte lowering is VERIFIED Coq.**
`Lower.lower_ruleset : (string → option nat) → sruleset → lres lowered_ruleset`
does nft's frontend NAME RESOLUTION *in Rocq*: it expands `define`s (`$v`),
resolves symbolic constants (services like `https`, `ethertype`/`l4proto`/
`ct state`/`icmp` names) to the TYPED value of the selector's datatype via the
verified coercion lattice, inserts the implicit `meta l4proto` dependency
(emitted as the `BDep`-tagged conjunct with family-aware dedup+discharge), and
turns named-set/map *declarations* (and inline anonymous `{…}` sets / `vmap {…}`
maps, incl. **concatenated** keys like `ip daddr . oifname`) into named `env`
entries — anonymous sets DEDUPLICATED by contents. The typed value → register
bytes step is now VERIFIED end-to-end: the per-ATOM byte encoding is everywhere
the round-trip-proved `Nftval.encode`; set/map ELEMENT intervals (incl. CIDR
net/broadcast expansion), range endpoints (incl. the host-endian `byteorder
hton` reversal), vmap keys, NAT/tproxy/redirect target addresses and ports,
mangle/`vsrc` immediates, and bitwise masks are all composed by
`Lower.lower_ruleset`, with real erasure obligations (`set_interval_erasure`,
`concat_key_erasure`, `cidr_interval_agrees_prefix_expand`, the BE
byte-lex-vs-numeric range order, `hton` re-encode). Every construct out of
reach FAILS LOUD as an explicit `lerr` constructor — never a silent OCaml byte
fallback. The four scalar shapes (typed **eq / neq / CIDR-prefix /
ifname-wildcard**, first-class `Typed.txmatch` constructors) route through the
VERIFIED `Typed.elab_tx` / `Typed.prefix_expand`
(`Lower_Proofs.eq/neq/prefix/wildcard_erasure`; the retired legacy module
`IR/Elab.v` and its definitional `elab_matchcond_correct` are documented in
THEOREMS.md § "Strata retirement").

**The residue in `nft_inject.ml` is not value→byte logic** — it is (a) the
single host-dependent `ifindex` oracle (`nametoindex "lo" → 1`; see the ledger
entry below), (b) pure structural `Nft_ast → Ast.*` constructor injection
(character/string/int shuffling, no decoding), and (c) the 2^40 extraction-seam
guard. The `.nft`-derived `*_Gen.v` bytes are additionally re-checked by the
differential gates (corpus/validate/parse-test/e2e). `Nft_parse.parse_file` adds
`include` expansion (relative to the file dir).

**The proof bridge (`nft_emit.ml` + `nft2coq`).** `make gen` runs the parser on a
`.nft` file and EMITS its **surface** tree as a Coq `Definition <name>_surface :
sruleset` — `theories/Generated/Optiplex_Gen.v`, `theories/Generated/Ruleset_Gen.v`
then define the chains and the `set_decls`/`env` their lookups read as the
VERIFIED `Lower.lower_ruleset` applied to that surface term (`_lowered :=
lower_or_empty ifindex_pins _surface`, reduced by `Eval vm_compute`, carved into
the per-table `filter_chains`/`filter_input`/`decls`/… by the `lr_*`
projections).  So the emitter writes NO byte: every match operand, set element,
NAT target and hook priority the proofs reason about is the kernel-checked output
of the verified lowering, and a construct the lowering refuses fails the
generated `Example <name>_lowers_ok : lower_ok ifindex_pins <name>_surface = true`
(fail-loud — `make proofs` breaks, never a silent OCaml byte).  The proof files
`Require Import` these and prove properties about the *parser's actual output*,
closing the previously-eyeballed "the AST mirrors the text" link.  `nft2coq` IS
the frontend; the emitted `.v` is checked by the Rocq kernel (untrusted emitter,
kernel-checked result — same trust story as the renderer).

**Proven about the parsed rulesets (all axiom-free):**
  - `Ruleset_Verified.v` — the 8 packet-verdict properties of `../rulesets/ruleset.nft`
    (established/invalid/loopback/ssh/smtp/ipv6-nd/forward), now about the
    *generated* `firewall_inbound` rather than a hand copy.
  - `Optiplex_Antispoof.v` — **anti-spoofing** for `../rulesets/optiplex.nft`'s bridge
    `output` chain: a frame to a protected VM address leaving br.20 on the wrong
    interface is **dropped** (`antispoof_general_any_env`, env-universal; concrete
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
    not match — `pre1_streaming_noop_real`) and is matched by rule 2, which BOTH marks
    the packet (the body) AND destination-NATs it (the terminal `dnat ip to
    $windows` = 192.168.51.186).  The headline `streaming_prerouting_io_real`
    characterises **what comes out**: `eval_chain_trace filter_prerouting p =
    (Accept, apply_nat … pre2 (set_meta p MKmark 0x99))` — the marked packet with
    the terminal dnat applied; `pre2_apply_dnat` shows the dnat rewrites the
    destination address to the windows box, and `streaming_prerouting_mark_real` shows
    the mark SURVIVES it.  `streaming_flow_whole_ruleset_real` then carries that packet
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
`theories/Examples/Example_Ruleset.v`, which encodes `../rulesets/ruleset.nft` by hand and proves
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

**Gen-file drift (`make gen-check`).** The `*_Gen.v` files are checked in and
regenerated only by an explicit `make gen`, so there is a failure mode the
proofs alone cannot see: a stale Gen file (or a parser change without a
regeneration) yields a *valid* proof about a ruleset that is not the one the
`.nft` source deploys.  `make gen-check` closes it mechanically: for each of
the FOUR rulesets (`optiplex`, `ruleset`, `tutorial`, `router`) it runs
`nft2coq` fresh and byte-diffs the output against the checked-in
`theories/Generated/*_Gen.v`, failing on any difference.  It is part of
`make gates`.  (Residual scope, stated honestly: gen-check pins
"checked-in == today's parser output"; a *mis-parse* — parser output that
does not mean what the `.nft` text means — is the separate concern covered by
the differential validations above, parse-test/difftest/e2e.)

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
