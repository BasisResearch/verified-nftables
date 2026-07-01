# Project notes — status & remaining work

Consolidates the former `TODO.md` and `OPTIMIZER_TODO.md` handoff files. For the
design log and the honest scope of the "2532/2532" claim see
[`proof/DEVELOPMENT.md`](proof/DEVELOPMENT.md); for the data-plane fidelity audit
see [`adversarial.md`](adversarial.md).

## What's shipped (verified, axiom-free)

- **Verified compiler + optimizer**: `Compile.compile_chain` (`compile_chain_correct`)
  and the whole-pipeline `Optimize_Uncond.optimize_table_uncond{,_compile}_correct`
  — verdict-preserving for **any** input ruleset, no `rules_clean`/freshness
  precondition. All three headline theorems `Closed under the global context`.
- **Register-free source AST** (`Syntax.v`): nat/tproxy/fwd/queue terminals and the
  dup/dynset statements name VALUES; the compiler allocates every netlink register.
- **Optimizer pipeline** (each pass verified & composed into `optimize_table`):
  base dedup/DCE → **dnat** bare-map → **snat** bare-map → value→set (setsN) →
  K-field concat → meta-mark map (mapN, sound superset) → 2-field concat →
  **transport-guarded concat** (concatM, e.g. `ip saddr . tcp dport`) → **interval
  set** (ivset) → value+verdict→vmap. Matches `nft -o` on every safe consolidation.
- **Untrusted tooling**: the `nftc` CLI (`compile`/`optimize`/`send`), a full
  netlink sender that stands up a whole ruleset atomically (NEWTABLE/CHAIN/SET/…),
  and a rootless-VM end-to-end harness (`make vmtest`).
- **nft bug found**: `nft --optimize` merges overlapping-key rules into invalid
  interval sets/vmaps the kernel rejects (fail-closed) — our optimizer soundly
  declines. Reproducer under `proof/battery_cases/`.

## Remaining work

### Optimizer — the only gaps left vs `nft -o` (all sound under-consolidation)
Our value→set/vmap merge fires for network-address keys and guarded concats but
NOT yet for **bare non-network single-field keys** — `tcp dport`, `udp dport`,
`ct state` (flag masks), `iifname`, `meta mark` (match), `ether saddr` — nor for
disjoint-prefix unions. `nft` folds each into a set/vmap; we leave sequential
`cmp` rules (always first-match-equivalent). Closing these is the active
optimizer track; the differential harness is `proof/difftest_battery.sh`.

### Data-plane fidelity (compiler/semantics, not the optimizer)
- **Register byte-order sweep**: the ct_state wire-order bug (model stored it
  big-endian; kernel holds ct registers host-order) was fixed in the untrusted
  sender. Sweep the other host-order register values (other ct keys, some meta
  keys, `rt`) the model may store big-endian and that would likewise fail on a
  real kernel — use the runtime-counter kernel-round-trip gate the fix added
  (text-render gates are structurally blind to this class).
- **Field-unit faithfulness**: `FPayload` off/len are in bytes vs nft's bits;
  `SMangle`/`SExthdrWrite` carry raw byte geometry rather than a `field`.
- **Network-state model**: single-address-per-interface assumption; the long-term
  goal is faithful `ct`/`fib` against real conntrack/routing state.

### Tooling
- The `send` netlink encoder covers the common instruction set; a few exotic
  P3 instructions remain at an honest `Unsupported` catch-all.
