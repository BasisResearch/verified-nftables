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
  **transport-guarded concat** (concatM, e.g. `ip saddr . tcp dport`) →
  **transport-guarded single-field set** (setg, e.g. bare `tcp dport { … }` /
  `udp dport { … }`) → **interval set** (ivset) → value+verdict→vmap. Matches
  `nft -o` on every safe consolidation.
- **Untrusted tooling**: the `nftc` CLI (`compile`/`optimize`/`send`), a full
  netlink sender that stands up a whole ruleset atomically (NEWTABLE/CHAIN/SET/…),
  and a rootless-VM end-to-end harness (`make vmtest`).
- **nft bug found**: `nft --optimize` merges overlapping-key rules into invalid
  interval sets/vmaps the kernel rejects (fail-closed) — our optimizer soundly
  declines. Reproducer under `proof/battery_cases/`.

## Remaining work

### Optimizer — no sound-to-close gap remains on the 20-shape differential battery
Every consolidation the differential battery (`proof/difftest_battery.sh`, 20 shapes,
`proof/battery_cases/README.md`) surfaces as *sound* is now MATCHed or EXCEEDed by our
verified optimizer, each a machine-checked axiom-free pass composed into
`optimize_table_uncond`:
- transport-guarded single-field SET (`Optimize_Setg.v`) — bare `tcp/udp dport { … }`;
- transport-guarded value+verdict → **VMAP** (`Optimize_Vmapg.v`) — `tcp dport vmap
  { 22:drop, 80:accept, … }` (shape 18);
- fixed-width metafield SET (`Optimize_Merge.v`) — `meta mark`, and adjacent-prefix
  union (shape 06) folds here to an interval-equivalent set;
- same-verdict prefix **ABSORPTION** (`Optimize_Absorb.v`) — `10.0.0.0/24` inside
  `10.0.0.0/16` collapses to the covering `/16` (shape 05);
- plus the pre-existing network-address set/vmap, K-field concat, guarded concat,
  interval set, dnat/snat bare-map stages.
All kernel-confirmed (netns packet-level verdict differential, not just loadability).
The only remaining non-matches are **principled, not gaps**: soundness-necessary
declines where `nft -o`'s fold is unsound in general (overlapping-verdict concat→vmap,
shapes 14/15) and **confirmed `nft --optimize` fail-closed bugs** (shapes 03/04/07/13 +
MINIMAL — valid ruleset → kernel-rejected). Untested-by-the-battery field types (`ct
state` flag-masks, `iifname` strings, `ether saddr` L2) have no battery shape yet — a
consolidation pass for them is possible future work, not a known divergence.

### Data-plane fidelity (compiler/semantics, not the optimizer)
- **Register byte-order sweep**: the ct_state wire-order bug (model stored it
  big-endian; kernel holds ct registers host-order) was fixed in the untrusted
  sender. `meta`/`ct mark` were kernel-adjudicated (netns packet counters) and found
  CORRECT on the wire — the apparent reversal was a **display-only** artifact of the
  untrusted `codec.ml` renderer (it read host-LE bytes big-endian), now fixed, with a
  new **`make byteorder-gate`** compiling the host-order corpus blocks from source and
  diffing against `.payload` (closes the blind spot `make corpus`'s render round-trip
  has). Still to adjudicate against a real kernel: `ct state`'s own representation and
  the remaining host-order `ct`/`meta`/`rt` keys the display fix covers by class but
  that were not individually packet-tested.
- **Field-unit faithfulness**: `FPayload` off/len are in bytes vs nft's bits;
  `SMangle`/`SExthdrWrite` carry raw byte geometry rather than a `field`.
- **Network-state model**: single-address-per-interface assumption; the long-term
  goal is faithful `ct`/`fib` against real conntrack/routing state.

### Tooling
- The `send` netlink encoder covers the common instruction set; a few exotic
  P3 instructions remain at an honest `Unsupported` catch-all.
