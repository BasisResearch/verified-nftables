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
- **Optimizer pipeline** (base dedup/DCE + **18** verified consolidation passes,
  each machine-checked & composed into `optimize_table` — see `Optimize_Table.v`
  for the exact order). The families now folded (each verdict-preserving,
  kernel-datapath-checked):
  - **value → SET**: network addresses (`valueset`); transport ports & `ether saddr`
    L2 (`setg`); fixed-width meta scalars — `mark`/`skuid`/`skgid`/`l4proto`/
    `nfproto`/`pkttype`/`cpu`/`protocol` — plus `iifname`/`oifname` strings and
    scalar `ct mark` (`Optimize_ValueSet`).
  - **value+verdict → VMAP**: network address + transport + `ether saddr` L2
    (`vmapguarded`), network (`vmap`), `ip dscp` (`dscpvmap`).
  - **interval RANGE → set**: network (`intervalset`), host-order `ct mark` (`intervalsethostorder`),
    guarded transport/inet (`intervalsetguarded`), mixed point+range (`mixedpointrangeguarded`).
  - **concat**: K-field (`concatmulti`), 2-field (`concat`), transport-guarded
    (`concatguarded`, e.g. `ip saddr . tcp dport`).
  - **maps**: `dnat`/`snat` bare-map, meta-mark map (`datamap`, sound superset).
  - **`ct state` bitmask-UNION** (`ctmask` — the *sound* `state & 0x0a != 0`,
    NOT nft's exact-set; see the nft bitmask defect below), **`ip dscp` masked
    set** (`dscp`), same-verdict **prefix absorption** `/24 ⊂ /16 → /16` (`absorb`).

  Matches `nft -o` on every *representable, verdict-preserving* consolidation, and
  **exceeds** it where nft declines (e.g. `saddr → meta mark` map).
- **Untrusted tooling**: the `nftc` CLI (`compile`/`optimize`/`send`), a full
  netlink sender that stands up a whole ruleset atomically (NEWTABLE/CHAIN/SET/…),
  and a rootless-VM end-to-end harness (`make vmtest`).
- **Two `nft --optimize` defects found** (we soundly decline both; dedicated
  write-up with minimal examples + live-kernel evidence in
  [`NFT_BUGS.md`](NFT_BUGS.md); full per-shape analysis + reproducers under
  `proof/battery_cases/`):
  1. **Overlapping-key merge → unloadable ruleset.** It merges overlapping-key
     rules into an interval set/vmap **without checking representability**;
     nftables correctly rejects the result (userspace `intervals.c` for
     single-field overlaps, kernel `pipapo` for dead-rule concats), so `-f`
     aborts with **0 rules applied**. A valid disjoint merge exists; nft doesn't
     compute it.
  2. **Bitmask-field exact-set merge → changed verdict.** For bitmask fields
     (`ct state`, `tcp flags`) a single rule compiles to a *bit-test*
     (`bitwise & mask; cmp neq 0`), but nft folds `{a, b}` into an *exact-value*
     set (dropping the bitwise). A packet with extra bits set (e.g. `tcp flags`
     `0x12` = SYN+ACK) matches the bit-test but misses the exact set → the fold
     silently changes the verdict. We instead fold the *sound* same-verdict
     mask-union (`state & (a|b) != 0`, one masked compare; `Optimize_CtMask`).

## Remaining work

### Optimizer — one soundly-closeable gap (G1) + one needing new semantics (14/15)
The pipeline (above) MATCHes or EXCEEDs `nft -o` on every
*representable, verdict-preserving* consolidation the differential battery
(`proof/difftest_battery.sh`, `proof/battery_cases/README.md`) surfaces — all
kernel-confirmed by netns packet-level verdict differential, not just loadability.
What remains open:

- **G1 — differing-verdict multi-field concat → concat VMAP** (soundly closeable,
  no new semantics; the honest deferral from the 2026-07-02 G1–G4 round). The
  *same-verdict* concat→SET case already folds (`concatmulti/N/M`); the open case is
  `ip saddr X tcp dport Y accept; … Z drop` → `saddr . tcp dport vmap { X.Y :
  accept, … : drop }`. No stage today produces a *concat-keyed vmap* (every vmap
  stage has a single-field key; every concat stage yields a single-verdict set).
  Spec: a new `Optimize_ConcatVmap.v` = `Optimize_ConcatGuarded` (multi-field concat-key
  recogniser) × `Optimize_Vmap` (`assoc_verdict` first-match order), composed
  between `concatguarded` and `setg`. A substantial new proof, not a template tweak.

- **Shapes 14/15 — strictly-interior overlapping-verdict concat → vmap** (needs a
  semantics extension). `nft -o`'s fold *is* verdict-correct here: a concatenated
  interval set (kernel `pipapo`) is an *ordered* first-match structure (lookup
  returns the lowest rule index, `pipapo_refill`/`__builtin_ctzl`), and nft emits
  the elements in rule order, so `dport 22→drop, 50→accept` matches first-match
  (datapath-verified); the wrong (dead-rule) order is refused by the kernel. We
  decline only because `Semantics.v` models set/vmap lookup as unordered/disjoint-key.
  Closing it needs modeling the kernel's ordered/rule-indexed interval-set
  semantics — genuine open work.

The remaining non-matches are **not our gaps** — they are the two `nft --optimize`
defects (see "What's shipped" above): the overlapping-key unloadable merge
(battery 03/04/07/13/MINIMAL) and the bitmask-field exact-set verdict change
(`ct state`/`tcp flags`). We decline both. See `proof/battery_cases/README.md` for
the per-shape classification and kernel-source citations.

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
  **Source-side corpus coverage (measured 2026-07; the widen-the-gate TODO).** Driving
  the WHOLE corpus source-side (parse each block's `# <src>` header, compile with the
  verified compiler, diff all rendered lines): of **1742** attemptable headered blocks,
  **1142 (65.6 %)** are already byte-identical, **517** fail loudly on frontend syntax
  gaps, and **83** are genuine text mismatches — host-order byte-order divergences on
  keys *outside* byteorder-gate's set (`meta length/cpu/skuid/skgid`, `ct expiration`,
  bitwise mask/xor operands), nft constant-folds/merges we don't replicate (`xor`
  fold, adjacent-payload merge), and render/lowering text differences with no
  adjudicated wire divergence (dependency guards, reject/log defaults).
  A full source gate would be red today (83), and most of that red is *unadjudicated
  display-vs-wire divergence*, so the gate stays scoped to the adjudicated host-order
  plain-cmp/range class (13 blocks). TODO: adjudicate the mismatch classes against a
  real kernel (netns packet counters, as for meta/ct mark), then widen the gate
  class-by-class. Details: `proof/DEVELOPMENT.md` § "What the round-trip does and does
  NOT validate".
- **Field-unit faithfulness**: `FPayload` off/len are in bytes vs nft's bits;
  `SMangle`/`SExthdrWrite` carry raw byte geometry rather than a `field`.
- **Network-state model**: single-address-per-interface assumption; the long-term
  goal is faithful `ct`/`fib` against real conntrack/routing state.

### Tooling
- The `send` netlink encoder covers the common instruction set; a few exotic
  P3 instructions remain at an honest `Unsupported` catch-all.
