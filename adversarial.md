# Adversarial semantics audit

How we stress-tested the Rocq nftables semantics for *fidelity* to the real kernel,
and the 52 infidelities it found and fixed.

The compiler-correctness theorem (`compile_chain_correct`) only says the **bytecode VM
agrees with the DSL semantics** — it is silent on whether that semantics actually matches
*real nftables*. A semantics that models every NAT statement as `accept` can still be
"correct" against itself. This audit attacks that gap: an adversary tries to show the
semantics diverges from the linux kernel, and a fixer makes it faithful, looping until the
adversary can no longer substantiate a divergence.

The audit converged on 2026-06-22: after a final round of diligent, C-source-grounded
search, the red agent could not substantiate any new infidelity (`satisfied=true`).

> **As-of note (snapshot).** This document is a historical record of that audit run: its
> commit references (`75df26b` baseline, `1a17d10` HEAD) and "52 fixes" tally are accurate
> *as of 2026-06-22 on the then-current `verified-nft-compiler` branch*. That branch has
> since been merged into `main`, which has moved on: as of 2026-06-25, `main` is ~47 commits
> past `1a17d10` and carries later objectives that postdate this audit — the table optimizer
> (`optimize_table_correct`), multi-address NAT primary selection
> (`masq_saddr_is_selected_primary`), fib precision (`fib_local_hostwide_crossiface`), and
> the per-datatype validity layer. To verify a single fix from the list below, read it in its
> historical context; the *current* headline guarantees live in `proof/DEVELOPMENT.md`. The
> audit narrative itself (which infidelities were found and how each was made faithful)
> remains valid.

---

## The workflow

Driver: [`.claude/workflows/adversarial-semantics-audit.js`](.claude/workflows/adversarial-semantics-audit.js)
(a Claude Code multi-agent workflow). Baseline commit `75df26b`; all fixes below are on
branch `verified-nft-compiler`.

```
Recon ──▶ ┌─────────────────── loop (≤ maxRounds, default 10) ───────────────────┐ ──▶ Synthesis
          │  RED: verify last fix is real, then find ONE new infidelity          │
          │   via (1) reading kernel C source, (2) a TRUE property the model     │
          │       cannot prove, or (3) a FALSE property the model CAN prove.     │
          │  BLUE: fix the SPEC faithfully, keep every gate green + axiom-free,   │
          │        commit (or git-restore and report failure — never leave red). │
          │  stop when RED returns satisfied=true (or blue flags a repo risk).   │
          └──────────────────────────────────────────────────────────────────────┘
```

### Roles

- **Red (adversary).** Each round, first *adversarially re-verifies the previous fix*
  (re-runs its repro, re-checks gates and axiom-freedom — a bogus fix or a regression is
  itself a finding). Then hunts for one new, highest-severity infidelity by the most
  rigorous method available:
  1. **C source** — quote `net/netfilter/*.c` at `file:line` and show the semantics differs.
  2. **Unprovable-correct** — state a property TRUE of the kernel and show it is *not*
     provable in Coq (semantics too weak / wrong).
  3. **Provable-incorrect** — state a property FALSE of the kernel and show it *is*
     provable (semantics unsound / vacuous).

  Findings are returned through a strict JSON schema (`title, kind, description, evidence,
  repro, suggested_fix, severity, satisfied`), so every claim ships with reproducible
  evidence — usually a kernel quote plus an axiom-free coqtop transcript.

- **Blue (fixer).** Fixes the **specification** (`Semantics.v` / `Syntax.v` / `Packet.v`,
  and the parser `nft_lower.ml` / `parser.mly` / `nft_emit.ml`, regenerating `*_Gen.v` when
  the AST shape changes). Hard constraints: never make a theorem pass by weakening it or
  adding an axiom; keep **all** gates green; commit only when green, otherwise
  `git restore` and report `fixed=false` (never leave the tree broken). Returns a JSON
  report with real gate numbers.

- **Synthesis.** Tabulates findings, fixes, and residual infidelities at the end of a run.

### The gates (every fix must keep all of these green)

| Gate | Command (from `proof/`) | Invariant |
|---|---|---|
| Proofs | `make proofs` | all `.v` check + re-extract; 0 errors, 0 `Admitted` |
| Corpus | `make corpus` | upstream `tests/py` round-trip: **2532/2532**, 0 mismatches |
| Validate | `make validate` | `field_load` offsets vs **live nft**: **28/28** |
| Parser | `make parse-test` | parser harness incl. anti-spoof + mark + saddr checks |
| Axiom-freedom | `Print Assumptions compile_chain_correct` | "Closed under the global context" |

### Running it

```
# from the repo, in Claude Code:
Workflow { name: "adversarial-semantics-audit", args: { maxRounds: 10, focus: "<optional steer>" } }
```

`focus` narrows the hunt (e.g. avoid an area with no model representation, or target an
unexplored selector). Runs are **chained**: each is capped at `maxRounds`, and you re-run
from the improved repo state until a run returns `satisfied=true`.

### Operational notes (learned the hard way)

- **Convergence is multi-run.** Reaching `satisfied=true` took nine chained runs. Most
  10-round runs found and fixed 10 real infidelities; the loop only stops when an *entire
  round* yields nothing substantiable.
- **Suspend kills a run.** If the laptop suspends for hours, the orchestrator zombies
  (reports `running` but its subagents stop writing). Detect via a long-frozen newest mtime
  + no recent writes (including `.vo`/`.glob`/`.aux` build artifacts) + no new commit, then
  recover: `TaskStop`, `git checkout -- .`, `rm -f proof/theories/Red_*.v`, re-verify green,
  relaunch.
- **Not every red lead is a real bug.** One run stalled on "read-only ct state is a
  per-packet oracle"; a later run *substantiated* it (ct state is flow-derived in the
  kernel, consistent across a flow's packets) and fixed it (`13db31b`). When in doubt the
  loop self-corrects — but steer red away from areas the model has no representation for
  (raw payload bytes, L4 transport-checksum internals) to avoid wedging.

---

## Issues identified and fixed (52)

Grouped by theme. Every fix is axiom-free and keeps all gates green; commit hashes are on
branch `verified-nft-compiler`. Full ordered list: `git log --reverse 75df26b..HEAD`.

### Conntrack & statefulness (the biggest class)
The original model treated conntrack as a per-packet *oracle*. The kernel keeps writable
state in the shared flow entry and derives read-only state per-skb at lookup. These fixes
rebuilt that.

- `4b90569` — ct mark/label persist across a flow's packets (shared conntrack table).
- `13db31b` — ct **state** and all read-only ct keys are flow-keyed, not a per-packet oracle.
- `6c0f15e` — ct **direction** derived from `pkt_ctdir_orig`, not a free oracle byte.
- `e8fe429` — `connlimit` is a flow-keyed connection counter, not a per-packet bucket.
- `a7a848d` — ct-state **INVALID** encoding fixed (`NF_CT_STATE_INVALID_BIT` = 1<<0, not 1<<5).
- `1ecc297` — a non-state ct key on a **no-entry** packet BREAKs the rule (kernel `NFT_BREAK`).
- `1a17d10` — `ct … set` (mark/secmark/label) is a **no-op** when the packet has no entry.
- `528b12d` / `6d2711a` — `notrack` sets ct state to UNTRACKED, observed by later reads,
  threaded intra-rule into the rule's own matches/terminal.
- `598cf8b` — `notrack` is a **no-op** when a conntrack entry already exists (kernel guard).

### NAT (it was modelled as bare `accept`)
- `0dc940e` — dnat/snat/redirect actually rewrite the address in the data-plane trace.
- `9bd72ba` / `9fa4ac8` — address rewrite & masquerade geometry are family-aware (ip6 = 16 bytes).
- `5af126a` / `e01f290` — L4 **port** rewrite, including un-rewriting the reply-direction port.
- `f5aaa1c` — port-only dnat/snat preserves the L3 address (operand-presence gating).
- `8c2a226` / `5bc0f66` / `74ab93e` — IPv4 header checksum *and* L4 (TCP/UDP) checksum updated
  on rewrite; a zero UDP checksum is left untouched (RFC 768).
- `72cfca2` / `8189ee7` — NAT is flow-stateful: map once, store in a flow-keyed table, reuse
  per flow, and un-NAT replies (store original addr + ctdir bit).
- `e6f5907` — redirect destination-NAT is hook-dependent (loopback at the output hook).
- `8be02fe` — NAT-core returns **NF_DROP** when the interface has no usable address.
- `391987f` — inet-table NAT dispatches the L3 family at **runtime per packet**, not pinned to IPv4.

### Rate limiting & accounting (were inert / per-packet)
- `c44fc09` — honour the `over` (invert) flag in limit/quota/connlimit matches.
- `aa3d9fe` — limit/quota/connlimit are shared **consuming** token buckets, not oracles.
- `42d80bc` — limit rate/unit/burst made live (real token-bucket cost & cap; was inert).
- `c2287e1` — quota counts **bytes** (`skb->len`) per eval, not a fixed −1.

### Payload / header loads (BREAK semantics)
- `04407c0` — a failed transport-payload load fails the rule (`NFT_BREAK`); never truncates.
- `c123b4a` — link-layer (`ether`) loads guard on MAC-header presence (`NFT_PAYLOAD_LL_HEADER`).
- `8a5ebc6` — exthdr / TCP-option value loads guard on not-present (`NFT_BREAK`).

### Matching, sets & encoding
- `5058ab9` / `a85c4fa` — single positive `ct state` / `tcp flags` lower to a **bitmask** test, not exact equality.
- `dac1092` — distinguish a `ct state` comma OR-list from a brace set (bitmask fold).
- `43202ed` / `13ee781` — concat-set membership is per-field cross-product, split by 4-byte
  register slots (ifname = 16) — this underpins the anti-spoofing proof.
- `8b168f8` — non-wildcard ifname matches padded to the kernel's 16-byte exact compare.
- `3e03cd3` / `e107418` — iif/oif lower to the numeric interface **index** (host-endian, via `hton`), not the ASCII name.
- `deb409a` / `c322ceb` / `44ef815` — `meta nfproto` wired to the L3 family table, with the
  implicit nfproto guard lowered before inet ip/ip6 and icmp/icmpv6 matches.
- `b52690b` / `420aaab` — host-endian `mark` ranges & interval-set membership emit `byteorder hton`.
- `ab4c83d` — byteorder swaps each SIZE-byte element, not the whole LEN-byte chunk.
- `91274be` — ct/meta `set` values encoded at the key's register width, not always u32.
- `6fc196d` — interval/prefix verdict-map keys (`NFT_SET_INTERVAL | NFT_SET_MAP`).
- `77f9a08` — fib route-type `anycast` = `RTN_ANYCAST` (4), not `RTN_BLACKHOLE` (6).
- `ce6aa07` — fib route-type encoded host-endian (`BYTEORDER_HOST_ENDIAN`).

### Verdicts & control flow
- `e1d3455` — synproxy is verdict-bearing (STOLEN/DROP/BREAK), not a no-op.
- `eac4e54` — jump/goto fidelity bridged: `eval_chain` routed through the faithful
  `eval_table`; jump-aware drop locked in.
- `ee5193a` — `numgen inc` is a shared persistent round-robin counter, not a per-packet oracle.

*(10 conntrack + 14 NAT + 4 rate/accounting + 3 payload + 18 matching/sets/encoding + 3 verdicts/control-flow = 52.)*

### Verifying any single fix

```
eval $(opam env --switch=vst)
cd proof && coq_makefile -f _CoqProject -o CoqMakefile
git show <hash>                      # see the spec change + its axiom-free demo theorem
make -f CoqMakefile theories/<File>.vo
```

---

## Outcome

| | |
|---|---|
| Total fixes | **52** axiom-free fidelity fixes since `75df26b` |
| HEAD | `1a17d10` |
| `make proofs` | ok (0 errors, 0 `Admitted`) |
| `make corpus` | 2532/2532, 0 mismatches |
| `make validate` | 28/28 |
| `make parse-test` | ALL PASSED |
| `compile_chain_correct` | Closed under the global context |
| Red verdict | **satisfied** — no further infidelity substantiable |

The model is now faithful enough that an adversarial prover, given the linux-6.18.33 kernel
source, concedes. Re-running the workflow from this state is the way to keep it honest as the
semantics grows.
