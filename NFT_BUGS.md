# Three bugs found in `nft --optimize`

This project differentially tests its formally verified rule-consolidation
optimizer against nftables' own `nft --optimize` (`nft -o`): every ruleset shape
is run through both optimizers, loaded into a real kernel in an unprivileged
netns, and — where the outputs differ — settled by packet-level data-plane
probes, not just loadability. That process surfaced **two genuine mis-merge
defects in `nft -o`** (the userspace optimizer, `src/optimize.c`), reported as
Bugs 1 and 2 below. A **third** defect — an outright optimizer crash (Bug 3) —
was found separately, by running `nft -o` over a corpus of real-world GitHub
configs as a crash-oracle rather than through the formal differential.
Everything below was re-verified on **nftables v1.1.6** / Linux 6.18 (Bugs 1–2
on 2026-07-13, Bug 3 on 2026-07-15) — and Bugs 1–2 additionally on upstream
**git HEAD** and on **v1.0.2**, the first release with `-o` (see "Upstream
status" under each); per-shape classification and the full battery live in
[`proof/battery_cases/`](proof/battery_cases/README.md) (run
`bash difftest_battery.sh` from `proof/`).

Bugs 1 and 2 share one root cause: **`nft -o` merges adjacent rules on the same
selector without checking that the merged form means the same thing — or can be
represented at all.** In Bug 1 the merged form loads but matches fewer packets
(silent verdict change). In Bug 2 the merged form is unrepresentable, nftables
itself rejects it, and the whole transaction is discarded. Bug 3 is unrelated to
merging: the optimizer's statement-matrix builder `assert()`-aborts on a valid
single rule of the form `field & $mask == value`.

To be clear about blame: the nftables **core** (userspace validator and kernel
set backends) behaves correctly in every case below. All three defects are
confined to the optimizer (`src/optimize.c`) — Bugs 1 and 2 to its rewrite step,
Bug 3 to its statement-matrix builder.

---

## Bug 1 — bitmask fields folded into an exact set: silent verdict change

**Severity: high — the rewritten ruleset loads cleanly (exit 0) and drops
packets the original accepted.**

### Explanation

For a bitmask-typed field, a single nft rule compiles to a *bit test*:

```
tcp flags syn accept
    ⇓
[ payload load 1b @ transport header + 13 => reg 1 ]
[ bitwise reg 1 = ( reg 1 & 0x00000002 ) ^ 0x00000000 ]   ; mask to the SYN bit
[ cmp neq reg 1 0x00000000 ]                              ; ≠ 0 → any pkt WITH SYN set
[ immediate reg 0 accept ]
```

i.e. `tcp flags syn` means "the SYN bit is set" — it matches SYN (0x02),
SYN+ACK (0x12), SYN+ECE, etc.

`nft -o` folds two such rules into a set — and the set form compiles to an
**exact-value lookup with no bitwise step**:

```
tcp flags { syn, ack } accept
    ⇓
[ payload load 1b @ transport header + 13 => reg 1 ]
[ lookup reg 1 set __set%d ]                              ; flags byte ∈ {0x02, 0x10} EXACTLY
[ immediate reg 0 accept ]
```

`{ syn, ack }` as a set means "the flags byte **equals** 0x02 or **equals**
0x10". Any packet with more than one flag bit set — most notably the SYN+ACK
(0x12) of every TCP handshake — matched the originals but misses the fold. The
optimizer replaces a union of bit-tests with a strictly narrower exact-match
object and reports success.

### Minimal example

```nft
table inet t {
  chain c {
    type filter hook input priority 0; policy drop;
    tcp flags syn accept
    tcp flags ack accept
  }
}
```

```console
$ nft -o -f repro.nft        # exits 0, loads fine
Merging:
    tcp flags syn accept
    tcp flags ack accept
into:
	tcp flags { syn, ack } accept
```

### Data-plane proof (loopback TCP connect, policy drop)

One real `connect()` to a listening socket on 127.0.0.1, both forms, with
counters (netns, nft v1.1.6):

| ruleset | handshake | counters |
|---|---|---|
| original two bit-test rules | **SUCCEEDED** | `tcp flags syn` matched 2 pkts (SYN *and* SYN+ACK), `tcp flags ack` 4 |
| `nft -o` fold `tcp flags { syn, ack }` | **FAILED (timed out)** | set rule matched only the bare SYNs; 3 packets — the SYN+ACKs (0x12) — fell through to `policy drop` |

Same input ruleset, same kernel: the optimized form breaks every TCP
connection the original allowed. Because the fold loads without any warning,
nothing tells the operator the firewall's semantics changed.

### The strongest real-world case: `ct status` on a NAT gateway

`tcp flags` is the clean textbook illustration, but the most damaging *and* most
realistic instance of this bug is **`ct status`**. On any router or gateway,
`ct status dnat` / `ct status snat` are the idiomatic way to match
port-forwarded / masqueraded connections. And unlike `ct state` (single-bit per
packet), conntrack **status is always multi-bit**: a real DNAT'd packet carries
`dnat | confirmed | assured | seen-reply | dst-nat-done | …` all at once — never
the bare `dnat` bit alone.

A gateway that accepts its NAT'd flows:

```nft
table inet filter {
  chain forward {
    type filter hook forward priority 0; policy drop;
    ct status snat accept
    ct status dnat accept
  }
}
```

```console
$ nft -o -f gateway.nft        # exits 0, loads fine
Merging:
    ct status snat accept
    ct status dnat accept
into:
	ct status { snat, dnat } accept
```

The single rule `ct status dnat` compiles to a bit-test; the fold compiles to an
exact-value set — the same mechanism as `tcp flags`:

```
ct status dnat            ⇒   [ ct load status => reg 1 ]
                              [ bitwise reg 1 = ( reg 1 & 0x00000020 ) ^ 0x0 ]   ; any pkt WITH the dnat bit
                              [ cmp neq reg 1 0x00000000 ]

ct status { snat, dnat }  ⇒   [ ct load status => reg 1 ]
                              [ lookup reg 1 set __set%d ]                        ; status EXACTLY 0x10 or 0x20
```

Because a real DNAT'd packet's status is `0x20` **plus** other bits, it equals
neither set element — so the fold matches **none** of the traffic the original
rule matched. This is not a corner case like the SYN+ACK gap; it silently
breaks the *entire* forwarded flow.

#### Data-plane proof (DNAT 9999→8080 on loopback, policy drop, netns)

Three real `connect()`s through the DNAT rule, counters on both forms
(`proof/battery_cases/nft_optimize_bug1_scope/ct_status_dnat.sh`):

| rule | matched |
|---|---|
| original `ct status dnat` (bit-test) | **24 packets** |
| `nft -o` fold `ct status { snat, dnat }` (exact set) | **0 packets** |

Same packets, same kernel: the optimized gateway accepts none of its own NAT'd
traffic. With `policy drop`, every forwarded connection is silently broken.

### Scope — which fields trigger it, and how realistic each is

The bug fires for **any bitmask-typed field** where two consecutive
same-verdict rules use the *bit-test* form (`field flag`, compiling to
`field & flag != 0`) and differ only in the flag. `nft -o` folds them into an
exact-value set `field { a, b }` (compiling to `lookup set`), which is strictly
narrower. It is **not** triggered by the masked-equality form
(`field & M == v`) — commit `447ac8a3` (1.1.2) added a *separate, sound* fold
for that. Negated matches (`tcp flags != syn`) are **not folded** at all, so
negation is not an additional trigger.

**The set of vulnerable fields is closed and small.** A field has the
any-of-bits semantics that this bug exploits iff its datatype's basetype is
`TYPE_BITMASK` in the nftables source (`.basetype = &bitmask_type`). Grepping
the tree, that is **exactly five** datatypes — there are no others:

| datatype (`src/`) | match syntax | live trigger? |
|---|---|---|
| `tcp_flag` (`proto.c`) | `tcp flags syn` | **yes** — multi-flag packets (SYN+ACK, …) are routine |
| `ct_status` (`ct.c`) | `ct status dnat` | **yes, worst** — status is *always* multi-bit |
| `ct_label` (`ct.c`) | `ct label foo` | **yes** — labels co-occur by design (128-bit bitmap) |
| `ct_state` (`ct.c`) | `ct state new` | no — folds, but single-bit per packet (safe by accident) |
| `ct_event` (`ct.c`) | `ct event new` | no — not a match; kernel rejects it (`Operation not supported`), statement-only |

Ordered by how damaging and realistic the bug is on each:

- **`ct status` — the strongest case (realistic *and* catastrophic)** — the
  NAT-gateway example worked through above (24 packets → 0). Realistic on every
  router, genuinely multi-bit, and the fold breaks the entire matched flow
  rather than a corner case.

- **`tcp flags` — realistic, both directions provable.** Real firewalls
  routinely match TCP flags — MSS clamping on SYN, SYNPROXY, and invalid-flags
  anti-scan drops. Caveat on realism: the *hardened* anti-scan rules usually use
  the masked-equality form (`tcp flags & (fin|syn|rst|…) == …`), which folds
  **soundly**; the bit-test form that triggers the bug is more typical of
  hand-written / simple rules. Two directions, both data-plane-verified:
  - *fail-closed* (accept verdict, narrower → breaks connectivity): the headline
    example above — folding `tcp flags syn accept; tcp flags ack accept` drops
    every SYN+ACK (0x12), so no TCP handshake completes.
  - *fail-open* (drop verdict, narrower → security hole, "wider accept"):
    `tcp flags fin drop; tcp flags rst drop` → `tcp flags { fin, rst } drop`
    stops dropping SYN+FIN (0x03, a scan) and FIN+ACK (0x11) — they carry the
    FIN bit but are not in the exact set, so they pass. Proof
    (`nft_optimize_bug1_scope/tcp_flags_failopen.sh`): original bit-test rule
    matched **2** crafted scan packets, folded exact set matched **0**.

- **`ct label` — same hazard as `ct status`, by design.** Connlabels are a
  128-bit bitmap and a connection routinely carries *several at once* (that is
  the point of labels). `ct label foo` compiles to a 128-bit bit-test
  (`ct load label; bitwise & 0x…01; cmp neq 0`), and `nft -o` folds
  `ct label foo accept; ct label bar accept` into `ct label { foo, bar } accept`
  (exact-value set) — verified against a built `nft` with a `connlabel.conf`. A
  connection labelled both `foo` and `bar` (bitmap `0x…03`) matched both
  original rules but is in neither set element, so the fold silently stops
  matching it. Realistic wherever labels drive policy (e.g. a classifier chain
  tags flows, later chains match the tags). Not data-plane-scripted here only
  because it needs a `connlabel.conf` at a root-owned path; the compile-level
  evidence (bit-test bytecode + the fold) is conclusive.

- **`ct state` — universal but not a live trigger.** Every firewall has
  `ct state` rules, and `ct state new accept; ct state established accept` does
  fold to `ct state { established, new }`. But conntrack *state* (unlike
  *status*/*label*) is single-bit per packet, so exact-set and bit-union
  coincide in-kernel and the fold is correct by accident of an invariant the
  optimizer never checks. (Our verified optimizer instead emits the sound
  mask-union form, `ct state new,established` = `(state & 0x0a) != 0`, one masked
  compare — see `proof/theories/Optimize_Ctmask.v` and battery case 20.)

- **`ct event` — not a trigger.** It *looks* foldable (a `TYPE_BITMASK`
  datatype), but `ct event` is statement-only; used as a match the kernel
  rejects it (`Could not process rule: Operation not supported`), so no rule
  pair to fold ever exists.

**Takeaway:** three of the five `TYPE_BITMASK` fields are live triggers
(`tcp flags`, `ct status`, `ct label`); the danger is highest on the two that
are *routinely multi-bit* — `ct status` and `ct label` — where the exact-set
fold matches essentially none of the real traffic, versus `tcp flags` where it
misses specific multi-flag combinations. The most compelling real-world case is
**`ct status` on a NAT gateway** (a rule pattern real routers use, fold breaks
*all* matched traffic); `tcp flags` is the cleaner textbook illustration and is
the one for which both the fail-closed and fail-open directions are
data-plane-verified here.

Reproducers for both live cases:
[`proof/battery_cases/nft_optimize_bug1_scope/`](proof/battery_cases/nft_optimize_bug1_scope/)
(run each under `unshare --net --map-root-user --map-auto -- bash <script>`).

---

## Bug 2 — overlapping-key merge is emitted without a representability check: valid ruleset becomes unloadable

**Severity: medium — fails loud (exit 1), but in apply mode the atomic
transaction aborts and 0 rules are committed; a boot script that runs
`nft -o -f /etc/nftables.conf` without checking the exit code brings the host
up with no firewall at all.**

### Explanation

`nft -o` groups consecutive rules that match on the same field (same verdict →
set, differing verdicts → verdict map) and emits the merged interval set
**without checking that the overlapping keys are representable**. nftables'
interval machinery is strict about overlaps:

- **single-field interval sets** are a partition: nft's own userspace validator
  (`src/intervals.c`) rejects *any* overlap with `conflicting intervals`
  before netlink is even sent (and the kernel `rbtree` backend would too);
- **concatenated (multi-field) sets** slip past userspace and are adjudicated
  by the kernel `pipapo` backend, which rejects any element whose endpoint
  falls inside an existing element (`File exists`).

So on overlapping input rules — a perfectly valid, meaningful first-match
sequence — the optimizer proposes a merge that nftables itself then refuses.
The rejection is correct; *emitting the unrepresentable merge* is the bug. A
correct optimizer would either emit the equivalent **disjoint** form or decline
the merge. `nft -o` does neither.

### Minimal example (single-field, rejected in userspace)

```nft
table ip filter {
  chain input {
    type filter hook input priority 0; policy accept;
    ip saddr 10.0.0.0/24 drop
    ip saddr 10.0.0.0/16 accept
  }
}
```

```console
$ nft -f repro.nft            # sanity: the ORIGINAL loads fine
$ nft -o -f repro.nft
Merging:
    ip saddr 10.0.0.0/24 drop
    ip saddr 10.0.0.0/16 accept
into:
	ip saddr vmap { 10.0.0.0/24 : drop, 10.0.0.0/16 : accept }
internal:0:0-0: Error: conflicting intervals specified
$ echo $?
1
$ nft list ruleset            # apply mode: atomic abort — NOTHING was committed
$
```

The verdict-identical disjoint form exists and loads fine — nft just never
computes it:

```nft
ip saddr vmap { 10.0.0.0/24 : drop, 10.0.1.0-10.0.255.255 : accept }
```

### Variants (all reproduced on v1.1.6)

- **Overlapping ranges, differing verdicts** (battery 13; also `bad.nft` at the
  repo root):
  `ip saddr 10.0.0.0-10.0.0.10 drop` + `ip saddr 10.0.0.5-10.0.0.20 accept`
  → `conflicting intervals`, exit 1.
- **NAT map** (battery 07): `ip daddr 10.0.0.0/24 dnat to 192.168.1.1` +
  `ip daddr 10.0.0.5 dnat to 192.168.1.2` → merged into a
  `dnat ip to ip daddr map { … }` with overlapping keys →
  `conflicting intervals`, exit 1. Same defect through the map (not vmap) path.
- **Concat, kernel-level rejection** (battery 04):
  `ip saddr 10.0.0.0/24 tcp dport 22 drop` + `ip saddr 10.0.0.1 tcp dport 22 accept`
  → merged into `ip saddr . tcp dport vmap { 10.0.0.0/24 . 22 : drop,
  10.0.0.1 . 22 : accept }`. This passes nft's userspace (which only validates
  single-field overlaps) and is rejected by the **kernel** pipapo backend:
  `Error: Could not process rule: File exists`, exit 1, transaction aborted.
  Here the second original rule shadowed by the first is *dead* under
  first-match — the honest optimization would be to note the dead rule, not to
  emit an insertable-by-neither-backend merge.

### Impact

The failure is loud (stderr + exit 1), so it is not silently wrong. The
operational hazard is `nft -o -f` in unattended contexts: the transaction is
atomic, so the kernel keeps whatever ruleset was loaded *before* — at boot,
that is the empty ruleset, i.e. **fail-open**. Any valid config containing an
overlapping first-match pair (a completely idiomatic "specific rule, then
general rule" pattern) triggers it.

---

## Bug 3 — optimizer aborts (SIGABRT) on `field & $mask == value`: a single rule crashes `nft -o`

**Severity: high as a robustness defect — `nft -o` calls `abort()` (exit 134,
core dumped) on a valid, single-rule ruleset that plain `nft -f` loads without
complaint. Not a mis-merge; an outright crash of the optimizer.**

Unlike Bugs 1 and 2, this one was **not** surfaced by the formal
differential — the verified optimizer never gets a say, because `nft -o`
crashes before producing any output to compare against. It fell out of running
`nft -o` over a corpus of **real-world** GitHub `.nft` configs as a
crash-oracle: one config
([`ms-jpq/lab`](https://github.com/ms-jpq/lab/blob/HEAD/layers/_/usr/local/opt/nftables/conf.d/1-base.nft))
aborts the optimizer outright. It is recorded here for completeness alongside
the two mis-merge bugs; the empirical route makes it *more* obviously realistic
than either, not less (see "Why this one is realistic").

### Minimal example (one rule, no merge involved)

```nft
define M = 0x1
table inet t {
  chain c {
    mark & $M == 0x1 accept
  }
}
```

```console
$ nft -c -f repro.nft         # sanity: plain check loads it fine
$ nft -c -o -f repro.nft
nft: src/optimize.c:529: rule_build_stmt_matrix_stmts: Assertion `k >= 0' failed.
Aborted (core dumped)
$ echo $?
134
```

Replacing the `define`d mask with the literal it expands to —
`mark & 0x1 == 0x1 accept` — makes the crash vanish. Plain `nft -f` (no `-o`)
loads either form cleanly, so this is an **optimizer-only** abort.

### Trigger — precisely characterised

The crash fires iff a rule contains a **masked-equality match**
`<field> & MASK == <value>` where **`MASK` is a `define`d variable** (not a
literal), **and** that rule contains no statement the optimizer's collector
already treats as *unsupported*. Both conditions are needed:

| ruleset | `nft -o` |
|---|---|
| `mark & $M == 0x1 accept` (mask = define) | **CRASH** |
| `mark & 0x1 == 0x1 accept` (mask = literal) | ok |
| `mark & 0x1 == $M accept` (only the RHS is a define) | ok |
| `mark & $M == $M` (no verdict at all) | **CRASH** |
| `mark & $M == $M ip dscp set cs1` (a mangle stmt is present) | ok |

It is field-agnostic: `mark`, `ct mark`, `ip dscp`, etc. all trigger it. A
single rule is enough — no second rule and no merge are required. Repro and the
full probe matrix:
[`proof/battery_cases/nft_optimize_bug3_crash/`](proof/battery_cases/nft_optimize_bug3_crash/)
(`MINIMAL_crash.nft` + `crash.sh`; run under
`unshare --net --map-root-user --map-auto -- bash crash.sh`).

### Root cause (`src/optimize.c`)

The optimizer builds its statement matrix in two passes with **inconsistent
notions of which statements are representable**:

1. **Collect (`rule_collect_stmts` → `stmt_type_find`).** For a
   `STMT_EXPRESSION`, the rule is admitted as a *supported* selector column
   based only on its operator (`OP_EQ`/`OP_IMPLICIT`) and that its left operand
   is not a concatenation. It is **not** checked that the expression can later
   be *matched* by `__expr_cmp`. So `field & $mask == v` is recorded as
   supported, and **no `STMT_INVALID` sentinel column is created**.

2. **Populate (`rule_build_stmt_matrix_stmts` → `cmd_stmt_find_in_stmt_matrix`
   → `__stmt_type_eq(.,.,false)` → `__expr_cmp`).** Locating each statement's
   column re-compares the left operand `field & MASK`, an `EXPR_BINOP`, by
   recursing into the mask operand. When the mask is a variable, `__expr_cmp`
   has no case for it and returns `false` via its `default:` branch — so the
   statement fails to match *even its own clone*. `cmd_stmt_find_in_stmt_matrix`
   returns `-1`; the fallback `unsupported_in_stmt_matrix` looks for the
   `STMT_INVALID` sentinel that pass 1 never inserted, also returns `-1`, and
   `assert(k >= 0)` at line 529 aborts.

This is exactly why a mangle statement in the same rule *suppresses* the crash:
`ip dscp set cs1` lands in the collector's `default:` arm, is marked
`STMT_INVALID`, and so a sentinel column exists for the fallback to find. The
assertion is the load-bearing check; it just fails on ordinary input instead of
catching a "can't happen".

A correct optimizer would either give the masked-equality-with-variable form a
real `__expr_cmp` case (so it matches and is optimised like the literal form) or
classify it `STMT_INVALID` up front in pass 1 (so it is skipped, as any other
unsupported statement is). It does neither.

### Why this one is realistic

The trigger is the **"mark a packet, then match the mark"** idiom with a named
mask — `define MARK_ACCEPT = 0x…` then `mark & $MARK_ACCEPT == $MARK_ACCEPT
accept` — which is textbook nftables and exactly what the real `ms-jpq/lab`
config does:

```nft
define MARK_ACCEPT = 0xb00b0000
# …
chain noinput {
  type filter hook input priority filter + 1
  policy drop
  mark & $MARK_ACCEPT == $MARK_ACCEPT accept
  counter reject with icmpx type admin-prohibited
}
```

Naming a bitmask with `define` and matching it back with `&…==…` is standard
practice, so an operator running `nft -o` over a perfectly good config gets a
core dump rather than an optimised ruleset. It fails loudly (like Bug 2), so it
is not silently wrong — but a crash-on-valid-input in a tool people run over
their live firewall config is a real defect.

### Upstream status

Reproduces on the installed **v1.1.6** and the identical code path — the
`assert(k >= 0)` at `optimize.c:529` and the pass-1 classification that omits
the self-comparability check — is present verbatim in **git HEAD**
(`8d97995`, 2026-07-10). The two-pass matrix builder is original optimizer
infrastructure, so this very likely dates back to the same 2022 series that
introduced Bugs 1 and 2; that was **not** bisected to a first-bad commit here
(unlike Bugs 1/2), so the exact introduction point is stated as probable, not
confirmed. No prior public report was searched for.

---

## Near-miss that is NOT a bug (recorded to prevent misreporting)

**Strictly-interior concat overlaps are folded *correctly*** (battery cases
14/15). For

```nft
ip saddr 10.0.0.1 tcp dport 22 drop
ip saddr 10.0.0.1 tcp dport 1-100 accept
```

`nft -o` emits `ip saddr . tcp dport vmap { 10.0.0.1 . 22 : drop,
10.0.0.1 . 1-100 : accept }`, which the kernel **accepts** (point 22 is strictly
inside 1–100, no shared endpoint) and resolves by **lowest rule index** —
insertion order = original rule order (`pipapo_refill`/`__builtin_ctzl`).
Data-plane probes (`proof/battery_cases/probe_overlap_vmap.sh`) confirm
`22 → drop, 50 → accept`, identical to the original first-match sequence; and
the verdict-changing order (wider first) is exactly the one pipapo rejects. So
this fold is verdict-preserving by construction, not by luck. Our verified
optimizer currently declines it only because our formal semantics models set
lookup as unordered/disjoint-key — a modeling gap on our side, not an nftables
defect.

---

## Upstream status (checked 2026-07-13)

Both bugs were confirmed present across the entire lifetime of `-o/--optimize`
by building upstream from source and re-running the repros:

- **v1.0.2** (2022-02-21, the release that introduced `-o`): both shapes
  already mis-merge identically (`tcp flags { syn, ack }` fold; `conflicting
  intervals`).
- **git HEAD** (`8d97995b`, v1.1.6-130, 2026-02-05): both still reproduce,
  bit-for-bit the same output. No commit in `v1.1.6..HEAD` touches the merge
  logic.

**No prior public report of either bug was found.** Channels searched:

- **netfilter bugzilla** — the tracker itself (bugzilla.netfilter.org) is
  behind an Anubis proof-of-work bot wall, so it was searched indirectly via
  search-engine indexes and the
  [netfilter-buglog list mirror](https://lists.netfilter.org/pipermail/netfilter-buglog/).
  No optimizer bug matches. The existing "conflicting intervals" /
  overlapping-interval bugs
  ([Bug 1361](https://lists.netfilter.org/pipermail/netfilter-buglog/2020-April/004792.html),
  [Bug 1438](https://lists.netfilter.org/pipermail/netfilter-buglog/2020-July/004839.html))
  are from 2020 — they predate `-o` entirely and concern hand-written
  sets/auto-merge, not optimizer output.
- **netfilter-devel / netfilter mailing lists** — lore.kernel.org is also
  bot-walled (even for plain curl); searched via the
  [mail-archive.com](https://www.mail-archive.com/netfilter-announce@lists.netfilter.org/)
  and [spinics.net](https://www.spinics.net/lists/netfilter/) mirrors. The one
  suggestive hit, a 2021 thread
  ["Regarding `tcp flags` (and a potential bug)"](https://www.spinics.net/lists/netfilter/msg60313.html),
  is about parser/display normalization of flag expressions — not the
  optimizer.
- **Debian BTS** for the nftables package — no optimizer-related bugs at all.
- **LWN release coverage** of every 1.0.x/1.1.x release (e.g.
  [1.1.2](https://lwn.net/Articles/1017461/), which announced the *sound*
  same-mask bitmask fold) — release notes list `-o` fixes, none matching
  either defect.
- General web/forum searches (Stack Exchange, Reddit, GitHub issues).

**Caveats on "not found":** the two primary upstream channels (bugzilla and
lore.kernel.org) could not be searched exhaustively — only through what search
engines have indexed of them and through unwalled mirrors — so a report that
was never indexed or that used very different wording could have been missed.
"Unreported" is therefore a strong conclusion but not airtight. Additionally,
all mailing-list searches were keyword-based (tcp flags / ct state / bitmask /
conflicting intervals / optimize); a report describing the same root cause in
unrelated vocabulary would not have surfaced.

Closest upstream activity — none of it covers these defects:

- `447ac8a3` ("optimize: compact bitmask matching in set/map", 2025-03-26,
  released in 1.1.2) folds same-mask `tcp flags & M == V` rules into
  `tcp flags & M == { … }` — that fold is *sound* (the mask is kept). Bug 1
  lives in the older generic value-merge path, which treats the boolean form
  `tcp flags syn` (`& syn != 0`) as an exact match and drops the semantics.
- `ba6985a1` ("optimize: invalidate merge in case of duplicated key in
  set/map", 2025-04-09, in 1.1.6) fixes the *exactly-duplicated* key subcase of
  Bug 2's class (`ip protocol icmp jump A` / `… goto B` → EEXIST). Upstream met
  a sibling symptom and fixed only key equality; overlapping intervals were
  left unhandled — our Bug 2 reproduces on the very version carrying this fix.
- Upstream's own test suite hints at awareness of the Bug 1 distinction:
  `tests/shell/testcases/optimizations/single_anon_set` notes a set conversion
  is valid "because ct state cannot be both established and related at the same
  time" — the mutual-exclusivity justification that holds for `ct state` and
  fails for `tcp flags`. No upstream test exercises the boolean `tcp flags`
  fold.
- The `nft(8)` manpage itself documents that `tcp flags syn,ack` (any-of
  bit-test) and `tcp flags { syn, ack }` (exact match) are *different* matches
  — so Bug 1's rewrite is contrary to nft's own documented semantics, not a
  defensible reinterpretation.

Both bugs therefore appear to be **unreported as of 2026-07-13** and worth
sending to netfilter-devel@vger.kernel.org (reports must be plain text;
bugzilla.netfilter.org is the alternative channel).

### When each bug was introduced (`git bisect`)

Bisected on the upstream `nftables` tree with `git bisect run`, one session per
bug, over the range `v1.0.1` (good) `..` `v1.0.2` (bad) — the 94-commit window
in which `-o` first appeared. Each step did a full `autogen && configure &&
make` against a locally built libnftnl and ran the minimal case through
`nft -c --optimize` in a fresh netns; the test script classified a revision as
*bad* iff the optimizer **proposed** the faulty merge (independent of whether
the kernel then rejected it), so the result pinpoints the rewrite logic, not
the downstream validator. Both bisects converged with no skips.

**Neither bug was ever a regression — each was present in the commit that
introduced its code path.** `-o` shipped broken.

- **Bug 1 (bitmask exact-set fold) — first bad commit
  [`fb298877`](https://git.netfilter.org/nftables/commit/?id=fb298877ece2739ffb08b1967c10829969859e2c)**,
  "src: add ruleset optimization infrastructure" (Pablo Neira Ayuso,
  2022-01-02). This is the very first optimizer commit — it adds `src/optimize.c`
  and the same-verdict value→set merge. The value-merge path treated the boolean
  `tcp flags syn` match as an exact value from day one, so folding it into a set
  dropped the bitmask in the first release that had an optimizer at all. (The
  later same-mask bitmask work in
  [`447ac8a3`](https://git.netfilter.org/nftables/commit/?id=447ac8a3), 1.1.2,
  added a *separate*, sound fold for the `& M == V` form and did not touch this
  path.)

- **Bug 2 (overlapping-key merge → unloadable) — first bad commit
  [`1542082e`](https://git.netfilter.org/nftables/commit/?id=1542082e259b4a9270e0726904796730a5c310d6)**,
  "optimize: merge same selector with different verdict into verdict map" (Pablo
  Neira Ayuso, 2022-01-02). This is the commit that first builds a verdict map
  from consecutive same-selector rules — i.e. the first code that can emit
  `<selector> vmap { … }` / `map { … }` from differing-verdict rules. It shipped
  with no representability check on the resulting interval keys, so the
  overlapping-prefix case produced an unloadable merge immediately. (Its
  predecessor `8b4c95da`, "merge rules with same selectors into a
  concatenation", tested *good*: it only builds concatenations, never a
  differing-verdict interval map, so it cannot emit this shape.)

Both first-bad commits landed on the same day (2022-01-02) in the initial
optimizer patch series and first reached users in **v1.0.2**. So the bugs are
~4 years old and have been in every `-o`-capable release. The bisect harness,
full session logs, and per-revision optimizer output are archived under
[`proof/battery_cases/nft_optimize_bisect/`](proof/battery_cases/nft_optimize_bisect/)
(`bisect_test.sh` is the `git bisect run` script; `bisect_bug1.log` /
`bisect_bug2.log` record every revision's optimizer output).

## Reproducing

Everything runs unprivileged:

```console
$ unshare --net --map-root-user --map-auto -- bash
# nft -f case.nft            # sanity-load the original
# nft flush ruleset
# nft -o -f case.nft         # watch the merge + the failure / silent narrowing
```

- Minimal cases: `proof/battery_cases/*.nft`
  (`MINIMAL_nft_optimize_failclosed_bug.nft` is the canonical Bug 2 repro;
  `20_ctstate_mask_union.nft` is the Bug 1 `ct state` shape).
- Full differential battery: `cd proof && bash difftest_battery.sh`.
- Ordered-pipapo data-plane probe: `proof/battery_cases/probe_overlap_vmap.sh`.
- Bug 3 crash + probe matrix:
  `proof/battery_cases/nft_optimize_bug3_crash/` (`bash crash.sh`).

## How these were found

**Bugs 1 and 2 — from the formal differential.** The verified optimizer
(`proof/theories/Optimize_*.v`, composed in `Optimize_Uncond.v`) must *prove*
every fold verdict-preserving against the project's mechanized nftables
semantics. Every shape where `nft -o` merged and our optimizer refused was
investigated as a potential gap on our side; Bugs 1 and 2 are the residue where
the refusal was correct — the proof obligation that could not be discharged
corresponds exactly to the packet (Bug 1) or the representability condition
(Bug 2) that `nft -o` gets wrong.

**Bug 3 — from a real-world crash-oracle, not the proof.** The formal
differential could not see Bug 3, because `nft -o` aborts before emitting any
output to compare. It was found instead by running `nft -o` over the project's
corpus of real GitHub `.nft` configs
([`proof/parser_corpus/github/`](proof/parser_corpus/github/)) and watching for
non-zero exits: one config crashed the optimizer, and delta-debugging reduced it
to the single-rule `field & $mask == value` case. It is included here because it
is a genuine, easily-triggered `nft -o` defect on valid input, even though it
came from differential fuzzing of the real tool rather than from a discharged
(or undischarged) proof obligation.
