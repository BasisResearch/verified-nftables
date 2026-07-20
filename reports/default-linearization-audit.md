# Default-linearization audit: the source-sweep residual, block by block

Date: 2026-07-20.  Context: the T3-residue commit wires nft's two ALWAYS-ON
single-rule rewrites — the adjacent-payload merge (class I,
`Optimize_PayMerge`) and the bitwise-xor constant fold (class L,
`Optimize_XorFold`) — into the DEFAULT compile pipeline
(`Optimize_Linearize.compile_chain_default`, axiom-gated
`compile_chain_default_correct`), so plain `nftc compile` now matches plain
`nft`'s default netlink linearization.  The source-sweep and byteorder gates
compile through the shipped default pipeline (no harness-side ad-hoc passes).

This report is the audit the task mandates AFTER that wiring: every remaining
compile-from-source mismatch in the sweep, classified.  (The corpus-divergence
class ledger A–O lives in the owner's working notes; classes named here extend
that lettering: P, Q, R, S, plus the class-L residual.)

## Headline numbers

| measure | before | after |
|---|---|---|
| source-sweep pass (of 1742 headered blocks) | 1196 | **1198** |
| source-sweep mismatches | 51 | **49** |
| pinned floor (`source-sweep-gate.sh`) | 1196 | **1198** |

- Switching the sweep from harness-side `paymerge_chain` to the shipped
  `compile_chain_default` (which adds the always-on `xorfold_chain`) moved NO
  block in either direction: the class-I blocks were already closed by the
  T2B pass application, and the class-L blocks stay open for reasons
  independent of the fold (below).
- The +2 comes from one implemented audit finding: the fib concat-selector
  spelling fix (class S0 below).

## Classes I and L: status after default wiring

**Class I (adjacent-payload merge) — CLOSED, default-on.**  The 5 class-I
blocks (`inet/payloadmerge.t.payload:1`, `inet/tcp.t.payload:166/173/182`,
`bridge/vlan.t.payload:279`) are byte-identical through the DEFAULT pipeline;
plain `nftc compile` now emits nft's merged single load
(`default_pipeline_merges_payload_loads`, Compute-pinned).

**Class L (xor constant fold) — the REWRITE is closed, default-on; the four
blocks stay text-open on two stacked residuals.**  `nftc compile` now performs
nft's `binop_transfer` by default (`default_pipeline_folds_xor`,
Compute-pinned: the emitted bitwise xor operand is 0 and the compare value is
`V ^ C`).  The blocks (`any/meta.t.payload:174/179`,
`any/ct.t.payload:151/156`) still mismatch because:
1. nft additionally DELETES the now-trivial `(reg & 0xffffffff) ^ 0x0` binop.
   Unsound to replicate: the packet model's registers are unbounded byte
   strings (`pkt_meta`/`e_ct` read raw data), so the all-ones mask is not
   provably the identity; dropping it needs a byte-well-formedness hypothesis
   the UNCONDITIONAL pass theorems forbid (pinned in `Optimize_XorFold.v`'s
   scope note).
2. The folded compare value is a host-endian `mark` immediate — the ledgered
   endian-unportable display class (b) below.

## Classification of the 49 remaining mismatches

### (b) Host-endian display residual — 27 blocks (ledgered, T2A)

Corpus `.t.payload` goldens print host-endian (BYTEORDER_HOST_ENDIAN)
immediates in the recording host's byte order; the rendered text is
endian-unportable and was adjudicated as such in T2A (DEVELOPMENT.md, "The 83
source-divergences").  No wire divergence is claimed by these blocks.

| blocks | source form |
|---|---|
| `any/meta.t.payload:1,6,11` | `meta length` cmp immediates |
| `any/meta.t.payload:134,140` | `meta mark and` mask+value |
| `any/meta.t.payload:162,168` | `meta mark or` mask+xor+value |
| `any/meta.t.payload:514,519` | `meta skuid` / `meta skgid` |
| `any/meta.t.payload:568,573` | `meta cpu` |
| `any/meta.t.payload:671,676` | `meta cgroup` |
| `any/ct.t.payload:127,133,139,145` | `ct mark or/and` mask+xor+value |
| `any/ct.t.payload:223` | `ct mark set` immediate |
| `any/ct.t.payload:250` | `ct expiration` |
| `any/ct.t.payload:413` | `ct event set` immediate |
| `any/ct.t.payload:429` | `ct label set` (128-bit label bit position) |
| `any/ct.t.payload:439,444,449,454` | `ct zone` (2-byte host-endian) |
| `any/ct.t.payload:512` | `ct id` (class O: WE are kernel-faithful) |
| `ip/ip_tcp.t.payload:8` | `meta mark set` immediate |

### Class-L residual — 4 blocks (see above)

`any/meta.t.payload:174,179`, `any/ct.t.payload:151,156` — identity-binop
elision (model-unsound to replicate) stacked on host-endian display.

### (a) Further baked-in default rewrites nft performs — 12 blocks, 4 new classes

None is implementable as a small UNCONDITIONAL verdict-preserving
`chain -> chain` pass; each needs a fact our per-chain, over-approximating
model deliberately does not carry.  Catalogued with the blocking reason:

**Class P — family-implied `meta protocol` elision (2).**
`ip/meta.t.payload:48`, `ip6/meta.t.payload:57` (`meta protocol ip udp dport
67` on an ip-family table): nft's evaluate DROPS a `meta protocol` match that
is implied by the table family; we emit the load+cmp.  Not a sound
chain-level pass: dropping the match changes verdicts on packets outside the
family, and `Syntax.chain` carries no family — the fact lives in the hook
dispatch, not the chain.  Closing it would need a family-indexed chain
semantics (or a frontend-side elision, which would be an UNPROVED semantic
delete — worse).

**Class Q — dependency-guard hoisting for `reject with tcp reset` (3).**
`ip6/reject.t.payload.ip6:33`, `ip/reject.t.payload:37`,
`inet/reject.t.payload.inet:67` (`mark ... reject with tcp reset`): nft emits
the synthesised `meta l4proto tcp` guard FIRST in the rule; our lowering
emits it adjacent to the reject.  Same instruction multiset, packet-equal
conjunction; a pure placement decision in the verified reject lowering.
Tractable in principle, but reordering body items is only verdict-preserving
for stateless bodies (a limiter/quota/counter between the two positions
breaks commutation), so the fix belongs in the LOWERING's emission order (per
rule shape), not an optimizer pass — future work, not small enough here.

**Class R — reject family concretization (5).**
`inet/reject.t.payload.inet:79,85,135`, `bridge/reject.t.payload:81,87`:
when the rule pins the L3 family (`meta nfproto ipv4`, `ether type ip`), nft
rewrites the family-agnostic `reject` (ICMPX, our `reject type 2 code 1`)
into the family-specific ICMP form (`reject type 0 code 3`).  NOT closable as
an eval-preserving pass at all: the two encodings are DIFFERENT `Reject`
verdict values in the DSL (`Reject typ code`), equal only on the wire — the
model would have to quotient reject encodings (or the frontend concretize at
lowering time under the pinned-family context).  Representation gap,
catalogued.

**Class S — link-layer dependency choice on inet (1, stacked on R).**
`inet/reject.t.payload.inet:135` (`ether saddr ... ip daddr ... reject`): for
an ether match on an inet chain nft synthesises a PAYLOAD ethertype guard,
which then payload-merges with `ether saddr` into ONE 8-byte link-layer load;
our frontend synthesises a `meta nfproto` guard, which sits between the
payload equalities and (correctly) blocks the merge.  The divergence is the
GUARD CHOICE in the frontend dependency synthesis (the bridge/netdev
in-frame-ethertype guard landed in class G; inet kept nfproto), not the merge
pass.  Fix = lowering-side guard selection for inet+ether; touches the
class-G guard machinery.

**Class P′ — transport-dependency dedup (2).**
`inet/icmpX.t.payload:19`, `bridge/icmpX.t.payload:19` (`ip6 nexthdr icmpv6
icmpv6 type echo-request`): nft's dependency tracker knows `ip6 nexthdr
icmpv6` already pins the transport protocol and emits NO second guard for the
`icmpv6 type` match; we synthesise `meta l4proto 0x3a`.  Eliding our guard is
unsound in the model: `pkt_meta l4proto` and the network-header nexthdr byte
are independent oracles (over-approximation); their agreement is a
packet-well-formedness fact the unconditional theorems cannot assume.

### (c) Render/attribute-materialization — 6 blocks (untrusted-glue text, no wire claim)

**Log option canonicalization (4).**  `any/log.t.payload:45,49,53,57`:
`ILog` carries the source option string near-verbatim (`canon_log_opts` only
numbers `level <name>`); nft's netlink debug prints canonical order and
materialized defaults (`log prefix X group N snaplen 0 qthreshold 0`,
spelling `qthreshold`, `flags all` expanded to `tcpseq tcpopt ipopt uid
macdecode`).  Closable by canonicalizing the (behaviorally inert) option
string in the verified frontend lowering; needs per-form care to avoid
regressing currently-passing bare `log`/`log prefix` blocks — catalogued, not
done here.

**Fib presence-check shape (2).**  `inet/fib.t.payload:24,29` (`fib daddr oif
exists` / `check missing`): nft carries the result column in the key (`fib
daddr oif present`) and compares `cmp eq 0x01`; our `lower_presence` drops
the column (`fib daddr present`) and emits `cmp neq 0x00` for `exists`.
Closing needs the fib presence register pinned boolean in the model (to
justify `eq 1` ≡ `neq 0`) plus the result-column selector — touches
`Fib_Local`'s oracle-key discipline; catalogued.

### Implemented audit finding (closed in this change)

**Class S0 — fib concat-selector spelling (2 closed).**
`inet/fib.t.payload:6,11` (`fib saddr . iif oifname "lo"`, `fib daddr . iif
type local`): the ONLY divergence was the selector text — parser.mly joined
concat fib keys with `"."` (`saddr.iif`) while nft's netlink debug prints
`" . "` (`saddr . iif`).  The spaced spelling was ALREADY the canonical one
everywhere else in the development: `corpus_test` `validate_pairs` confirms
`FFib ("daddr . iif", …)` against live nft, and `Fib_Local.fibkey_wf` keys
`"daddr . iif"`/`"saddr . iif"` — i.e. the parser was producing a selector
string the fib theorems never talk about.  Fixed the join (one token in
`parser.mly`); single-key selectors unaffected; sweep 1196 → 1198, floor
raised accordingly.

## Coverage check

27 (host-endian display) + 4 (class-L residual) + 2 (P) + 3 (Q) + 5 (R,
incl. the S-stacked block) + 2 (P′) + 4 (log) + 2 (fib presence) = **49**. ✓
