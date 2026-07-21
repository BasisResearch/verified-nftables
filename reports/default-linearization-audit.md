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

| measure | before | after | after W3 elision | after W4 audit |
|---|---|---|---|---|
| source-sweep pass (of 1742 headered blocks) | 1196 | **1198** | **1202** | **1209** |
| source-sweep mismatches | 51 | **49** | **45** | **38** |
| pinned floor (`source-sweep-gate.sh`) | 1196 | **1198** | **1202** | **1209** |
| byteorder-gate plain-cmp blocks | 21/21 | 21/21 | **25/25** | 25/25 |

W4 (the post-faithful-widths re-audit) closed class Q (3 blocks, reject-guard
emission order) and class R (4 blocks, bare-reject family concretization; the
5th, S-stacked block keeps its concretized reject but stays open on the
class-S guard choice), and re-adjudicated every remaining class against the
W1–W3 by-construction width discipline — the per-class verdicts below each
carry their post-W1 blocking reason.

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

**Class L (xor constant fold) — WIRE-CLOSED, default-on (W3 adjudication);
the four blocks stay text-open on the display residual alone.**  `nftc
compile` performs nft's `binop_transfer` by default
(`default_pipeline_folds_xor`, Compute-pinned) AND, since the W3
identity-elision stage (`Optimize_Elide.elide_chain`, in
`linearize_chain` after the fold), also nft's deletion of the spent
`(reg & 0xffffffff) ^ 0x0` binop (`binop_transfer_handle_lhs`, OP_XOR):
the default compile of a pure-xor match is a bare load + cmp with NO
bitwise instruction (`default_pipeline_elides_trivial_binop`,
Compute-pinned; live check: `nft --debug=netlink add rule ip t c meta mark
xor 0x3 == 0x1 counter` emits `meta load mark => reg 1; cmp eq reg 1
0x00000002` and `nftc compile` emits the same two instructions with value
bytes `02 00 00 00`).  The former blocking reason — "the all-ones mask is
not provably the identity over unbounded bytes" — is DISCHARGED: register
reads are octet-clamped by construction (`Bytes.octets` composed with
`Bytes.fit` at the `do_load` boundary), making the elision unconditional
(`elide_chain_eval`, axiom-gated; no byte-well-formedness hypothesis).

Per-block adjudication of the four blocks (`any/meta.t.payload:174/179`,
`any/ct.t.payload:151/156`): CLOSED, byte-identical from source.  The
endian-unportable part of these blocks was the DELETED bitwise's mask/xor
immediates; what remains is a plain host-order cmp on `mark`/`ct mark`,
which the renderer prints in the goldens' recorded byte order (the
kernel-adjudicated host-order plain-cmp class).  Consequently the four
blocks also ENTER `byteorder-gate`'s plain-cmp scope and pass it
(21 -> 25 blocks, 0 failed).  Sweep floor raised 1198 -> 1202.

## Classification of the remaining mismatches (38 since W4)

### (b) Host-endian display residual — 27 blocks (ledgered, T2A)

Corpus `.t.payload` goldens print host-endian (BYTEORDER_HOST_ENDIAN)
immediates in the recording host's byte order; the rendered text is
endian-unportable and was adjudicated as such in T2A (DEVELOPMENT.md, "The 83
source-divergences").  No wire divergence is claimed by these blocks.

W4 re-adjudication: NOT width-blocked (and never was).  W1 pinned every one
of these registers' widths by construction (mark/skuid/skgid/cpu/cgroup/
expiration/zone/…), which changed nothing here: the mismatch is the GOLDEN
TEXT's recorded byte order, not a model fact — the same compiled bytes render
differently on a different-endian recording host.  Still-true blocker: the
corpus text is endian-unportable for BYTEORDER_HOST_ENDIAN immediates; only a
wire-level (netlink readback) gate could judge these, and `byteorder-gate`
already covers the kernel-adjudicated plain-cmp subset (25/25).

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

### Class-L residual — CLOSED (0 blocks since W3)

`any/meta.t.payload:174,179`, `any/ct.t.payload:151,156` are byte-identical
from source since the W3 default `Optimize_Elide` stage (wire form verified
against live nft; see the class-L adjudication above).  The class is kept in
the ledger for traceability; it contributes 0 to the mismatch count.

### (a) Further baked-in default rewrites nft performs — 5 blocks open, 2 classes closed in W4

W4 re-derived every blocking reason with the W1–W3 width discipline landed.
Two classes were never width-blocked but WERE small, unambiguous
emission-fidelity fixes in the verified lowering — implemented and closed.
The three survivors are catalogued with their post-W1 blocker, none of which
is a width fact:

**Class Q — reject dependency-guard placement (3) — CLOSED (W4).**
`ip6/reject.t.payload.ip6:33`, `ip/reject.t.payload:37`,
`inet/reject.t.payload.inet:67` (`mark ... reject with tcp reset`) are
byte-identical from source: the reject lowering now emits the synthesised
`meta l4proto tcp` guard at the RULE HEAD (`Lower.ensure_dep_head` /
`rl_push_head`), mirroring nft's evaluation-time list_add
(src/evaluate.c stmt_reject_gen_dependency: "Unlike payload deps this adds
the dependency at the beginning […] Otherwise we'd log things that won't be
rejected").  CORRECTION of this ledger's previous claim: the two placements
were NOT "packet-equal conjunction / pure placement".  That holds only for
stateless bodies — with a counter/log/mark-write between the two positions,
guard-last runs the effect on packets the guard then breaks on, guard-first
does not (the kernel evaluates in instruction order); the emission order is
observable state, which is exactly nft's stated reason for the head
placement.  The fix is in the LOWERING's emission order, not a reordering
pass; `Regression/Reject_GuardFirst.v` pins guard-before-effects on both
evaluators (DSL `dsl_rule_step` and compiled VM `vm_rule_step`: a non-TCP
packet leaves the body's mark write unexecuted and gets no verdict; a TCP
packet takes the write and the Reject) plus the counterfactual (the pre-fix
guard-last body leaks the write on the same non-TCP packet).

**Class R — bare-reject family concretization (4 of 5) — CLOSED (W4).**
`inet/reject.t.payload.inet:79,85`, `bridge/reject.t.payload:81,87` are
byte-identical from source: `Lower.reject_type_code` now takes the rule's
pinned network family (`Lower.deps_pinned_nfproto` over the per-rule
guard/dedup set — `meta nfproto`, `meta protocol`, `ether type`, or the
in-frame `payload @ link+12/+16` guard, the `layer_class` spelling set; the
0x8100 vlan tag does not pin) and concretizes a BARE `reject` in a multi-L3
family from icmpx port-unreach (2,1) to icmp (0,3) / icmpv6 (0,4) once a
family is pinned — exactly evaluate.c stmt_evaluate_reject_default (network
desc NULL => ICMPX, else family-specific port-unreach); an explicit `reject
with icmpx ...` never concretizes (the ICMPX break in
stmt_evaluate_reject_inet_family), pinned by
`reject_icmpx_explicit_stays_abstract`.  The previous entry's "NOT closable
as an eval-preserving pass" reasoning was correct but incomplete: it is not
a pass, it is the LOWERING concretizing under the rule's own pinned-family
context (the entry itself named this alternative), and the reject
type/code is filtering-semantics-inert (both are terminal `Reject`
verdicts; only the ICMP flavour on the wire differs).  The 5th block
(`inet:135`) now emits the concretized `reject type 0 code 3` too but stays
open on class S below.

**Class P — family-implied `meta protocol` elision (2) — OPEN, re-ledgered.**
`ip/meta.t.payload:48`, `ip6/meta.t.payload:57` (`meta protocol ip udp dport
67` on an ip-family table): nft's evaluate DROPS a `meta protocol` match that
is implied by the table family; we emit the load+cmp.  W4 re-adjudication:
NOT width-blocked — W1/W3 made the `meta protocol` read a by-construction
2-byte register, but the elision needs a fact no read-width supplies: that
every packet REACHING the chain has that ethertype, which is the hook
dispatch's family, and `Syntax.chain` carries no family.  Dropping the match
changes verdicts on out-of-family packets under the chain-level
all-packets quantification, so it stays out of scope for an unconditional
pass; closing needs a family-indexed chain semantics (or an UNPROVED
frontend delete — worse).  Blocker unchanged and still true post-W1.

**Class S — link-layer dependency choice on inet (1) — OPEN, re-ledgered.**
`inet/reject.t.payload.inet:135` (`ether saddr ... ip daddr ... reject`): for
an ether match on an inet chain nft synthesises a PAYLOAD ethertype guard,
which then payload-merges with `ether saddr` into ONE 8-byte link-layer load;
our frontend synthesises a `meta nfproto` guard, which sits between the
payload equalities and (correctly) blocks the merge.  W4 re-adjudication:
NOT width-blocked — both candidate guards have by-construction widths (W1);
the divergence is the GUARD CHOICE in the frontend dependency synthesis (the
bridge/netdev in-frame-ethertype guard landed in class G; inet kept
`meta nfproto` for network matches).  The reject half of this block closed
with class R; what remains is lowering-side guard selection for inet+ether
(synthesise the in-frame ethertype guard when the rule's network dependency
is triggered under a link-layer match, so the payload merge can fire) —
touches the class-G guard machinery, an emission-fidelity work item with no
model blocker, deferred as not small (guard-choice interacts with the
once-per-layer dedup and the vlan shift).

**Class P′ — transport-dependency dedup (2) — OPEN, re-ledgered (oracle
independence, NOT width).**
`inet/icmpX.t.payload:19`, `bridge/icmpX.t.payload:19` (`ip6 nexthdr icmpv6
icmpv6 type echo-request`): nft's dependency tracker treats `ip6 nexthdr
icmpv6` as pinning the transport protocol and emits NO `meta l4proto` guard
for the `icmpv6 type` match; we synthesise `meta l4proto 0x3a`.  W4
re-adjudication with W1 landed: both reads now have by-construction widths
(the l4proto register is a 1-byte octet-clamped read, the nexthdr byte a
1-byte payload load) — width was never the missing fact.  The elision needs
the VALUE implication `nexthdr = 58 -> l4proto = 58`, which is true of real
skbs (a nexthdr byte of 58 means the transport header follows immediately,
so pkt->tprot — what nft_meta's NFT_META_L4PROTO stores, resolved past IPv6
extension headers by ipv6_find_hdr — is 58) but couples two oracles the
model keeps separate: `pkt_meta MKl4proto` and byte 6 of `pkt_nh`.  They are
genuinely DIFFERENT kernel reads (`meta l4proto` skips extension headers;
`ip6 nexthdr` is the raw first next-header byte — on a hop-by-hop packet
carrying ICMPv6 they disagree: 58 vs 0), so a blanket definitional equation
would be kernel-UNFAITHFUL; the faithful by-construction coupling is to
DERIVE `MKl4proto` from the header chain (an exthdr-walking tprot in the
packet record, the Fib_Local de-oracle move applied to the transport
protocol), which also has to couple `pkt_eh`'s walker — a packet-record
restructure, not a W4-sized fix.  Until then the guard we emit is redundant
but sound on exactly the packets nft's rule matches, and the blocker is
ORACLE INDEPENDENCE (a value-coupling fact), not width.

### (c) Render/attribute-materialization — 6 blocks (untrusted-glue text, no wire claim)

**Log option canonicalization (4).**  `any/log.t.payload:45,49,53,57`:
`ILog` carries the source option string near-verbatim (`canon_log_opts` only
numbers `level <name>`); nft's netlink debug prints canonical order and
materialized defaults (`log prefix X group N snaplen 0 qthreshold 0`,
spelling `qthreshold`, `flags all` expanded to `tcpseq tcpopt ipopt uid
macdecode`).  W4 re-adjudication: NOT width-blocked (no register is
involved; `ILog` is a verdict-neutral attribute carrier) — the blocker is
unchanged: a string-canonicalization in the frontend lowering with per-form
care to avoid regressing currently-passing bare `log`/`log prefix` blocks.
Catalogued, unchanged by W1–W3.

**Fib presence-check shape (2).**  `inet/fib.t.payload:24,29` (`fib daddr oif
exists` / `check missing`): nft carries the result column in the key (`fib
daddr oif present`) and compares `cmp eq 0x01`; our `lower_presence` drops
the column (`fib daddr present`) and emits `cmp neq 0x00` for `exists`.
W4 re-adjudication: the old phrasing "needs the fib presence register pinned
boolean" sounds width-shaped but is NOT dischargeable by the W1 width
discipline: the presence value comes from `lpm_fib`'s route RESULT column
(`e_routes`' `fib_result -> data` function — an env oracle column
deliberately outside W1's meta/ct/rt/socket read tables), and a `Bytes.fit
1`/octet clamp would pin it to ONE BYTE, not to {0,1} — `cmp eq 0x01` vs
`cmp neq 0x00` differ on any other byte value, a VALUE-RANGE fact, not a
width fact.  The kernel derives presence, never reads it: nft_fib.c
nft_fib_store_result stores `!!index` under NFTA_FIB_F_PRESENT.  The
by-construction close is therefore the Fib_Local de-oracle move applied to
the RESULT side (derive `FRpresent` from the lookup's own oif column
instead of reading a free route column) plus the result-column selector
text — it touches `Fib_Local`'s route-table discipline (17 theorems) and
the fib renderer, so it is re-ledgered with the precise blocker:
ORACLE-TYPED FIB RESULT COLUMN (value derivation), not width.

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

Since W4: 27 (host-endian display) + 0 (class L, closed W3) + 0 (class Q,
closed W4) + 0 (class R, closed W4) + 2 (P) + 1 (S) + 2 (P′) + 4 (log) +
2 (fib presence) = **38**. ✓
(Since W3: the same plus 3 (Q) + 4 (R) = 45; pre-W3 the class-L residual
contributed 4 more, totalling 49.)

## W4 optimizer scope-note re-audit

Every scope note / refusal in `theories/Optimizer/*.v` and DEVELOPMENT.md
that cited unbounded widths or well-formedness was re-read post-W1–W3:

- `Optimize_XorFold.v` (the pinned unsoundness argument this workflow
  attacked) and `IR/Syntax.v`'s register note were already rewritten by W3:
  the spent-binop deletion is the default-on `Optimize_Elide`, sound with no
  side condition because reads are width-normalised AND octet-clamped by
  construction.  Nothing width-conditional remains in either note.
- `Optimize_Concat.v` (guard-field exclusion note): updated in W1 — cites
  the TOTAL `Syntax.meta_width` table as the reason the recognisers must
  exclude implicit-guard meta keys; a statement about nft's hoisting
  behaviour, not a width refusal.  Still true.
- `Optimize_DataMap.v` ("would be UNSOUND for a `meta mark` key whose value
  the map's own write would change"): a WRITE-ALIASING restriction (the
  demo's key must not be the written field), not a width fact.  Unchanged
  by W1.  Still true.
- `Optimize_Vmap.v` / `Optimize_Uncond.v` merge scope notes (body SYN-proxy
  STOP, per-chain verdict-only quantification): control-flow and
  quantification-scope facts, no width content.  Still true.
- `Regression/Known_Infidelities.v` `gate_limit_drained` (the unconditional
  whole-body limiter sweep): an effect-threading infidelity, owned by the
  queued unify-semantics workflow; W1's widths are orthogonal.  Still true —
  and it is why `Reject_GuardFirst.v` pins the class-Q effect ordering with
  a mark WRITE (position-sensitive in the model) rather than a limiter.
- `Semantics/Fib_Local.v` ("Bytes are unbounded [nat] in this model, so we
  carry the catch-all bounds … explicitly"): still true and CORRECT to keep
  — W1/W3 clamp the kernel-fixed-width ORACLE families (meta/ct/rt/socket/
  osf/numgen/symhash); PAYLOAD bytes (which the de-oracled fib key reads,
  `fibkey_wf`) take their width from the load descriptor and are not
  octet-clamped, so `Fib_Local` rightly carries its interval-containment
  facts instead of assuming a numeric ceiling.  Not a refusal — a
  deliberately explicit hypothesis on catch-all coverage, orthogonal to
  widths.

No optimizer scope note remains that refuses a rewrite on unbounded-width or
byte-range grounds; the surviving refusals are quantification scope
(per-chain, verdicts-only), write-aliasing, control-flow, and the two
oracle-coupling items ledgered above (P′ transport derivation, fib result
column).
