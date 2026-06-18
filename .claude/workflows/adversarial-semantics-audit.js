export const meta = {
  name: 'adversarial-semantics-audit',
  description: 'Red agent finds nftables-semantics infidelities (C source / provable-or-not properties); blue agent fixes them, keeping every gate green and axiom-free; loop until red is satisfied.',
  whenToUse: 'Repeat the red/blue adversarial audit of the Rocq nftables semantics. Re-run any time to continue from the (improved) repo state. args: {maxRounds?: number (default 10), focus?: string}.',
  phases: [
    { title: 'Recon', detail: 'map semantics, gates, C source, corpus' },
    { title: 'Audit', detail: 'red: one concrete infidelity per round (verify prior fix first)' },
    { title: 'Fix', detail: 'blue: fix it, keep ALL gates green + axiom-free, commit or revert' },
    { title: 'Synthesis', detail: 'summarise findings, fixes, residual infidelities' },
  ],
}

const REPO = '/home/yiyun/Projects/certified-nft'
const PROOF = REPO + '/proof'
const MAX_ROUNDS = (args && args.maxRounds) || 10
const FOCUS = (args && args.focus) ? `\nFOCUS HINT for this run: ${args.focus}\n` : ''

const BRIEF = `
PROJECT: a Rocq-verified nftables DSL->control-plane-bytecode compiler + a Menhir
.nft parser, at ${REPO} (proofs in ${PROOF}).

TOOLCHAIN: run \`eval $(opam env --switch=vst)\` first (gives coqtop/dune/menhir).

THE SEMANTICS (what "correct" means; this is what may be infidelitous):
- ${PROOF}/theories/Packet.v   : the packet + env (shared state)
- ${PROOF}/theories/Syntax.v   : DSL AST, field_load/do_load (how a field reads the packet)
- ${PROOF}/theories/Semantics.v: eval_chain / run_chain / eval_table / mutation
  (body_writes/dsl_writes) / eval_chain_trace / apply_masq / set_saddr etc.
- ${PROOF}/theories/Compile.v, Correct.v: compiler + correctness theorems
- ${PROOF}/extracted/*.ml{,i} (extracted), nft_lower.ml/parser.mly/lexer.mll (parser),
  nft_emit.ml/nft2coq (emit AST as Coq terms), parse_test.ml (harness)
- example proofs: theories/Optiplex_Antispoof.v, Optiplex_Antispoof_Gaps.v,
  Optiplex_Mark.v, Ruleset_Verified.v ; generated ASTs: Optiplex_Gen.v, Ruleset_Gen.v
- rulesets: ${REPO}/optiplex.nft, ${REPO}/ruleset.nft

GATES (ALL must stay green; from ${PROOF}/):
  make proofs            # all .v check + re-extract (regenerates extracted/*.ml)
  make corpus            # upstream tests/py round-trip: MUST stay 2532/2532, 0 mismatches
  make validate          # field_load offsets vs live nft: MUST stay 28/28
  make parse-test        # parser harness incl. anti-spoof + mark + saddr checks
  axiom-freedom: cd theories && printf 'From Nft Require Import Correct Optimize.\\nPrint Assumptions compile_chain_correct.\\n' | coqtop -R . Nft  # must say "Closed under the global context"
  build one file: cd ${PROOF} && coq_makefile -f _CoqProject -o CoqMakefile && make -f CoqMakefile theories/FOO.vo
  (PITFALL: running menhir/ocamllex standalone in extracted/ leaves parser.ml/lexer.ml that
   collide with dune -> "Multiple rules generated"; rm them. In hand .ml qualify Stdlib.List/String.)

KNOWN APPROXIMATIONS (standing worklist — target the highest-value one and make it
CONCRETE with evidence, or find a NEW one; do not re-report something already fixed):
  1. conntrack (ct state/mark/...) is a PER-PACKET ORACLE (Syntax.v do_load: LCt k => pkt_ct p k),
     not a flow-keyed table accumulating across packets. (biggest gap)
  2. dnat/snat/redirect/tproxy lower to bare terminal Accept: NO address rewrite
     (only masquerade SOURCE ADDRESS is modelled; masquerade source PORT is not).
  3. iif/oif lowered to compare ASCII of the interface NAME, but iif/oif are interface
     INDICES (numbers) nft resolves at load time -> compares the wrong thing.
  4. concatenated-set membership concatenates RAW field bytes; the kernel pads each
     element to its 4-byte (ifname to 16-byte) register slot -> wrong for sub-slot fields;
     this affects the anti-spoofing proof (ip daddr . oifname @vmantispoof).
  5. fib: key extraction (pkt_fibkey sel) is an oracle; route-type encoding unvalidated.
  6. reject/queue drop their params (Reject(0,0)/Queue(0,0,...)); reject ICMP not modelled.
  7. limit/quota/connlimit pass iff 0<remaining (env count), not a real token bucket.
  8. counter/log/comment verdict-neutral. byte ops (byteorder/shift/jhash/le) eyeballed.
  9. meta obrname/ibrname -> MK bri_oifname/bri_iifname mapping not validated vs live nft.

C SOURCE for the oracle of truth: nftables userspace + linux kernel net/netfilter.
Look in ${REPO}/kernel (if present), the tests/py corpus cache that 'make corpus' clones,
and you MAY use WebFetch/WebSearch on git.netfilter.org / kernel.org source.
${FOCUS}`

const FINDING_SCHEMA = {
  type: 'object', additionalProperties: false,
  required: ['satisfied','title','kind','description','evidence','repro','suggested_fix','severity'],
  properties: {
    satisfied: { type: 'boolean', description: 'true ONLY if, after honest effort, you found NO new infidelity this round (loop stops). false if you found one.' },
    title: { type: 'string', description: 'short name of the infidelity (empty if satisfied)' },
    kind: { enum: ['c-source','unprovable-correct-property','provable-incorrect-property','other'], description: 'how you found it' },
    description: { type: 'string', description: 'precisely what the Rocq semantics does vs what real nftables does' },
    evidence: { type: 'string', description: 'C-source file:line + quote, OR the exact property + ruleset + expected-vs-actual verdict, OR the coqtop transcript showing a correct property unprovable / an incorrect one provable' },
    repro: { type: 'string', description: 'exact commands/files a fixer can run to see it' },
    suggested_fix: { type: 'string', description: 'concrete change to Semantics.v/Syntax.v/Packet.v (+ parser) to make it faithful' },
    severity: { enum: ['high','medium','low'] },
  },
}

const FIX_SCHEMA = {
  type: 'object', additionalProperties: false,
  required: ['fixed','summary','files_changed','gates','axiom_free','committed','notes'],
  properties: {
    fixed: { type: 'boolean', description: 'true only if the infidelity is genuinely fixed AND all gates stay green' },
    summary: { type: 'string' },
    files_changed: { type: 'array', items: { type: 'string' } },
    gates: { type: 'string', description: 'status of make proofs / corpus / validate / parse-test (with numbers)' },
    axiom_free: { type: 'boolean' },
    committed: { type: 'boolean', description: 'true if you committed the green fix; false if you reverted because gates failed' },
    notes: { type: 'string' },
  },
}

phase('Recon')
const briefing = await agent(
  `You are reconnaissance for an adversarial audit of a Rocq nftables semantics.
${BRIEF}

Do, concretely (use Bash):
1. Confirm the toolchain: \`cd ${PROOF} && eval $(opam env --switch=vst) && make -f CoqMakefile theories/Semantics.vo 2>&1 | tail -3\`.
2. Locate nftables/kernel C source on this machine: ${REPO}/kernel, the 'make corpus'
   cache (find the tests/py dir), /usr/src, /usr/include/linux/netfilter*, and whether
   WebFetch to git.netfilter.org works. Report exact paths that exist.
3. List real rulesets to test properties against (optiplex.nft, ruleset.nft,
   /usr/share/nftables/*, /usr/share/doc/nftables/examples/*, the tests/py corpus).
4. Run each gate and capture the current pass line.
Output a tight briefing (paths + exact commands + reachable C source). Concrete, no fluff.`,
  { label: 'recon', agentType: 'general-purpose' }
)

const history = []
let round = 0
let satisfied = false

while (round < MAX_ROUNDS && (!budget.total || budget.remaining() > 80000)) {
  round++
  const hist = history.map(h =>
    `Round ${h.round}: [${h.finding.severity}] ${h.finding.title} (${h.finding.kind})\n  finding: ${h.finding.description}\n  blue: fixed=${h.fix?.fixed} committed=${h.fix?.committed} — ${h.fix?.summary}\n  blue notes: ${h.fix?.notes}`
  ).join('\n\n') || '(none yet)'

  phase('Audit')
  const finding = await agent(
    `You are the RED agent (adversary/auditor) in an adversarial audit of a Rocq nftables
semantics. Find ONE concrete, high-value infidelity per round — a place where the Rocq
semantics diverges from REAL nftables — and prove it is real.

${BRIEF}

RECON BRIEFING:
${briefing}

HISTORY (verify the most recent fix is real before hunting anew):
${hist}

PROCEDURE:
A. If history is non-empty, FIRST adversarially verify the latest blue fix: re-run its
   repro / re-check its property, confirm gates green (proofs/corpus/validate/parse-test)
   and axiom-free. A bogus fix or regression IS your finding (kind=other).
B. Otherwise find a NEW infidelity by ONE method (prefer the most rigorous):
   1. READ THE C SOURCE and show (file:line + quote) the Rocq semantics differs.
   2. State a CORRECT property about a real ruleset and show it is NOT provable (paste the
      coqtop attempt) -> semantics too weak/wrong.
   3. State an INCORRECT property and show it IS provable -> semantics unsound/vacuous.
Be concrete and reproducible. Pick the highest-severity infidelity you can substantiate.
If after genuine effort you cannot substantiate any new infidelity, set satisfied=true
(and explain what you checked). You have Bash/coqtop/WebFetch; actually run things.`,
    { label: `red r${round}`, agentType: 'general-purpose', effort: 'high', schema: FINDING_SCHEMA }
  )

  if (!finding || finding.satisfied) {
    satisfied = !!(finding && finding.satisfied)
    log(`Round ${round}: red satisfied — no new infidelity. Stopping.`)
    break
  }
  log(`Round ${round}: red found [${finding.severity}] ${finding.title} (${finding.kind})`)

  phase('Fix')
  const fix = await agent(
    `You are the BLUE agent (fixer). The red agent substantiated this infidelity — make the
semantics faithful.

${BRIEF}

RECON BRIEFING:
${briefing}

THE INFIDELITY:
title: ${finding.title}  severity: ${finding.severity}  kind: ${finding.kind}
description: ${finding.description}
evidence: ${finding.evidence}
repro: ${finding.repro}
suggested_fix: ${finding.suggested_fix}

PRIOR ROUNDS (do not undo earlier fixes):
${hist}

HARD CONSTRAINTS:
- Fix the SPECIFICATION faithfully (Semantics.v/Syntax.v/Packet.v + parser
  nft_lower.ml/parser.mly + nft_emit.ml + regenerate *_Gen.v if AST shape changes). Do NOT
  make a theorem pass by weakening it or adding axioms.
- ALL gates stay green after your change: make proofs, make corpus (2532/2532, 0 mismatch),
  make validate (28/28), make parse-test. EVERY top-level theorem still prints "Closed
  under the global context" (no new axioms/Admitted).
- If you add a theorem demonstrating the fix, prove it axiom-free; ideally add a check to
  parse_test.ml.
- If you CANNOT keep all gates green, \`git restore\`/\`git checkout --\` your working-tree
  changes (leave the repo at HEAD, green) and report fixed=false with why. Never leave the
  repo broken.
- On success, \`git add -A && git commit\` on the current branch with a clear message ending:
  Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>  (do NOT push). committed=true.
- Touch only files under ${PROOF} (and the two .nft rulesets if strictly needed).
Work iteratively: change, build the affected .vo, run gates, fix breakage, commit. Return
the structured report with real gate numbers.`,
    { label: `blue r${round}`, agentType: 'general-purpose', effort: 'high', schema: FIX_SCHEMA }
  )

  history.push({ round, finding, fix })
  log(`Round ${round}: blue fixed=${fix?.fixed} committed=${fix?.committed}`)

  if (fix && fix.fixed === false && fix.committed === false && /broke|cannot leave|still failing/i.test(fix.notes || '')) {
    log(`Round ${round}: blue could not fix and flagged repo risk — stopping for human review.`)
    break
  }
}

phase('Synthesis')
const report = await agent(
  `You are the synthesis agent for an adversarial audit of a Rocq nftables semantics.
Summarise the run honestly.

ROUNDS (${history.length} fix attempts; red satisfied at end = ${satisfied}):
${history.map(h => `Round ${h.round}: [${h.finding.severity}] ${h.finding.title}\n  infidelity: ${h.finding.description}\n  fix: fixed=${h.fix?.fixed} committed=${h.fix?.committed} — ${h.fix?.summary}\n  gates: ${h.fix?.gates} axiom_free=${h.fix?.axiom_free}\n  residual: ${h.fix?.notes}`).join('\n\n') || '(no rounds ran)'}

Produce: (1) a table of infidelities found and whether each was fixed (with commit), (2) the
gate status NOW (run make proofs/corpus/validate/parse-test from ${PROOF}; report numbers),
(3) the most important infidelities that REMAIN, ranked. Honest and concrete.`,
  { label: 'synthesis', agentType: 'general-purpose' }
)

return { rounds: history.length, satisfied, history, report }
