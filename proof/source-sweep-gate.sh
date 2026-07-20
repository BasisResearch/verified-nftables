#!/usr/bin/env bash
# Compile-from-source SOURCE-SWEEP — a TRACKED-COUNT RATCHET.
#
# For EVERY `.t.payload` block, compile its `# <src>` header from source through
# the parser + verified compiler + renderer and diff the rendered rule against
# the block's recorded instructions.  Unlike `byteorder-gate` (red/green
# byte-identity on the narrow host-order class), this is a broad sweep whose
# corpus goldens are endian-unportable for hton'd host-endian constants and
# whose several benign display/optimization classes render differently — so it
# can never be red/green.  It is a RATCHET: the byte-identical PASS count is
# pinned as a FLOOR below; a frontend regression that drops a block below the
# floor turns the build red, while the open display classes stay visible.
#
# The floor is a lower bound, not the exact count: raise it (never silently
# lower it) whenever a fix lifts the pass count.  See DEVELOPMENT.md
# § "The 83 source-divergences, adjudicated (T2A)".
#
# Requires: git, dune.  Reuses the corpus clone (NFT_CORPUS, default /tmp/nftables-src).
set -euo pipefail
cd "$(dirname "$0")"

# Pinned pass-count FLOOR (compile-from-source blocks byte-identical to corpus).
# Raised 1166 -> 1176 when the class-G in-frame-ethertype network guard landed
# (8 bridge/netdev vlan+icmp blocks moved from divergent to byte-identical).
# Raised 1176 -> 1181 when the adjacent-payload-load merge landed
# (Optimize_PayMerge, corpus class I: the 5 tcp sport/dport + ether saddr/type
# fusion blocks — inet/payloadmerge.t.payload:1, inet/tcp.t.payload:166/173/182,
# bridge/vlan.t.payload:279 — moved from divergent to byte-identical; the pass is
# applied source-side in parse_test's sweep, verdict-preserving by
# Optimize_PayMerge.paymerge_chain_eval).
# Raised 1181 -> 1187 when T3 named-object references landed (ip/objects.t.payload
# `counter name`/`quota name`/`ct helper set`/`limit name`/`ct timeout set`/`ct
# expectation set` blocks now compile from source to byte-identical
# `[ objref type N name X ]`).
# Raised 1187 -> 1196 when compound flag masks landed (T3 residue R2:
# `tcp flags & (fin | syn | rst | ack) == syn | ack` — LPAREN/RPAREN lexed,
# the pipe group carried UNRESOLVED as Ast.SVOr, symbol values + OR-fold in
# verified Coq (Typecheck.resolve_value); 9 paren/OR blocks, e.g.
# inet/tcp.t.payload:425-455, moved from parse-fail to byte-identical).
# HELD at 1196 when the DEFAULT pipeline landed (T3 residue: the sweep now
# compiles through the SHIPPED Optimize_Linearize.compile_chain_default —
# always-on paymerge + xorfold — instead of an ad-hoc harness-side paymerge;
# same 1196 passes: the class-L xor blocks stay open on the host-endian
# DISPLAY residual + nft's identity-binop elision, see
# reports/default-linearization-audit.md).
# Raised 1196 -> 1198 when the fib concat-selector spelling was aligned to
# nft's netlink-debug form (`saddr . iif`, spaces — the spelling validate
# confirms against live nft and Fib_Local.fibkey_wf keys; parser.mly join
# was "."): inet/fib.t.payload:6/:11 moved from divergent to byte-identical.
# Raised 1198 -> 1202 when the trivial-binop elision landed (W3,
# Optimize_Elide in the default pipeline: the spent `& 0xff.. ^ 0` binop the
# xor fold leaves is deleted, nft's binop_transfer_handle_lhs).  The 4
# class-L xor blocks — any/meta.t.payload:174/179, any/ct.t.payload:151/156
# — moved from divergent to byte-identical: their remaining instruction is a
# PLAIN host-order cmp, which renders in the goldens' recorded byte order
# (the endian-unportable part was the deleted bitwise's mask/xor operands).
# The same 4 blocks also entered byteorder-gate's plain-cmp scope (21 -> 25
# blocks, all green).
SOURCE_SWEEP_FLOOR="${SOURCE_SWEEP_FLOOR:-1202}"

CORPUS_DIR="${NFT_CORPUS:-/tmp/nftables-src}"
if [ ! -d "$CORPUS_DIR/tests/py" ]; then
  echo ">> fetching nftables corpus into $CORPUS_DIR"
  git clone --depth 1 https://git.netfilter.org/nftables "$CORPUS_DIR" \
    || git clone --depth 1 https://github.com/torvalds/nftables "$CORPUS_DIR"
fi

echo ">> building parser + verified compiler + renderer"
( cd extracted && dune build ./parse_test.exe )

payloads=$(find "$CORPUS_DIR/tests/py" -name '*.t.payload*')
echo ">> source-sweep over $(echo "$payloads" | wc -l) payload files (floor $SOURCE_SWEEP_FLOOR)"
exec extracted/_build/default/parse_test.exe source-sweep-gate "$SOURCE_SWEEP_FLOOR" $payloads
