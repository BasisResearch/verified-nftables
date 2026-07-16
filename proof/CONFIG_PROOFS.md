# Proving properties about *your* nftables ruleset

This guide shows how to take a concrete `.nft` file and prove a security property
about the **parser's own output** for it, using the readable
predicate/notation/tactic layer in [`theories/Examples/Nft_Tactics.v`](theories/Examples/Nft_Tactics.v).

The point of that layer is to turn the recurring boilerplate — the
`unfold … ; cbn -[…] ; rewrite … ; vm_compute` rituals and raw byte literals — into
a property that **reads like the nftables intent** and a one-line proof. It is a
thin, *additive*, **sound** layer: every notation is definitionally the underlying
`eval_table` / `field_value` statement (the `*_spec` lemmas and the `demo_*_def`
examples prove exactly this), so nothing you state through it is weaker than the
raw statement.

Worked end-to-end examples live in
[`theories/Examples/Nft_Demo_Symbolic.v`](theories/Examples/Nft_Demo_Symbolic.v) (packets
constrained by hypotheses) and
[`theories/Examples/Nft_Demo_Concrete.v`](theories/Examples/Nft_Demo_Concrete.v) (fully concrete
packets, plus a demonstration that the tactics **cannot** prove a false property).

---

## The four-step recipe

### 1. Get your ruleset in as Coq terms (`make gen`)

The Menhir frontend (`extracted/nft2coq`) reads a `.nft` file and emits its chains
and set/map declarations as Coq terms in a `*_Gen.v` file. The proofs are then
about **the parser's output**, not a hand copy:

```sh
cd proof
make gen        # regenerates theories/Generated/Optiplex_Gen.v and theories/Generated/Ruleset_Gen.v
```

To onboard a new file, add a line to the `gen` target in the `Makefile`:

```make
cd extracted && dune exec ./nft2coq.exe -- ../../rulesets/myrules.nft > ../theories/Generated/Myrules_Gen.v
```

then `make gen`, add `theories/Generated/Myrules_Gen.v` to `_CoqProject`, and you have
`my_chain`, `my_chains` (the `(name, chain)` association list) and `gen_env` (the
set/map environment) as Coq definitions.

> `*_Gen.v` is auto-generated — **never hand-edit it**; regenerate with `make gen`.

### 2. Open the layer and register your chains

In your new `Myrules_Proof.v`:

```coq
From Nft Require Import Bytes Verdict Packet Syntax Semantics Nftval Eval_Fw
                       Myrules_Gen Nft_Tactics.
Import ListNotations. Open Scope string_scope.

(* So nft_eval needs no per-module unfold list (delta-only; nothing semantic). *)
#[local] Hint Unfold my_fuel my_chains my_chain : nft_chains.
```

### 3. State the property with the readable notations

The layer gives you (all in `nft_scope`, opened by importing `Nft_Tactics`):

| Notation                                             | Means (definitionally)                        |
|------------------------------------------------------|-----------------------------------------------|
| `C accepts p under cs budget f`                      | `eval_table f cs C p = Accept`                |
| `C denies  p under cs budget f`                      | `eval_table f cs C p = Drop`                  |
| `C gives v on p under cs budget f`                   | `eval_table f cs C p = v`                     |
| `fieldof F p === v`                                  | `field_value F p = encode v`                  |

`v` in `fieldof … === v` is a **typed** [`Nftval`](theories/IR/Nftval.v) value —
`ip4 192 168 51 20`, `ifname "eth0"`, `port 25`, `ct_established`, … — so the
hypothesis routes through the validity-checked datatype constructors instead of a
bare byte list. (`encode (ip4 …)` `vm_compute`s to exactly the bytes the kernel
compares.)

```coq
Theorem lan_smtp_denied : forall p,
  pkt_env p = gen_env ->
  fieldof FCtState     p === ct_new ->
  fieldof FMetaIifname p === ifname "eth0" ->
  fieldof FMetaL4proto p === inet_proto 6 ->   (* tcp  *)
  fieldof FThDport     p === port 25 ->        (* smtp *)
  read_payload_ok PTransport 2 2 p = true ->
  my_chain denies p under my_chains budget my_fuel.
```

### 4. Prove it with one tactic

- **Symbolic packet** (constrained by `pkt_env`/`field_value` hypotheses) — pass
  the `pkt_env p = …` hypothesis to **`nft_eval`**:

  ```coq
  Proof. intros p Hpe Hct Hiif Hl4 Hdp Hok. nft_eval Hpe. Qed.
  ```

  `nft_eval Hpe` unfolds the predicate, `autounfold`s your registered chains, and
  runs the shared symbolic engine (`Eval_Fw.eval_fw_core`), which steps the chain
  one rule at a time, rewriting each `field_value F p` from your hypotheses.

- **Fully concrete packet** (a closed `packet` record, closed chains) — use
  **`nft_decide`**:

  ```coq
  Theorem dns_accepted : my_chain accepts pkt_dns under my_chains budget my_fuel.
  Proof. nft_decide. Qed.
  ```

  `nft_decide` is `unfold … ; vm_compute; reflexivity` (it also closes concrete
  field facts and concrete-verdict disequalities).

That is the whole loop. See `theories/Nft_Demo_*.v` for compiling instances.

---

## Tutorial: prove a ruleset blocks *exactly* one IP range

Everything above proves one *direction* at a time ("this packet is dropped").
This tutorial walks the full workflow end-to-end on a fresh ruleset and proves an
**exactness** statement — an *iff*, universally quantified over packets and over
the four source-address bytes: *the chain drops a packet **iff** its source is in
the range*. So no in-range packet escapes **and** no out-of-range packet is
caught. The finished artifacts are checked in
([`rulesets/tutorial.nft`](../rulesets/tutorial.nft),
[`theories/Generated/Tutorial_Gen.v`](theories/Generated/Tutorial_Gen.v),
[`theories/Examples/Tutorial_Proofs.v`](theories/Examples/Tutorial_Proofs.v)) — this section
retraces how they were made.

### 1. Write the ruleset

`rulesets/tutorial.nft` — a one-rule filter: block `192.168.100.0/24`, accept
everything else.

```nft
table ip tutorial {
  chain input {
    type filter hook input priority 0; policy accept;
    ip saddr 192.168.100.0/24 drop
  }
}
```

Sanity-check it against the real tool: `nft -c -f rulesets/tutorial.nft`.

### 2. Parse it into Coq terms

Add the generation line to the `gen` target in `proof/Makefile`:

```make
cd extracted && dune exec ./nft2coq.exe -- ../../rulesets/tutorial.nft > ../theories/Generated/Tutorial_Gen.v
```

then run `make gen`. The parser emits `theories/Generated/Tutorial_Gen.v`; its interesting
part is the chain, *as the parser understood it*:

```coq
Definition tutorial_input : chain :=
  {| c_policy := Accept;
     c_rules := [{| r_body := [(BMatch (MEq (FPayload PNetwork 12 3) [192; 168; 100]))];
                    r_verdict := Drop; r_vmap := None; (* … no NAT/queue/… *) |}] |}.
```

Two things to notice. The `/24` became a **3-byte payload compare**: the IPv4
source address lives at network-header offset 12, and a byte-aligned /24 prefix
only needs its first 3 bytes, so the parser lowers `ip saddr 192.168.100.0/24` to
`MEq (FPayload PNetwork 12 3) [192;168;100]` — exactly the `payload load 3b @
network header + 12` + `cmp` that `nft --debug=netlink` shows for this rule. And
the chain records `policy Accept`, so the *only* way to `Drop` is that rule.

Finally add `theories/Generated/Tutorial_Gen.v` and (in step 3) `theories/Examples/Tutorial_Proofs.v`
to `_CoqProject`.

### 3. State the exactness theorem

`theories/Examples/Tutorial_Proofs.v`, using only the readable layer:

```coq
Theorem tutorial_blocks_exactly : forall (p : packet) (a b c d : nat),
  fieldof FIp4Saddr p === ip4 a b c d ->
  read_payload_ok PNetwork 12 4 p = true ->
  ( tutorial_input denies p under tutorial_chains budget tut_fuel
    <-> a = 192 /\ b = 168 /\ c = 100 ).
```

Read it aloud: *for every packet whose IPv4 source address is `a.b.c.d` (and
which really carries an IPv4 header — that is all `read_payload_ok … 12 4` says),
the chain drops it **iff** `a.b.c` = `192.168.100`* — i.e. iff the source lies in
192.168.100.0–192.168.100.255. Both quantifiers matter: `p` ranges over *all*
packets (any conntrack state, any interface, any ports — note there is no
`pkt_env` hypothesis at all), and `a b c d` range over all addresses.

### 4. Prove it — with the exactness lemmas, not the internals

An iff needs reasoning on the *non*-matching side too, which the one-directional
tactics don't do. `Nft_Tactics` ships an exactness kit so the proof stays at the
level of the statement:

```coq
Proof.
  intros p a b c d Hs Hok.
  (* the rule's 3-byte read is in bounds because the 4-byte one is *)
  assert (Hok3 : read_payload_ok PNetwork 12 3 p = true)
    by (apply read_payload_ok_shorter with (w := 4); [lia | exact Hok]).
  (* chain-level iff: a one-rule accept-policy chain drops IFF its
     prefix-match fires *)
  eapply iff_trans.
  { apply (nft_prefix_chain_drop_iff 15 tutorial_chains _ _ _ _ _ Hok3). }
  (* the 3-byte prefix field is [firstn 3] of the saddr your hypothesis names *)
  rewrite (nft_saddr_prefix 3) by lia.
  unfold nft_field_is in Hs. rewrite Hs. cbn.
  (* [a;b;c] = [192;168;100]  <->  a = 192 /\ b = 168 /\ c = 100 *)
  apply bytes3_eq_iff.
Qed.
```

The pieces (all in [`Nft_Tactics.v`](theories/Examples/Nft_Tactics.v), all proved sound
against the semantics, none requiring you to unfold the evaluator):

| lemma | what it says |
|---|---|
| `nft_prefix_chain_drop_iff` / `…_accept_iff` | an Accept-policy chain whose single rule is "payload-prefix match ⇒ Drop" drops `p` **iff** the prefix equation holds (accepts iff it doesn't) |
| `nft_saddr_prefix` / `nft_daddr_prefix` | the parser's k-byte prefix field is `firstn k` of the 4-byte source/destination address field |
| `read_payload_ok_shorter` | in-bounds for a longer read ⇒ in-bounds for a shorter one |
| `bytes3_eq_iff` / `bytes4_eq_iff` | byte-list equation ⟺ the per-byte conjunction you state the range with |
| `nft_match_MEq_iff` | (lower level) an `MEq` match fires iff its prefix equation holds |
| `nft_single_rule_drop_iff` / `…_accept_iff` | (lower level) the one-rule chain iff for any rule you've shown loadable & terminal-Drop |

The complement theorem `tutorial_accepts_rest` (`accepts ⟺ ¬(a=192∧b=168∧c=100)`)
is the same five lines with the `accept` variants — together they pin the chain's
entire behaviour.

### 5. Guard against vacuity, then check the axioms

A universally quantified iff would also hold if *no* packet satisfied the
hypotheses, so `Tutorial_Proofs.v` closes the loop with concrete witnesses: a
`mk_tut a b c d` packet builder that provably satisfies both hypotheses for *any*
bytes, `vm_compute` runs of the real evaluator on `192.168.100.7` (dropped) and
`192.168.101.7` / `8.8.8.8` (accepted), a refutation that the next /24 over is
blocked, and a `Fail now nft_decide` witness that the tactic cannot prove that
false claim. Finally:

```coq
Print Assumptions tutorial_blocks_exactly.   (* Closed under the global context *)
```

axiom-free — and since the statement is about the parser's own output, via
`Correct.compile_table_correct` the same verdict holds of the compiled netlink
bytecode.

To adapt this to your own ruleset: swap the prefix bytes/offset (`nft_daddr_prefix`
for destination ranges), or for multi-rule chains drop down to the
`nft_single_rule_*`/`rule_fires_*`/`rule_skips` layer.

---

## Helpers for hand proofs

When a chain needs bespoke threading, the layer also exports the one-step lemmas
(`eval_rules_j` is kept `Global Opaque`, so these are how you step it):

- `rule_fires_drop` / `rule_fires_accept` — a rule that loads, applies, and yields
  a terminal verdict decides the chain at that rule;
- `rule_skips` — a rule whose match does not apply is skipped, continuing at the
  tail.

and the typed-match predicates `nft_match_fires` / `nft_match_blocks`
(`eval_matchcond_body m p = true/false`).

---

## Why this is sound (and how it's checked)

- **Notations don't weaken anything.** Each predicate is a transparent
  `Definition` equal *by conversion* to its `eval_table` / `field_value`
  statement. `Nft_Tactics.v` proves `nft_accepts_spec`, `nft_drops_spec`,
  `nft_field_is_spec`, … (all by `reflexivity`), and the demos prove
  `demo_accepts_def : (C accepts p …) = (eval_table … = Accept)` by `reflexivity`.
  `Nft_Demo_Symbolic.demo_recovers_original` re-derives the *original*
  `Ruleset_Verified`-shaped statement (raw `eval_table`, raw byte literal) from
  the readable one — proof that the readable form is no weaker.
- **The tactics can't prove false goals.** They only run reduction
  (`cbn`/`vm_compute`) and rewrite *your* hypotheses — no `admit`, no `Axiom`, no
  goal-closing by over-eager computation of an unrelated term.
  `Nft_Demo_Concrete.demo_smtp_not_accepted` refutes a false property, and
  `demo_nft_decide_cannot_prove_false` shows `nft_decide` leaves the false goal
  open (`Fail now nft_decide`).
- **Axiom-free.** Every headline theorem here is guarded by
  `Print Assumptions … = "Closed under the global context"`.

**What the `*_Gen.v` bytes rest on (read this before citing a config theorem).**
A theorem proved through this workflow is about the *parser's output*, and the
value bytes inside that output have two different trust stories:

- For the four typed match shapes (`Elab.tmatch`: eq / neq / CIDR-prefix /
  ifname-wildcard), the Gen term carries a **typed** immediate and the
  bytes are produced by the **verified** `Nftval.encode`/`Elab.elab_m`
  (`elab_matchcond_correct`) — the typed→bytes step is a theorem.
- Every **other** immediate in a Gen file is a raw byte list composed by the
  **unverified** OCaml frontend (`extracted/nft_lower.ml`): set/map *elements*
  (including its own CIDR net/broadcast interval expansion), range endpoints
  (including the host-endian `enc_atom_be` reversal), vmap keys, **NAT/tproxy
  target addresses and ports**, mangle/`vsrc` immediates, and bitwise masks.

The second class matters for exactly the theorems this guide helps you state:
if `nft_lower` mis-encoded a NAT target or a set element, `make gen` would emit
a *wrong-but-well-typed* AST, the proof would go through, and your theorem
would be true **about the wrong addresses**. The checks standing between you
and that outcome are the *untrusted differential gates*, not a proof: the
corpus round-trip (2532/2532), `make validate` (28/28 vs live `nft`),
`make parse-test`/`make e2e` (source-side diffs vs live `nft`), and
`make gen-check` (the checked-in Gen file matches today's parser output).
Concretely: sanity-check the Gen file's literals against your `.nft` source
(step 2 above prints the interesting part), and remember the theorem's meaning
is conditional on those frontend bytes being the ones `nft` itself would emit.
The precise boundary statement lives in `theories/IR/Elab.v`'s header.

The verdict you prove is about `eval_table` (the DSL specification); via
`Correct.compile_table_correct` the same verdict holds of the compiled netlink
bytecode, so the property transports to what the kernel actually runs.
