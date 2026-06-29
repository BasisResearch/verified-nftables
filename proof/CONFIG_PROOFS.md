# Proving properties about *your* nftables ruleset

This guide shows how to take a concrete `.nft` file and prove a security property
about the **parser's own output** for it, using the readable
predicate/notation/tactic layer in [`theories/Nft_Tactics.v`](theories/Nft_Tactics.v).

The point of that layer is to turn the recurring boilerplate — the
`unfold … ; cbn -[…] ; rewrite … ; vm_compute` rituals and raw byte literals — into
a property that **reads like the nftables intent** and a one-line proof. It is a
thin, *additive*, **sound** layer: every notation is definitionally the underlying
`eval_table` / `field_value` statement (the `*_spec` lemmas and the `demo_*_def`
examples prove exactly this), so nothing you state through it is weaker than the
raw statement.

Worked end-to-end examples live in
[`theories/Nft_Demo_Symbolic.v`](theories/Nft_Demo_Symbolic.v) (packets
constrained by hypotheses) and
[`theories/Nft_Demo_Concrete.v`](theories/Nft_Demo_Concrete.v) (fully concrete
packets, plus a demonstration that the tactics **cannot** prove a false property).

---

## The four-step recipe

### 1. Get your ruleset in as Coq terms (`make gen`)

The Menhir frontend (`extracted/nft2coq`) reads a `.nft` file and emits its chains
and set/map declarations as Coq terms in a `*_Gen.v` file. The proofs are then
about **the parser's output**, not a hand copy:

```sh
cd proof
make gen        # regenerates theories/Optiplex_Gen.v and theories/Ruleset_Gen.v
```

To onboard a new file, add a line to the `gen` target in the `Makefile`:

```make
cd extracted && dune exec ./nft2coq.exe -- ../../myrules.nft > ../theories/Myrules_Gen.v
```

then `make gen`, add `theories/Myrules_Gen.v` to `_CoqProject`, and you have
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

`v` in `fieldof … === v` is a **typed** [`Nftval`](theories/Nftval.v) value —
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

The verdict you prove is about `eval_table` (the DSL specification); via
`Correct.compile_table_correct` the same verdict holds of the compiled netlink
bytecode, so the property transports to what the kernel actually runs.
