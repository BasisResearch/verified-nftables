# certified-nft

**Formally verifying nftables.** The substance of this repo is a **Rocq-verified,
semantics-preserving compiler** from the declarative nftables DSL to the control-plane
(netlink) bytecode `nft` emits.

## The verified compiler (`proof/`)

- **Semantics-preserving compilation + a verified DSL optimizer**, machine-checked in Rocq.
  `compile_chain_correct` says the bytecode VM agrees with the DSL semantics, and
  `optimize_table_uncond_compile_correct` says the compiled bytecode of the *optimized*
  ruleset preserves every packet's verdict — for **any** input ruleset, with no
  `rules_clean` or freshness precondition.
- **Differential-tested against the upstream nftables test corpus.** Extracted to OCaml, it
  reproduces the real tool's bytecode on **2532/2532 (100%)** of the corpus's rule-blocks
  with zero mismatches (`cd proof && make corpus`), and validates field offsets / meta-ct
  names against a live `nft` (`make validate`, 28/28).
- **Data-plane semantics hardened by an adversarial red/blue fidelity audit** against the
  linux kernel source — see **[adversarial.md](adversarial.md)**.
- **Headline guarantees are axiom-free** ("Closed under the global context"): the
  anti-spoofing, established-accept, NAT-masquerade, multi-address primary-selection, fib
  host-local, and ct-state results.

Start at **[proof/DEVELOPMENT.md](proof/DEVELOPMENT.md)**; build/check everything with
`cd proof && make` (then `make corpus validate parse-test semtest`).

## Secondary: kernel-dev environment

A reproducible VM/kernel sandbox for the *later* data-plane (VST) work described in
`instructions.org` — download/compile an upstream kernel and boot it to iterate on
out-of-tree modules and direct kernel patches. This is future-facing scaffold, not the
verification effort; its full setup lives in **[KERNEL_DEV.md](KERNEL_DEV.md)** (host
package lists in [SETUP.md](SETUP.md)).
