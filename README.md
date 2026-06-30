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

Start at **[proof/DEVELOPMENT.md](proof/DEVELOPMENT.md)** for the design notes and the
honest scope of the "2532/2532" claim.

## Build & run

Everything below runs from the **`proof/`** directory.

**Prerequisites**

- **Rocq (Coq) 9.1.1** and an **OCaml 4.14 / dune** toolchain, in an opam switch. If your
  Rocq lives in a named switch, activate it first, e.g. `eval $(opam env --switch=vst)`.
- A live **`nft`** (nftables; tested against v1.1.6) for the differential gates
  (`corpus`, `validate`, `difftest`, `e2e`, `parse-test`).
- `git` + network access the first time you run `make corpus` (it clones the upstream
  nftables test corpus to `/tmp/nftables-src`, overridable with `NFT_CORPUS=...`).
- `unshare` with unprivileged user namespaces for `make nl-send` / `make difftest`.

**Build & check the proofs** (also extracts the verified compiler to `extracted/*.ml`
and builds the OCaml glue):

```sh
cd proof
make                 # build/check every theory + extract + build glue
```

**The verified CLI — `nftc`** (parse → optimize/compile → netlink text; the
optimize/compile core is the *extracted verified term*):

```sh
make cli             # builds extracted/_build/default/nftc_cli.exe
./extracted/_build/default/nftc_cli.exe optimize ../ruleset.nft   # parse->optimize_table_uncond->compile->render
./extracted/_build/default/nftc_cli.exe compile  ../router.nft    # parse->compile_chain->render
# equivalently, via dune (note the `--` and the ../../ path from extracted/):
cd extracted && dune exec ./nftc_cli.exe -- optimize ../../ruleset.nft
```

`nftc` has three modes — `compile`, `optimize`, and `send` (the last pushes the
verified-compiled rules to the kernel over a real `NETLINK_NETFILTER` socket; it mutates
kernel state and requires `--commit`, otherwise it dry-runs). Flags: `--table T`,
`--chain C`, `--no-optimize`, `--commit`. Read from stdin with `-`.

> **Scope of `send`:** `compile`/`optimize` render the full `--debug=netlink` text for
> everything the verified compiler supports. The `send` mode's binary netlink encoder
> currently covers only a *subset* of instructions, so it refuses (`cannot encode for
> netlink: …`) on rules that use, e.g., `ct`/named-set lookups. Use `compile`/`optimize`
> to inspect those.

**Gates, demos, and other executables** (each is `make <target>` from `proof/`):

| target | what it builds/runs |
| --- | --- |
| `make corpus` | round-trip the upstream nftables corpus through the verified compiler — **2532/2532, 0 mismatches** |
| `make validate` | field offsets / meta-ct names vs a live `nft` (28/28) |
| `make semtest` | run the extracted DSL semantics + bytecode VM + compiler on concrete packets (a witness of the correctness theorems) |
| `make parse-test` | the `.nft` frontend's round-trip checks (also a CLI: `dune exec ./parse_test.exe -- FILE.nft`) |
| `make e2e` | full `.nft` → parse → optimize → compile → render, checked against live `nft` |
| `make nl-send` | push verified-compiled rules to the kernel in a fresh net namespace, read back with `nft list ruleset` |
| `make difftest` | byte-identical forward check of a hand-written ruleset vs the local `nft` |
| `make lib` / `make example` | build the reusable `nftc` library / build+run its standalone consumer demo |
| `make gen` | regenerate the parser-output Coq terms (`theories/*_Gen.v`) from the `.nft` sources |

Sample rulesets to try the CLI on live in the repo root: `ruleset.nft`, `router.nft`,
`optiplex.nft`.

## Secondary: kernel-dev environment

A reproducible VM/kernel sandbox for the *later* data-plane (VST) work described in
`instructions.org` — download/compile an upstream kernel and boot it to iterate on
out-of-tree modules and direct kernel patches. This is future-facing scaffold, not the
verification effort; its full setup lives in **[KERNEL_DEV.md](KERNEL_DEV.md)** (host
package lists in [SETUP.md](SETUP.md)).
