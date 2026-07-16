# certified-nft / proof — verified nftables DSL->bytecode compiler (Rocq)
#
#   make            build + check all proofs (incl. extraction to extracted/)
#   make glue       build the untrusted OCaml glue around the extracted compiler
#   make difftest   compile a ruleset and diff our bytecode against real `nft`
#   make lib        build the reusable `nftc` library
#   make example    build+run the standalone library-consumer demo
#   make semtest    run the extracted semantics+VM on packets (theorem witness)
#   make clean      remove build artifacts

ROCQBIN ?=
COQMAKE  = CoqMakefile

.PHONY: all proofs glue lib example semtest difftest corpus byteorder-gate validate parse-test gen clean cli e2e nl-send parser-corpus axioms

all: proofs glue

# Build the reusable verified-compiler library (Compile/Optimize + Nftc facade).
lib: proofs
	cd extracted && dune build

# Build and run the standalone library-consumer example.
example: proofs
	cd extracted && dune exec ./example.exe

# Build+run the executable witness of compile_chain_correct / optimize_chain_correct:
# run the extracted DSL semantics, bytecode VM, and compiler on concrete packets.
semtest: proofs
	cd extracted && dune exec ./semtest.exe

# Build+run the .nft frontend's validation harness (TODO 9, milestone M1):
# parse ../rulesets/ruleset.nft and check the parsed AST's verdicts against the
# Example_Ruleset.v theorems; parse difftest.sh's ruleset and check it lowers to
# glue.ml's known-good AST; and (best-effort) a live `nft --debug=netlink`
# round-trip.  A file argument turns it into a CLI: `dune exec ./parse_test.exe
# -- path/to/ruleset.nft` parses and prints the compiled bytecode.
parse-test: proofs
	cd extracted && dune exec ./parse_test.exe

# Regenerate the parser's output as Coq terms (theories/Generated/*_Gen.v) from the .nft
# sources, so the proofs (Optiplex_Antispoof, Ruleset_Verified) are about the
# actual parser output.  Checked in for reproducibility; rerun after a parser
# change.  nft2coq IS the frontend; the emitted .v is checked by the Rocq kernel.
gen: lib
	cd extracted && dune exec ./nft2coq.exe -- ../../rulesets/optiplex.nft > ../theories/Generated/Optiplex_Gen.v
	cd extracted && dune exec ./nft2coq.exe -- ../../rulesets/ruleset.nft  > ../theories/Generated/Ruleset_Gen.v
	cd extracted && dune exec ./nft2coq.exe -- ../../rulesets/tutorial.nft > ../theories/Generated/Tutorial_Gen.v

# Build/check every .v listed in _CoqProject; Extract.v writes extracted/*.ml.
proofs: $(COQMAKE)
	$(MAKE) -f $(COQMAKE)

$(COQMAKE): _CoqProject
	coq_makefile -f _CoqProject -o $(COQMAKE)

glue: proofs
	cd extracted && dune build ./glue.exe corpus_test.exe

# The verified optimizer/compiler CLI (parse -> optimize_table_uncond/compile_chain
# -> render | send).  Bottoms out in the extracted verified terms.
cli: proofs
	cd extracted && dune build ./nftc_cli.exe

# End-to-end pipeline test (TODO 2c): run real .nft files through the nftc CLI
# (parse -> optimize -> compile -> render) and check against live `nft`.
e2e: cli
	./e2e.sh

# Netlink sender round-trip (TODO 2d): in a fresh user+net namespace, push the
# verified-compiled rules to the kernel over a real NETLINK_NETFILTER socket and
# read them back with `nft list ruleset`.  Needs unshare (unprivileged userns).
nl-send: cli
	cd extracted && unshare --net --map-root-user --map-auto bash nl_send_test.sh

# Byte-identical forward check on a hand-written ruleset vs the local `nft`.
difftest: glue
	./difftest.sh

# Round-trip the upstream nftables corpus through the verified compiler and
# report measured coverage (fails on any mismatch).
corpus: proofs
	./corpus.sh

# Compile the host-order (mark/iif/oif/ct-mark/fib-type) corpus blocks FROM SOURCE
# through the parser+verified compiler+renderer and diff the cmp/range immediates
# against the corpus .payload.  Closes the byteorder blind spot that `make corpus`
# (payload->render round-trip only) cannot see.  Fails on any mismatch.
byteorder-gate: proofs
	./byteorder-gate.sh

# Honest coverage of the UNTRUSTED .nft frontend: run `nftc compile` over a
# large, diverse, REAL rule corpus (nftables tests/py + shipped examples + mined
# GitHub configs) and print a parsed / parser-bug / out-of-model coverage table.
parser-corpus: cli
	./parser_corpus.sh

# Independently validate field_load offsets / meta-ct names against live `nft`
# (the corpus round-trip shares its tables between parse and render, so it can't
# check these; this uses nft as an external oracle).
validate: glue
	./extracted/_build/default/corpus_test.exe validate

# Axiom-freedom gate: Print Assumptions over the THEOREMS.md HEADLINE set plus
# the Correct.v strata (needs the .vo files — run after `make proofs`).  Prints
# one verdict line per theorem and fails unless EVERY one is "Closed under the
# global context" (i.e. no axiom, no Admitted, anywhere in its proof).
AXIOM_GATE_THEOREMS = compile_chain_correct compile_chain_mut_correct \
  compile_chain_mut_env_correct compile_seq_mut_correct compile_table_correct \
  compile_ruleset_correct compile_hook_correct compile_seq_correct \
  optimize_table_uncond_correct optimize_table_uncond_compile_correct \
  elab_matchcond_correct Semantics.run_rule_outcome_eq

axioms:
	@cd theories && { printf 'From Nft Require Import Correct Optimize_Uncond Elab.\n'; \
	  for t in $(AXIOM_GATE_THEOREMS); do printf 'Print Assumptions %s.\n' "$$t"; done; } \
	| coqtop -R . Nft 2>/dev/null \
	| grep -E 'Closed under the global context|Axioms' \
	| { fail=0; for t in $(AXIOM_GATE_THEOREMS); do \
	      if ! read -r line; then echo "$$t: NO VERDICT (build theories first: make proofs)"; fail=1; break; fi; \
	      echo "$$t: $$line"; \
	      case "$$line" in *"Closed under the global context"*) ;; *) fail=1 ;; esac; \
	    done; exit $$fail; }

clean:
	-[ -f $(COQMAKE) ] && $(MAKE) -f $(COQMAKE) clean || true
	rm -f $(COQMAKE) $(COQMAKE).conf
	find theories \( -name '*.vo' -o -name '*.vok' -o -name '*.vos' -o -name '*.glob' -o -name '.*.aux' \) -delete
	cd extracted && dune clean 2>/dev/null || true
