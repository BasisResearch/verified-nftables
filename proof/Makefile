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

.PHONY: all proofs glue lib example semtest difftest corpus byteorder-gate validate parse-test gen gen-check gates clean cli e2e nl-send parser-corpus axioms

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
# change — `make gen-check` (below, part of `make gates`) FAILS the build if a
# checked-in Gen file drifts from fresh nft2coq output.  nft2coq IS the
# frontend; the emitted .v is checked by the Rocq kernel.
gen: lib
	cd extracted && dune exec ./nft2coq.exe -- ../../rulesets/optiplex.nft > ../theories/Generated/Optiplex_Gen.v
	cd extracted && dune exec ./nft2coq.exe -- ../../rulesets/ruleset.nft  > ../theories/Generated/Ruleset_Gen.v
	cd extracted && dune exec ./nft2coq.exe -- ../../rulesets/tutorial.nft > ../theories/Generated/Tutorial_Gen.v
	cd extracted && dune exec ./nft2coq.exe -- ../../rulesets/router.nft   > ../theories/Generated/Router_Gen.v

# Drift gate for the proof bridge: the checked-in theories/Generated/*_Gen.v
# MUST be byte-identical to a fresh `nft2coq` run over the .nft sources.
# Without this, a stale Gen file (or a parser change not followed by `make
# gen`) yields valid proofs about a ruleset that is NOT the one deployed —
# the theorems would be true of yesterday's parse.  Covers ALL FOUR rulesets
# (router.nft included).  Fails on any diff.
gen-check: lib
	@set -e; tmp=$$(mktemp -d); trap 'rm -rf "$$tmp"' EXIT; \
	for pair in optiplex:Optiplex_Gen ruleset:Ruleset_Gen tutorial:Tutorial_Gen router:Router_Gen; do \
	  f=$${pair%%:*}; g=$${pair##*:}; \
	  (cd extracted && dune exec ./nft2coq.exe -- ../../rulesets/$$f.nft) > "$$tmp/$$g.v"; \
	  if ! cmp -s "$$tmp/$$g.v" theories/Generated/$$g.v; then \
	    echo "gen-check FAIL: theories/Generated/$$g.v differs from fresh nft2coq output of rulesets/$$f.nft (stale Gen file or unregenerated parser change; run 'make gen')"; \
	    diff -u theories/Generated/$$g.v "$$tmp/$$g.v" | head -40; exit 1; \
	  fi; \
	  echo "gen-check ok: theories/Generated/$$g.v == nft2coq(rulesets/$$f.nft)"; \
	done

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

# Axiom-freedom gate: Print Assumptions over EVERY theorem the README claims
# axiom-free (needs the .vo files — run after `make proofs`).  Prints one
# verdict line per theorem and fails unless EVERY one is "Closed under the
# global context" (i.e. no axiom, no Admitted, anywhere in its proof).
# The in-file `Print Assumptions` lines scattered through theories/*.v are
# INFORMATIONAL (they print to the `make proofs` log but cannot fail a build);
# THIS target is the enforcement point.
#
# The list = the THEOREMS.md HEADLINE set + the Correct.v strata + the
# README §"Headline guarantees are axiom-free" claim surface:
#   anti-spoofing        Optiplex_Antispoof (any-env general + pinned original
#                        + 3 concrete corollaries)
#   established-accept   Example_Ruleset.established_accepted
#   NAT-masquerade +
#   multi-address        Netstate_MultiAddr (selection + drop-iff)
#   fib host-local       Fib_Local (all 17 heads)
#   ct-state             Ct_State (all 5 theorems)
#   fuel adequacy (M4)   Semantics jx monotonicity/adequacy + eval_table
#                        fuel-independence + compiled mirror + the tutorial
#                        fuel-free corollary
#   mark de-vacuized(M4) Optiplex_Mark _real heads + the gen_env/fib
#                        contradiction + the witnessed instance
# Any NEW README-claimed result must be added here in the same commit.
AXIOM_GATE_THEOREMS = compile_chain_correct compile_chain_mut_correct \
  compile_chain_mut_env_correct compile_seq_mut_correct compile_table_correct \
  compile_ruleset_correct compile_hook_correct compile_seq_correct \
  optimize_table_uncond_correct optimize_table_uncond_compile_correct \
  elab_matchcond_correct Semantics.run_rule_outcome_eq \
  Semantics.eval_rules_jx_monotone Semantics.eval_rules_j_fuel_stable \
  Semantics.eval_rules_jx_adequate Semantics.eval_table_fuel_indep \
  Semantics.eval_table_policy_is_fallthrough \
  Correct.run_table_fuel_indep_compiled \
  Nft_Tactics.nft_yields_fuel_indep \
  Tutorial_Proofs.tutorial_blocks_exactly_any_fuel \
  Optiplex_Antispoof.antispoof_general_any_env \
  Optiplex_Antispoof.antispoof_general \
  Optiplex_Antispoof.vikunja_cannot_spoof_budget \
  Optiplex_Antispoof.gentoo_cannot_spoof_hass \
  Optiplex_Antispoof.budget_legitimate_allowed \
  Optiplex_Mark.genenv_fib_local_contradiction \
  Optiplex_Mark.streaming_prerouting_io_real \
  Optiplex_Mark.streaming_prerouting_mark_real \
  Optiplex_Mark.streaming_flow_whole_ruleset_real \
  Optiplex_Mark.streaming_whole_ruleset_witnessed \
  Example_Ruleset.established_accepted \
  Netstate_MultiAddr.masq_saddr_is_selected_primary \
  Netstate_MultiAddr.masq_drop_iff_no_eligible_addr \
  Fib_Local.fib_key_is_daddr Fib_Local.fib_key_is_saddr \
  Fib_Local.fib_daddr_load_is_real Fib_Local.fib_addr_type_no_dev \
  Fib_Local.fib_local_hostwide_crossiface \
  Fib_Local.fib_local_iif_scoped_downgrade Fib_Local.fib_local_iif_scoped_match \
  Fib_Local.fib_daddr_type_local_iff Fib_Local.lpm_fib_compiled_is_addr_type \
  Fib_Local.fib_daddr_type_base_is_kernel \
  Fib_Local.fib_daddr_local_iif_independent \
  Fib_Local.fib_fires_local Fib_Local.fib_no_fire_remote \
  Fib_Local.fib_iif_scoped_not_local Fib_Local.fib_base_fires \
  Fib_Local.fib_base_no_fire Fib_Local.fib_base_is_kernel_demo \
  Ct_State.estab_matches_pure Ct_State.estab_matches_established_plus_other \
  Ct_State.estab_misses_without_bit Ct_State.refuted_meq_rejects \
  Ct_State.refuted_alternative_diverges \
  Lower_Proofs.range_erasure_be Lower_Proofs.range_erasure_host \
  Lower_Proofs.bitmask_erasure Lower_Proofs.bitfield_erasure

axioms:
	@cd theories && { printf 'From Nft Require Import Correct Optimize_Uncond Elab Optiplex_Antispoof Optiplex_Mark Nft_Tactics Tutorial_Proofs Example_Ruleset Netstate_MultiAddr Fib_Local Ct_State Lower_Proofs.\n'; \
	  for t in $(AXIOM_GATE_THEOREMS); do printf 'Print Assumptions %s.\n' "$$t"; done; } \
	| coqtop -R . Nft 2>/dev/null \
	| grep -E 'Closed under the global context|Axioms' \
	| { fail=0; for t in $(AXIOM_GATE_THEOREMS); do \
	      if ! read -r line; then echo "$$t: NO VERDICT (build theories first: make proofs)"; fail=1; break; fi; \
	      echo "$$t: $$line"; \
	      case "$$line" in *"Closed under the global context"*) ;; *) fail=1 ;; esac; \
	    done; exit $$fail; }

# THE aggregate gate: every README-advertised guarantee behind one command.
# Sequential (not parallel prerequisites) so a failure is attributable to one
# stage.  This is the enforcement point of the "every change keeps all gates
# green" norm — see DEVELOPMENT.md § "Enforcement model" (there is no CI).
gates:
	$(MAKE) proofs
	$(MAKE) axioms
	$(MAKE) corpus
	$(MAKE) validate
	$(MAKE) parse-test
	$(MAKE) gen-check
	@echo "ALL GATES GREEN: proofs axioms corpus validate parse-test gen-check"

clean:
	-[ -f $(COQMAKE) ] && $(MAKE) -f $(COQMAKE) clean || true
	rm -f $(COQMAKE) $(COQMAKE).conf
	find theories \( -name '*.vo' -o -name '*.vok' -o -name '*.vos' -o -name '*.glob' -o -name '.*.aux' \) -delete
	cd extracted && dune clean 2>/dev/null || true
