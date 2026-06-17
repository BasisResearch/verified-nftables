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

.PHONY: all proofs glue lib example semtest difftest corpus validate parse-test gen clean

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
# parse ../ruleset.nft and check the parsed AST's verdicts against the
# Example_Ruleset.v theorems; parse difftest.sh's ruleset and check it lowers to
# glue.ml's known-good AST; and (best-effort) a live `nft --debug=netlink`
# round-trip.  A file argument turns it into a CLI: `dune exec ./parse_test.exe
# -- path/to/ruleset.nft` parses and prints the compiled bytecode.
parse-test: proofs
	cd extracted && dune exec ./parse_test.exe

# Regenerate the parser's output as Coq terms (theories/*_Gen.v) from the .nft
# sources, so the proofs (Optiplex_Antispoof, Ruleset_Verified) are about the
# actual parser output.  Checked in for reproducibility; rerun after a parser
# change.  nft2coq IS the frontend; the emitted .v is checked by the Rocq kernel.
gen: lib
	cd extracted && dune exec ./nft2coq.exe -- ../../optiplex.nft > ../theories/Optiplex_Gen.v
	cd extracted && dune exec ./nft2coq.exe -- ../../ruleset.nft  > ../theories/Ruleset_Gen.v

# Build/check every .v listed in _CoqProject; Extract.v writes extracted/*.ml.
proofs: $(COQMAKE)
	$(MAKE) -f $(COQMAKE)

$(COQMAKE): _CoqProject
	coq_makefile -f _CoqProject -o $(COQMAKE)

glue: proofs
	cd extracted && dune build ./glue.exe corpus_test.exe

# Byte-identical forward check on a hand-written ruleset vs the local `nft`.
difftest: glue
	./difftest.sh

# Round-trip the upstream nftables corpus through the verified compiler and
# report measured coverage (fails on any mismatch).
corpus: proofs
	./corpus.sh

# Independently validate field_load offsets / meta-ct names against live `nft`
# (the corpus round-trip shares its tables between parse and render, so it can't
# check these; this uses nft as an external oracle).
validate: glue
	./extracted/_build/default/corpus_test.exe validate

clean:
	-[ -f $(COQMAKE) ] && $(MAKE) -f $(COQMAKE) clean || true
	rm -f $(COQMAKE) $(COQMAKE).conf
	rm -f theories/*.vo theories/*.vok theories/*.vos theories/*.glob theories/.*.aux
	cd extracted && dune clean 2>/dev/null || true
