# certified-nft / proof — verified nftables DSL->bytecode compiler (Rocq)
#
#   make            build + check all proofs (incl. extraction to extracted/)
#   make glue       build the untrusted OCaml glue around the extracted compiler
#   make difftest   compile a ruleset and diff our bytecode against real `nft`
#   make lib        build the reusable `nftc` library
#   make example    build+run the standalone library-consumer demo
#   make clean      remove build artifacts

ROCQBIN ?=
COQMAKE  = CoqMakefile

.PHONY: all proofs glue lib example difftest corpus validate clean

all: proofs glue

# Build the reusable verified-compiler library (Compile/Optimize + Nftc facade).
lib: proofs
	cd extracted && dune build

# Build and run the standalone library-consumer example.
example: proofs
	cd extracted && dune exec ./example.exe

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
