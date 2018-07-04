

COQDOCOPTS=-g --html

COQINCLUDES=-R VPL/coq/ Vpl
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQ2HTML=coq2html
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)

FILES=Linalg.v Loop.v PolyLang.v CodeGen.v Instr.v Misc.v VplInterface.v Result.v PolyLoop.v ImpureAlarmConfig.v Canonizer.v Projection.v Heuristics.v TopoSort.v Semantics.v LoopGen.v

proof: $(FILES:.v=.vo)

Extraction.vo: $(FILES:.v=.vo) Extraction.v
	mkdir -p extraction
	$(COQC) Extraction.v
	rm extraction/ImpureConfig.mli
#	rm extraction/*.mli
#	tools/fix_extract.sh extraction/PedraQBackend.ml
#	cp extraction/PedraQBackend.ml.1 extraction/PedraQBackend.ml

%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

documentation: $(FILES)
	@echo "Generating documentation"
	@$(COQ2HTML) -d doc/html/ $(FILES:%.v=doc/%.glob) $^

.depend: $(FILES)
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend

all: proof documentation

extract: Extraction.vo

vplsetup:
	cp -f VPL/ocaml/src/Wrapper_no_glpk.ml VPL/ocaml/src/Wrapper.ml

ocaml: extract
	rm -f ocaml/.depend
	$(MAKE) -C ocaml .depend
	$(MAKE) -C ocaml

-include .depend
