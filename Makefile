

COQDOCOPTS=-g --html

COQINCLUDES=-R VPL/coq/ Vpl
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQ2HTML=coq2html
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)

FILES=Linalg.v Loop.v PolyLang.v CodeGen.v Instr.v Misc.v VplInterface.v Result.v PolyLoop.v PolyLoopSimpl.v ImpureAlarmConfig.v Canonizer.v Projection.v Heuristics.v TopoSort.v Semantics.v LoopGen.v Mymap.v ImpureOperations.v ASTGen.v PolyTest.v PolyOperations.v

proof: $(FILES:.v=.vo)

Extraction.vo: $(FILES:.v=.vo) Extraction.v
	mkdir -p extraction
	$(COQC) Extraction.v
	rm extraction/ImpureConfig.mli

%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

documentation: $(FILES) proof
	@echo "Generating documentation"
	@$(COQ2HTML) -d doc/html/ $(FILES:%.v=doc/%.glob) $(FILES)

.depend: $(FILES)
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend || { rm -f .depend; exit 2; }

all: proof documentation

extract: Extraction.vo

vplsetup:
	cp -f VPL/ocaml/src/Wrapper_no_glpk.ml VPL/ocaml/src/Wrapper.ml
	$(MAKE) -C VPL/coq

ocaml: extract
	rm -f ocaml/.depend
	$(MAKE) -C ocaml .depend
	$(MAKE) -C ocaml

clean:
	$(MAKE) -C ocaml clean
	$(MAKE) -C VPL/coq clean
	rm -f VPL/ocaml/src/Wrapper.ml
	rm -rf *.vo doc/*.glob *.aux doc/html/*.html *.cache extraction

-include .depend
