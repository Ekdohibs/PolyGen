

COQDOCOPTS=-g --html

COQINCLUDES=
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQ2HTML=coq2html
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)

FILES=Linalg.v Loop.v PolyLang.v CodeGen.v Instr.v Misc.v VplInterface.v Result.v

proof: $(FILES:.v=.vo)

Extraction.vo: $(FILES:.v=.vo) Extraction.v
	mkdir -p extraction
	$(COQC) Extraction.v
	rm extraction/ImpureConfig.mli

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

ocaml: extract
	$(MAKE) -C ocaml .depend
	$(MAKE) -C ocaml

-include .depend
