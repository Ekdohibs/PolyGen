

COQDOCOPTS=-g --html

COQINCLUDES=
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQ2HTML=coq2html
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)

FILES=Linalg.v Loop.v PolyLang.v CodeGen.v Instr.v Misc.v VplInterface.v Result.v

proof: $(FILES:.v=.vo)

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

-include .depend
