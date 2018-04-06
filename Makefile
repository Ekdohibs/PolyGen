

COQINCLUDES=
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)

FILES=Linalg.v Loop.v PolyLang.v CodeGen.v Instr.v Misc.v

proof: $(FILES:.v=.vo)

%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

.depend: $(FILES)
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend

-include .depend
