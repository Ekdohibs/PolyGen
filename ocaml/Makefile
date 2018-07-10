
# Exclude VPL/extracted : it is populated by VPL's own extracted files.
# Exclude VPL/smt: it is unused and its parser doesn't compile.
DIRS=. ../extraction $(shell find ../VPL/ocaml/src -type d ! -name extracted ! -name smt)

INCLUDES=$(patsubst %,-I %, $(DIRS))
PACKAGES=-package zarith
LIBS=unix.cmxa zarith.cmxa

OCAMLC=ocamlfind ocamlc -unsafe-string $(PACKAGES) $(INCLUDES)
OCAMLOPT=ocamlfind ocamlopt -unsafe-string $(PACKAGES) $(INCLUDES)
OCAMLDEP=ocamldep
MENHIR=menhir
OCAMLLEX=ocamllex

MLY=$(foreach d,$(DIRS),$(wildcard $(d)/*.mly))
MLL=$(foreach d,$(DIRS),$(wildcard $(d)/*.mll))

MENHIR_GENERATED_ML=$(patsubst %.mly,%.ml, $(MLY))
MENHIR_GENERATED_MLI=$(patsubst %.mly,%.mli, $(MLY))
MENHIR_GENERATED_DUMMY=$(patsubst %.mly,%.dummy, $(MLY))
OCAMLLEX_GENERATED_ML=$(patsubst %.mll,%.ml, $(MLL))

GENERATED=$(MENHIR_GENERATED_ML) $(MENHIR_GENERATED_MLI) $(OCAMLLEX_GENERATED_ML)

MODORDER=ocaml str.cma ../tools/modorder.ml .depend

ifeq ($(wildcard .depend),.depend)

OBJS:=$(shell $(MODORDER) ./test_extract.cmx)

test: $(OBJS)
	@echo "Linking $@"
	@$(OCAMLOPT) -o $@ $(LIBS) $+

include .depend

endif

$(MENHIR_GENERATED_ML): %.ml: %.dummy
$(MENHIR_GENERATED_MLI): %.mli: %.dummy
.INTERMEDIATE: $(MENHIR_GENERATED_DUMMY)
$(MENHIR_GENERATED_DUMMY): %.dummy: %.mly
	@echo "MENHIR $<"
	@$(MENHIR) $< > $@

$(OCAMLLEX_GENERATED_ML): %.ml: %.mll
	@echo "OCAMLLEX $<"
	@$(OCAMLLEX) $< -o $@


%.cmi: %.mli
	@echo "OCAMLC $<"
	@$(OCAMLC) -c -annot $<

%.cmo: %.ml
	@echo "OCAMLC $<"
	@$(OCAMLC) -c -annot $<

%.cmx: %.ml
	@echo "OCAMLOPT $<"
	@$(OCAMLOPT) -c -annot $<

clean:
	rm -f $(GENERATED)
	for d in $(DIRS); do rm -f $$d/*.cm[iotx] $$d/*cmti $$d/*.o; done

.depend: $(GENERATED)
	@echo "Analyzing OCaml dependencies"
	@$(OCAMLDEP) -slash $(INCLUDES) $(foreach d,$(DIRS),$(wildcard $(d)/*.ml $(d)/*.mli)) $(GENERATED) >.depend  || { rm -f .depend; exit 2; }
