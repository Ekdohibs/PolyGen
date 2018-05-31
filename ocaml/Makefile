
OCAMLC=ocamlc -I ../extraction
OCAMLOPT=ocamlopt -I ../extraction
OCAMLDEP=ocamldep

MODORDER=ocaml str.cma ../tools/modorder.ml .depend

ifeq ($(wildcard .depend),.depend)

OBJS:=$(shell $(MODORDER) test_extract.cmx)

test: $(OBJS)
	@echo "Linking $@"
	@$(OCAMLOPT) -o $@ $+

include .depend

endif

%.cmi: %.mli
	@echo "OCAMLC $<"
	@$(OCAMLC) -c -annot $<

%.cmo: %.ml
	@echo "OCAMLC $<"
	@$(OCAMLC) -c -annot $<

%.cmx: %.ml
	@echo "OCAMLOPT $<"
	@$(OCAMLOPT) -c -annot $<

.depend:
	@echo "Analyzing OCaml dependencies"
	@$(OCAMLDEP) -slash -I ../extraction/ *.ml *.mli ../extraction/*.ml ../extraction/*.mli >.depend || { rm -f .depend; exit 2; }
