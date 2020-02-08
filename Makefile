SRC_DIRS := 'src'
VFILES := $(shell find $(SRC_DIRS) -name "*.v")

COQARGS :=

default: $(VFILES:.v=.vo)

.coqdeps.d: $(VFILES)
	@echo "COQDEP $@"
	@coqdep -f _CoqProject $(VFILES) > $@

ifneq ($(MAKECMDGOALS), clean)
-include .coqdeps.d
endif

%.vo: %.v
	@echo "COQC $<"
	@coqc $(COQARGS) $(shell cat '_CoqProject') $< -o $@

clean:
	@echo "CLEAN vo glob aux"
	@rm -f $(VFILES:.v=.vo) $(VFILES:.v=.glob)
	@find $(SRC_DIRS) -name ".*.aux" -exec rm {} \;
	rm -f .coqdeps.d

.PHONY: default clean
.DELETE_ON_ERROR:
