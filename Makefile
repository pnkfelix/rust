FILES=foo1.rs foo2.rs foo3.rs foo4.rs foo5.rs foo6.rs foo7.rs foo8.rs

all: $(patsubst %.rs,%.dot,$(FILES))

RUSTC_LIB=$(RUSTC) --crate-type=lib

define FIND_LAST_FN
LAST_FN_NUM_$(1) := $(shell $(RUSTC_LIB) --pretty=expanded,identified $(1) \
			 | grep block
			 | tail -1
			 | sed -e 's@.*/\* block \([0-9]*\) \*/ /\* \([0-9]*\) \*/.*@\2@')
endef

%.dot: %.rs Makefile
	$(eval $(call FIND_LAST_FN,$<))
	$(RUSTC_LIB) -Z flowgraph-print-needs-drop --pretty flowgraph=$(LAST_FN_NUM_$<) $< -o $@
