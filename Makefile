FILES= test.bin
# FILES= test_gensym.bin test.bin

all: $(patsubst %.rs,%.dot,$(FILES))

RUSTC_LIB=$(RUSTC) --crate-type=lib

STAGE=stage2

RUSTC ?= objdir-dbg/x86_64-apple-darwin/$(STAGE)/rustc

rwildcard=$(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2) \
  $(filter $(subst *,%,$2),$d))

objdir-dbg/x86_64-apple-darwin/$(STAGE)/rustc: src/etc/rustc-wrapper.macosx.sh objdir-dbg/x86_64-apple-darwin/$(STAGE)/bin/rustc Makefile $(call rwildcard,src/,*.rs)
	cd objdir-dbg && make-rustc-$(STAGE)
	cp $< $@
	chmod +x $@

RUST_LOG=rustc::middle::borrowck,rustc::middle::ty,rustc::middle::typeck,rustc::middle::expr_use_visitor,rustc::middle::region,rustc::middle::trans

%.dylib: %.rs Makefile objdir-dbg/x86_64-apple-darwin/$(STAGE)/rustc
	$(RUSTC) $<

%.bin: %.rs Makefile objdir-dbg/x86_64-apple-darwin/$(STAGE)/rustc
	$(RUSTC) $< -L. -o $@

test.bin: plugin.dylib

test_gensym.bin: gensym.dylib

%.dot: %.rs Makefile objdir-dbg/x86_64-apple-darwin/$(STAGE)/rustc
	$(RUSTC) -Z flowgraph-print-all --pretty flowgraph=% $< -o $@

%.pp: %.rs Makefile objdir-dbg/x86_64-apple-darwin/$(STAGE)/rustc
	$(RUSTC)                        --pretty expanded,identified $< -o $@

%.log: %.rs Makefile objdir-dbg/x86_64-apple-darwin/$(STAGE)/rustc
	RUST_LOG=$(RUST_LOG) RUST_BACKTRACE=1 $(RUSTC_LIB) $< 2> $@
