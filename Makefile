FILES= test.bin
# FILES= test_gensym.bin test.bin

all: $(patsubst %.rs,%.dot,$(FILES))

STAGE=stage2
OBJDIR=objdir-dbgopt

RUSTC ?= $(OBJDIR)/x86_64-apple-darwin/$(STAGE)/rustc

define RUSTLIB_STAMP
  x86_64-apple-darwin/$(STAGE)/lib/rustlib/x86_64-apple-darwin/lib/stamp.$(1)
endef

RUSTC_SUPPORT_LIBS= $(OBJDIR)/$(call RUSTLIB_STAMP,syntax) \
                    $(OBJDIR)/$(call RUSTLIB_STAMP,rustc)

rwildcard=$(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2) \
  $(filter $(subst *,%,$2),$d))

$(OBJDIR)/x86_64-apple-darwin/$(STAGE)/bin/rustc: $(call rwildcard,src/,*.rs)
	$(MAKE) -C $(OBJDIR) x86_64-apple-darwin/$(STAGE)/bin/rustc

$(OBJDIR)/$(call RUSTLIB_STAMP,syntax):
	$(MAKE) -C $(OBJDIR) $(call RUSTLIB_STAMP,syntax)

$(OBJDIR)/$(call RUSTLIB_STAMP,rustc):
	$(MAKE) -C $(OBJDIR) $(call RUSTLIB_STAMP,rustc)

$(OBJDIR)/x86_64-apple-darwin/$(STAGE)/rustc: src/etc/rustc-wrapper.macosx.sh $(OBJDIR)/x86_64-apple-darwin/$(STAGE)/bin/rustc Makefile
	cd $(OBJDIR) && make-rustc-$(STAGE)
	cp $< $@
	chmod +x $@

RUST_LOG=rustc::middle::borrowck,rustc::middle::ty,rustc::middle::typeck,rustc::middle::expr_use_visitor,rustc::middle::region,rustc::middle::trans,syntax

%.dylib: %.rs Makefile $(RUSTC)
	$(RUSTC) $<

plugin.dylib: $(RUSTC_SUPPORT_LIBS)

%.bin: %.rs Makefile $(RUSTC)
	$(RUSTC) $< -L. -o $@

test.bin: plugin.dylib

test_gensym.bin: gensym.dylib

%.dot: %.rs Makefile $(RUSTC)
	$(RUSTC) -Z flowgraph-print-all --pretty flowgraph=% $< -o $@

%.pp: %.rs Makefile $(RUSTC)
	$(RUSTC)                        --pretty expanded,identified $< -o $@

#%.log: %.rs Makefile $(RUSTC)
#	RUST_LOG=$(RUST_LOG) RUST_BACKTRACE=1 $(RUSTC) --crate-type=lib $< 2> $@

test.log: test.rs Makefile $(RUSTC) plugin.dylib
	RUST_LOG=$(RUST_LOG) RUST_BACKTRACE=1 $(RUSTC) test.rs -L. -o test.bin > $@ 2>&1
