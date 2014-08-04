FILES_WARN=foo01_warn.rs               foo03_warn.rs foo04_warn.rs foo05_warn.rs \
           foo06_warn.rs foo07_warn.rs foo08_warn.rs foo09_warn.rs foo10_warn.rs \
                         foo17_warn.rs foo18_warn.rs                             \
                                                                   foo25_warn.rs \
           foo26_warn.rs foo27_warn.rs foo28_warn.rs                             \
           foo31_warn.rs

FILES_FINE=              foo02_fine.rs                                           \
           foo11_fine.rs foo12_fine.rs foo13_fine.rs foo14_fine.rs foo15_fine.rs \
                                       foo23_fine.rs foo24_fine.rs               \
                                                     foo29_fine.rs foo30_fine.rs

FILES_UNCATEGORIZED=                                                             \
           foo16.rs                                  foo19.rs      foo20.rs      \
           foo21.rs      foo22.rs                                                \
           dlist01.rs \
           iter1.rs iter2.rs \
           num01.rs \
           option01.rs \
           result01.rs result02.rs result03.rs \
           str01.rs

FILES=$(FILES_WARN) $(FILES_FINE) $(FILES_UNCATEGORIZED)

all: $(patsubst %.rs,%.dot,$(FILES))
.PHONY: touch_fine
touch_fine:
	touch *fine.rs
.PHONY: touch_warn
touch_warn:
	touch *warn.rs
.PHONY: fine
fine: touch_fine $(patsubst %.rs,%.dot,$(FILES_FINE))
.PHONY: warn
warn: touch_warn $(patsubst %.rs,%.dot,$(FILES_WARN))

RUSTC_LIB=$(RUSTC) --crate-type=lib

RUSTC ?= objdir-dbg/x86_64-apple-darwin/stage1/rustc

rwildcard=$(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2) \
  $(filter $(subst *,%,$2),$d))

objdir-dbg/x86_64-apple-darwin/stage1/rustc: src/etc/rustc-wrapper.macosx.sh objdir-dbg/x86_64-apple-darwin/stage1/bin/rustc Makefile $(call rwildcard,src/,*.rs)
	cd objdir-dbg && make-rustc-stage1 --no-libs
	cp $< $@
	chmod +x $@

RUST_LOG=rustc::middle::borrowck,rustc::middle::ty,rustc::middle::typeck,rustc::middle::expr_use_visitor,rustc::middle::region,rustc::middle::trans,rustc::middle::resolve

%.dot: %.rs Makefile objdir-dbg/x86_64-apple-darwin/stage1/rustc
	$(RUSTC_LIB) -Z flowgraph-print-all --pretty flowgraph=foo $< -o $@

%.pp: %.rs Makefile objdir-dbg/x86_64-apple-darwin/stage1/rustc
	$(RUSTC_LIB)                        --pretty expanded,identified $< -o $@

%.log: %.rs Makefile objdir-dbg/x86_64-apple-darwin/stage1/rustc
	RUST_LOG=$(RUST_LOG) RUST_BACKTRACE=1 $(RUSTC_LIB) $< 2> $@

#	RUST_LOG=$(RUST_LOG) $(RUSTC_LIB) -Z flowgraph-print-all --pretty flowgraph=foo $< -o $@.dot 2> $@
