FILES=foo1.rs foo2.rs  foo3.rs  foo4.rs  foo5.rs  foo6.rs  foo7.rs  foo8.rs \
      foo9.rs         foo11.rs foo12.rs foo13.rs foo14.rs \
      dlist01.rs \
      iter1.rs iter2.rs \
      num01.rs \
      option01.rs \
      result01.rs result02.rs result03.rs \
      str01.rs

all: $(patsubst %.rs,%.dot,$(FILES))

RUSTC_LIB=$(RUSTC) --crate-type=lib

RUSTC ?= objdir-dbg/x86_64-apple-darwin/stage1/rustc

rwildcard=$(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2) \
  $(filter $(subst *,%,$2),$d))

objdir-dbg/x86_64-apple-darwin/stage1/rustc: src/etc/rustc-wrapper.macosx.sh objdir-dbg/x86_64-apple-darwin/stage1/bin/rustc Makefile $(call rwildcard,src/,*.rs)
	cd objdir-dbg && make-rustc-stage1 --no-libs
	cp $< $@
	chmod +x $@

RUST_LOG=rustc::middle::borrowck,rustc::middle::ty,rustc::middle::typeck,rustc::middle::expr_use_visitor,rustc::middle::region,rustc::middle::trans

%.dot: %.rs Makefile objdir-dbg/x86_64-apple-darwin/stage1/rustc
	$(RUSTC_LIB) -Z flowgraph-print-all --pretty flowgraph=foo $< -o $@

%.pp: %.rs Makefile objdir-dbg/x86_64-apple-darwin/stage1/rustc
	$(RUSTC_LIB)                        --pretty expanded,identified $< -o $@

%.log: %.rs Makefile objdir-dbg/x86_64-apple-darwin/stage1/rustc
	RUST_LOG=$(RUST_LOG) RUST_BACKTRACE=1 $(RUSTC_LIB) $< 2> $@

#	RUST_LOG=$(RUST_LOG) $(RUSTC_LIB) -Z flowgraph-print-all --pretty flowgraph=foo $< -o $@.dot 2> $@
