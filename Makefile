FILES=foo1.rs foo2.rs foo3.rs foo4.rs foo5.rs foo6.rs foo7.rs foo8.rs

all: $(patsubst %.rs,%.dot,$(FILES))

RUSTC_LIB=$(RUSTC) --crate-type=lib

RUSTC ?= objdir-dbg/x86_64-apple-darwin/stage1/rustc

rwildcard=$(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2) \
  $(filter $(subst *,%,$2),$d))

objdir-dbg/x86_64-apple-darwin/stage1/rustc: src/etc/rustc-wrapper.macosx.sh objdir-dbg/x86_64-apple-darwin/stage1/bin/rustc Makefile $(call rwildcard,src/,*.rs)
	cd objdir-dbg && make-rustc-stage1 --no-libs
	cp $< $@
	chmod +x $@

%.dot: %.rs Makefile objdir-dbg/x86_64-apple-darwin/stage1/rustc
	$(RUSTC_LIB) -Z flowgraph-print-needs-drop --pretty flowgraph=foo $< -o $@
