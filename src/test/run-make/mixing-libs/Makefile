-include ../tools.mk

all:
	$(RUSTC) rlib.rs
	$(RUSTC) dylib.rs && exit 1 || exit 0
	$(RUSTC) rlib.rs --crate-type=dylib
	$(RUSTC) dylib.rs
	$(call REMOVE_DYLIBS,rlib)
	$(RUSTC) prog.rs && exit 1 || exit 0
