default: smoke-test

RUSTC=./objdir-dbgopt/x86_64-apple-darwin/stage2/bin/rustc
RUSTC_SRC=$(shell find src/libsyntax src/librustc -name '*.rs')
cfg: cfg.rs $(RUSTC)
	$(RUSTC) cfg.rs

./objdir-dbgopt/x86_64-apple-darwin/stage2/bin/rustc: $(RUSTC_SRC)
	make -C ./objdir-dbgopt/Makefile

smoke-test: cfg
	./cfg
