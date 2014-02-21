default: smoke-test

RUSTC=./objdir-dbgopt/x86_64-apple-darwin/stage2/bin/rustc
RUSTC_SRC=$(shell find src/libsyntax src/librustc -name '*.rs')
cfg.bin: cfg.rs cfg/*.rs $(RUSTC)
	$(RUSTC) --debuginfo cfg.rs -o $@

./objdir-dbgopt/x86_64-apple-darwin/stage2/bin/rustc: $(RUSTC_SRC)
	make -C ./objdir-dbgopt/

smoke-test: cfg.bin
	./cfg.bin
