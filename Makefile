default: smoke-test

RUSTC=./objdir-dbgopt/x86_64-apple-darwin/stage2/bin/rustc
RUSTC_SRC=$(shell find src/libsyntax src/librustc -name '*.rs')
cfg.bin: cfg.rs cfg/*.rs $(RUSTC)
	$(RUSTC) --debuginfo 2 cfg.rs -o $@

./objdir-dbgopt/x86_64-apple-darwin/stage2/bin/rustc: $(RUSTC_SRC)
	remake --trace -j8 -C ./objdir-dbgopt/

smoke-test: cfg.bin
	RUST_LOG=rustc,cfg ./cfg.bin
