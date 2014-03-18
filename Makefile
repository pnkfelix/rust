default: smoke-test

RUSTC=./objdir-dbgopt/x86_64-apple-darwin/stage2/bin/rustc
RUSTC_SRC=$(shell find src/libsyntax src/librustc -name '*.rs')
cfg.bin: cfg/mod.rs cfg/*.rs $(RUSTC) Makefile
	$(RUSTC) -g $< -o $@

./objdir-dbgopt/x86_64-apple-darwin/stage2/bin/rustc: $(RUSTC_SRC)
	remake --trace -j8 -C ./objdir-dbgopt/ --environment-overrides WFLAGS_ST0=-Awarnings

smoke-test: cfg.bin
	RUST_LOG=rustc,cfg ./cfg.bin
