default: smoke-test

RUST_OBJDIR=./objdir-dbg
RUSTC=$(RUST_OBJDIR)/x86_64-apple-darwin/stage1/bin/rustc
RUSTC_SRC=$(shell find src/libsyntax src/librustc -name '*.rs')
cfg.bin: cfg/mod.rs cfg/*.rs cfg/*/*.rs $(RUSTC) Makefile
	time $(RUSTC) -g $< -o $@

# $(info RUSTC_SRC,$(RUSTC_SRC))

$(RUSTC): $(RUSTC_SRC)
	remake --trace -j8 -C $(RUST_OBJDIR) --environment-overrides WFLAGS_ST0=-Awarnings rustc-stage1

smoke-test: cfg.bin $(RUSTC)
	RUST_BACKTRACE=1 RUST_LOG=rustc,cfg ./cfg.bin loans l_loop_while_v_bw_if_w_and_x_by_break_l_else_call_z
