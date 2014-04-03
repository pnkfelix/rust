default: smoke-test

RUSTC=$(RUSTC_STAGE0)

RUST_OBJDIR=./objdir-dbg
TGT=x86_64-apple-darwin

RUSTC_STAGE1=$(RUST_OBJDIR)/$(TGT)/stage1/bin/rustc
RUSTC_STAGE0=$(RUST_OBJDIR)/$(TGT)/stage0/bin/rustc
RUSTC_STAGE0_STAMP=$(TGT)/stage0/lib/rustlib/$(TGT)/lib/stamp.rustc
RUSTC_STAGE1_STAMP=$(TGT)/stage1/lib/rustlib/$(TGT)/lib/stamp.rustc

RUSTC_SRC=$(shell find src/libsyntax src/librustc -name '*.rs')


cfg.bin: cfg/mod.rs cfg/*.rs cfg/*/*.rs $(RUSTC) Makefile
	time $(RUSTC) -g $< -o $@

# $(info RUSTC_SRC,$(RUSTC_SRC))

$(RUST_OBJDIR)/$(RUSTC_STAGE0_STAMP): $(RUSTC_SRC)
	remake --trace -j8 -C $(RUST_OBJDIR) --environment-overrides WFLAGS_ST0=-Awarnings $(RUSTC_STAGE0_STAMP)

$(RUST_OBJDIR)/$(RUSTC_STAGE1_STAMP): $(RUSTC_SRC)
	remake --trace -j8 -C $(RUST_OBJDIR) --environment-overrides WFLAGS_ST0=-Awarnings $(RUSTC_STAGE1_STAMP) rustc-stage1

$(RUSTC_STAGE1): $(RUST_OBJDIR)/$(RUSTC_STAGE1_STAMP)

$(RUSTC_STAGE0): $(RUST_OBJDIR)/$(RUSTC_STAGE0_STAMP)

smoke-test: cfg.bin $(RUSTC)
	RUST_BACKTRACE=1 RUST_LOG=rustc,cfg ./cfg.bin loans l_loop_while_v_bw_if_w_and_x_by_break_l_else_call_z
