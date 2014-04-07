default: smoke-test

RUSTC=$(RUSTC_STAGE1)

RUST_OBJDIR=./objdir-dbg
TGT=x86_64-apple-darwin

.PHONY: force-make-rustc-stage0
force-rebuild-rustc-stage0:
	time remake --trace -j8 -C $(RUST_OBJDIR) --environment-overrides WFLAGS_ST0=-Awarnings $(STAGE0_STAMP_RUSTC) rustc-stage1

.PHONY: force-make-rustc-stage1
force-rebuild-rustc-stage1:
	time remake --trace -j8 -C $(RUST_OBJDIR) --environment-overrides WFLAGS_ST0=-Awarnings $(STAGE1_STAMP_RUSTC) rustc-stage1

RUSTC_STAGE1=$(RUST_OBJDIR)/$(TGT)/stage1/bin/rustc
RUSTC_STAGE0=$(RUST_OBJDIR)/$(TGT)/stage0/bin/rustc
STAGE0_STAMP_RUSTC=$(TGT)/stage0/lib/rustlib/$(TGT)/lib/stamp.rustc
STAGE1_STAMP_RUSTC=$(TGT)/stage1/lib/rustlib/$(TGT)/lib/stamp.rustc

RUSTC_SRC=$(shell find src/libsyntax src/librustc -name '*.rs')

cfg.bin: cfg/mod.rs cfg/*.rs cfg/*/*.rs $(RUSTC)
	time $(RUSTC) -g $< -o $@

$(RUSTC_STAGE1): force-rebuild-rustc-stage1

$(RUSTC_STAGE0): force-rebuild-rustc-stage0

smoke-test: cfg.bin $(RUSTC)
	RUST_BACKTRACE=1 RUST_LOG=rustc,cfg,syntax::ext::mtwt ./cfg.bin loans l_while_x_break_l loans just_x
#	RUST_BACKTRACE=1 RUST_LOG=rustc,cfg ./cfg.bin loans '*'
