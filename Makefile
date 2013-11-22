BUILD_DIR=./objdir-dbgopt
RUSTC=$(BUILD_DIR)/x86_64-apple-darwin/stage2/bin/rustc

sro-test: sro-play-debug sro-play
	./sro-play-debug
	./sro-play

sro-play: sro-play.rs $(RUSTC)
	$(RUSTC) -o $@ $<

sro-play-debug: sro-play.rs $(RUSTC)
	$(RUSTC) -o $@ -Z debug-info -Z extra-debug-info $<

.PHONY: rustc

$(RUSTC): rustc
	cd $(BUILD_DIR) && make
