BUILD_DIR=./objdir-dbgopt
RUSTC=$(BUILD_DIR)/x86_64-apple-darwin/stage2/bin/rustc

cheney-test: cheney-play
	./cheney-play

sro-test: sro-play-debug sro-play
	./sro-play-debug
	./sro-play

%-play: %-play.rs $(RUSTC)
	$(RUSTC) -o $@ $<

%-play-debug: %-play.rs $(RUSTC)
	$(RUSTC) -o $@ -Z debug-info -Z extra-debug-info $<

.PHONY: rustc

$(RUSTC): rustc
	cd $(BUILD_DIR) && make
