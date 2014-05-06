-include ../tools.mk

# This hits an assertion in the linker on older versions of osx apparently
ifeq ($(shell uname),Darwin)
all:
	echo ignored
else
all: $(call DYLIB,cfoo)
	$(RUSTC) foo.rs
	$(RUSTC) bar.rs
	LD_LIBRARY_PATH=$(TMPDIR) $(call RUN,bar)
	$(call REMOVE_DYLIBS,cfoo)
	$(call FAIL,bar)
endif
