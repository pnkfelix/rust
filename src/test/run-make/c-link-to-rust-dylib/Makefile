-include ../tools.mk

all:
	$(RUSTC) foo.rs
	ln -s $(call DYLIB,foo-*) $(call DYLIB,foo)
	$(CC) bar.c -lfoo -o $(call RUN_BINFILE,bar) -Wl,-rpath,$(TMPDIR)
	$(call RUN,bar)
	$(call REMOVE_DYLIBS,foo)
	$(call FAIL,bar)
