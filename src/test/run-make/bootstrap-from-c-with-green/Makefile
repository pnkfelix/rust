-include ../tools.mk

all:
	env
	$(RUSTC) lib.rs
	ln -nsf $(call DYLIB,boot-*) $(call DYLIB,boot)
	$(CC) main.c -o $(call RUN_BINFILE,main) -lboot
	$(call RUN,main)
	$(call REMOVE_DYLIBS,boot)
	$(call FAIL,main)
