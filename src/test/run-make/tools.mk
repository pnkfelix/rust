export LD_LIBRARY_PATH:=$(TMPDIR):$(LD_LIBRARY_PATH)
export DYLD_LIBRARY_PATH:=$(TMPDIR):$(DYLD_LIBRARY_PATH)

RUSTC := $(RUSTC) --out-dir $(TMPDIR) -L $(TMPDIR)
CC := $(CC) -L $(TMPDIR)

# This is the name of the binary we will generate and run; use this
# e.g. for `$(CC) -o $(RUN_BINFILE)`.
RUN_BINFILE = $(TMPDIR)/$(1)
# This the basic way we will invoke the generated binary.  It sets the
# LD_LIBRARY_PATH environment variable before running the binary.
RUN = $(TARGET_RPATH_ENV) $(RUN_BINFILE)
FAIL = $(TARGET_RPATH_ENV) $(RUN_BINFILE) && exit 1 || exit 0

RLIB_GLOB = lib$(1)*.rlib
STATICLIB = $(TMPDIR)/lib$(1).a
STATICLIB_GLOB = lib$(1)*.a
BIN = $(1)

UNAME = $(shell uname)
ifneq (,$(findstring MINGW,$(UNAME)))
IS_WINDOWS=1
endif

ifeq ($(UNAME),Darwin)
DYLIB_GLOB = lib$(1)*.dylib
DYLIB = $(TMPDIR)/lib$(1).dylib
RPATH_LINK_SEARCH =
else
ifdef IS_WINDOWS
DYLIB_GLOB = $(1)*.dll
DYLIB = $(TMPDIR)/$(1).dll
BIN = $(1).exe
RPATH_LINK_SEARCH =
export PATH := $(PATH):$(LD_LIBRARY_PATH)
else
DYLIB_GLOB = lib$(1)*.so
DYLIB = $(TMPDIR)/lib$(1).so
RPATH_LINK_SEARCH = -Wl,-rpath-link=$(1)
endif
endif

REMOVE_DYLIBS     = rm $(TMPDIR)/$(call DYLIB_GLOB,$(1))
REMOVE_RLIBS      = rm $(TMPDIR)/$(call RLIB_GLOB,$(1))

%.a: %.o
	ar crus $@ $<
%.dylib: %.o
	$(CC) -dynamiclib -Wl,-dylib -o $@ $<
%.so: %.o
	$(CC) -o $@ $< -shared
%.dll: lib%.o
	$(CC) -o $@ $< -shared

$(TMPDIR)/lib%.o: %.c
	$(CC) -c -o $@ $<

