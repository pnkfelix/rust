# Extract the snapshot host compiler



$(HBIN0_H_$(CFG_BUILD_TRIPLE))/rustc$(X_$(CFG_BUILD_TRIPLE)):		\
		$(S)src/snapshots.txt					\
		$(S)src/etc/get-snapshot.py $(MKFILE_DEPS)
	@$(call E, fetch: $@)
#   Note: the variable "SNAPSHOT_FILE" is generally not set, and so
#   we generally only pass one argument to this script.
ifdef CFG_ENABLE_LOCAL_RUST
	$(Q)$(C) $(S)src/etc/local_stage0.sh $(CFG_BUILD_TRIPLE) $(CFG_LOCAL_RUST_ROOT)
else
	$(Q)$(C) $(CFG_PYTHON) $(S)src/etc/get-snapshot.py $(CFG_BUILD_TRIPLE) $(SNAPSHOT_FILE)
ifdef CFG_ENABLE_PAX_FLAGS
	@$(call E, apply PaX flags: $@)
	@"$(CFG_PAXCTL)" -cm "$@"
endif
endif
	$(Q)$(C) touch $@

# Host libs will be extracted by the above rule

$(HLIB0_H_$(CFG_BUILD_TRIPLE))/$(CFG_RUNTIME_$(CFG_BUILD_TRIPLE)): \
		$(HBIN0_H_$(CFG_BUILD_TRIPLE))/rustc$(X_$(CFG_BUILD_TRIPLE))
	$(Q)$(C) touch $@

$(HLIB0_H_$(CFG_BUILD_TRIPLE))/$(CFG_STDLIB_$(CFG_BUILD_TRIPLE)): \
		$(HBIN0_H_$(CFG_BUILD_TRIPLE))/rustc$(X_$(CFG_BUILD_TRIPLE))
	$(Q)$(C) touch $@

$(HLIB0_H_$(CFG_BUILD_TRIPLE))/$(CFG_EXTRALIB_$(CFG_BUILD_TRIPLE)): \
		$(HBIN0_H_$(CFG_BUILD_TRIPLE))/rustc$(X_$(CFG_BUILD_TRIPLE))
	$(Q)$(C) touch $@

$(HLIB0_H_$(CFG_BUILD_TRIPLE))/$(CFG_LIBRUSTC_$(CFG_BUILD_TRIPLE)): \
		$(HBIN0_H_$(CFG_BUILD_TRIPLE))/rustc$(X_$(CFG_BUILD_TRIPLE))
	$(Q)$(C) touch $@

$(HLIB0_H_$(CFG_BUILD_TRIPLE))/$(CFG_RUSTLLVM_$(CFG_BUILD_TRIPLE)): \
		$(HBIN0_H_$(CFG_BUILD_TRIPLE))/rustc$(X_$(CFG_BUILD_TRIPLE))
	$(Q)$(C) touch $@

# For other targets, let the host build the target:

define BOOTSTRAP_STAGE0
  # $(1) target to bootstrap
  # $(2) stage to bootstrap from
  # $(3) target to bootstrap from

$$(HBIN0_H_$(1))/rustc$$(X_$(1)):								\
		$$(TBIN$(2)_T_$(1)_H_$(3))/rustc$$(X_$(1))
	@$$(call E, cp: $$@)
	$$(Q)$(C) cp $$< $$@

$$(HLIB0_H_$(1))/$(CFG_RUNTIME_$(1)): \
		$$(TLIB$(2)_T_$(1)_H_$(3))/$(CFG_RUNTIME_$(1))
	@$$(call E, cp: $$@)
	$$(Q)$(C) cp $$< $$@

$$(HLIB0_H_$(1))/$(CFG_STDLIB_$(1)): \
		$$(TLIB$(2)_T_$(1)_H_$(3))/$(CFG_STDLIB_$(1))
	@$$(call E, cp: $$@)
	$$(Q)$(C) cp $$(TLIB$(2)_T_$(1)_H_$(3))/$(STDLIB_GLOB_$(1)) $$@

$$(HLIB0_H_$(1))/$(CFG_EXTRALIB_$(1)): \
		$$(TLIB$(2)_T_$(1)_H_$(3))/$(CFG_EXTRALIB_$(1))
	@$$(call E, cp: $$@)
	$$(Q)$(C) cp $$(TLIB$(2)_T_$(1)_H_$(3))/$(EXTRALIB_GLOB_$(1)) $$@

$$(HLIB0_H_$(1))/$(CFG_LIBRUSTC_$(1)): \
		$$(TLIB$(2)_T_$(1)_H_$(3))/$(CFG_LIBRUSTC_$(1))
	@$$(call E, cp: $$@)
	$$(Q)$(C) cp $$(TLIB$(2)_T_$(1)_H_$(3))/$(LIBRUSTC_GLOB_$(1)) $$@

$$(HLIB0_H_$(1))/$(CFG_RUSTLLVM_$(1)): \
		$$(TLIB$(2)_T_$(1)_H_$(3))/$(CFG_RUSTLLVM_$(1))
	@$$(call E, cp: $$@)
	$$(Q)$(C) cp $$< $$@

endef

# Use stage1 to build other architectures: then you don't have to wait
# for stage2, but you get the latest updates to the compiler source.
$(foreach t,$(NON_BUILD_HOST_TRIPLES),								\
 $(eval $(call BOOTSTRAP_STAGE0,$(t),1,$(CFG_BUILD_TRIPLE))))
