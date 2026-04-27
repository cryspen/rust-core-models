AENEAS_DIR = $$HOME/cryspen/aeneas
CHARON = $(AENEAS_DIR)/charon/bin/charon
AENEAS = $(AENEAS_DIR)/bin/aeneas

CRATE_NAME = aeneas_test
LLBC_FILE = $(CRATE_NAME).llbc
LEAN_DIR = lean
# `-subdir AeneasTest` makes Aeneas place its output at
# $(LEAN_DIR)/AeneasTest/ AND emit `import AeneasTest.<X>` rather than
# the auto-derived module prefix.
SUBDIR = AeneasTest

.PHONY: all llbc extract build clean

all: build

# 1. Run charon to produce LLBC from the Rust crate. Same Aeneas preset
#    as `test-suite/`, no exclusions — we want every reference to surface.
$(LLBC_FILE): src/lib.rs Cargo.toml
	$(CHARON) cargo --preset=aeneas --dest-file $(LLBC_FILE)

llbc: $(LLBC_FILE)

# 2. Run Aeneas to extract Lean files into $(LEAN_DIR)/$(SUBDIR)/, then
#    apply the parent's downstream-extraction patcher (allocator
#    stripping for Vec/Drain/IntoIter, slice-aliasing). The `noncomputable
#    section` insertion mirrors test-suite/Makefile and is needed because
#    several `alloc.vec.Vec.*` defs we reference are noncomputable.
extract: $(LLBC_FILE)
	mkdir -p $(LEAN_DIR)
	$(AENEAS) -backend lean $(LLBC_FILE) -split-files \
		-dest $(LEAN_DIR) -subdir $(SUBDIR)
	python3 ../patch_lean.py --downstream-dir $(LEAN_DIR)/$(SUBDIR)
	for f in $(LEAN_DIR)/$(SUBDIR)/*.lean; do \
	    grep -q '^noncomputable section' "$$f" || \
	        sed -i '/^set_option maxHeartbeats/a \\nnoncomputable section' "$$f"; \
	done
	# Strip axiom bodies from external templates and rename to drop
	# the `_Template` suffix so Lake's `roots` picks them up.
	for f in $(LEAN_DIR)/$(SUBDIR)/FunsExternal_Template.lean \
	         $(LEAN_DIR)/$(SUBDIR)/TypesExternal_Template.lean; do \
	    [ -f "$$f" ] || continue; \
	    out=$$(echo "$$f" | sed 's/_Template//'); \
	    sed -n '1,/^set_option maxHeartbeats/p' "$$f" > "$$out"; \
	    rm -f "$$f"; \
	done
	# Empty stubs for any external file Aeneas didn't emit.
	for stub in $(LEAN_DIR)/$(SUBDIR)/FunsExternal.lean \
	            $(LEAN_DIR)/$(SUBDIR)/TypesExternal.lean; do \
	    [ -f "$$stub" ] && continue; \
	    printf '%s\n' "import Aeneas" > "$$stub"; \
	done

# 3. Build the Lean library — this is the actual test.
build: extract
	cd $(LEAN_DIR) && lake build

clean:
	rm -f $(LLBC_FILE)
	rm -rf $(LEAN_DIR)/$(SUBDIR)
	rm -rf $(LEAN_DIR)/.lake
