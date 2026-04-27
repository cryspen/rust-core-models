AENEAS_DIR = $$HOME/cryspen/aeneas
CHARON = $(AENEAS_DIR)/charon/bin/charon
AENEAS = $(AENEAS_DIR)/bin/aeneas

CRATE_NAME = core_models_test_suite
LLBC_FILE = $(CRATE_NAME).llbc
LEAN_DIR = lean
# `-subdir TestSuite` makes Aeneas place its output at $(LEAN_DIR)/TestSuite/
# AND emit `import TestSuite.<X>` rather than the auto-derived module prefix.
SUBDIR = TestSuite

.PHONY: all llbc extract build clean

all: build

# 1. Run charon to produce LLBC from the Rust crate.
$(LLBC_FILE): src/lib.rs Cargo.toml
	$(CHARON) cargo --preset=aeneas --dest-file $(LLBC_FILE)

llbc: $(LLBC_FILE)

# 2. Run Aeneas to extract Lean files directly into $(LEAN_DIR)/$(SUBDIR)/.
extract: $(LLBC_FILE)
	mkdir -p $(LEAN_DIR)
	$(AENEAS) -backend lean $(LLBC_FILE) -split-files \
		-dest $(LEAN_DIR) -subdir $(SUBDIR)
	# The parent's `Aeneas.Alloc.Funs` provides `vec.Vec.*` as 1-arg
	# functions (`Vec α`, no explicit allocator). Aeneas extracts the
	# test crate's std `Vec<u32>` references with the original 2-arg
	# shape including a `Global` allocator. Strip both:
	#   `(v : alloc.vec.Vec T Global)` -> `(v : alloc.vec.Vec T)`
	#   `alloc.vec.Vec.foo Global v ...` -> `alloc.vec.Vec.foo v ...`
	# Also insert `noncomputable section` after the `set_option` block so
	# the calls to (noncomputable) `alloc.vec.Vec.push` etc. compile.
	# Apply the parent's allocator-stripping + slice aliasing transforms to
	# the freshly extracted test-suite files. Keeps the regex/transform
	# logic in one place (../patch_lean.py).
	python3 ../patch_lean.py --downstream-dir $(LEAN_DIR)/$(SUBDIR)
	for f in $(LEAN_DIR)/$(SUBDIR)/*.lean; do \
	    grep -q '^noncomputable section' "$$f" || \
	        sed -i '/^set_option maxHeartbeats/a \\nnoncomputable section' "$$f"; \
	done
	# Aeneas emits `*_Template.lean` files containing `axiom` stubs for
	# items whose body it can't see (here: `alloc::vec::Vec::*`, since the
	# test crate uses `std::vec::Vec` opaquely). The parent's
	# `Aeneas.Alloc.Funs` already provides defs for those names, so we
	# strip the axiom bodies and rename the templates to drop the
	# `_Template` suffix so Lake's `roots` picks them up.
	for f in $(LEAN_DIR)/$(SUBDIR)/FunsExternal_Template.lean \
	         $(LEAN_DIR)/$(SUBDIR)/TypesExternal_Template.lean; do \
	    [ -f "$$f" ] || continue; \
	    out=$$(echo "$$f" | sed 's/_Template//'); \
	    sed -n '1,/^set_option maxHeartbeats/p' "$$f" > "$$out"; \
	    rm -f "$$f"; \
	done
	# Create empty stubs for any external file Aeneas didn't emit (Lake's
	# `roots` insists they exist).
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
