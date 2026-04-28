CHARON ?= charon
AENEAS ?= aeneas

CRATE_NAME = tests
LLBC_FILE = $(CRATE_NAME).llbc
LEAN_DIR = lean
# `-subdir Tests` makes Aeneas place its output at $(LEAN_DIR)/Tests/ AND
# emit `import Tests.<X>` rather than the auto-derived module prefix.
SUBDIR = Tests

.PHONY: all llbc extract fix build clean

all: build

# 1. Run charon to produce LLBC from the Rust crate.
$(LLBC_FILE): src/lib.rs Cargo.toml
	$(CHARON) cargo --preset=aeneas --dest-file $(LLBC_FILE)

llbc: $(LLBC_FILE)

# 2. Run Aeneas to extract Lean files into $(LEAN_DIR)/$(SUBDIR)/.
extract: $(LLBC_FILE)
	$(AENEAS) -backend lean $(LLBC_FILE) -split-files \
		-dest $(LEAN_DIR) -subdir $(SUBDIR)
	# Aeneas writes `*External_Template.lean` files alongside its
	# real output. Our hand-written `FunsExternal.lean` /
	# `TypesExternal.lean` stubs satisfy the imports — drop the
	# templates so Lake doesn't pick them up by mistake.
	rm -f $(LEAN_DIR)/$(SUBDIR)/FunsExternal_Template.lean
	rm -f $(LEAN_DIR)/$(SUBDIR)/TypesExternal_Template.lean

# 3. Fix the `import`s and `open`s in the generated file:
fix: extract
	sed -i \
		'/^open Aeneas /c\open CoreModels Aeneas\nopen Aeneas.Std hiding namespace core alloc\nopen Result ControlFlow Error' \
		$(LEAN_DIR)/$(SUBDIR)/Funs.lean
	sed -i \
		's/import Aeneas/import CoreModels/' \
		$(LEAN_DIR)/$(SUBDIR)/Funs.lean

# 4. Build the Lean library — this is the actual test.
build: fix
	cd $(LEAN_DIR) && lake build

# Only remove files Aeneas re-generates; keep the hand-written
# `FunsExternal.lean` / `TypesExternal.lean` stubs in $(SUBDIR).
clean:
	rm -f $(LLBC_FILE)
	rm -f $(LEAN_DIR)/$(SUBDIR)/Funs.lean
	rm -f $(LEAN_DIR)/$(SUBDIR)/Types.lean
	rm -f $(LEAN_DIR)/$(SUBDIR)/FunsExternal_Template.lean
	rm -f $(LEAN_DIR)/$(SUBDIR)/TypesExternal_Template.lean
	rm -rf $(LEAN_DIR)/.lake
