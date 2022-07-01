BUILD_ROOT = build
SYSROOT = ./sysroot

ifdef RELEASE
	BUILD_DIR = $(BUILD_ROOT)/release
	CARGO_FLAGS = --release
	CARGO_TARGET_DIR = target/release
	CFLAGS += -O3
	ALUMINA_FLAGS += --sysroot $(SYSROOT) --timings
else
	BUILD_DIR = $(BUILD_ROOT)/debug
	CARGO_FLAGS =
	CARGO_TARGET_DIR = target/debug
	CFLAGS += -g3 -fPIE -rdynamic
	ALUMINA_FLAGS += --sysroot $(SYSROOT) --debug --timings
endif

LDFLAGS = -lm
ifndef NO_THREADS
	ALUMINA_FLAGS += --cfg threading
	LDFLAGS += -lpthread
endif

ALUMINA_BOOT = $(BUILD_DIR)/alumina-boot
ALUMINAC = $(BUILD_DIR)/aluminac
ALUMINAC_TESTS = $(BUILD_DIR)/aluminac-tests
CODEGEN = $(BUILD_DIR)/aluminac-generate
STDLIB_TESTS = $(BUILD_DIR)/stdlib-tests

# If grammar changes, we need to rebuild the world
COMMON_SOURCES = common/grammar.js
BOOTSTRAP_SOURCES = $(shell find src/alumina-boot/ -type f)
SYSROOT_FILES = $(shell find $(SYSROOT) -type f -name '*.alu')
ALU_LIBRARIES = $(shell find libraries/ -type f -name '*.alu')

SELFHOSTED_SOURCES = $(shell find src/aluminac/ -type f -name '*.alu')
CODEGEN_SOURCES = $(shell find tools/tree-sitter-codegen/ -type f -name '*.alu')

ALU_DEPS = $(ALUMINA_BOOT) $(SYSROOT_FILES) $(ALU_LIBRARIES)

# Ensure build directory exists, but do not pollute all the rules with it
$(BUILD_DIR)/.build:
	mkdir -p $(BUILD_DIR)
	touch $@

## ----------------- Bootstrap compiler (alumina-boot) -----------------

# alumina-boot is entirely built by cargo, it is here in the Makefile just so it can
# be a dependency and gets rebuilt if sources change.
$(ALUMINA_BOOT): $(BOOTSTRAP_SOURCES) $(COMMON_SOURCES) $(BUILD_DIR)/.build
	cargo build $(CARGO_FLAGS)
	cp $(CARGO_TARGET_DIR)/alumina-boot $(ALUMINA_BOOT)

## --------------------------- Stdlib tests ----------------------------

# Stdlib tests
$(STDLIB_TESTS).c: $(ALUMINA_BOOT) $(SYSROOT_FILES)
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS) --cfg test --cfg test_std --output $@

$(STDLIB_TESTS): $(STDLIB_TESTS).c
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

## ------------------ Self-hosted compiler (aluminac) ------------------

# Compile tree sitter grammar to C. Bootstrap compiler does it by itself in the Cargo
# build script, but for aluminac, we need to do it in the Makefile.
$(BUILD_DIR)/src/parser.c: common/grammar.js
	cd $(BUILD_DIR) && tree-sitter generate --no-bindings $(abspath common/grammar.js)

$(BUILD_DIR)/parser.o: $(BUILD_DIR)/src/parser.c
	$(CC) $(CFLAGS) -I $(BUILD_DIR)/src -c $(BUILD_DIR)/src/parser.c -o $@ $(LDFLAGS)

# Codegen util for aluminac
$(CODEGEN).c: $(ALU_DEPS) $(CODEGEN_SOURCES)
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS) --output $@ \
		$(foreach src,$(ALU_LIBRARIES),$(subst /,::,$(basename $(subst libraries/,,$(src))))=$(src)) \
		$(foreach src,$(CODEGEN_SOURCES),$(subst /,::,$(basename $(src)))=$(src))

$(CODEGEN): $(CODEGEN).c $(BUILD_DIR)/parser.o
	$(CC) $(CFLAGS) -o $@ $^ -ltree-sitter $(LD_FLAGS)

src/aluminac/lib/node_kinds.alu: $(CODEGEN)
	$(CODEGEN) > $@

# The actual self-hosted compiler
$(ALUMINAC).c: $(ALU_DEPS) $(SELFHOSTED_SOURCES) src/aluminac/lib/node_kinds.alu
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS) --output $@ \
		$(foreach src,$(ALU_LIBRARIES),$(subst /,::,$(basename $(subst libraries/,,$(src))))=$(src)) \
		$(foreach src,$(SELFHOSTED_SOURCES),$(subst /,::,$(basename $(src)))=$(src))

$(ALUMINAC_TESTS).c: $(ALU_DEPS) $(SELFHOSTED_SOURCES) src/aluminac/lib/node_kinds.alu
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS) --cfg test --output $@ \
		$(foreach src,$(ALU_LIBRARIES),$(subst /,::,$(basename $(subst libraries/,,$(src))))=$(src)) \
		$(foreach src,$(SELFHOSTED_SOURCES),$(subst /,::,$(basename $(src)))=$(src))

LLVM_CFLAGS = $(shell llvm-config-13 --cflags)
LLVM_LDFLAGS = $(shell llvm-config-13 --ldflags)
LLVM_LIBS = $(shell llvm-config-13 --libs engine)

$(BUILD_DIR)/llvm_target.o: libraries/llvm/target.c
	$(CC) $(CFLAGS) $(LLVM_CFLAGS) -c $^ -o $@ $(LDFLAGS)

$(ALUMINAC): $(ALUMINAC).c $(BUILD_DIR)/parser.o $(BUILD_DIR)/llvm_target.o
	$(CC) $(CFLAGS) -o $@ $^ $(LLVM_LDFLAGS) -ltree-sitter $(LLVM_LIBS) $(LDFLAGS)

$(ALUMINAC_TESTS): $(ALUMINAC_TESTS).c $(BUILD_DIR)/parser.o $(BUILD_DIR)/llvm_target.o
	$(CC) $(CFLAGS) -o $@ $^ $(LLVM_LDFLAGS) -ltree-sitter $(LLVM_LIBS)	$(LDFLAGS)

## --------------------------------Tools -------------------------------

ALUMINA_DOC = $(BUILD_DIR)/alumina-doc
ALUMINAC_LIB_SOURCES = $(shell find src/aluminac/lib/ -type f -name '*.alu')
ALUMINA_DOC_SOURCES = $(shell find tools/alumina-doc/ -type f -name '*.alu')

$(ALUMINA_DOC).c: $(ALU_DEPS) $(ALUMINAC_LIB_SOURCES) $(ALUMINA_DOC_SOURCES) src/aluminac/lib/node_kinds.alu
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS) --output $@ \
		$(foreach src,$(ALU_LIBRARIES),$(subst /,::,$(basename $(subst libraries/,,$(src))))=$(src)) \
		$(foreach src,$(ALUMINAC_LIB_SOURCES),$(subst /,::,$(basename $(subst src/,,$(src))))=$(src)) \
		$(foreach src,$(ALUMINA_DOC_SOURCES),$(subst /,::,$(basename $(subst alumina-doc/,alumina_doc/,$(src))))=$(src))

$(ALUMINA_DOC): $(ALUMINA_DOC).c $(BUILD_DIR)/parser.o
	$(CC) $(CFLAGS) -o $@ $^ -ltree-sitter $(LDFLAGS)

$(BUILD_ROOT)/docs/index.html: $(ALUMINA_DOC) $(SYSROOT_FILES)
	rm -rf $(BUILD_ROOT)/docs
	$(ALUMINA_DOC) \
		$(foreach src,$(SYSROOT_FILES),$(subst __root__,, $(subst /,::,$(basename $(subst ./sysroot,,$(src)))))=$(src))
	cp -rf tools/alumina-doc/static $(BUILD_ROOT)/docs/

.PHONY: docs serve-docs
docs: $(BUILD_ROOT)/docs/index.html

serve-docs: docs
	cd $(BUILD_ROOT)/docs && python3 -m http.server
## ------------------------------ Various ------------------------------

.PHONY: clean all
clean:
	rm -rf $(BUILD_ROOT)/

# Some convenience symlinks
alumina-boot: $(ALUMINA_BOOT)
	ln -sf $(ALUMINA_BOOT) $@

aluminac: $(ALUMINAC)
	ln -sf $(ALUMINAC) $@

.PHONY: test-std test-examples test test-fix test-aluminac

test-std: alumina-boot $(STDLIB_TESTS)
	$(STDLIB_TESTS) $(TEST_FLAGS)

test-examples: alumina-boot
	cd tools/snapshot-tests/ && pytest snapshot.py

test-aluminac: $(ALUMINAC_TESTS)
	$(ALUMINAC_TESTS) $(TEST_FLAGS)

test: test-std test-examples

test-fix: $(ALUMINA_BOOT)
	cd tools/snapshot-tests/ && pytest snapshot.py --snapshot-update

.DEFAULT_GOAL := all
all: alumina-boot aluminac

## ------------------ Ad-hoc manual testing shortcuts ------------------

$(BUILD_DIR)/quick.c: $(ALUMINA_BOOT) $(SYSROOT_FILES) quick.alu
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS) --output $@ quick=./quick.alu

$(BUILD_DIR)/quick: $(BUILD_DIR)/quick.c
	$(CC) $(CFLAGS) -o $@ $^ -ltree-sitter $(LD_FLAGS)

quick: $(BUILD_DIR)/quick
	ln -sf $^.c $@.c
	ln -sf $^ $@
