BUILD_ROOT = build
SYSROOT = ./stdlib

ifdef RELEASE
	BUILD_DIR = $(BUILD_ROOT)/release
	CARGO_FLAGS = --release
	CARGO_TARGET_DIR = target/release
	CFLAGS += -O3
	ALUMINA_FLAGS = --sysroot $(SYSROOT) --timings 
else
	BUILD_DIR = $(BUILD_ROOT)/debug
	CARGO_FLAGS = 
	CARGO_TARGET_DIR = target/debug
	CFLAGS += -g3
	ALUMINA_FLAGS = --sysroot $(SYSROOT) --debug --timings 
endif

ALUMINA_BOOT = $(BUILD_DIR)/alumina-boot
ALUMINAC = $(BUILD_DIR)/aluminac
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
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS) --cfg test --output $@

$(STDLIB_TESTS): $(STDLIB_TESTS).c
	$(CC) $(CFLAGS) -o $@ $(STDLIB_TESTS).c

## ------------------ Self-hosted compiler (aluminac) ------------------

# Compile tree sitter grammar to C. Bootstrap compiler does it by itself in the Cargo
# build script, but for aluminac, we need to do it in the Makefile.
$(BUILD_DIR)/src/parser.c: common/grammar.js
	cd $(BUILD_DIR) && tree-sitter generate --no-bindings $(abspath common/grammar.js)

$(BUILD_DIR)/parser.o: $(BUILD_DIR)/src/parser.c
	$(CC) $(CFLAGS) -I $(BUILD_DIR)/src -c $(BUILD_DIR)/src/parser.c -o $@

# Codegen util for aluminac
$(CODEGEN).c: $(ALU_DEPS) $(CODEGEN_SOURCES) 
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS) --output $@ \
		$(foreach src,$(ALU_LIBRARIES),$(subst /,::,$(basename $(subst libraries/,,$(src))))=$(src)) \
		$(foreach src,$(CODEGEN_SOURCES),$(subst /,::,$(basename $(src)))=$(src))

$(CODEGEN): $(CODEGEN).c $(BUILD_DIR)/parser.o
	$(CC) $(CFLAGS) -o $@ $^ -ltree-sitter

src/aluminac/node_kinds.alu: $(CODEGEN)
	$(CODEGEN) > $@

# The actual self-hosted compiler
$(ALUMINAC).c: $(ALU_DEPS) $(SELFHOSTED_SOURCES) src/aluminac/node_kinds.alu
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS) --output $@ \
		$(foreach src,$(ALU_LIBRARIES),$(subst /,::,$(basename $(subst libraries/,,$(src))))=$(src)) \
		$(foreach src,$(SELFHOSTED_SOURCES),$(subst /,::,$(basename $(src)))=$(src))


LLVM_CFLAGS = $(shell llvm-config-13 --cflags)
LLVM_LDFLAGS = $(shell llvm-config-13 --ldflags)
LLVM_LIBS = $(shell llvm-config-13 --libs engine)

$(BUILD_DIR)/llvm_target.o: libraries/llvm/target.c
	$(CC) $(CFLAGS) $(LLVM_CFLAGS) -c $^ -o $@

$(ALUMINAC): $(ALUMINAC).c $(BUILD_DIR)/parser.o $(BUILD_DIR)/llvm_target.o
	$(CC) $(CFLAGS) -o $@ $^ $(LLVM_LDFLAGS) -ltree-sitter $(LLVM_LIBS)

## ------------------------------ Various ------------------------------

.PHONY: clean all
clean:
	rm -rf $(BUILD_ROOT)/

# Some convenience symlinks
alumina-boot: $(ALUMINA_BOOT)
	ln -sf $(ALUMINA_BOOT) $@

aluminac: $(ALUMINAC)
	ln -sf $(ALUMINAC) $@

.PHONY: test-std test-examples test test-fix

test-std: alumina-boot $(STDLIB_TESTS)
	$(STDLIB_TESTS) --include-std
	
test-examples: alumina-boot
	cd tools/snapshot-tests/ && pytest snapshot.py

test: test-std test-examples

test-fix: $(ALUMINA_BOOT)
	cd tools/snapshot-tests/ && pytest snapshot.py --snapshot-update

.DEFAULT_GOAL := all
all: alumina-boot aluminac

## ------------------ Ad-hoc manual testing shortcuts ------------------

quickrun: $(ALUMINA_BOOT) $(SYSROOT_FILES) quick.alu
	RUST_BACKTRACE=1 $(ALUMINA_BOOT) $(ALUMINA_FLAGS) --output quick.c quick=./quick.alu
	$(CC) $(CFLAGS) -o quickrun -O0 quick.c

quicktest: $(ALUMINA_BOOT) $(SYSROOT_FILES) quick.alu
	RUST_BACKTRACE=1 $(ALUMINA_BOOT) $(ALUMINA_FLAGS) --cfg test --output quick.c quick=./quick.alu
	$(CC) $(CFLAGS) -o quicktest -O0 quick.c
