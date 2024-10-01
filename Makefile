PREFIX ?= /usr/local

BUILD_ROOT = build
SYSROOT = sysroot

ifdef RELEASE
	BUILD_DIR = $(BUILD_ROOT)/release
	CARGO_FLAGS += --profile release
	CARGO_TARGET_DIR = target/release
	CFLAGS += -O3
else ifdef FAST_DEBUG
	# Compile in debug mode, but with alumina-boot compiled in release mode.
	# It is significantly faster.
	BUILD_DIR = $(BUILD_ROOT)/fast-debug
	CARGO_FLAGS += --profile release
	CARGO_TARGET_DIR = target/release
	CFLAGS += -g0
	ALUMINA_FLAGS += --debug
else ifdef PROFILING
	BUILD_DIR = $(BUILD_ROOT)/profiling
	CARGO_FLAGS += --profile profiling
	CARGO_TARGET_DIR = target/profiling
	CFLAGS += -g3 -fPIE -rdynamic -O3
	ALUMINA_FLAGS += --debug
else ifdef COVERAGE
	CC ?= clang
	BUILD_DIR = $(BUILD_ROOT)/coverage
	CARGO_FLAGS += --profile coverage
	CARGO_TARGET_DIR = target/coverage
	CFLAGS += -g3 -fPIE -rdynamic -fprofile-instr-generate -fcoverage-mapping
	ALUMINA_FLAGS += --debug
	export RUSTFLAGS += -Cinstrument-coverage
	export LLVM_PROFILE_FILE = $(BUILD_ROOT)/coverage/profiles/%p-%m.profraw
else
	CARGO_FLAGS += --profile dev
	BUILD_DIR = $(BUILD_ROOT)/debug
	CARGO_TARGET_DIR = target/debug
	CFLAGS += -g3 -fPIE -rdynamic
	ALUMINA_FLAGS += --debug
endif

LDFLAGS ?= -lm
ifndef STD_BACKTRACE
	ALUMINA_FLAGS += --cfg libbacktrace
	LDFLAGS += -lbacktrace
endif
ifndef NO_THREADS
	ALUMINA_FLAGS += --cfg threading
	LDFLAGS += -lpthread
endif
ifndef NO_MINICORO
	MINICORO = $(BUILD_DIR)/minicoro.o
	ALUMINA_FLAGS += --cfg coroutines
else
	MINICORO =
endif

ifdef TIMINGS
	ALUMINA_FLAGS += -Ztimings
endif

# Convert a list of source files to a list of <module>=<file> pairs. mod.alu files are treated
# specially, they represent a module with the same name as the directory they are in.
define alumina_modules
    $(foreach src,$(1),$(subst -,_,$(subst ::mod,::,$(subst /,::,$(basename $(subst $(2),$(3),$(src))))))=$(src))
endef

ALUMINA_BOOT = $(BUILD_DIR)/alumina-boot
CODEGEN = $(BUILD_DIR)/aluminac-generate
STDLIB_TESTS = $(BUILD_DIR)/stdlib-tests
LIBRARIES_TESTS = $(BUILD_DIR)/libraries-tests
LANG_TESTS = $(BUILD_DIR)/lang-tests
DOCTEST = $(BUILD_DIR)/doctest

SYSROOT_AST = $(BUILD_DIR)/sysroot.ast
SYSROOT_TEST_AST = $(BUILD_DIR)/sysroot-test.ast
SYSROOT_TEST_STD_AST = $(BUILD_DIR)/sysroot-test-std.ast

# If grammar changes, we need to rebuild the world
COMMON_SOURCES = common/grammar.js
BOOTSTRAP_SOURCES = $(shell find src/alumina-boot/ -type f) $(shell find src/alumina-boot-macros/ -type f)
SYSROOT_FILES = $(shell find $(SYSROOT) -type f -name '*.alu')
ALU_LIBRARIES = $(shell find libraries/ -type f -name '*.alu')

# Ensure build directory exists, but do not pollute all the rules with it
$(BUILD_DIR)/.build:
	mkdir -p $(BUILD_DIR)
	@touch $@

## ----------------- Bootstrap compiler (alumina-boot) -----------------

# alumina-boot is entirely built by cargo, it is here in the Makefile just so it can
# be a dependency and gets rebuilt if sources change.
$(ALUMINA_BOOT): $(BOOTSTRAP_SOURCES) $(COMMON_SOURCES) $(BUILD_DIR)/.build
	cargo build $(CARGO_FLAGS)
	cp $(CARGO_TARGET_DIR)/alumina-boot $(ALUMINA_BOOT)

## ---------------------- Sysroot AST caching ------------------------

ifdef CACHE_AST
$(SYSROOT_AST): $(ALUMINA_BOOT) $(SYSROOT_FILES)
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS) --sysroot $(SYSROOT) \
		-Zdump-ast=$@ -Zast-only

$(SYSROOT_TEST_AST): $(ALUMINA_BOOT) $(SYSROOT_FILES)
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS) --sysroot $(SYSROOT) \
		-Zdump-ast=$@ -Zast-only --cfg test

$(SYSROOT_TEST_STD_AST): $(ALUMINA_BOOT) $(SYSROOT_FILES)
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS) --sysroot $(SYSROOT) \
		-Zdump-ast=$@ -Zast-only --cfg test --cfg test_std

ALU_DEPS = $(SYSROOT_AST)
ALU_TEST_DEPS = $(SYSROOT_TEST_AST)
ALU_TEST_STD_DEPS = $(SYSROOT_TEST_STD_AST)
ALUMINA_FLAGS_COMMON = --ast $(SYSROOT_AST) $(ALUMINA_FLAGS)
ALUMINA_FLAGS_TEST = --ast $(SYSROOT_TEST_AST) $(ALUMINA_FLAGS) --cfg test
ALUMINA_FLAGS_TEST_STD = --ast $(SYSROOT_TEST_STD_AST) $(ALUMINA_FLAGS) --cfg test --cfg test_std
else
ALU_DEPS = $(ALUMINA_BOOT) $(SYSROOT_FILES)
ALU_TEST_DEPS = $(ALUMINA_BOOT) $(SYSROOT_FILES)
ALU_TEST_STD_DEPS = $(ALUMINA_BOOT) $(SYSROOT_FILES)
ALUMINA_FLAGS_COMMON = --sysroot $(SYSROOT) $(ALUMINA_FLAGS)
ALUMINA_FLAGS_TEST = --sysroot $(SYSROOT) $(ALUMINA_FLAGS) --cfg test
ALUMINA_FLAGS_TEST_STD = --sysroot $(SYSROOT) $(ALUMINA_FLAGS) --cfg test --cfg test_std
endif

## ----------------------------- Minicoro ------------------------------

$(BUILD_DIR)/minicoro.o: common/minicoro/minicoro.h
	$(CC) $(CFLAGS) -DMINICORO_IMPL -xc -c $^ -o $@

## --------------------------- Stdlib tests ----------------------------

# Stdlib tests
$(STDLIB_TESTS).c: $(ALU_TEST_STD_DEPS)
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS_TEST_STD) -Zdeny-warnings --output $@

$(STDLIB_TESTS): $(STDLIB_TESTS).c $(MINICORO)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

## ---------------------------- Lang tests -----------------------------

LANG_TEST_FILES = $(shell find tests/lang -type f -name '*.alu')

$(LANG_TESTS).c: $(ALU_TEST_DEPS) $(LANG_TEST_FILES)
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS_TEST) -Zdeny-warnings --output $@ \
		$(call alumina_modules,$(LANG_TEST_FILES),tests/,)

$(LANG_TESTS): $(LANG_TESTS).c $(MINICORO)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

## ------------------ Libraries  ------------------

# Compile tree sitter grammar to C. Bootstrap compiler does it by itself in the Cargo
# build script, but for aluminac, we need to do it in the Makefile.
$(BUILD_DIR)/src/parser.c: common/grammar.js
	cd $(BUILD_DIR) && tree-sitter generate --no-bindings $(abspath common/grammar.js)

$(BUILD_DIR)/parser.o: $(BUILD_DIR)/src/parser.c
	$(CC) $(CFLAGS) -I $(BUILD_DIR)/src -c $(BUILD_DIR)/src/parser.c -o $@ $(LDFLAGS)

# node_kinds.alu is generated by the codegen util.
CODEGEN_SOURCES = $(shell find tools/tree-sitter-codegen/ -type f -name '*.alu')
TREE_SITTER_SOURCES = $(shell find libraries/tree_sitter/ -type f -name '*.alu')

$(CODEGEN).c: $(ALU_DEPS) $(TREE_SITTER_SOURCES) $(CODEGEN_SOURCES)
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS_COMMON) --output $@ \
		$(call alumina_modules,$(TREE_SITTER_SOURCES),libraries/,/) \
		$(call alumina_modules,$(CODEGEN_SOURCES),tools/,/)

$(CODEGEN): $(CODEGEN).c $(BUILD_DIR)/parser.o $(MINICORO)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS) -ltree-sitter

libraries/aluminac/lib/node_kinds.alu: $(CODEGEN)
	$(CODEGEN) --output $@

$(LIBRARIES_TESTS).c: $(ALU_TEST_DEPS) $(ALU_LIBRARIES)
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS_TEST) -Zdeny-warnings --output $@ \
		$(call alumina_modules,$(ALU_LIBRARIES),libraries/,/)

$(LIBRARIES_TESTS): $(LIBRARIES_TESTS).c $(MINICORO)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS) -ltree-sitter

## --------------------------------Tools -------------------------------

ALUMINA_DOC = $(BUILD_DIR)/alumina-doc
ALUMINA_DOC_SOURCES = $(shell find tools/alumina-doc/ -type f -name '*.alu')

$(ALUMINA_DOC).c: $(ALU_DEPS) $(ALU_LIBRARIES) $(ALUMINA_DOC_SOURCES) libraries/aluminac/lib/node_kinds.alu
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS_COMMON) --output $@ \
		$(call alumina_modules,$(ALU_LIBRARIES),libraries/,/) \
		$(call alumina_modules,$(ALUMINA_DOC_SOURCES),tools/,/)

$(ALUMINA_DOC): $(ALUMINA_DOC).c $(BUILD_DIR)/parser.o $(MINICORO)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS) -ltree-sitter

$(BUILD_DIR)/doctest.alu: $(ALUMINA_DOC) $(SYSROOT_FILES) tools/alumina-doc/static/*
	@mkdir -p $(BUILD_DIR)/~doctest
	ALUMINA_DOC_OUTPUT_DIR=$(BUILD_DIR)/~doctest $(ALUMINA_DOC) \
		$(call alumina_modules,$(SYSROOT_FILES),sysroot/,/) \
		$(call alumina_modules,$(ALU_LIBRARIES),libraries/,/)
	@cp -rf tools/alumina-doc/static $(BUILD_DIR)/~doctest/html/
	@rm -rf $(BUILD_DIR)/html $(BUILD_DIR)/doctest.alu
	mv $(BUILD_DIR)/~doctest/* $(BUILD_DIR)/
	@rmdir $(BUILD_DIR)/~doctest

$(DOCTEST).c: $(ALU_TEST_DEPS) $(BUILD_DIR)/doctest.alu
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS_TEST) --output $@ $(BUILD_DIR)/doctest.alu \
		$(call alumina_modules,$(ALU_LIBRARIES),libraries/,/)

$(DOCTEST): $(DOCTEST).c $(MINICORO)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

.PHONY: docs test-docs serve-docs watch-docs
docs: $(BUILD_DIR)/doctest.alu

test-docs: $(DOCTEST)
	$(DOCTEST) $(TEST_FLAGS) || true

serve-docs:
	@cd $(BUILD_DIR)/html && python3 -m http.server

watch-docs:
	@BUILD_DIR=$(BUILD_DIR) tools/alumina-doc/watch_docs.sh

## ------------------------------ Examples -----------------------------

.PHONY: examples

EXAMPLES = $(shell find examples/ -type f -name '*.alu')

$(BUILD_DIR)/examples/.build:
	mkdir -p $(BUILD_DIR)/examples
	@touch $@

$(BUILD_DIR)/examples/%.c: examples/%.alu $(ALU_DEPS) $(BUILD_DIR)/examples/.build
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS_COMMON) --output $@ main=$<

$(BUILD_DIR)/examples/%: $(BUILD_DIR)/examples/%.c $(MINICORO)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

examples: $(patsubst examples/%.alu,$(BUILD_DIR)/examples/%,$(EXAMPLES))

## ------------------------------ Various ------------------------------

.PHONY: clean clean-all all install
clean:
	rm -rf $(BUILD_ROOT)/
	rm -f quick.c quick alumina-boot

clean-all: clean
	cargo clean

install: $(ALUMINA_BOOT) $(SYSROOT_FILES)
	install -T $(ALUMINA_BOOT) $(PREFIX)/bin/alumina-boot
	rm -rf $(PREFIX)/share/alumina
	mkdir -p $(PREFIX)/share/alumina
	cp -r $(SYSROOT)/* $(PREFIX)/share/alumina

# Some convenience symlinks
alumina-boot: $(ALUMINA_BOOT)
	ln -sf $(ALUMINA_BOOT) $@

.PHONY: test-std test-alumina-boot test-libraries test-lang test

test-std: alumina-boot $(STDLIB_TESTS)
	$(STDLIB_TESTS) $(TEST_FLAGS)

test-lang: alumina-boot $(LANG_TESTS)
	$(LANG_TESTS) $(TEST_FLAGS)

test-libraries: alumina-boot $(LIBRARIES_TESTS)
	$(LIBRARIES_TESTS) $(TEST_FLAGS)

test-alumina-boot:
	cargo test $(CARGO_FLAGS) --all-targets

test: test-alumina-boot test-std test-lang

.DEFAULT_GOAL := all
all: alumina-boot

## ------------------ Ad-hoc manual testing shortcuts ------------------

$(BUILD_DIR)/quick.c: $(ALU_DEPS) quick.alu
	$(ALUMINA_BOOT) $(ALUMINA_FLAGS_COMMON) --output $@ quick=./quick.alu

$(BUILD_DIR)/quick: $(BUILD_DIR)/quick.c $(MINICORO)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

quick: $(BUILD_DIR)/quick
	ln -sf $^.c $@.c
	ln -sf $^ $@

## ------------------------------ Benchmarking -------------------------

.PHONY: bench-std bench-std-cc flamegraph samply

BENCH_CMD = ./tools/bench.py -n$(if $(TIMES),$(TIMES),20) $(if $(MARKDOWN),--markdown,)

bench-std: $(ALUMINA_BOOT) $(SYSROOT_FILES)
	$(BENCH_CMD) $(ALUMINA_BOOT) $(ALUMINA_FLAGS) --sysroot $(SYSROOT) -Ztimings --cfg test --cfg test_std --output /dev/null

bench-std-cached: $(ALU_TEST_STD_DEPS)
	@ if [ -z "$(CACHE_AST)" ]; then \
		echo "ERROR: CACHE_AST=1 is not set"; \
		exit 1; \
	fi
	$(BENCH_CMD) $(ALUMINA_BOOT) $(ALUMINA_FLAGS_TEST_STD) -Ztimings --cfg test --cfg test_std --output /dev/null

bench-std-cc: $(STDLIB_TESTS).c $(MINICORO)
	$(BENCH_CMD) $(CC) $(CFLAGS) -o/dev/null $^ $(LDFLAGS)

$(BUILD_DIR)/flamegraph.svg: $(ALUMINA_BOOT) $(SYSROOT_FILES)
	cargo flamegraph $(CARGO_FLAGS)  \
		-F 10000 --dev -o $@ -- $(ALUMINA_FLAGS) --sysroot $(SYSROOT) -Ztimings --cfg test --cfg test_std --output /dev/null

flamegraph: $(BUILD_DIR)/flamegraph.svg

samply: $(ALUMINA_BOOT) $(SYSROOT_FILES)
	samply record -r 10000 --reuse-threads --iteration-count 5  $(ALUMINA_BOOT) $(ALUMINA_FLAGS_TEST_STD) -Ztimings --cfg test --cfg test_std --output /dev/null

## ------------------------------ Diag tests ----------------------------

DIAG_CMD = ./tools/diag.py
DIAG_CASES = $(shell find tests/diag -type f -name '*.alu')

$(BUILD_DIR)/diag/.build:
	mkdir -p $(BUILD_DIR)/diag
	@touch $@

$(BUILD_DIR)/diag/%-check: tests/diag/%.alu $(ALU_DEPS) $(BUILD_DIR)/diag/.build
	@$(DIAG_CMD) $< $(ALUMINA_BOOT) $(ALUMINA_FLAGS_COMMON)
	@touch $@

$(BUILD_DIR)/diag/%-annotate: tests/diag/%.alu $(ALU_DEPS) $(BUILD_DIR)/diag/.build
	$(DIAG_CMD) --fix $< $(ALUMINA_BOOT) $(ALUMINA_FLAGS_COMMON)
	@touch $@

test-diag: $(patsubst tests/diag/%.alu,$(BUILD_DIR)/diag/%-check,$(DIAG_CASES))
diag-fix: $(patsubst tests/diag/%.alu,$(BUILD_DIR)/diag/%-annotate,$(DIAG_CASES))

## ------------------------------ Coverage ------------------------------
.PHONY: coverage all-tests-with-coverage
coverage:
	COVERAGE=1 CACHE_AST=1 $(MAKE) all-tests-with-coverage

all-tests-with-coverage: test test-docs test-libraries test-diag examples
	llvm-profdata$(LLVM_SUFFIX) merge \
		-sparse  \
		$(BUILD_DIR)/profiles/* \
		-o $(BUILD_DIR)/profiles/merged.profdata

	llvm-cov$(LLVM_SUFFIX) export \
		-Xdemangler=rustfilt \
		-format=lcov \
		-instr-profile=$(BUILD_DIR)/profiles/merged.profdata $(ALUMINA_BOOT) \
		$(BOOTSTRAP_SOURCES) > $(BUILD_DIR)/coverage.txt

	llvm-cov$(LLVM_SUFFIX) show \
		-Xdemangler=rustfilt \
		-format=html \
		-instr-profile=$(BUILD_DIR)/profiles/merged.profdata $(ALUMINA_BOOT) \
		-output-dir=$(BUILD_DIR)/html \
		$(BOOTSTRAP_SOURCES)

serve-coverage:
	@cd $(BUILD_ROOT)/coverage/html && python3 -m http.server

## ----------------------------- Random ---------------------------------

.PHONY: cloc
cloc:
	@cloc --read-lang-def=tools/cloc_language_def.txt $(shell git ls-files)

## ------------------------------ Dist ----------------------------------

.PHONY: lint-rust dist-check

lint-rust: $(BOOTSTRAP_SOURCES) $(COMMON_SOURCES) $(BUILD_DIR)/.build
	cargo fmt -- --check
	cargo clippy $(CARGO_FLAGS) --all-targets

dist-check: lint-rust test-libraries test-docs test-diag test examples
