# Alumina: the compiler (aluminac), its standard library, tools, tests and docs.
#
# aluminac is written in Alumina and compiles to native code with LLVM. It is
# bootstrapped with alumina-boot, the original compiler (Rust, emitting C):
#
#   alumina-boot -> aluminac stage 1 (via C) -> stage 2, which is `aluminac`
#
# and `make bootstrap` checks the fixpoint (stage 3, built by stage 2, emits
# the same LLVM IR). Everything else is compiled with aluminac.
#
# Common targets:
#   make                 build aluminac (./aluminac)
#   make test            aluminac's test suites (see `test` below)
#   make check           everything CI checks
#   make docs            the standard library's documentation (build/<profile>/html)
#   make install         aluminac and the sysroot, into PREFIX
#   make boot            alumina-boot only (lint-boot, test-boot: its Rust lints and tests)
#
# Profiles: debug (default), RELEASE=1 (-O3), PROFILING=1 (optimized, with
# debug info). Requirements: cargo, a C compiler, tree-sitter (the library and
# the CLI), LLVM 22 (or LLVM_CONFIG=<path to llvm-config>), python3 (tests).

PREFIX ?= /usr/local
LLVM_CONFIG ?= llvm-config-22
# (For the debug information tests.)
LLDB ?= $(shell command -v lldb-22 || command -v lldb)

BUILD_ROOT = build
SYSROOT = sysroot

ifdef RELEASE
	PROFILE = release
	CFLAGS += -O2
	ALUMINAC_FLAGS += -O3
else ifdef PROFILING
	PROFILE = profiling
	CFLAGS += -O2 -g
	ALUMINAC_FLAGS += -O2 -g
else
	PROFILE = debug
	CFLAGS += -g
	ALUMINAC_FLAGS += -g --debug
endif
ALUMINAC_FLAGS += --cfg threading

BUILD_DIR = $(BUILD_ROOT)/$(PROFILE)

.DEFAULT_GOAL := all
.PHONY: all aluminac boot
all: aluminac

# A list of source files as <module>=<file> arguments: a/b/c.alu under $(2) is
# module $(3)a::b::c, and a/b/mod.alu is module $(3)a::b.
define alumina_modules
	$(foreach src,$(1),$(subst -,_,$(subst ::mod,::,$(subst /,::,$(basename $(subst $(2),$(3),$(src))))))=$(src))
endef

SYSROOT_FILES := $(shell find $(SYSROOT) -type f -name '*.alu')
LIBRARY_SOURCES := $(shell find libraries -type f -name '*.alu')
TREE_SITTER_SOURCES := $(shell find libraries/tree_sitter -type f -name '*.alu')
ALUMINAC_COMMON_SOURCES := $(shell find libraries/aluminac-common -type f -name '*.alu')
ALUMINAC_SOURCES := $(shell find src/aluminac -type f -name '*.alu')

# (Evaluated only where used, so that targets not needing LLVM do not either.)
LLVM_LIBS = $(shell $(LLVM_CONFIG) --ldflags --libs --system-libs)

.PHONY: check-llvm
check-llvm:
	@command -v $(LLVM_CONFIG) >/dev/null 2>&1 || (echo "error: \`$(LLVM_CONFIG)\` not found: install LLVM 22, or pass LLVM_CONFIG=<path to llvm-config>." && exit 1)

## ------------------------------ alumina-boot ------------------------------

# Built by cargo (always optimized: it only generates aluminac's stage 1);
# here so that it is rebuilt when its sources change.
BOOT = $(BUILD_ROOT)/alumina-boot
BOOT_SOURCES := $(shell find src/alumina-boot src/alumina-boot-macros -type f) common/grammar.js

$(BOOT): $(BOOT_SOURCES)
	cargo build --release
	@mkdir -p $(@D)
	cp $${CARGO_TARGET_DIR:-target}/release/alumina-boot $@

boot: $(BOOT)

.PHONY: lint-boot test-boot
lint-boot:
	cargo fmt -- --check
	cargo clippy --all-targets

test-boot:
	cargo test --all-targets

## ------------------------------ The grammar -------------------------------

# The tree-sitter parser (alumina-boot's build script makes its own).
PARSER = $(BUILD_DIR)/parser.o

$(BUILD_DIR)/src/parser.c: common/grammar.js
	cd common && tree-sitter generate -o $(abspath $(BUILD_DIR))/src grammar.js

$(PARSER): $(BUILD_DIR)/src/parser.c
	$(CC) $(CFLAGS) -I$(BUILD_DIR)/src -c $< -o $@

## -------------------------------- aluminac --------------------------------

ALUMINAC = $(BUILD_DIR)/aluminac
STAGE1 = $(BUILD_DIR)/aluminac-stage1
STAGE3 = $(BUILD_DIR)/aluminac-stage3

ALUMINAC_MODULES = \
	$(call alumina_modules,$(TREE_SITTER_SOURCES) $(ALUMINAC_COMMON_SOURCES),libraries/,/) \
	$(call alumina_modules,$(ALUMINAC_SOURCES),src/,/)
ALUMINAC_DEPS = $(SYSROOT_FILES) $(TREE_SITTER_SOURCES) $(ALUMINAC_COMMON_SOURCES) $(ALUMINAC_SOURCES) $(PARSER)
ALUMINAC_LINK = -ltree-sitter $(PARSER) $(LLVM_LIBS) -lpthread

# Compiling with aluminac.
ALUMINAC_CMD = $(ALUMINAC) $(ALUMINAC_FLAGS) --sysroot $(SYSROOT)

$(STAGE1).c: $(BOOT) $(ALUMINAC_DEPS) | check-llvm
	@mkdir -p $(@D)
	$(BOOT) --sysroot $(SYSROOT) --debug --cfg threading --cfg boot --output $@ $(ALUMINAC_MODULES)

# (Uninitialized locals filled with a pattern: the compiler reading one is
# then a bug that shows, not one that depends on what the stack held.)
$(STAGE1): $(STAGE1).c $(PARSER)
	$(CC) -g -w -ftrivial-auto-var-init=pattern -o $@ $(STAGE1).c $(PARSER) -lm -lpthread -ltree-sitter $(LLVM_LIBS)

$(ALUMINAC): $(STAGE1) $(ALUMINAC_DEPS)
	$(STAGE1) $(ALUMINAC_FLAGS) --sysroot $(SYSROOT) --link-args "$(ALUMINAC_LINK)" -o $@ $(ALUMINAC_MODULES)

aluminac: $(ALUMINAC)
	ln -sf $(ALUMINAC) $@

# The bootstrap fixpoint: stage 2 (aluminac) and stage 3 must compile aluminac
# to the same LLVM IR. (The linked binaries can differ, e.g. the macOS linker
# stamps a UUID in them.)
$(STAGE3): $(ALUMINAC) $(ALUMINAC_DEPS)
	$(ALUMINAC) $(ALUMINAC_FLAGS) --sysroot $(SYSROOT) --link-args "$(ALUMINAC_LINK)" -o $@ $(ALUMINAC_MODULES)

$(BUILD_DIR)/bootstrap/stage2.ll: $(ALUMINAC) $(ALUMINAC_DEPS)
	@mkdir -p $(@D)
	$(ALUMINAC) $(ALUMINAC_FLAGS) --sysroot $(SYSROOT) --emit-llvm -o $@ $(ALUMINAC_MODULES)

$(BUILD_DIR)/bootstrap/stage3.ll: $(STAGE3) $(ALUMINAC_DEPS)
	@mkdir -p $(@D)
	$(STAGE3) $(ALUMINAC_FLAGS) --sysroot $(SYSROOT) --emit-llvm -o $@ $(ALUMINAC_MODULES)

.PHONY: bootstrap
bootstrap: $(BUILD_DIR)/bootstrap/stage2.ll $(BUILD_DIR)/bootstrap/stage3.ll
	@cmp -s $^ && echo "Bootstrap successful: stage 2 and stage 3 emit the same IR." \
		|| (echo "Bootstrap failed: stage 2 and stage 3 emit different IR." && exit 1)

## ------------------------------- Node kinds -------------------------------

# The names of the grammar's node kinds and fields, for aluminac and its tools
# (their ids are looked up at run time, see tools/tree-sitter-codegen). The file
# is committed; `make regen-node-kinds` regenerates it when the grammar gains
# or loses names, and `make check-node-kinds` checks that it is up to date.
NODE_KINDS = libraries/aluminac-common/node_kinds.alu
CODEGEN = $(BUILD_DIR)/tree-sitter-codegen
CODEGEN_SOURCES := $(shell find tools/tree-sitter-codegen -type f -name '*.alu')

$(CODEGEN): $(ALUMINAC) $(SYSROOT_FILES) $(TREE_SITTER_SOURCES) $(CODEGEN_SOURCES) $(PARSER)
	$(ALUMINAC_CMD) --link-args "-ltree-sitter $(PARSER)" -o $@ \
		$(call alumina_modules,$(TREE_SITTER_SOURCES),libraries/,/) \
		$(call alumina_modules,$(CODEGEN_SOURCES),tools/,/)

$(BUILD_DIR)/gen/node_kinds.alu: $(CODEGEN)
	@mkdir -p $(@D)
	$(CODEGEN) --output $@

.PHONY: regen-node-kinds check-node-kinds
regen-node-kinds: $(BUILD_DIR)/gen/node_kinds.alu
	cp $< $(NODE_KINDS)

check-node-kinds: $(BUILD_DIR)/gen/node_kinds.alu
	@cmp -s $< $(NODE_KINDS) || (echo "$(NODE_KINDS) is out of date, run \`make regen-node-kinds\`." && exit 1)

## --------------------------------- Tests ----------------------------------

# Coroutines (for the programs that use them) are minicoro's until they are
# LLVM's; nothing else links it.
MINICORO = $(BUILD_DIR)/minicoro.o
CORO_FLAGS = --cfg coroutines

$(MINICORO): common/minicoro/minicoro.h
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) -DMINICORO_IMPL -DNDEBUG -xc -c $< -o $@

LANG_TEST_FILES := $(shell find tests/lang -type f -name '*.alu')
TESTS_DIR = $(BUILD_DIR)/tests

# The standard library's unit tests.
$(TESTS_DIR)/std: $(ALUMINAC) $(SYSROOT_FILES) $(MINICORO)
	@mkdir -p $(@D)
	$(ALUMINAC_CMD) $(CORO_FLAGS) --test --cfg test_std --link-args "$(MINICORO) -lpthread" -o $@

# The language tests (tests/lang).
$(TESTS_DIR)/lang: $(ALUMINAC) $(SYSROOT_FILES) $(LANG_TEST_FILES) $(MINICORO)
	@mkdir -p $(@D)
	$(ALUMINAC_CMD) $(CORO_FLAGS) --test --link-args "$(MINICORO) -lpthread" -o $@ \
		$(call alumina_modules,$(LANG_TEST_FILES),tests/,)

# The libraries' unit tests (libraries/).
$(TESTS_DIR)/libraries: $(ALUMINAC) $(SYSROOT_FILES) $(LIBRARY_SOURCES) $(PARSER) $(MINICORO)
	@mkdir -p $(@D)
	$(ALUMINAC_CMD) $(CORO_FLAGS) --test --link-args "-ltree-sitter $(PARSER) $(MINICORO) -lpthread" -o $@ \
		$(call alumina_modules,$(LIBRARY_SOURCES),libraries/,/)

# aluminac's own unit tests.
$(TESTS_DIR)/aluminac: $(ALUMINAC) $(ALUMINAC_DEPS)
	@mkdir -p $(@D)
	$(ALUMINAC_CMD) --test --link-args "$(ALUMINAC_LINK)" -o $@ $(ALUMINAC_MODULES)

.PHONY: test test-std test-lang test-libraries test-unit test-features test-diag test-debuginfo test-docs cross-check
test-std: $(TESTS_DIR)/std
	$< $(TEST_FLAGS)

test-lang: $(TESTS_DIR)/lang
	$< $(TEST_FLAGS)

test-libraries: $(TESTS_DIR)/libraries
	$< $(TEST_FLAGS)

test-unit: $(TESTS_DIR)/aluminac
	$< $(TEST_FLAGS)

# The compiler's feature tests (tests/aluminac/*.alu; TEST_FILTER=<name part>).
test-features: $(ALUMINAC)
	./tests/aluminac/run_tests.sh $(ALUMINAC) $(TEST_FILTER)

# The diagnostics tests (tests/diag): the errors and warnings on the lines
# the annotations give.
test-diag: $(ALUMINAC)
	python3 tests/aluminac/diag_check.py $(ALUMINAC) $(TEST_FILTER)

# The debug information tests (tests/debuginfo): programs run in lldb.
test-debuginfo: $(ALUMINAC)
	LLDB="$(LLDB)" LLVM_DWARFDUMP="$$($(LLVM_CONFIG) --bindir)/llvm-dwarfdump" \
		python3 tests/debuginfo/run.py $(ALUMINAC) $(TEST_FILTER)

# Every example in the standard library's documentation, run.
test-docs: $(BUILD_DIR)/doctest
	$< $(TEST_FLAGS)

test: test-unit test-features test-std test-lang test-libraries test-diag test-debuginfo test-docs

# The feature tests compiled with alumina-boot: they must behave the same.
cross-check: $(BOOT)
	./tests/aluminac/cross_check.sh $(BOOT) $(TEST_FILTER)

## ---------------------------------- Docs ----------------------------------

ALUMINA_DOC = $(BUILD_DIR)/alumina-doc
ALUMINA_DOC_SOURCES := $(shell find tools/alumina-doc -type f -name '*.alu')
DOC_INPUTS = $(call alumina_modules,$(SYSROOT_FILES),$(SYSROOT)/,/) $(call alumina_modules,$(LIBRARY_SOURCES),libraries/,/)

$(ALUMINA_DOC): $(ALUMINAC) $(SYSROOT_FILES) $(LIBRARY_SOURCES) $(ALUMINA_DOC_SOURCES) $(PARSER)
	$(ALUMINAC_CMD) --link-args "-ltree-sitter $(PARSER) -lpthread" -o $@ \
		$(call alumina_modules,$(LIBRARY_SOURCES),libraries/,/) \
		$(call alumina_modules,$(ALUMINA_DOC_SOURCES),tools/,/)

# The HTML (build/<profile>/html) and the examples in it as tests (doctest.alu),
# written together.
$(BUILD_DIR)/doctest.alu: $(ALUMINA_DOC) $(SYSROOT_FILES) $(LIBRARY_SOURCES) tools/alumina-doc/static/*
	@rm -rf $(BUILD_DIR)/~doctest && mkdir -p $(BUILD_DIR)/~doctest
	ALUMINA_DOC_OUTPUT_DIR=$(BUILD_DIR)/~doctest $(ALUMINA_DOC) $(DOC_INPUTS)
	@cp -R tools/alumina-doc/static $(BUILD_DIR)/~doctest/html/
	@rm -rf $(BUILD_DIR)/html $(BUILD_DIR)/doctest.alu
	@mv $(BUILD_DIR)/~doctest/* $(BUILD_DIR)/ && rmdir $(BUILD_DIR)/~doctest

$(BUILD_DIR)/doctest: $(BUILD_DIR)/doctest.alu $(ALUMINAC) $(PARSER) $(MINICORO)
	$(ALUMINAC_CMD) $(CORO_FLAGS) --test --link-args "-ltree-sitter $(PARSER) $(MINICORO) -lpthread" -o $@ \
		$(BUILD_DIR)/doctest.alu $(call alumina_modules,$(LIBRARY_SOURCES),libraries/,/)

.PHONY: docs serve-docs watch-docs
docs: $(BUILD_DIR)/doctest.alu

serve-docs:
	@cd $(BUILD_DIR)/html && python3 -m http.server

watch-docs:
	@BUILD_DIR=$(BUILD_DIR) tools/alumina-doc/watch_docs.sh

## -------------------------------- Examples --------------------------------

EXAMPLES := $(shell find examples -type f -name '*.alu')

$(BUILD_DIR)/examples/%: examples/%.alu $(ALUMINAC) $(SYSROOT_FILES) $(MINICORO)
	@mkdir -p $(@D)
	$(ALUMINAC_CMD) $(CORO_FLAGS) --link-args "$(MINICORO) -lpthread" -o $@ main=$<

.PHONY: examples
examples: $(patsubst examples/%.alu,$(BUILD_DIR)/examples/%,$(EXAMPLES))

## ---------------------------------- CI ------------------------------------

.PHONY: check
check: lint-boot test-boot bootstrap check-node-kinds test examples

## -------------------------------- Install ---------------------------------

# aluminac finds the sysroot through ALUMINA_SYSROOT (or --sysroot); set it to
# $(PREFIX)/share/alumina. (Build with RELEASE=1 for an optimized compiler.)
# alumina-lldb is lldb with the formatters for Alumina's types.
.PHONY: install install-boot
install: $(ALUMINAC)
	mkdir -p $(DESTDIR)$(PREFIX)/bin $(DESTDIR)$(PREFIX)/share/alumina
	cp $(ALUMINAC) $(DESTDIR)$(PREFIX)/bin/aluminac
	rm -rf $(DESTDIR)$(PREFIX)/share/alumina/*
	cp -R $(SYSROOT)/. $(DESTDIR)$(PREFIX)/share/alumina/
	mkdir -p $(DESTDIR)$(PREFIX)/share/aluminac
	cp tools/lldb/alumina_lldb.py $(DESTDIR)$(PREFIX)/share/aluminac/
	cp tools/lldb/alumina-lldb $(DESTDIR)$(PREFIX)/bin/

install-boot: $(BOOT)
	mkdir -p $(DESTDIR)$(PREFIX)/bin $(DESTDIR)$(PREFIX)/share/alumina
	cp $(BOOT) $(DESTDIR)$(PREFIX)/bin/alumina-boot
	rm -rf $(DESTDIR)$(PREFIX)/share/alumina/*
	cp -R $(SYSROOT)/. $(DESTDIR)$(PREFIX)/share/alumina/

## -------------------------------- Various ---------------------------------

# quick.alu, for trying things out: `make quick` builds ./quick, `make quick-ir`
# writes its IR to quick.ll.
.PHONY: quick quick-ir
quick: $(ALUMINAC)
	$(ALUMINAC_CMD) -o $(BUILD_DIR)/quick quick=./quick.alu
	ln -sf $(BUILD_DIR)/quick $@

quick-ir: $(ALUMINAC)
	$(ALUMINAC_CMD) --emit-llvm -o quick.ll quick=./quick.alu

# Benchmarks and profiles of aluminac compiling the standard library's tests
# (use PROFILING=1 for an optimized compiler with symbols; TIMES=<n> runs,
# MARKDOWN=1 for a table).
BENCH_INPUT = --test --cfg test_std -c -o /dev/null
.PHONY: bench samply flamegraph
bench: $(ALUMINAC)
	./tools/bench.py -n$(or $(TIMES),20) $(if $(MARKDOWN),--markdown,) $(ALUMINAC_CMD) $(BENCH_INPUT)

samply: $(ALUMINAC)
	samply record -r 10000 --iteration-count 5 $(ALUMINAC_CMD) $(BENCH_INPUT)

flamegraph: $(ALUMINAC)
	flamegraph -F 10000 -o $(BUILD_DIR)/flamegraph.svg -- $(ALUMINAC_CMD) $(BENCH_INPUT)

.PHONY: libc-bindgen cloc clean clean-all
libc-bindgen:
	./tools/libc-bindgen/generate.sh

cloc:
	@cloc --read-lang-def=tools/cloc_language_def.txt $(shell git ls-files)

clean:
	rm -rf $(BUILD_ROOT)
	rm -f aluminac quick quick.ll

clean-all: clean
	cargo clean
