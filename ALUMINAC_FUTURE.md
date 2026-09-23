# aluminac — findings & opportunities

Status snapshot and forward-looking backlog for the self-hosted Alumina
compiler (`src/aluminac/`, Alumina → LLVM IR). Written 2026-05-16 at the
close of the alumina-boot → aluminac parity effort. This file replaces
the now-removed `PORTING.md` / `PORTING_STATUS.md` / `CLAUDE.md` parity
scaffolding; it is intentionally self-contained.

## Where the project stands

**The parity headline is DONE.** There is a single unified `sysroot/`;
`sysroot-aluminac/` has been deleted. The aluminac self-bootstrap
converges: alumina-boot compiles aluminac (s1), aluminac_s1 compiles
aluminac (s2), aluminac_s2 compiles aluminac (s3), and **s2 == s3
byte-identical**, all against `sysroot/`. `make porting-gates` (=
`test-aluminac` + `test-std-aluminac` + `bootstrap` + `test-std` +
`test-libraries` + `test-lang` + `test-diag`) is green. The full
alumina-boot test runner (`sysroot/test.alu`, reflective
`attributed::<()>("test")` discovery) runs under aluminac.

Quality gates (Makefile targets): `make` (build alumina-boot),
`make bootstrap` (3-stage aluminac, must converge), `make
test-aluminac` / `make test-std-aluminac` (aluminac suites),
`make test-std` / `make test-lang` / `make test-libraries` /
`make test-diag` (alumina-boot suites). `make porting-gates` runs the
whole set. `make build/debug/aluminac_s1` builds just stage-1 for fast
iteration; standalone repros: `build/debug/aluminac_s1 --sysroot
sysroot <file>.alu -o out`. alumina-boot is the language spec — when in
doubt, read `src/alumina-boot/src/` and compare; do not infer semantics
from aluminac (it is buggy by definition until proven otherwise).
alumina-boot emits C (not LLVM IR), so an "IR-level diff between the
two compilers" is not a valid debugging strategy.

Hosts: bootstrap works on x86_64 and aarch64 Linux. ABI-sensitive
codegen in `src/aluminac/codegen/` runtime-detects host arch from the
LLVM target triple (`CodegenCtx::is_x86_64` / `needs_sret` /
`uses_byval_attr`); check both when touching those paths.

Coroutines / minicoro / `codegen_func` / `codegen_const` are
deliberately out of scope for aluminac (alumina-boot emits C and
dispatches through them; aluminac uses LLVM intrinsics). LLVM stackless
coroutines is a separate future project, not tracked here.

## Beyond parity (effort started 2026-09-23)

Goal: make aluminac meaningfully better than alumina-boot (diagnostics,
robust mono without "unpopulated symbol"-style failures, cross-compilation,
idiomatic Alumina code), while it stays compilable by alumina-boot and the
sysroot needs few `#[cfg(boot)]`s. alumina-boot remains the default
reference; aluminac rejects what boot accepts only for boot bugs or where
boot misreads the language (record such cases here).

### Done

- **Mono-context isolation (the former headline, `test_dyn`).** Root causes:
  `mono_function` lowered every body against the caller's shared
  `type_map` (new bindings leaked out, unrelated ones leaked in) and kept
  the caller's `expected_type` hint / loop stack; `mono_struct` and type
  aliases bound params into the shared map and never removed them; struct
  type args were never completed with defaults, so `HashMap<K, V>` and
  `HashMap<K, V, DefaultHash>` were distinct types (receiver unification
  then failed and inference fell back to unhinted arguments). Now each
  instantiation gets its own context (own generic params, protocol
  Self/generics the caller binds, and the enclosing context for local
  fns/closures only), and type args are canonicalized. `test_dyn`
  ungated. Regression: `tests/aluminac/mono_context_isolation.alu`.
- Code that relied on the leaks now infers properly: operator-overload
  method generics are unified from the operands (`infer_type_args_from_ir`);
  bare generic struct literals are inferred without first monomorphizing
  the struct with unbound params.
- **if/else branch types** are unified like alumina-boot (a diverging arm
  takes the other's type, otherwise one arm is coerced to the other's
  type, else "mismatched types"). Previously the arm with "more struct
  fields" won and the other arm was *reinterpreted* (an `&[]` arm read a
  garbage slice length).
- **Slice indexing goes through `#[lang(slice_index)]` /
  `#[lang(slice_range_index)]`** like alumina-boot, so `--debug` builds
  are bounds-checked (they never were). Slice range bounds are lowered as
  usize (explicit `range_bound_hint`, not the leaky `expected_type`).
- **Generic statics/consts** are one global per instantiation
  (`lower_static_ref` / `emit_static`, `static_cache`). They used to be
  inlined values: a generic static lost writes, and slicing a generic
  const array (`Type::variants()`) returned a dangling pointer.
- **Consts that cannot be evaluated are an error** that points at the
  sub-expression the evaluator gave up on (`ConstEvalFailure`), instead of
  a silently zero-initialized global. The const evaluator now handles
  slice fields on string constants reached through variables.
- **Macro resolution matches alumina-boot**: unresolved macros are an
  error (they used to be silently dropped — several tests "passed"
  vacuously that way); there is no global by-name fallback (unqualified
  `cfg!` etc. resolved from anywhere); macro invocations/references in a
  macro body resolve at the definition site (hygiene), by stored id.
- **Targets / cfg**: `aluminac::target::Target` (parsed once from the
  triple; `arm64-apple-*` is AArch64) drives cfg keys, LLVM backend init
  and ABI decisions; `aluminac::cfg::CfgSet` has alumina-boot's key/value
  semantics (bare `key` predicates, `target_family`, `output_type`);
  `#[cfg_attr]` and file-level `#![cfg]` work; malformed cfg predicates are
  errors. New CLI: `--target <triple>`, `-d/--debug` (cfg `debug`, as in
  alumina-boot; the Makefile passes it with `-g`), real errors for unknown
  options / missing values.
- The `ir_functions` use-after-free (element pointer held across pushes).
- macOS (arm64, Homebrew LLVM 21) bootstraps; `make bootstrap` compares
  the IR emitted by stage 2 and 3 (linked binaries are not reproducible on
  macOS).
- Stdlib: `HashMap::contains`, `Command::status`, `Type::variant_name`.
- Test runner: compile-fail tests can require `// EXPECTED_ERROR: text`.

- Codegen and mono caches are keyed by value, not by weak hashes: the
  djb2 `name_hash` collided (`"gz"` and `"i8"` shared a string constant;
  the same hash keyed function/global declarations), lang items were
  looked up by djb2 hash, and the mono caches by an FNV hash of pointers
  (`MonoKey` now compares id, type args and enclosing instantiation).
- Module paths match alumina-boot: a file given without `module=` is a
  module named after its stem, and `module_path` is absolute (`::a::b`).
  Test names print correctly. Stdlib: `Path::{file_name, file_stem,
  extension}`, `string::rfind_char`.
- `tests/aluminac/cross_check.sh` runs every aluminac test through
  alumina-boot. `// BOOT_DIVERGES: reason` marks justified divergences.

- **Threading works under aluminac** (`--cfg threading`; the Makefile now
  passes it, like for alumina-boot). Fixes: the entry point is the
  sysroot's `#[lang(entrypoint_glue)]` instantiated for `main` (it runs
  `threading_init`; codegen's hand-built C `main` is only a fallback for
  freestanding programs); `#[link_name]` symbols are emitted raw (`\x01`),
  like alumina-boot's C asm labels; method receivers auto-deref through
  any number of pointers; `for x in e` iterates `e` in place rather than a
  copy (a channel's copied mutex deadlocked the thread pool).
- `for const` loops: each step builds a fresh const evaluator (the old one
  held slices of `ir_functions` across lowering — use-after-free that cut
  loops short), and `const_replacements` are per instantiation (a
  recursive instantiation clobbered the caller's loop variable). With
  closure captures in `fields<T>`, `test_debug_formatter` is ungated.
- Unresolved identifiers/paths are errors ("could not resolve the path"),
  as are paths to non-values; they used to become a silent bogus local
  (`let b = undefined_thing;` compiled; `libc::libc::X` in the sysroot
  became `undef` and broke `RwLock` on macOS).

### alumina-boot bugs found (aluminac deliberately differs)

- `Ty::gcd` joins `&mut T` and `&T` to `&mut T` (its own `assignable_from`
  treats `&T` as the supertype), so `if c { &x } else { &y as &T }` is
  rejected. aluminac joins to `&T` (`if_branch_mut_const_pointer.alu`).
- Later path segments resolve lexically in the module found so far, so
  `std::std::mem::size_of` and `libc::libc::X` compile (the latter was a
  typo in `std::sync`, now fixed). aluminac resolves each later segment in
  the module named so far only, and reports the path.

### Cross-check divergences to resolve (2026-09-23 snapshot)

aluminac-only by design: `atomic_intrinsics`, `llvm_intrinsics`,
`lang_items`. The rest are aluminac leniencies (invalid tests to fix, and
aluminac checks to add) or possible alumina-boot bugs to confirm:
- generic arity unchecked ("N generic parameters expected"): `cmp_enhanced`,
  `fmt_extended`, `fn_bounds_test`, `iter_sum`, `mem_extended`,
  `proto_meta`, `proto_same_base_as`, `vector_iter`;
- protocol conformance (bounds / mixins) unchecked:
  `builtin_protocol_conformance`, `operator_overload`, `switch_nonint`,
  `unified_sysroot_basic`, `mixin_own_generics`;
- name resolution too permissive: `never_named` (`never` is not a name),
  `range_equatable` (`RangeFull`), `tuple_return_infer` (`zeroed`),
  `method_arg_slice_empty_inference` (`std::mem::Pointer`), and
  `std::io::ErrorKind`;
- integer literal range unchecked: `bit_twiddle` (171 as i8);
- implicit coercions: `char_literal_expected_type` (`Option<u8>` as
  `Option<u16>`), `collections_extended` (`i32` as `&mut i32`),
  `default_type_arg` (`A` as `&A`), `closure_features` (distinct closure
  types), `switch_arm_type_unify` (`()` arm vs tuple arm);
- field vs method precedence: `iter_adapters`;
- misc: `nested_items` (impl without type), `typing_extended`,
  `typeop_args_return`, `dyn_fmt_byte_slice` (boot: cyclic dependency);
- possible alumina-boot bugs: `mixin_features` / `mixin_self_subst`
  (boot ICE "unbound placeholder"), `protocol_conformance` (boot-compiled
  binary segfaults), `bit_twiddle_const` (boot cannot const-eval);
- runtime disagreement: `fields_intrinsic` (exit 23),
  `protocol_bound_strict` (exit 1), `link_name_attr` (C compile error).

### Backlog (found along the way)

- **Strictness gaps vs alumina-boot** (aluminac accepts invalid code):
  protocol bounds are not fully checked (`unified_sysroot_basic`'s `Point`
  lacked `not_equals`); `use std::io::ErrorKind` resolved although
  `ErrorKind` lives in `std::io::unix`; `coerce_int` inserts implicit casts
  between *any* builtin types (incl. float→int); `resolve_type` maps an
  unbound placeholder to `void` silently; an undefined variable reported
  nothing and an undefined function "expression is not callable".
- Codegen turns a missing function/global into a warning + `undef`; these
  are internal errors.
- Const-eval gaps (now reported, not silent): array-to-slice casts, slices
  of slices, pointer arithmetic into arrays.
- Mono lowers call arguments twice (once for inference without hints, once
  for real); inference should be driven by expected types like
  alumina-boot's type hints.
- `make test-std-aluminac` still lacks `--cfg libbacktrace` and
  coroutines (aluminac has no stackful coroutines).
- Duplicate `#[lang]` items are not rejected (a later one silently wins).
- One unresolved path yields several cascading errors in mono ("expression
  is not callable" ×N, "could not resolve field on ()").
- macOS: 13 `std::net` tests fail (aluminac-compiled only);
  `warning: codegen: field index out of bounds` at `std/fmt/mod.alu:525`.
- Cross-compilation: `--target` exists, but ABI lowering only knows
  x86_64 SysV / AAPCS64 (Apple arm64 variadics differ), there is no
  per-target sysroot/linker story, and only x86_64/aarch64 parse.

## Remaining `#[cfg(boot)]` gated tests (the cleanup queue)

Goal: `#[cfg(boot)]` should be a small, justified allowlist. All 54
`cfg(boot)`/`cfg(not(boot))` sites were reviewed and this
classification confirmed by the maintainer. Items 1, 2, 5 are DONE
this effort (13+ gates removed); the rest is backlog.

### APPROPRIATE — keep (genuine boot-only-by-design; both sides real)

The legitimate, permanent allowlist — aluminac fundamentally uses a
different mechanism and both paths are fully implemented:

- `std/intrinsics.alu` `#[cfg(boot)]`/`#[cfg(not(boot))]` blocks:
  `codegen_func`/`codegen_const`/`codegen_type_func` (boot, C
  emission) vs aluminac LLVM intrinsics (`llvm`, `stack_alloc`,
  `atomic_*`). The core divergence model.
- `std/builtins.alu` `count_ones`/`ctlz`/`cttz` (C/libc vs
  `intrinsics::llvm`), `checked_add/sub/mul` vs `__builtin_*_overflow`,
  `wrapping_add/sub/mul` (C vs LLVM wrap). Real C-vs-LLVM semantics.
  *Style nit only:* could be inline `if in_const_context() … else
  when cfg!("boot") … else …` — but see the `when cfg!`
  name-resolution constraint under item 6.
- `std/mem.alu` `stack_alloc` fn pair + `test_stack_alloc` /
  `test_const_stack_alloc` (boot-only codegen_func; aluminac has its
  own `intrinsics::stack_alloc` tested elsewhere).
- `std/sync/mod.alu` `test_ordering_values_match` (boot-only
  `codegen_const` C-constant check; aluminac coverage is
  `tests/aluminac/atomic_intrinsics.alu`).

### DONE this effort

1. **i128/u128 literal gap — fixed, 10 gates removed.** Root: integer
   literals stored as `u64` across parser/AST/IR, truncating 128-bit
   literals (`i128::max_value()` = `0x7fff…ffffu128 as i128` collapsed
   to all-ones). Threaded the full value: `parser/mod.alu`
   `parse_int_with_suffix` → `u128`; `ast.alu`
   `_ExprLitData`/`_IrLitData` gained `int_val_hi` (+`int_val_u128()`);
   `mono/lower.alu` `mk_int_lit_u128`; `llvm.alu` binds
   `LLVMConstIntOfArbitraryPrecision`; both IntLit codegen paths emit
   `[lo,hi]` words for >64-bit int types. Regression
   `tests/aluminac/i128_u128_literals.alu`. **Deferred sub-item
   (non-blocking):** const-eval of 128-bit values
   (`_CVIntData`/`const_eval.alu` int arithmetic still `u64`) — only
   matters for a 128-bit literal in a `const`/static initializer
   (none of the removed gates needed it). If needed: add `int_val_hi`
   to `_CVIntData`, `ConstValue::make_int_u128`, and 128-bit paths in
   `const_eval.alu` int arithmetic/compare/cast.
2. **per-call mono-context (test_fuse/test_flatten_2) — ungated.**
   Eliminated by this effort's union/`mk_if`/empty-StructLit fixes.
   The deeper variant survives as `test_dyn` (headline section).
5. **vestigial `test_cases!()` deleted** end-to-end (dead since
   `test.alu` uses `attributed::<()>("test")`): the macro decl
   (`std/macros.alu` now cfg-clean), `expand_test_cases` + builtin
   dispatch (`parser/expr.alu`), `all_test_functions` /
   `share_test_functions` (`parser/mod.alu`), call site (`main.alu`).

### TODO — backlog

3. ~~`test_dyn` (typing.alu)~~ — fixed by mono-context isolation, ungated.
4. **Three distinct deeper feature gaps** (probed 2026-05-16, each
   still independently fails):
   - `std/typing.alu` `test_type` / `element_types`: needs
     **type-level tuple *range* slicing `Tup.(1..)` + splat in tuple
     construction** (the `tuple_map_of<T,U>` typeop). This effort
     added single-index type-level projection (`TyTag::TupleIndexOf`,
     the `tuple_index_of` grammar node — `parser/pass2.alu`
     `parse_type` + `mono/lower.alu` `resolve_type` + `ast.alu`);
     extend to a range/splat form (check `node-types.json`).
   - `std/fmt/mod.alu` `test_const_println`: const-eval doesn't fold
     the `format!`/`_finish_format(...)` helper-call chain in a
     `const { … }` block. Overlaps the deferred const-eval work.
   - `std/fmt/mod.alu` `test_debug_formatter`: the `debug()` adapter
     needs broader reflection (closure introspection, enum-as-integer
     cast fmt, union-as-`<union>`, named-type display). This effort
     added fn-type reflection (`Type::new::<fn>().name()`/
     `.module_path()` via `IrTyTag::Fn` in
     `lower_type_name`/`lower_module_path` +
     `scope.alu::find_fn_container_scope_by_id`); isolate the first
     failing `debug()` sub-case (`fmt!("{}", debug(42))`).
6. **atomics inline-dispatch refactor** — *gated on item 3*. Desired
   shape: statement-level `#[cfg(boot)] return …; #[cfg(not(boot))
   return …; intrinsics::unreachable()` inlined into each `Atomic<T>`
   method, deleting `std/sync/mod.alu`'s `atomic_internal` `#[cfg]`
   twin. Compiles cleanly under both compilers (verified) but
   re-triggers the item-3 mono-context pollution
   (`test_flatten_2` SIGSEGV). Land after the mono-context root is
   fixed. `atomic_internal` stays meanwhile (correct, just not the
   desired shape).

   **Name-resolution constraint (important, was stale in prior
   comments):** aluminac **elides** the non-selected branch of a
   statement-level `when cfg!(...)` from name resolution;
   **alumina-boot does NOT**. A statement-level `#[cfg(...)]`
   attribute **does** elide in *both*. So inline boot/aluminac
   dispatch must use `#[cfg]`-attributed statements, not `when cfg!`
   (the aluminac `intrinsics::atomic_*` are `#[cfg(not(boot))]`-
   declared and would fail to name-resolve under alumina-boot in a
   non-selected `when cfg!` arm).

## Codegen / mono audit class (focused pass)

Recurring family resolved several times this effort: an expression
that is ZST / void / never-typed is short-circuited in codegen or mono
**without evaluating its side-effecting base or control flow**. Fixed
instances: `IrTag::FieldAccess` returning `undef` for a ZST field
without evaluating `expr.lhs()` (broke `HashMap<K,()>` `?`-early-
return); empty-StructLit const init (`&fields[0]` on a 0-len slice);
`mk_if` result type collapsing to `never` when a sibling switch arm
diverged (the std/net `SocketAddr::new` union miscompile); zero-sized
aggregate member layout using an `i8` placeholder (HashSet stride).

**Opportunity:** sweep `src/aluminac/codegen/fn_codegen.alu` and
`src/aluminac/mono/lower.alu` for every `is_void_type` /
`is_zero_sized` / "Fn is a ZST" / void-result early `undef`
short-circuit (~20 sites); verify each still evaluates operands/base
for effect before discarding. Known un-acted asymmetry: `gen_switch`
derives the phi/result type from the reaching arm when
`llvm_type(result_ty)` is void; `gen_if` does not (bails to
`LLVMGetUndef(void)`). The `mk_if` IR-level fix removed the immediate
trigger but the asymmetry is latent — port `gen_switch`'s
derive-from-reaching-arm + single-predecessor-no-phi handling into
`gen_if`, with a regression.

## Other architectural opportunities (non-blocking)

- **Type-level tuple ops.** `TyTag::TupleIndexOf` (single index)
  added; range slicing + splat-in-tuple-construction still missing
  (blocks `tuple_map_of` / `element_types`). Likely a clean extension
  of the same parse_type/resolve_type machinery.
- **Reflection breadth.** `Type::new::<fn>()` name/module_path now
  work and `type_of<typeof(x)>` resolves (via `tuple_index_of`);
  closure/enum/union/named-type `debug()` is the remaining gap. A
  pass enumerating `std::typing::Type` methods vs alumina-boot's
  `intr_*` would cheaply surface what's left.
- **Const-eval completeness.** Doesn't fold calls through
  `format!`/`_finish_format`; `u64`-bounded for 128-bit ints.
  Structured comparison vs `src/alumina-boot/src/ir/` const-eval if
  this becomes a priority (alumina-boot's interpreter is ~2000 LoC;
  aluminac's gaps: pointer-arena chasing, dyn dispatch, heap-bake).
- **Fully-qualified macro paths.** `std::println!`/`std::eprintln!`
  silently expand to **nothing** under aluminac (no output, no
  error); unqualified prelude forms work. Real macro-path-resolution
  gap; own slice + regression. Not parity-blocking (sysroot uses
  unqualified forms) but a sharp edge.
- **`when cfg!` name-resolution asymmetry.** (See item 6.) Making
  aluminac and alumina-boot agree (ideally both elide non-selected
  `when cfg!` arms from name resolution) would unblock the cleaner
  inline-dispatch style across `builtins.alu` and `sync/mod.alu`.

## Test infrastructure backlog

- `make test-lang-aluminac` — run `tests/lang/lang.alu` under
  aluminac (`--cfg test --cfg test_std` already supported).
- `make test-libraries-aluminac` — compile `libraries/` with
  aluminac `--test` (may need closure/dyn coverage).
- `make test-docs` under aluminac — gated on full sysroot/doc parity.
- `make test-diag` stays alumina-boot-only by design.

`tests/aluminac/*.alu` is the aluminac feature suite (run by
`tests/aluminac/run_tests.sh`); add a regression per concrete fix.
Regressions added this effort: `i128_u128_literals`,
`typeop_tuple_index_of`, `reflect_fn_type_name`,
`use_exposes_top_module`, `const_zst_struct_descriptor`,
`union_switch_arm_value`.

## Operating notes (carried over from the retired scaffolding)

- alumina-boot's behavior is the spec; verify framings against
  `src/alumina-boot/src/`, not against prose — status narratives went
  stale repeatedly over this project.
- When patching the same dispatch site twice (a second special-case
  branch), stop: the model is likely wrong-shaped and the fix is
  upstream (the dyn-vtable 4-branch site at `mono/lower.alu` ~3821 is
  the canonical example).
- Alumina `switch` is sugar for if-else; when fixing switch-pattern
  bugs, check whether an integer fast-path is even needed.
- Add a `tests/aluminac/` regression for every concrete bug fixed.
