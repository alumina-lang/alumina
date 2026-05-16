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

## THE headline opportunity: per-call / global mono-context isolation

This is the single deepest remaining defect and it gates the majority
of the remaining work (items 3, 6, and part of 4 below). It has been
observed and deferred across many sessions as "the broader per-call
mono-context architectural debt".

**Symptom family.** A monomorphized value comes back as garbage that
characteristically looks like a small integer / line number / id, or
an uninitialized fill pattern (`0xAAAA`, `0xFFFF` = 65535). Concrete
historical instances:

- `test_dyn` (`sysroot/std/typing.alu`, currently `#[cfg(boot)]`):
  `let b: &mut dyn iter::Iterator<Self,i32> = &iter::repeat(42); …
  b.next()` returns `some(1065)` instead of `some(42)` (panic at
  `typing.alu:1066`).
- `test_fuse` / `test_flatten_2` (`std/iter.alu`): `Option<()>`
  debug-fmt rendered as `some((65535, 65535))`. These two were
  **resolved** as a side effect of this effort's union/`mk_if`/
  empty-StructLit fixes — now ungated and passing. Kept here because
  the *mechanism* is the same family and `test_dyn` survives it.

**Crucial diagnostic distinction (verified 2026-05-16):** this is
**NOT runtime test ordering**. `test_dyn`'s faithful standalone body
(shape: `b:&mut dyn Iterator<Self,i32>` = `&iter::repeat(42)`, alias
`a`, `size_hint`, `next×2`, reassign `&iter::once(10)`, `next×2`)
**passes** standalone. But `build/debug/stdlib-aluminac-tests --filter
test_dyn` (compiles the *whole* stdlib, runs only the 5 `test_dyn*`
tests) still **fails**. So a *sibling* monomorphization merely
**present in the same compiled binary** corrupts `test_dyn`'s
`iter::repeat`-backed `Iterator` vtable. It is compile-time global
mono state, not runtime ordering.

**Independent corroboration:** the atomics refactor (item 6) — inlining
each `Atomic<T>` method via statement-level `#[cfg]` returns, which
compiles cleanly under *both* compilers — **re-triggers** this:
`make test-std-aluminac` → `test_flatten_2` SIGSEGV. Merely changing
the mono shape of the `Atomic` methods perturbs global mono enough to
re-break the canary. This proves item 6 is gated on this root.

**Where to look.** aluminac's monomorphizer almost certainly reuses or
aliases a cache/table keyed insufficiently, so a later mono overwrites
or shadows an earlier one. Prime suspects, in rough priority:

1. The **dyn vtable build** at `src/aluminac/mono/lower.alu` ~line
   3821. This site historically had four branches matching
   `def.generic_params.len()` against
   `impl_args.len() + proto_non_self_count`; a fifth was nearly added
   before realizing the real cause is upstream asymmetry in
   `pass2.alu`'s two FnDef-building paths producing asymmetric
   `generic_params` shapes. The right fix is one uniform construction,
   not another branch. Start here for `test_dyn`.
2. `make_fn_ty` / `ir_functions` lookups — a prior id-vs-mangled_name
   ambiguity bug lived here (resolved earlier for a different
   symptom). Re-audit whether vtable/method lookups can still collide
   by id when mangled names differ (or vice versa).
3. The mono `type_map` lifecycle and the const evaluator's
   `ConstEvaluator.variables` / `remapped` / `const_values`
   (`src/aluminac/const_eval.alu`). The `Option<()>` /
   `assert_eq_helper<Option<()>>` formatter-state-leak symptom points
   at per-call mono context not being reset/keyed per instantiation.

**Suggested next concrete step:** a minimal 2-test repro. Take
`test_dyn`'s body plus exactly one sibling
(`test_dyn_multi_protocol` / `_empty_protocol` / `_if_coercion` /
`_if_coercion_switch`, all using Foo/Bar/Quux/Frob defined in the
`typing.alu` tests module) compiled into one program; find which
sibling's presence flips `b.next()` to garbage. The 4 siblings pass
individually; only `test_dyn` (the generic-iterator-adapter dyn) is
corrupted by their co-presence. That isolates the keying bug.

Reproduce and bisect; do not trust narrative — several status entries
about this debt were wrong over the project's life.

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

3. **`test_dyn` (typing.alu)** — flagship instance of the mono-context
   headline. `#[cfg(boot)]`-gated with a precise in-source comment.
   Gated on the mono-context investigation above.
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
