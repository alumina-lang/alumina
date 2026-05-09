# Porting status

Live source of truth for the aluminac → alumina-boot parity work. See `PORTING.md` for the rules and workflow.

**Statuses:**

- `[DONE]` — implemented and verified by a test, plus `make bootstrap` passes.
- `[PARTIAL]` — work started, gaps remain. **Must include a `Missing:` block.**
- `[TODO]` — identified, not started.

**At session start:** prefer closing `[PARTIAL]` entries over picking up new `[TODO]` ones. Don't mark anything `[DONE]` without a test exercising it.

---

## [DONE] Initial audit

Completed 2026-05-09. Categories below populated by parallel audit of `src/alumina-boot/src/` vs `src/aluminac/`, the two sysroots, the Makefile and existing test runners. The audit is intentionally non-exhaustive in spots (especially language features — see the `[PARTIAL]` extension below); future sessions should grow the lists as gaps surface.

## [PARTIAL] Audit extension — language-feature deep dive

The first audit pass produced only ~7 language-feature gaps. That's almost certainly low: aluminac is roughly 1/3 the LoC of alumina-boot and the boot AST has machinery (closures' captured-env lowering, mixin substitution, full macro hygiene, etc.) that one short audit doesn't enumerate.

Missing:
- Side-by-side AST node coverage: enumerate every `ExprKind` / `Ty` / `Statement` variant in `src/alumina-boot/src/ast/mod.rs` and verify aluminac's `ast.alu` covers it (or note the gap).
- Side-by-side macro support: `src/alumina-boot/src/ast/macros.rs` is ~800 LoC; map each capability (universal-call macros, `et cetera` packs, named-arg expansion, hygiene, recursion limits) to the aluminac equivalent or a `[TODO]`.
- Side-by-side mixin support: alumina-boot's mixin substitution rules vs aluminac's; verify with deliberately tricky cases (mixin with generics, mixin referencing Self, mixin chaining).
- Closure capture: aluminac has tests/aluminac/closures.alu so the basic case works, but capture-by-reference, closure-of-closure, and ProtoClosure conformance need confirming.
- Attribute parity: walk every variant of `enum Attribute<'ast>` in `src/alumina-boot/src/ast/mod.rs` (Packed, TupleCall, ConstOnly, NoConst, Transparent, MustUse, LinkName, Coroutine, Custom) and add a `[TODO]` per gap.

---

## Language features

*(Parser/AST/type system features in alumina-boot but not aluminac.)*

- [PARTIAL] **`dyn` / dynamic dispatch.** Aluminac now PARSES `&dyn Proto` and `&mut dyn Proto`, COERCES `&T` to `&dyn Proto` (with a null-vtable fat pointer), and DISPATCHES method calls on dyn-typed receivers (emits Unreachable typed as the method's return type — runtime would crash but mono completes). This unblocks `panic_impl`'s body — Option::unwrap and friends now compile through the unified sysroot. Verified by `tests/aluminac/unified_sysroot_basic.alu` (Option::unwrap on the happy path).

  Missing (real dyn semantics, not just typecheck):
  - Vtable construction at `&x as &dyn Proto`: build a static array of fn pointers for each method in Proto, emit pointer to it. Currently the vtable is null, so any actual dispatch crashes.
  - dyn_vtable_index runtime path: emit `dyn_vtable_index(dyn_val, idx)(dyn_data(dyn_val), args...)` instead of Unreachable.
  - Multi-protocol bounds: `&dyn (A + B)` is parsed but only the first protocol is captured.
  - dyn_self lang item — `Self` substitution in protocol method signatures inside dyn context (currently resolves to void via the existing fallback, which works for monomorphic cases like Formattable's Self).
  - Self-substitution in protocol method return types: e.g. `fn foo() -> &Self` would currently resolve to `&void`. Test before declaring DONE on that path.

  Used by `sysroot/std/regex/`, `sysroot/std/runtime/backtrace.alu`, `sysroot/std/io/`, `sysroot/std/typing.alu`, and `sysroot/std/panicking.alu`'s `panic_impl`. With the dyn shim in place, the milestone test now exercises Option::unwrap end-to-end on the happy path.
- [DONE] **`when` for types (`when_type`).** Already supported. `tests/aluminac/when_type.alu` covers `type T<X> = when cond { A } else { B };`. Audit was wrong on this one.
- [TODO] **`Ty::Tag` / `Expr::Tag` wrapper nodes.** alumina-boot uses these for type-level metadata; absent in aluminac. Confirm whether sysroot actually requires them (may be internal to boot).
- [TODO] **Coroutines / yield (out of scope per `PORTING.md`).** Grammar has `yield_expression` and the `*`-marked coroutine function form; aluminac never parses either. Keep gated under `cfg(coroutines)` in sysroot. Listed for completeness only — no porting work.
- [TODO] **Attribute: `#[transparent]`.** alumina-boot recognizes; aluminac's `AttrTag` doesn't. Used in sysroot to mark layout-equivalent newtypes.
- [DONE] **Attribute: `#[link_name("…")]`.** Wired through pass1 → AttrTag::LinkName → mono mangled-name override. `tests/aluminac/link_name_attr.alu` declares `extern "C" fn c_string_len` pointing at libc `strlen` and verifies the call resolves correctly (and the negative — without the attribute it link-fails on `c_string_len`). The previous mis-routing to `AttrTag::Extern` is fixed.
- [TODO] **Attribute: `#[packed(N)]`.** alumina-boot's `Attribute::Packed(usize)`; missing in aluminac. Affects struct layout for FFI structs.
- [TODO] **Attribute: `#[tuple_call]`.** alumina-boot's `Attribute::TupleCall`; missing in aluminac.
- [TODO] **Attribute: `#[const_only]` / `#[no_const]`.** alumina-boot has both; aluminac has neither. Used in `sysroot/std/intrinsics.alu` to mark functions that must / must-not run at const time.
- [TODO] **Attribute: `#[must_use]` / `Diagnostic(MustUse)`.** alumina-boot warns on dropped values; aluminac doesn't model the diagnostic.
- [PARTIAL] **Attribute: `#[inline(...)]` modes.** Pass1 parses the meta-item argument and dispatches to `Inline` / `AlwaysInline` / `NeverInline` / `InlineIr`. NeverInline lowers to LLVM `noinline`. Verified by `tests/aluminac/inline_attr_modes.alu`.
  Missing:
  - alumina-boot's `Inline::DuringMono` is what `#[inline(ir)]` maps to in alumina-boot — a mono-time inliner. Aluminac maps `#[inline(ir)]` to `AttrTag::InlineIr` (parsed correctly) but doesn't *act* on it: the mono pass doesn't inline marked functions before codegen. Many sysroot helpers (e.g. `mem.alu`'s slice constructors, util.alu's `cast`/`coerce`/`transmute`) rely on this for correctness when the body uses generics that would otherwise become unresolved at runtime. Wiring a real IR-level inliner is a substantial slice — aluminac currently emits a regular call and trusts LLVM to inline.
  - The redundant `#[always_inline]` standalone attribute name is still parsed for backwards-compat with sysroot-aluminac code; consider deprecating once the sysroot uses the canonical `#[inline(always)]` form.
- [TODO] **Custom attributes (`Attribute::Custom`).** alumina-boot stores arbitrary `#[name(args…)]` on AST items so intrinsics like `attributed(...)` can find them. aluminac drops anything not in its `AttrTag` enum.
- [PARTIAL] **u128 / i128 codegen + const-eval coverage.** Runtime arithmetic, comparison and casts verified by `tests/aluminac/u128_i128_basic.alu`. LLVM 128-bit integer codegen works; integer-literal parser is u64-bounded so values needing >64 bits must be constructed via shifts / wrapping arithmetic.
  Missing:
  - 128-bit integer literals beyond u64 range (e.g. `170141183460469231731687303715884105727i128`) — `parse_int_with_suffix` stores in u64. Consider a u128-internal representation.
  - Const-evaluation of u128/i128 arithmetic — `const_eval.alu` may still represent integer values as 64-bit; verify and extend.
  - Formatting (`fmt`) — sysroot-aluminac's u128/i128 lang stubs don't implement `fmt`; values can't be printed without precision-loss-causing cast to u64.
- [PARTIAL] **Operator-overload dispatch.** Operator overloading works in aluminac, but via method-name matching (`try_operator_overload` in `mono/lower.alu`), not via the `operator_*` lang items. User-defined `equals` / `compare` etc. on structs is dispatched through `==` / `<` correctly (verified by `tests/aluminac/operator_overload.alu`). The unused `binop_lang_name` helper is dead code.
  Missing:
  - Wire actual `operator_eq` / `operator_neq` / `operator_lt` / `operator_lte` / `operator_gt` / `operator_gte` lang-item queries so impls can be tagged with `#[lang(operator_…)]` and resolved through the lang item indirection (matches alumina-boot's mechanism). Lower priority — method-name dispatch covers the same functional ground for now.
- [PARTIAL] **`Lang::EntrypointGlue`.** Aluminac still uses a hardcoded entrypoint in codegen/mod.alu (sysroot's `entrypoint_glue` lang item is unused). Several blockers for migrating to sysroot-defined glue have been fixed: function names now resolve as types (parser pass2 + mono resolve_named_type → Fn IrTy), calls returning Fn-typed values now codegen correctly (Fn is treated like void at the LLVM level). Verified by `tests/aluminac/fn_item_via_generic.alu` exercising the `unit::<F>()` → `func()` pattern.
  Missing:
  - Recognize the `entrypoint_glue` lang item and dispatch to the sysroot-defined function instead of building the hardcoded entrypoint.
  - Coroutine-aware logic in the sysroot glue (gated under `cfg(coroutines)` — out of scope).
  - The `arguments_of<F>` typeop and `typing::matches::<A, B>()` are also referenced by sysroot's glue; these need separate slices.
- [TODO] **Verify `ProtoZeroSized` is enforced as a generic-bound at typecheck (not just `is`-check).** The `proto_zero_sized` lang item is queried in the `t is Proto` runtime/typecheck path (good); confirm it's also enforced when used in a `where` clause / generic bound (e.g. rejecting `unit::<i32>()` where `i32: ZeroSized` is false). Test by writing a function bounded on `ZeroSized` and instantiating with a non-ZST.

- [DONE] **Range-literal type inference.** `mono/lower.alu` previously hardcoded `Range<usize>` for every range literal. Now infers T from the lower / upper operand types (both must agree, otherwise falls back to usize). `0i32..10i32` produces `Range<i32>` as expected. Verified by the strengthened `tests/aluminac/proto_range_of.alu`.

- [PARTIAL] **Slice `_ptr` / `_len` field access.** `mono/lower.alu`'s `resolve_field` now treats slice values as having pseudo-fields `_ptr` and `_len` matching sysroot's `slice<Ptr>` struct convention. Verified by `tests/aluminac/slice_field_access.alu`. Unblocks the unified `sysroot/std/mem.alu` past the `slice::len` / `slice::as_ptr` impls.
  Missing:
  - Field-write access through `_ptr` / `_len` (currently read-only). `s._len = 5` does not work; sysroot doesn't seem to mutate these fields, but verify before declaring DONE.
  - `_ptr` / `_len` access on `&slice` (auto-deref) — should already work via the existing pointer auto-deref path; not yet exercised.

## Const evaluation

- [TODO] **Signed-integer overflow detection.** alumina-boot rejects signed overflow as UB at const time; aluminac silently wraps. Affects correctness of `const FOO: i32 = …` that overflows.
- [TODO] **`checked_add` / `checked_sub` / `checked_mul` / `checked_div` intrinsics.** Used by `std::math` and various sysroot bounds checks. tests/aluminac/checked_arithmetic.alu exists — confirm whether it exercises the const path.
- [TODO] **`checked_shl` / `checked_shr` intrinsics.** Reject shift ≥ bitwidth at const time.
- [TODO] **`const_panic` intrinsic.** Halts compilation with a message during const eval. aluminac currently no-ops; needed for `static_assert`-style patterns.
- [PARTIAL] **`compile_fail` / `compile_warn` / `compile_note` intrinsics.** Now emit real compile-time diagnostics via `m.emit_diag` with the call-site span and the literal-string argument. Verified by `tests/aluminac/compile_fail_intrinsic.alu`. compile_fail correctly aborts the build.
  Missing:
  - `const_warning` / `const_note` / `const_panic` (the const-eval-context variants) are still no-ops in `lower_const_runtime_noop`. They should fire when reached through the const evaluator, not when reached at runtime — wire once the const-eval recursive interpreter actually invokes them.
  - Non-string-literal message argument (e.g. `compile_fail!(format!(...))`) is silently treated as empty. Either accept that limitation explicitly or evaluate the argument as a const-string at compile time.
- [TODO] **`const_alloc` / `const_free` / `const_bake` intrinsics.** Needed to let const evaluation build heap-allocated descriptors that get baked into rodata. Big lift; required for `enum_variants`, `fields`, etc. to return slices.
- [TODO] **Const-evaluable function calls.** alumina-boot has a full interpreter (`ir/const_eval.rs` ≈2000 LoC) that evaluates arbitrary pure functions. aluminac's interpreter (`const_eval.alu` ≈1400 LoC) is narrower — characterize and close the gap. (Bang-for-buck task; many other items depend on it.)
- [TODO] **`enum_variants` intrinsic.** Returns slice of variant descriptors. Depends on `const_alloc` / `const_bake` and on lang item `enum_variant_new`.
- [TODO] **`fields` intrinsic.** Returns slice of field descriptors. Depends on lang items `field_descriptor_new` / `field_descriptor_new_unnamed`.
- [TODO] **`vtable` intrinsic.** Builds a protocol vtable at const time. Blocks `dyn`.
- [TODO] **`attributed` intrinsic.** Finds items by attribute name. Depends on custom-attribute support landing first.
- [TODO] **`value_of` intrinsic.** Yields the runtime lvalue of a const/static.
- [TODO] **`named_type_name` intrinsic.** Short form of `type_name` (struct/enum simple name only).
- [TODO] **Float classification (`is_finite` / `is_nan` / `is_infinite` / `is_normal`) at const time.** alumina-boot supports; aluminac runtime-only.
- [TODO] **Bit-twiddling intrinsics: `count_ones` / `count_zeros` / `leading_zeros` / `trailing_zeros` / `swap_bytes`.** Both at const-eval and codegen. alumina-boot maps to `__builtin_popcount` etc.; aluminac should map to the corresponding LLVM intrinsics.
- [TODO] **Const-evaluable indexing into string / byte-string / array literals.** Re-confirm behavior matches alumina-boot for OOB and for negative indices via wrapping arithmetic.

## Codegen

*(LLVM IR coverage: intrinsics, ABI, attributes, debug info, panic/backtrace.)*

- [TODO] **Intrinsic: `codegen_func`.** alumina-boot calls arbitrary C builtins by name. aluminac has the lower-level `llvm<>()` escape but no by-name dispatch. Either expose a similar lowering path or migrate sysroot to use `llvm<>()` directly (see `PORTING.md` "Out of scope" — this is the intrinsic explicitly called out).
- [TODO] **Intrinsic: `codegen_const`.** Reference C macro / linker constants by name.
- [TODO] **Intrinsic: `codegen_type_func`.** Type-level compiler functions beyond `size_of` / `align_of`.
- [PARTIAL] **Intrinsic: `expect`.** Recognized in `mono/intrinsics.alu`; lowered as identity (returns its value-argument unchanged). Verified by `tests/aluminac/expect_intrinsic.alu`. Sysroot `likely!` / `unlikely!` macros now compile under aluminac.
  Missing:
  - Lower to actual `llvm.expect.i1` for branch-prediction benefit. Requires bool-as-i8 ↔ i1 conversion sandwich (aluminac stores bools as i8 in memory to avoid i1-load UB).
- [TODO] **Intrinsic: `tuple_invoke`.** Apply a callable to a tuple of args. Used in macro-heavy code paths.
- [TODO] **Intrinsic: `module_path`.** Returns the module path string of an item.
- [TODO] **Intrinsic: `has_attribute`.** Already partially needed for the `attributed` intrinsic above.
- [TODO] **Function attribute lowering: `#[align(N)]` on functions.** Codegen ignores; emit `align N` on LLVM function.
- [TODO] **Global attribute lowering: `#[align(N)]` on statics.** Codegen ignores.
- [DONE] **Function attribute lowering: `#[link_name("…")]`.** mono/lower.alu now consults LinkName when computing mangled_name; the LLVMAddFunction call uses the override. Tested in `tests/aluminac/link_name_attr.alu`.
- [TODO] **Verify `#[returns_twice]` on declarations.** `add_fn_attribute(... "returns_twice")` is called in `codegen/mod.alu:849` for definitions; confirm it's also set on extern declarations of `setjmp`-family functions.
- [TODO] **Variadic / va_list intrinsics.** `va_start` / `va_arg` / `va_end` — confirm whether sysroot needs these (they appear in `libc/bindings.alu`).
- [TODO] **`#[link("…")]` / linker-arg attributes.** alumina-boot threads `-llib` flags from `#[link]`; aluminac currently relies on `--link-args`. Migrate to attributes so sysroot doesn't need the Makefile to know what to link.
- [TODO] **Debug info (DWARF).** alumina-boot emits `#line` directives in C; aluminac emits no DWARF. Required for `std/runtime/backtrace.alu` to produce useful traces.
- [TODO] **Panic location capture.** Compiler intrinsic that yields the caller `(file, line)` pair for `panic!`. Verify aluminac path matches alumina-boot's.
- [TODO] **ZST elision pass.** alumina-boot has `codegen/elide_zst.rs`; aluminac generates LLVM IR for ZST loads/stores anyway. LLVM may eliminate them — not a correctness issue, just IR quality.

## Lang items

*(Names from `src/alumina-boot/src/ast/lang.rs`. "Defined" = declared via `#[lang(…)]` in the sysroot. "Queried" = the compiler actually looks the name up.)*

- [DONE] **Builtin types** (`builtin_bool`, `builtin_u8…u64`, `builtin_usize`, `builtin_i8…i64`, `builtin_isize`, `builtin_f32`, `builtin_f64`, `builtin_array`, `builtin_tuple`, `builtin_callable`). Defined and queried in aluminac. Verified by tests/aluminac/lang_builtin.alu.
- [DONE] **`builtin_never`, `builtin_u128`, `builtin_i128`.** All three are now registered in aluminac's BuiltinType-name table and have `#[lang(builtin_X)]` stubs in `sysroot-aluminac/std/builtins.alu`. Verified by `tests/aluminac/u128_i128_basic.alu` (u128/i128 arithmetic + lang methods) and `tests/aluminac/never_named.alu` (`-> never` and `-> !` interchangeable; never coerces to other types).
- [DONE] **Protocol lang items** for: `proto_primitive`, `proto_numeric`, `proto_integer`, `proto_floating_point`, `proto_signed`, `proto_unsigned`, `proto_pointer`, `proto_array`, `proto_tuple`, `proto_struct`, `proto_enum`, `proto_union`, `proto_range`, `proto_named_function`, `proto_function_pointer`, `proto_closure`, `proto_callable`, `proto_any`, `proto_none`. Verified by tests/aluminac/protocol_conformance.alu.
- [DONE] **`proto_zero_sized`.** Queried in `mono/lower.alu` (line 2909) inside the `t is Protocol` lowering path. Audit was wrong on this one.
- [PARTIAL] **`proto_const`, `proto_static`, `proto_array_of`, `proto_pointer_of`, `proto_range_of`, `proto_meta`, `proto_same_base_as`, `proto_same_layout_as`.** All eight are now declared as `#[lang(...)]` protocols in `sysroot-aluminac/std/builtins.alu`. Real query semantics implemented for `proto_array_of`, `proto_pointer_of`, `proto_same_layout_as` in `mono/lower.alu`'s TypeCheck path. Verified by `tests/aluminac/proto_extras.alu`.
  Missing:
  - `proto_const` / `proto_static`: item-vs-type bound semantics (the bound applies to a named const/static, not to a value's type). Aluminac currently treats them as trivially-true empty protocols. Needs a separate machinery to distinguish.
  - `proto_meta`: should match types that are protocols themselves. Aluminac's IrTy doesn't currently expose protocol-ness reflectively; trivially-true today.
  - ~~`proto_range_of<T>`: should match a range whose endpoint type is T~~ — done in commit following this entry. Verified by `tests/aluminac/proto_range_of.alu`. Caveat: aluminac's range-literal lowering separately forces the element type to `usize` regardless of operand types — see new entry below.
  - `proto_same_base_as<T>`: should match types that are monomorphizations of the same base generic as T. Trivially-true today.
- [TODO] **Slice operation lang items** (`slice_new`, `slice_const_coerce`, `slice_const_cast`, `slice_index`, `slice_range_index`, `slice_slicify`). aluminac open-codes slice operations today instead of going through these; sysroot uses them. Wire queries so the unified sysroot's `impl Slice` blocks are reached.
- [TODO] **Range constructor lang items** (`range_full_new`, `range_from_new`, `range_to_new`, `range_to_inclusive_new`, `range_new`, `range_inclusive_new`). aluminac inlines range construction. Query so user-written range literals dispatch through them.
- [TODO] **`range_full`, `range_from`, `range_to`, `range_to_inclusive`.** Type-level lang items. aluminac queries `range` and `range_inclusive` only; add the rest.
- [PARTIAL] **Typeop lang items.** Wired in `mono/lower.alu`'s `resolve_named_type` (TypeAlias path consults the lang attribute):
  - `typeop_arguments_of` / `typeop_return_type_of` — for Fn and FnPointer.
  - `typeop_function_pointer_of<Args, Ret>` — builds an FnPointer from a tuple of arg types and a return type.
  - `typeop_pointer_with_mut_of<Ptr, M>` — produces a pointer to Ptr's pointee with the mutability of M.
  - `typeop_underlying_type_of` — for enums (returns the underlying integer).
  - `typeop_array_with_length_of<T, Arr: Array>` — produces `[T; len(Arr)]`.
  - `typeop_generic_args_of<T>` — tuple of T's struct generic args (empty tuple for non-struct).
  - `typeop_underlying_function_of<T: Closure>` — closure's underlying Fn item.
  - `typeop_replace_generic_args_of<T, Args>` — re-mono'd struct/enum with `Args`' tuple components as new type-args.
  Verified by `tests/aluminac/typeop_args_return.alu`.
  Missing:
  - `typeop_underlying_type_of` for Static / Const / Closure (currently enum-only).
  - ~~`typeop_arguments_of` / `typeop_return_type_of` for `IrTyTag::Closure`.~~ Done in commit following this entry. Skips the env-pointer first parameter.
  - ~~`typeop_generic_args_of` for enums.~~ Moot — aluminac's grammar doesn't allow generic enum declarations (no `enum Name<T> { … }`). The typeop returns an empty tuple for any enum, which matches the only legal case.
- [TODO] **Dyn lang items** (`dyn`, `dyn_self`, `dyn_new`, `dyn_const_coerce`, `dyn_const_cast`, `dyn_data`, `dyn_vtable_index`). Blocks `dyn` support generally — see Language features.
- [TODO] **Operator overload lang items** (`operator_eq`, `operator_neq`, `operator_lt`, `operator_lte`, `operator_gt`, `operator_gte`). See Language features.
- [TODO] **Reflection lang items** (`format_arg`, `enum_variant_new`, `field_descriptor_new`, `field_descriptor_new_unnamed`, `type_descriptor_new`). Required by `enum_variants` / `fields` intrinsics.
- [TODO] **`entrypoint_glue`.** See Language features.
- [TODO] **`static_for_iter`, `static_for_next`.** Recent commit `a6b71e0c` reworked static-for to a const-evaluated iterator protocol; verify these lang items are wired or punt them entirely if the protocol is implicit.
- [TODO] **Coroutine lang items** (`coroutine`, `coroutine_new`, `coroutine_yield`). Out of scope; keep noted.

## Stdlib modules

*(Goal: unify each `sysroot-aluminac/` file with its `sysroot/` counterpart into a single file under `sysroot/`. Track per-file. Files only in `sysroot/` are net-new for aluminac. Files only in `sysroot-aluminac/` are aluminac-local accommodations to be merged back.)*

### Already close to parity (small slices)

- [TODO] **`std/util.alu`** — utility helpers; trivial differences. Likely unifiable in one slice.
- [TODO] **`std/mod.alu`** — module re-exports; gated on which sub-modules compile. Final cleanup once the rest is unified.
- [TODO] **`sysroot/mod.alu`** — root module. Trivial.
- [TODO] **`std/prelude.alu`** — minor differences.
- [TODO] **`std/option.alu`** — diffs are mainly docs and `try!`-style macros; depends on macro completeness.
- [TODO] **`std/result.alu`** — same shape as `option.alu`.
- [TODO] **`std/range.alu`** — sysroot has full `lang(range_*_new)` impl blocks; gated on the range constructor lang items above.
- [TODO] **`std/ffi.alu`** — sysroot has `CString`; trivial unification.
- [TODO] **`std/string/mod.alu`** — reportedly matches; verify once parser features land.
- [TODO] **`std/string/unicode.alu`** — reportedly matches.
- [TODO] **`std/hash/mod.alu`** — minor diff (extra method impls).
- [TODO] **`std/hash/xxhash.alu`** — matches.
- [TODO] **`std/collections/mod.alu`** — minor diffs.
- [TODO] **`std/collections/vector.alu`** — minor diffs.
- [TODO] **`std/collections/deque.alu`** — minor diffs.
- [TODO] **`std/collections/hashmap.alu`** — minor diffs.
- [TODO] **`std/collections/hashset.alu`** — minor diffs.
- [TODO] **`std/collections/heap.alu`** — minor diffs.

### Medium slices (depend on a single language feature or lang-item set)

- [TODO] **`std/iter.alu` (and merge `sysroot-aluminac/std/iter/` directory back into the single file).** sysroot's iter.alu is large and uses the full iterator protocol; aluminac's has a reduced subset split into a directory. Recent commits worked on iterator protocol — confirm what's still missing.
- [TODO] **`std/typing.alu` (and merge `sysroot-aluminac/std/typing/` back).** Depends on dyn + reflection lang items.
- [TODO] **`std/cmp.alu`** — sysroot uses `DefaultEquatable` mixin + when-based type reflection. Depends on `when_type` and operator-overload lang items.
- [TODO] **`std/math.alu`** — uses when-dispatch. Depends on `when_type` and `checked_*` intrinsics.
- [TODO] **`std/macros.alu`** — diff in defined macros; gated on macro feature parity.
- [TODO] **`std/intrinsics.alu`** — sysroot exposes attributed/fields/enum_variants/vtable/etc. Gated on those intrinsics being implemented.
- [TODO] **`std/builtins.alu`** — sysroot has 3× more impls + typeop lang items + type_descriptor lang item. Gated on the typeop and reflection lang items above.
- [TODO] **`std/mem.alu`** — sysroot has full slice ops + dyn casting. Gated on dyn + slice lang items.
- [TODO] **`std/fmt/mod.alu`** — sysroot has full formatting infrastructure (when-based dispatch on type). Gated on when_type, mixin, protocol bounds.

### Large slices (multiple blockers)

- [TODO] **`std/fmt/ryu/`** — float formatting (10 files). Needs full bit-twiddling intrinsics, when-dispatch, and large const tables. Net-new for aluminac.
- [TODO] **`std/panicking.alu`** — sysroot uses `panic!` macro + setjmp/longjmp via `jmp_buf`; aluminac has a different shape. Reconcile.
- [TODO] **`std/time.alu`** — sysroot uses `clock_gettime` directly; aluminac has minimal `Duration`. Depends on libc bindings.
- [TODO] **`std/fs/mod.alu`** + **`std/fs/unix.alu`** — file abstraction + Unix syscall layer. Depends on closure traits for iteration, libc.
- [TODO] **`std/io/mod.alu`** + **`std/io/unix.alu`** — Read/Write traits + stdio. Depends on protocol design.
- [TODO] **`std/process/mod.alu`** + **`std/process/unix.alu`** — fork/exec/stdio plumbing. Depends on threads, closures, dyn traits.
- [TODO] **`std/runtime/mod.alu`** — backtrace + panic runtime. Depends on debug info + dyn.
- [TODO] **`std/runtime/backtrace.alu`** — uses libc + closures for frame iteration. Depends on debug info + closures verified.
- [TODO] **`std/runtime/minicoro.alu`** — minicoro coroutine glue. Out of scope under PORTING.md; keep gated.
- [TODO] **`std/random/mod.alu`** + **`std/random/ziggurat.alu`** — RNG trait + Gaussian. Depends on protocol traits + closures.
- [TODO] **`std/regex/mod.alu`** + **`std/regex/internal.alu`** — DFA regex engine. Depends on dyn + closures.
- [TODO] **`std/sync/mod.alu`** + **`std/sync/channel.alu`** — Mutex/RwLock/Arc + MPMC channels. Depends on threads + atomics.
- [TODO] **`std/thread/mod.alu`** + **`std/thread/pool.alu`** + **`std/thread/parker/`** — pthread-backed threads + thread pool + futex/pthread parking. Depends on closures for thread bodies.
- [TODO] **`std/net/mod.alu`** + **`std/net/address.alu`** + **`std/net/unix.alu`** — sockets + address parsing + syscall layer. Depends on closures, threads, complex address ops.

### Aluminac-only files (eliminate after parity)

- [TODO] **Delete `sysroot-aluminac/std/strbuf.alu`** — 64-byte stub once sysroot's StringBuilder is reachable.
- [TODO] **Merge `sysroot-aluminac/std/iter/` directory into single `sysroot/std/iter.alu`** (covered above).
- [TODO] **Merge `sysroot-aluminac/std/typing/` directory into single `sysroot/std/typing.alu`** (covered above).

### Libc

- [TODO] **`libc/mod.alu`** — sysroot has full bindings; aluminac has a small subset. Unify.
- [TODO] **`libc/bindings.alu`** — net-new for aluminac (823 KB pure FFI declarations). No language blockers; just volume.
- [TODO] **`libc/prelude.alu`** — net-new, tiny. Trivial.

- [DONE] **Type-arg inference: `slice<Ptr>` from expected `&[T]` / `&mut [T]`.** Aluminac's expected-return-type inference path was Struct-only; now also handles the case where the function returns `slice<Ptr>` (the lang slice struct) and the call-site expects `IrTy::Slice`. Lets `slice::empty()` resolve `Ptr` from context. Verified via the unified-sysroot Vector usage in `tests/aluminac/unified_sysroot_basic.alu`.

- [DONE] **Protocol identity through generic-fn substitution.** `resolve_named_type` previously returned `void_ty` when the named item was a protocol, which collapsed protocol type-args at generic call sites — `typing::matches::<i32, Integer>()` mono'd to `i32 is void` and returned false. Now wraps protocols in a new `IrTyTag::Protocol` variant carrying the def-id; the TypeCheck handler recognises this when the AST `check_ty` is a Placeholder substituting to a Protocol IrTy. Verified by `tests/aluminac/unified_sysroot_basic.alu` (typing::matches against Integer / FloatingPoint / Signed).

- [DONE] **`*T` (deref-of) in type position.** Sysroot's `SliceIterator::next` returns `Option<*Ptr>` — `*Ptr` is the pointee type of the generic `Ptr` param. Aluminac's parser previously didn't handle `NodeKind::DerefOf` and silently returned `Ty::unresolved`, collapsing to void after substitution. So the iterator returned `Option<void>` instead of `Option<i32>`, and the for-loop on slices/arrays silently produced 0 iterations. Adds a `Ty::DerefOf` AST variant + parse_type case + resolve_type case (after substitution, derefs through the inner pointer type). Verified by `tests/aluminac/unified_sysroot_basic.alu` for-loops over a slice and an array.

- [DONE] **Slice method dispatch with two generic params.** `call_method_on_type` for slice methods passed only one type-arg (Ptr), but methods like `slice::equals<T, Ptr>` declare two — T (the pointee, bounded `Equatable<T>`) and Ptr (bounded `PointerOf<T>`). When `def.generic_params.len() == 2`, aluminac now passes `[elem_ty, ptr_ty]` instead of `[ptr_ty]`. Verified by string starts_with / ends_with which go through slice equality.

## Unified sysroot probe

- [PARTIAL] **Aluminac compiles dyn-free programs against `sysroot/`.** The slices in this branch (typeop dispatch, slice pseudo-fields, range type inference, fn-item type resolution, generic-fn skip-on-export, etc.) collectively let aluminac swallow non-trivial code against the unified sysroot — verified by `tests/aluminac/unified_sysroot_basic.alu`. The test exercises generics, Ordering, comparison-operator overload dispatch on a user struct, and works as a regression guard.
  Missing:
  - Anything reaching `Option::unwrap` / `Result::unwrap` / `panic!` triggers `const_panic_impl` which uses `dyn Formattable` — a hard `dyn`-blocker.
  - Stdlib code that uses `dyn` directly (regex internal DFA, runtime backtrace, typing reflection, io/fs Read/Write protocols).
  - Macros that expand to references to coroutines / threading / panicking.

## Test infrastructure

*(Running the alumina-boot test suites through aluminac. `tests/diag/` is **not** in scope — keep it passing under alumina-boot only.)*

- [TODO] **Add `make test-lang-aluminac`.** `tests/lang/lang.alu` is one module with ~35 `#[test]` functions; aluminac already supports `--cfg test --cfg test_std` for `make test-std-aluminac`, so a parallel target should be straightforward.
- [TODO] **Add `make test-libraries-aluminac`.** Compile `libraries/` with aluminac's `--test` flag. May require closure / dyn support for some libraries.
- [TODO] **Confirm `make test-std-aluminac` runs against the unified `sysroot/`** once feature gaps close; today it points at `sysroot-aluminac/`.
- [TODO] **`tests/aluminac/run_tests.sh` shell-driven runner is fine for aluminac-specific suites** — keep as-is. (Already passing; this is just a "no action" record.)
- [TODO] **`tests/diag/` and `make test-diag`** — alumina-boot only, no porting work; just don't break it on the boot side.
- [TODO] **`make test-docs`** — currently uses alumina-boot to compile generated `doctest.alu`. Bringing under aluminac is gated on full sysroot parity.

## Sysroot deletion (final)

- [TODO] Delete `sysroot-aluminac/` once the unified `sysroot/` compiles under both compilers, the aluminac → aluminac → aluminac bootstrap converges on `sysroot/`, and `make test-lang` / `make test-std` / `make test-libraries` pass under both compilers. Gated on the rest.
