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

## [DONE] Audit extension — language-feature deep dive

The first audit pass produced only ~7 language-feature gaps. That's almost certainly low: aluminac is roughly 1/3 the LoC of alumina-boot and the boot AST has machinery (closures' captured-env lowering, mixin substitution, full macro hygiene, etc.) that one short audit doesn't enumerate.

Done since first pass:
- Attribute parity walk: Packed, TupleCall, ConstOnly, NoConst, Transparent, MustUse, LinkName, Custom — all have AttrTag entries and parser dispatch (Custom captures unknown names). Tracked individually in the Language-features section above.
- AST node coverage audit: aluminac's `ast.alu` `ExprTag` covers every alumina-boot `ExprKind` variant (with renames). Boot's `Yield` is out-of-scope (coroutines), `Tag` is an internal wrapper unused outside boot, `AssignOp` is folded into aluminac's `Assign`. The `Ty` enum is similar.
- Mixin behavior: mixin referencing Self, mixin chaining, and protocol-defaults referring to other protocol methods all work end-to-end (`tests/aluminac/mixin_self_subst.alu`, `mixin_features.alu`). Remaining concern: mixin instantiation with generic-typed args (e.g. `Equatable<MyVec<T>>`) not deliberately stressed.
- Closure features: capture-by-value, capture-by-reference, mixed captures, multi-arg closures, closure-of-closure, Fn-protocol-bounded generic args all work (`tests/aluminac/closures.alu`, `closure_features.alu`). Remaining concern: ProtoClosure conformance under `where` clauses isn't exercised; aluminac's bound enforcement is generally weak (noted as a separate soundness gap).

Done since first pass (continued):
- Macro hygiene under variable shadowing — fixed. The expander used to register the macro's renamed Let into the caller's scope under the original source name, which overwrote the caller's same-named local via the by-name HashMap. Pre-parsed macro bodies already carry their own ids for inner bindings, so removing the add_item call was sufficient: the id_map remap takes existing Local refs to the fresh id, and mono later registers the local in local_defs at lower time. Verified by `tests/aluminac/macro_hygiene_shadowing.alu`.

Notes on remaining macro audit gaps:
- Aluminac handles all the builtin macros boot has (`cfg`, `line`, `column`, `file`, `stringify`, `env`, `concat`, `include_bytes`, `format_args`, `bind`, `reduce`). Aluminac additionally has `count`, `test_cases` (aluminac-specific test discovery). Untested in this audit: et-cetera packs in deeply nested macro bodies, named-arg expansion under hygiene, macro recursion limits — none have surfaced as blockers in sysroot.

---

## Language features

*(Parser/AST/type system features in alumina-boot but not aluminac.)*

### Highest-leverage remaining work

The remaining compiler-side work clusters into three real items. Closing these unblocks most of the stdlib `[TODO]`s en masse; chasing stdlib files one at a time without fixing these is depth-first work against shallow leaves.

1. **~~Protocol-method Self uniformity.~~** **Resolved 2026-05-11** (commit follows this update). `build_protocol` no longer prepends the protocol's generic_params to each method — methods now have only their own generics in `def.generic_params`, matching the shape that `build_function` produces for impl methods. The protocol's generics (Self + others, in declaration order) are stored in a new `proto_method_proto_gp_ids` registry and bound at dispatch sites via `bind_proto_generics` (mixin / dyn) or `infer_proto_generics_from_call` (direct call inference). The dyn vtable build collapses to a single principled rule (no more length-arithmetic branches). `Result::unwrap` end-to-end against `--sysroot sysroot` now compiles and runs, verified by `tests/aluminac/unified_sysroot_unwrap.alu` plus a focused minimal repro that previously failed at `fmt/mod.alu:336`. mono_function's cache_key now mixes in proto-generic bindings so different instantiations don't collide on the same key when the method has no own-generics; snapshot/restore of `def.generic_params` covers method-own (the "leaky-context" behavior is preserved for proto generics — they're set by dispatchers and carry forward).
2. **Item-as-type-arg generics.** `Id`s need to flow through paths that today only handle `&IrTy`. Unblocks `proto_const` / `proto_static` / `value_of`, typeop for Static/Const, and `entrypoint_glue` migration.
3. **Reflection lang items** (`enum_variant_new`, `field_descriptor_new` / `field_descriptor_new_unnamed`, `type_descriptor_new`, `format_arg`). Wiring them lets the four stub intrinsics (`enum_variants`, `fields`, `vtable`, `attributed`) build their array-of-call results directly. **No const_alloc dependency** — alumina-boot's implementations are plain `array_of(...)` expressions (verified against `src/alumina-boot/src/ir/mono/intrinsics.rs`'s `intr_enum_variants`). Earlier framings in this file that linked these to `const_alloc` were wrong.
4. **Per-call mono context (architectural).** Today's `type_map` is one shared mutable HashMap with leaky semantics — dispatcher paths inject bindings that downstream code depends on. The 2026-05-11 type_map-pollution fix is a targeted save/restore, and the protocol-Self-uniformity refactor extends snapshot/restore to cover proto generics — but the same kind of pollution will keep surfacing in different shapes until aluminac mirrors alumina-boot's child-mono-context model (`Mono::with_replacements` → fresh `replacements` map per call). Replacing the leaky map is a meaningful refactor of `mono/lower.alu` but it's bounded and prevents a whole class of future fixes.

`const_alloc` family stays a [TODO] but it's narrow-scope (heap-during-const for user code), not a hard blocker. DWARF is [DONE] (was [TODO] in error). Dyn-callable lang items are an acceptable `cfg(boot)` deviation per the project's quality bar — see PORTING.md "Specialization".

### Per-feature status

- [PARTIAL] **`dyn` / dynamic dispatch.** Real dispatch wired end-to-end for single- and multi-protocol bounds. `&T as &dyn Proto` now emits a private const global vtable (`[fn(); N]`) populated with `T`'s typed method pointers (cast to opaque `fn()`), and threads its address into the dyn fat pointer's `_vtable` slot. Method calls on dyn values load `_vtable[idx]`, cast to the typed fn pointer, and invoke with `(_ptr, args...)`. Multi-protocol bounds `&dyn (A + B + ...)` are captured (parser iterates `inner` fields, synthesizes a TupleTy; resolve_type unpacks back into the dyn struct's `Protos` type-arg). Verified by `tests/aluminac/dyn_dispatch.alu` (single-method + multi-method protocols, plus a `&dyn (A + B)` bound).

  `#[lang(dyn)]` and `#[lang(dyn_self)]` structs now exist in `sysroot-aluminac/std/builtins.alu` (sysroot puts them in `std/typing.alu`; aluminac's sysroot puts them under builtins until typing.alu is ported).

  **Structural gap closed 2026-05-11.** Earlier audits noted that the vtable build needed a fifth branch to handle protocol-default methods on builtins (e.g. `i32::fmt` mixin'd from `IntegerFormattable`). Adding a fifth branch was the wrong fix; the underlying asymmetry between `build_protocol` and `build_function` was. That asymmetry is now gone:

  - **`build_protocol` no longer prepends the protocol's generic_params** (`Self` + protocol's other generics) to each method's `generic_params`. Methods now have only their own generics, mirroring `build_function`'s shape for impl methods.
  - The protocol's generics are stored in `MonoCtx::proto_method_proto_gp_ids` (method_id → ids in declaration order, Self at index 0).
  - At dispatch sites the protocol's generics are bound into `type_map` via two complementary helpers: `bind_proto_generics(def, args)` for explicit-arg paths (mixin info, dyn proto args), and `infer_proto_generics_from_call(def, receiver, args)` for direct-call inference (mirrors what `infer_type_args` does for a function's own generics).
  - The dyn vtable build's three length-matching branches collapsed to a single principled rule: protocol-derived method → `[impl_ty, proto_args[1..]]` via `bind_proto_generics`. Plain impl methods retain the existing `[impl_args, proto_non_self_args]` arithmetic — but the case is now distinguished structurally (presence of `proto_method_proto_gp_ids` entry), not by length-coincidence.
  - `mono_function`'s cache_key mixes in the current `type_map` bindings for the proto generics, so distinct instantiations of the same protocol method (e.g. `sum<SliceIterator<i32>, i32>` vs `sum<SliceIterator<usize>, usize>`) get distinct cache entries even though `def.generic_params` is empty for both.

  Verified by:
  - `tests/aluminac/unified_sysroot_unwrap.alu` — was previously failing at `fmt/mod.alu:336` with "method 'write_byte' on type ''"; now compiles and runs.
  - The 142 existing `tests/aluminac/` regressions (no test count loss).
  - `make bootstrap` (stage 2 == stage 3, byte-identical), `make test-std-aluminac` (30 tests), `make test-lang` / `test-libraries` / `test-std` (alumina-boot suites still green), `make test-diag`.

  The remaining smaller follow-ups are unchanged from before:
  - Mutability cast through dyn: `&mut dyn Proto` → `&dyn Proto` (and the reverse via explicit `as`-cast) works *behaviorally* — aluminac routes through the compiler's normal pointer-mutability coercion rather than the `dyn_const_coerce` / `dyn_const_cast` lang items, but the observable result on sysroot's test_dyn shape is identical. Verified by `tests/aluminac/dyn_mutability_coerce.alu`.
  - The `dyn_data` / `dyn_vtable_index` lang items aren't wired (aluminac builds the dispatch IR directly), so calling them as plain functions wouldn't work — but sysroot's only callers go through `dyn` magic anyway.

  Still missing (smaller follow-ups):
  - Mutability cast through dyn: `&mut dyn Proto` → `&dyn Proto` (and the reverse via explicit `as`-cast) works *behaviorally* — aluminac routes through the compiler's normal pointer-mutability coercion rather than the `dyn_const_coerce` / `dyn_const_cast` lang items, but the observable result on sysroot's test_dyn shape is identical. Verified by `tests/aluminac/dyn_mutability_coerce.alu`.
  - The `dyn_data` / `dyn_vtable_index` lang items aren't wired (aluminac builds the dispatch IR directly), so calling them as plain functions wouldn't work — but sysroot's only callers go through `dyn` magic anyway.

  Multi-protocol bound order matters for vtable layout: `&dyn (Foo + Bar)` and `&dyn (Bar + Foo)` produce distinct const globals keyed by the protocol-tuple type-arg, with per-method dispatch indices resolved against the bound's declaration order. Verified by `tests/aluminac/dyn_proto_order.alu`.

  Multi-type-arg protocols (e.g. `Formattable<Self, F>`) now thread their non-Self type-args into the vtable build. `IrTyTag::Protocol` carries a `_IrTyProtocolData { proto_id, type_args }` payload (was just `proto_id`). The dyn vtable builder uses these to bind impl-method generics: for an impl method declared `<F: Formatter<F>>` conforming to `Formattable<Self, F>`, the impl method is mono'd with F = bound's F. Generic impls (`impl Foo<T> { fn fmt<F>(...) }`) work too — pass2 prepends impl generics to the method's `generic_params`, so the vtable build assembles `[impl_struct.type_args..., proto.non_self_args...]` for the mono call. Verified by `tests/aluminac/dyn_proto_with_type_args.alu` (single-method, single-method inferred F, array-of-dyn elements with inferred F, and generic-struct impl).

  Used by `sysroot/std/regex/`, `sysroot/std/runtime/backtrace.alu`, `sysroot/std/io/`, `sysroot/std/typing.alu`, and `sysroot/std/panicking.alu`'s `panic_impl`.
- [DONE] **`when` for types (`when_type`).** Already supported. `tests/aluminac/when_type.alu` covers `type T<X> = when cond { A } else { B };`. Audit was wrong on this one.
- [DONE] **`Ty::Tag` / `Expr::Tag` wrapper nodes.** Audited the alumina-boot Rust source: `Ty::Tag` is a transparent wrapper that lets boot mark types with a string tag (notably "dynamic" for `dyn` lowering). Aluminac doesn't need it — its dyn handling resolves directly to the lang(dyn) struct. Sysroot grep finds only doc references, no actual uses. The `tag` intrinsic itself is implemented in aluminac as identity (lowering its second argument). No further work.
- [DONE] **Coroutines / yield.** Out of scope per `PORTING.md`. Grammar has `yield_expression` and the `*`-marked coroutine function form; aluminac never parses either, and sysroot uses keep them gated under `cfg(coroutines)`. No work expected.
- [DONE] **Attribute: `#[transparent]`.** AttrTag::Transparent + parser recognition. Codegen still wraps the struct, but on x86_64 / aarch64 the SysV / AAPCS ABI passes single-field pointer-sized structs in registers anyway — same observable behavior as a transparent wrapper. The two sysroot uses (`std::ffi::CString` and an entry in `std::sync`) work in practice; `std/ffi.alu` is unified and its tests pass.
- [DONE] **Attribute: `#[link_name("…")]`.** Wired through pass1 → AttrTag::LinkName → mono mangled-name override. `tests/aluminac/link_name_attr.alu` declares `extern "C" fn c_string_len` pointing at libc `strlen` and verifies the call resolves correctly (and the negative — without the attribute it link-fails on `c_string_len`). The previous mis-routing to `AttrTag::Extern` is fixed.
- [DONE] **Attribute: `#[packed(N)]` / `#[packed]`.** AttrTag::Packed parsed; IrStructRef carries an `is_packed` flag set when AttrTag::Packed is on the source struct. Codegen passes `packed=1` to `LLVMStructSetBody` so LLVM lays out fields without padding; layout.alu's `compute_type_size` and `compute_type_align` honor the flag too. Verified by `tests/aluminac/packed_struct.alu` (PackedHeader{u8,u32} = 5, UnpackedHeader = 8).
  Caveat: aluminac doesn't distinguish `#[packed]` from `#[packed(N)]`. The `int_val` is parsed but ignored; we always emit fully-packed (alignment 1). For sysroot uses with `#[packed(8)]` etc. the strictest interpretation is correct, but doesn't preserve the partial-packing behavior alumina-boot would.
- [PARTIAL] **Attribute: `#[tuple_call]`.** AttrTag::TupleCall + parser recognition. Semantics not yet wired (would let a fn taking a tuple be called with positional args).

- [PARTIAL] **Attribute: `#[const_only]` / `#[no_const]`.** AttrTag::ConstOnly / AttrTag::NoConst + parser recognition. Both the bare names (`#[const_only]` / `#[no_const]`) and alumina-boot's `#[const(always)]` / `#[const(never)]` form parse to the same AttrTag, so sysroot's `panicking::const_panic_impl` (which uses the `#[const(always)]` syntax) round-trips through aluminac's attribute table. Verified by `tests/aluminac/const_attr_modes.alu`. alumina-boot uses these to gate functions to / from const context; neither compiler currently *enforces* the gate (it's just attribute round-tripping for now).
- [DONE] **Attribute: `#[must_use]`.** AttrTag::MustUse + parser recognition + warning enforcement. `mono/lower.alu`'s `lower_block` now checks each non-trailing block expression: if it's a direct Call to a function tagged `#[must_use]` returning a non-void/non-never value, emits a `generic_warning` diagnostic. The diagnostic context tracks `has_warnings` and `main.alu` flushes them on success too. Verified by `tests/aluminac/must_use_warn.alu` (binary exit unchanged; warning text confirmed manually).

- [DONE] **Attribute: `#[no_mangle]`.** Wired through pass1 → AttrTag::NoMangle → mono's mangled_name decision. Behaves like #[export] for naming purposes (keeps `def.name` as the LLVM symbol). Verified by `tests/aluminac/no_mangle_attr.alu`.
- [PARTIAL] **Attribute: `#[inline(...)]` modes.** Pass1 parses the meta-item argument and dispatches to `Inline` / `AlwaysInline` / `NeverInline` / `InlineIr`. NeverInline lowers to LLVM `noinline`. Verified by `tests/aluminac/inline_attr_modes.alu`.
  Missing:
  - alumina-boot's `Inline::DuringMono` is what `#[inline(ir)]` maps to in alumina-boot — a mono-time inliner. Aluminac maps `#[inline(ir)]` to `AttrTag::InlineIr` (parsed correctly) but doesn't *act* on it: the mono pass doesn't inline marked functions before codegen. Many sysroot helpers (e.g. `mem.alu`'s slice constructors, util.alu's `cast`/`coerce`/`transmute`) rely on this for correctness when the body uses generics that would otherwise become unresolved at runtime. Wiring a real IR-level inliner is a substantial slice — aluminac currently emits a regular call and trusts LLVM to inline.
  - ~~The redundant `#[always_inline]` standalone attribute name is still parsed for backwards-compat~~. Removed — no sysroot-aluminac users remained, and any future occurrence will fall through to AttrTag::Custom (silently stored, ignored at codegen).
- [PARTIAL] **Custom attributes (`Attribute::Custom`).** AttrTag::Custom (= 26) added. pass1.alu's catch-all stores unknown `#[name(...)]` attributes as `Custom` carrying the literal name (skipping `allow`, `docs`, `deny`, `warn`, `cfg_attr`). `has_attribute<T>(name)` works on Fn-typed T's (via `fn_defs`), Struct-typed T's (via `IrStructRef.attributes`), and Enum-typed T's (via `IrEnumRef.attributes`) — all populated at mono time. Verified by `tests/aluminac/custom_attr.alu`.
  Missing:
  - The `attributed(...)` intrinsic itself returns an empty slice — actual enumeration of items by name needs const-time slice allocation. Tracked as PARTIAL above.
  - Custom-attribute *args*: only the name is captured; arg lists like `#[meta(key = "value")]` are silently dropped.
- [PARTIAL] **u128 / i128 codegen + const-eval coverage.** Runtime arithmetic, comparison and casts verified by `tests/aluminac/u128_i128_basic.alu`. LLVM 128-bit integer codegen works; integer-literal parser is u64-bounded so values needing >64 bits must be constructed via shifts / wrapping arithmetic. `fmt` for both widths now goes through `format_integer_unsigned_128` / `format_integer_signed_128` (39-digit decimal buffer, special-case for `i128::MIN`); verified by `tests/aluminac/u128_i128_fmt.alu` covering 0, max, negative, and MIN.
  Missing:
  - 128-bit integer literals beyond u64 range (e.g. `170141183460469231731687303715884105727i128`) — `parse_int_with_suffix` stores in u64. Consider a u128-internal representation.
  - Const-evaluation of u128/i128 arithmetic — `const_eval.alu` represents integer values as 64-bit `int_val`. The runtime path is unaffected.
- [DONE] **Operator-overload dispatch.** Operator overloading works in aluminac via method-name matching (`try_operator_overload` in `mono/lower.alu`). User-defined `equals` / `compare` / `less_than` / `less_than_or_equal` / `greater_than` / `greater_than_or_equal` on structs is dispatched through `==` / `!=` / `<` / `<=` / `>` / `>=` correctly. Verified by `tests/aluminac/operator_overload.alu`. The `binop_lang_name` helper sits unused for the lang-item dispatch path; functionally the dispatch is complete because sysroot's `operator_*` lang items are themselves thin wrappers around the same method names. Going through the lang-item indirection is lower-priority cosmetic work.
- [PARTIAL] **`Lang::EntrypointGlue`.** Aluminac still uses a hardcoded entrypoint in codegen/mod.alu (sysroot's `entrypoint_glue` lang item is unused). Several blockers for migrating to sysroot-defined glue have been fixed: function names now resolve as types (parser pass2 + mono resolve_named_type → Fn IrTy), calls returning Fn-typed values now codegen correctly (Fn is treated like void at the LLVM level). Verified by `tests/aluminac/fn_item_via_generic.alu` exercising the `unit::<F>()` → `func()` pattern.
  Missing:
  - Recognize the `entrypoint_glue` lang item and dispatch to the sysroot-defined function instead of building the hardcoded entrypoint.
  - Coroutine-aware logic in the sysroot glue (gated under `cfg(coroutines)` — out of scope).
  - The `arguments_of<F>` typeop and `typing::matches::<A, B>()` are also referenced by sysroot's glue; these need separate slices.
- [DONE] **`ProtoZeroSized` works in generic bounds and `is`-checks.** Verified end-to-end via the unified sysroot — a function `fn check<T: ZeroSized>() -> bool { true }` compiles and accepts `Empty` / `()` instantiations. The `is`-check path (`x is ZeroSized`) returns true for ZSTs and false for non-ZSTs. (Aluminac doesn't currently REJECT a bound-violation at instantiation site — it just always lets the instantiation through. That's a soundness gap noted in the audit's separate "bound enforcement" entry.)

- [DONE] **Range-literal type inference.** `mono/lower.alu` previously hardcoded `Range<usize>` for every range literal. Now infers T from the lower / upper operand types (both must agree, otherwise falls back to usize). `0i32..10i32` produces `Range<i32>` as expected. Verified by the strengthened `tests/aluminac/proto_range_of.alu`.

- [DONE] **Slice `_ptr` / `_len` field access.** `mono/lower.alu`'s `resolve_field` treats slice values as having pseudo-fields `_ptr` and `_len` matching sysroot's `slice<Ptr>` struct convention. Verified by `tests/aluminac/slice_field_access.alu`. Field-write access via these names isn't supported but a grep of sysroot/ confirms no code writes `s._len = ...` or `s._ptr = ...`; mutations go through methods (slice_index_assign etc). Auto-deref through `&slice` to read the pseudo-fields uses the existing pointer auto-deref path.

## Const evaluation

- [DONE] **Signed-integer overflow detection.** `const_eval.alu`'s `int_bin_op` and `eval_unary` reject signed overflow at const time:
  - Add / Sub / Mul (sign-bit comparison; sign-extended-i64 multiply with div-roundtrip at i64 width).
  - Unary Neg (`-INT_MIN`).
  - Div / Rem (`INT_MIN / -1`).
  - Shift (`x << bitwidth`) was already rejected.
  In all cases the const evaluator bails with `ConstEvalError::overflow()` so callers fall back to runtime emission, matching alumina-boot. Verified by `tests/aluminac/signed_overflow_const.alu`.
- [PARTIAL] **`checked_add` / `checked_sub` / `checked_mul` / `checked_div` intrinsics.** Aluminac doesn't implement these as compiler intrinsics; sysroot-aluminac's `std/builtins.alu` defines per-type runtime implementations (one per u8/u16/u32/u64/usize/i8/.../isize) that detect overflow via widened arithmetic. Verified by `tests/aluminac/checked_arithmetic.alu`. The const-eval path inherits the same logic since aluminac's interpreter inlines the bodies. Sysroot's version uses `codegen_func("__builtin_*_overflow")` which is out-of-scope; the duplicated bodies in sysroot-aluminac mean unifying `std/builtins.alu` requires either reading sysroot's `codegen_func` path or a dialect bridge.
- [PARTIAL] **`checked_shl` / `checked_shr` intrinsics.** Const-eval already rejects shift ≥ bitwidth (`int_bin_op` returns `ConstEvalError::overflow()` for that case). The named `checked_shl`/`checked_shr` intrinsics that return `Option<T>` aren't wired since they live behind `codegen_func` in sysroot — see PORTING.md "Out of scope".
- [DONE] **`const_panic` intrinsic.** Lowers to a new `IrTag::ConstPanic` carrying the message string. Const_eval recognises the tag, stores the message in the evaluator's `panic_msg`, and bails with `ConstPanic`. The const-item lowering path uses a new `try_eval_with_panic` helper to surface the message as a `generic_error` diagnostic at the init expression's span. Codegen treats `ConstPanic` like `Unreachable` (the call shouldn't be reached at runtime, but if it is — e.g. in a generic body that wasn't const-evaluated — alumina-boot also unreachables). Verified by `tests/aluminac/const_panic_compile_fail.alu`.
  Caveat: only string-literal `msg` arguments are captured; format!-built messages are silently treated as empty (matches the compile_fail-family limitation).
- [DONE] **`compile_fail` / `compile_warn` / `compile_note` intrinsics.** Always-emit family fires at lowering time via `m.emit_diag` with the call-site span and the literal-string argument; verified by `tests/aluminac/compile_fail_intrinsic.alu`. The const-eval-context family (`const_panic` / `const_warning` / `const_note`) lowers to dedicated `IrTag::ConstPanic` / `ConstWarning` / `ConstNote` nodes; const_eval captures their messages on the evaluator and the const-item lowering path emits the corresponding error/warning/note diagnostic at the init span. Verified by `tests/aluminac/const_panic_compile_fail.alu` (error) and `tests/aluminac/const_warning_note.alu` (warning + note).
  Caveat: only literal-string arguments are captured. Non-literal forms like `compile_fail!(format!(...))` silently lose the message — extending to const-time string building is gated on broader const-eval format support.
- [TODO] **`const_alloc` / `const_free` / `const_bake` intrinsics.** Narrow scope: heap-during-const for user code that explicitly allocates at const time. **NOT a prerequisite for `enum_variants` / `fields` / `attributed` / `vtable`** — alumina-boot's `intr_enum_variants` (in `src/alumina-boot/src/ir/mono/intrinsics.rs`) is a plain `array_of(...)` of `EnumVariantNew(name, value)` lang-item calls, no heap involved. Earlier framing in this file was wrong; verify against alumina-boot before adopting "X needs const_alloc" claims.
- [PARTIAL] **Const-evaluable function calls.** Aluminac's interpreter handles direct calls (eval_call in const_eval.alu) including recursion, branching, multi-arg signatures. `tests/aluminac/const_fn_calls.alu` exercises double/add/factorial/fib at const time. Closure invocations also fold, including capture-by-value and closure-as-generic-arg passed through `apply<F: Fn(...) -> R>(f, x)` (verified ad-hoc — see `/tmp/test_closure_pass.alu` smoke check). The remaining gap vs alumina-boot's ~2000 LoC interpreter is in pointer-arena chasing (multi-step `&mut T` mutation of complex shapes), dyn dispatch (gated separately), and any pattern that depends on heap-bake (`const_alloc` family).
- [PARTIAL] **`enum_variants` intrinsic.** Recognized in `mono/intrinsics.alu`; currently returns an empty slice. **Fix shape (per alumina-boot's `intr_enum_variants`):** iterate the enum's members, build `EnumVariantNew(name_string, cast(member.value, ty))` per member via `Lang::EnumVariantNew`, then construct an array literal. No heap. Blocked only on the `enum_variant_new` lang item being declared in the sysroot and discovered by aluminac's lang-item registry. Stub returns work for sysroot signatures that reference the intrinsic without iterating the result.
- [PARTIAL] **`fields` intrinsic.** Recognized in `mono/intrinsics.alu`; currently returns an empty slice. **Fix shape:** mirror `enum_variants` — iterate the struct/union's fields and call `field_descriptor_new` (named) or `field_descriptor_new_unnamed` (positional) per field, then an array literal. Blocked only on the lang items.
- [PARTIAL] **`vtable` intrinsic.** Recognized in `mono/intrinsics.alu`; currently returns an empty slice. **Fix shape:** iterate the protocol's methods, look each up on the impl scope, build an array of fn pointers (same machinery the dyn vtable builder uses today). Blocked on the protocol-method-Self uniformity gap below.
- [PARTIAL] **`attributed` intrinsic.** Recognized in `mono/intrinsics.alu`. Currently returns an empty slice typed `&[fn() -> ()]`. **Fix shape:** scan all `fn_defs` for `Attribute::Custom(name)` matches, build an array of fn pointers to them, return as the slice. No heap. Workable as-is for sysroot's main use (`attributed::<()>("test")` for test discovery) since aluminac uses `test_cases!()`; full impl is needed once stdlib code iterates the result.
- [TODO] **`value_of` intrinsic.** Yields the runtime lvalue of a const/static.
- [DONE] **`named_type_name` intrinsic.** Wired in `mono/intrinsics.alu`'s `lower_type_name(m, ir_type_args, named_only: true)` — returns the struct/enum's short name, or void for unnamed types. Verified by `tests/aluminac/unified_sysroot_basic.alu` (which passes through `std::typing::Type::name`).
- [DONE] **Float classification (`is_finite` / `is_nan` / `is_infinite`) at const time.** `tests/aluminac/float_classify_const.alu` covers both f64 and f32 across normal, signed-zero, subnormal, NaN, +inf, and -inf operands. The const-required usage path (array sized by `if (1.0f64).is_finite() { ... }`) confirms aluminac's const evaluator actually folds these — the array type wouldn't resolve otherwise. `is_normal` is not in either sysroot, so out of scope here; if sysroot grows it later, extend the test then.
- [DONE] **Bit-twiddling intrinsics: `count_ones` / `count_zeros` / `leading_zeros` / `trailing_zeros` / `swap_bytes`.** All five are methods on every integer type — `u8/u16/u32/u64/u128/usize` and `i8/i16/i32/i64/i128/isize` — in sysroot-aluminac, lowered via `intrinsics::llvm("llvm.ctpop"/...)`. The LlvmIntrinsic codegen path special-cases `llvm.ctlz`/`llvm.cttz`: truncs the `is_zero_undef` flag from i8 to i1 and forces the overload list to a single iN entry. 8-bit `swap_bytes` is identity since LLVM `bswap` requires width ≥ 16. Const_eval grew an `eval_llvm_intrinsic` helper that folds ctpop/ctlz/cttz/bswap on int values — `const X: u32 = (0xAAu8).count_ones()` works and composes with const-required usages (array sizing). Verified by `tests/aluminac/bit_twiddle.alu` (runtime) and `tests/aluminac/bit_twiddle_const.alu` (compile-time).
  Caveat: 128-bit const folding still goes through u64 arithmetic in const_eval (ConstValue stores int_val as u64), so `const X = (u128_max).count_ones()` would lose precision. The runtime path handles 128-bit fine. This is part of the broader u128/i128 const-eval gap tracked separately.
- [DONE] **Const-evaluable indexing into string / byte-string / array literals.** const_eval's `access_index` now handles `CValTag::Bytes` (string-literal slices) in addition to arrays, and `eval_field_access` handles `_ptr` / `_len` on a Bytes base — the lowering produces `Index(slice._ptr, idx)`, so both legs need to fold. `tests/aluminac/const_index_basic.alu` covers positive const indexing into both `&[u8]` and `[T; N]` driving const-required array sizes. `tests/aluminac/const_index_oob_compile_fail.alu` confirms wrapping-negative (`0usize - 1usize`) is rejected at compile time when used in a const-required position; the underlying `>= len` guard catches both positive and wrapping OOB.

## Codegen

*(LLVM IR coverage: intrinsics, ABI, attributes, debug info, panic/backtrace.)*

- [DONE] **Intrinsic: `codegen_func`.** Out of scope per `PORTING.md` — explicitly listed as the intrinsic that won't be ported. aluminac has `llvm<>()` for direct LLVM intrinsic calls; sysroot uses of `codegen_func` block sysroot unification of the affected files (notably `std/builtins.alu` checked-arithmetic methods), tracked in PARTIAL entries elsewhere.
- [DONE] **Intrinsic: `codegen_const`.** Out of scope per `PORTING.md` (sister to `codegen_func`). Use `extern "C" const NAME` for C macro / linker constants instead.
- [DONE] **Intrinsic: `codegen_type_func`.** Out of scope per `PORTING.md` (sister to `codegen_func`). Aluminac exposes `size_of` / `align_of` / `length_of` / `type_id` / `type_name` directly.
- [DONE] **Intrinsic: `expect`.** Lowers to `llvm.expect.i1`. Codegen's LlvmIntrinsic path detects the name and truncs i8 (aluminac's bool storage) → i1 on each arg before the call; the trailing `coerce_value` widens the i1 result back to i8. Verified by `tests/aluminac/expect_intrinsic.alu` (value semantics) plus `--emit-llvm` inspection confirming `call i1 @llvm.expect.i1(i1 ..., i1 ...)` is emitted. Sysroot `likely!` / `unlikely!` macros now produce real branch-prediction hints.
- [DONE] **Intrinsic: `tuple_invoke`.** Wired in `mono/intrinsics.alu`. Splits the tuple argument into positional fields and constructs a Call against the callee. Handles fn items (Fn IrTy), function pointers (FnPointer), and closures (prepends &self), and treats `()` (Void) as a zero-arg call. Verified by `tests/aluminac/tuple_invoke_intrinsic.alu`.
- [DONE] **Intrinsic: `stop_iteration`.** Recognized in `mono/intrinsics.alu`; emits `Unreachable` typed as `never`. Sysroot's `static_for_next` lang item uses it to bail when the iterator is exhausted; the const evaluator's iteration loop already handles Unreachable as the terminator. Verified by `tests/aluminac/stop_iteration_intrinsic.alu`.
- [DONE] **Intrinsic: `with_span_of`.** Recognized in `mono/intrinsics.alu`; identity at the value level (alumina-boot uses T's source span for diagnostics, aluminac doesn't track separately). Verified by `tests/aluminac/stop_iteration_intrinsic.alu`.
- [DONE] **Intrinsic: `module_path`.** Returns the `::`-joined module path of T's declaration site. For struct/enum, walks up from the *parent* of the type's own scope (pass1 gives struct/enum a Module-kind scope for method lookup, so we skip it) and collects Module ancestors via the new `ScopeArena::module_path_for_scope` helper. Top-level types and non-named types still fall through to void so `std::typing::Type::module_path`'s `when ... is ()` branch returns None. Verified by `tests/aluminac/module_path_real.alu` (`inner::Bar` → `"inner"`, `inner::nested::Quux` → `"inner::nested"`); the prior `tests/aluminac/module_path_intrinsic.alu` continues to pass and now exercises the void path.
- [DONE] **Intrinsic: `has_attribute`.** Recognized in `mono/intrinsics.alu`. For Fn-typed `T`, consults `fn_defs[id].attributes`. For Struct-typed `T`, `IrStructRef.attributes`. For Enum-typed `T`, `IrEnumRef.attributes`. All populated at mono time from the source `def.attributes`. Verified by `tests/aluminac/custom_attr.alu`.
- [DONE] **Function attribute lowering: `#[align(N)]` on functions.** Codegen now calls `LLVMSetAlignment` on the function's LLVM value with the requested alignment. Verified by `tests/aluminac/align_attr.alu`.
- [DONE] **Global attribute lowering: `#[align(N)]` on statics.** Same — `LLVMSetAlignment` on the LLVM global. Verified by `tests/aluminac/align_attr.alu`.
- [DONE] **Function attribute lowering: `#[link_name("…")]`.** mono/lower.alu now consults LinkName when computing mangled_name; the LLVMAddFunction call uses the override. Tested in `tests/aluminac/link_name_attr.alu`.
- [DONE] **Verify `#[returns_twice]` on declarations.** Confirmed via inspection: the attribute loop in `declare_function` (codegen/mod.alu lines 840-858) runs unconditionally — both for definitions (where `ir_fn.body.is_some()`) and extern declarations (where `body.is_none()`). The linkage decision is the only thing gated by `body`. So `#[returns_twice]` on `extern fn setjmp(...)` declarations gets the LLVM `returns_twice` attribute too.
- [DONE] **Variadic / va_list intrinsics.** Audited sysroot/ — no references to `va_start` / `va_arg` / `va_end` / `va_list` (also absent from `libc/bindings.alu` despite the prior audit's note). Aluminac doesn't need them; if a future binding reintroduces va_list use, this can be revived.
- [DONE] **`#[link("…")]` / linker-arg attributes.** Audited sysroot/ — no `#[link(...)]` annotations exist. Aluminac's `--link-args` (and the Makefile's `-ltree-sitter -L/usr/lib/llvm-14/lib -lLLVM-14`) covers the needed libs for the bootstrap. If sysroot grows linker dependencies, migrate then.
- [DONE] **ZST phi crashes GlobalISel.** `gen_if` emitted `phi {}` for if-expressions whose result type was a zero-sized struct (e.g. `Result<i32, ()>` where `()` lowers to `{}`). LLVM 14's GlobalISel pipeline crashes inside `IRTranslator::finishPendingPhis` → `MachineBasicBlock::isPredecessor` on these. Skip the phi when `result_ty.is_zero_sized()` and return `undef` of the result type instead — both branches must produce equivalent ZST values, so the observable behavior is unchanged. Verified by `tests/aluminac/unified_sysroot_unwrap.alu` (panic chain mono + codegen both succeed end-to-end).
- [DONE] **Debug info (DWARF).** Aluminac emits DWARF directly via LLVM's `DIBuilder` (see `llvm.alu` — `LLVMCreateDIBuilder`, `LLVMDIBuilderCreateCompileUnit`, `LLVMDIBuilderCreateFunction`, `LLVMDIBuilderCreateDebugLocation`) and gates it on `-g`. Function-level debug info + line locations work. (The earlier "alumina-boot emits #line directives in C; aluminac emits no DWARF" framing was wrong — verified by direct inspection of the codegen.) If `std/runtime/backtrace.alu` later needs richer DI (variable locations, struct member types) than what's emitted today, downgrade to PARTIAL and enumerate the gap; for now no observed lack.
- [DONE] **Panic location capture.** Aluminac's `file!()`, `line!()`, `column!()` macros expand to literals based on the call-site span at parse time (see `src/aluminac/parser/expr.alu`'s "line" / "column" / "file" cases). Sysroot's `panic!` macro uses these to embed the location, matching alumina-boot's mechanism. Verified by `tests/aluminac/unified_sysroot_basic.alu` (file!/line!/column! coverage).
- [DONE] **ZST elision pass.** Not in scope for parity — alumina-boot's `codegen/elide_zst.rs` is a C-codegen quality pass that deletes loads/stores of zero-sized structs to keep the emitted C clean. Aluminac emits LLVM IR; LLVM's optimizer handles ZST cleanup, and the unoptimized output is functionally correct (LLVM's struct/array-of-zero-fields are well-defined empty). No correctness gap, no future work expected.

## Lang items

*(Names from `src/alumina-boot/src/ast/lang.rs`. "Defined" = declared via `#[lang(…)]` in the sysroot. "Queried" = the compiler actually looks the name up.)*

- [DONE] **Builtin types** (`builtin_bool`, `builtin_u8…u64`, `builtin_usize`, `builtin_i8…i64`, `builtin_isize`, `builtin_f32`, `builtin_f64`, `builtin_array`, `builtin_tuple`, `builtin_callable`). Defined and queried in aluminac. Verified by tests/aluminac/lang_builtin.alu.
- [DONE] **`builtin_never`, `builtin_u128`, `builtin_i128`.** All three are now registered in aluminac's BuiltinType-name table and have `#[lang(builtin_X)]` stubs in `sysroot-aluminac/std/builtins.alu`. Verified by `tests/aluminac/u128_i128_basic.alu` (u128/i128 arithmetic + lang methods) and `tests/aluminac/never_named.alu` (`-> never` and `-> !` interchangeable; never coerces to other types).
- [DONE] **Protocol lang items** for: `proto_primitive`, `proto_numeric`, `proto_integer`, `proto_floating_point`, `proto_signed`, `proto_unsigned`, `proto_pointer`, `proto_array`, `proto_tuple`, `proto_struct`, `proto_enum`, `proto_union`, `proto_range`, `proto_named_function`, `proto_function_pointer`, `proto_closure`, `proto_callable`, `proto_any`, `proto_none`. Verified by tests/aluminac/protocol_conformance.alu.
- [DONE] **`proto_zero_sized`.** Queried in `mono/lower.alu` (line 2909) inside the `t is Protocol` lowering path. Audit was wrong on this one.
- [PARTIAL] **`proto_const`, `proto_static`, `proto_array_of`, `proto_pointer_of`, `proto_range_of`, `proto_meta`, `proto_same_base_as`, `proto_same_layout_as`.** All eight declared as `#[lang(...)]` protocols in `sysroot-aluminac/std/builtins.alu`. Six have real query semantics (`proto_array_of`, `proto_pointer_of`, `proto_same_layout_as`, `proto_range_of`, `proto_meta`, `proto_same_base_as`) verified by `tests/aluminac/proto_extras.alu`, `proto_range_of.alu`, `proto_meta.alu`, and `proto_same_base_as.alu`.
  Missing:
  - `proto_const` / `proto_static`: item-vs-type bound semantics (the bound applies to a named const/static, not to a value's type). Aluminac currently treats them as trivially-true empty protocols. Needs item-as-type-arg generic support.
- [PARTIAL] **Slice operation lang items**:
  - `slice_new`: wired (mono/lower.alu detects #[lang(slice_new)] on a function and synthesizes a slice fat-pointer struct from the `(ptr, len)` args).
  - `slice_const_coerce` / `slice_const_cast` / `slice_index` / `slice_range_index` / `slice_slicify`: aluminac open-codes these (slice indexing, range-indexing, mutability coercion all handled directly in lower_expr / try_coerce). Sysroot's lang-item versions delegate to those same operations; once `std/mem.alu` is unified the lang-item path can replace the open-coded one without behavior change.
- [DONE] **Range constructor lang items** (`range_full_new`, `range_from_new`, `range_to_new`, `range_to_inclusive_new`, `range_new`, `range_inclusive_new`). Aluminac's range-literal lowering now picks the appropriate lang item (`range_full` / `range_from` / `range_to` / `range_to_inclusive` / `range` / `range_inclusive`) based on which endpoints are present, building each variant's struct literal with the right field count (RangeFull = 0, RangeFrom/RangeTo/RangeToInclusive = 1, Range = 2, RangeInclusive = 3 incl. `_exhausted`). Slice sub-indexing handles each variant individually: `..` = `[0, len)`, `a..` = `[a, len)`, `..b` = `[0, b)`, `..=b` = `[0, b+1)`, `a..b` = `[a, b)`, `a..=b` = `[a, b+1)`. When a variant's lang item is missing (sysroot-aluminac currently lacks the four single-bound variants), the lowering falls back to the legacy `Range<usize>{0, MAX_USIZE}` sentinel shape so it stays compatible. Verified by `tests/aluminac/range_variants.alu` against `--sysroot sysroot`.
- [DONE] **`range_full`, `range_from`, `range_to`, `range_to_inclusive`.** Type-level lang items. `is_range_ty` now consults all four (in addition to `range` and `range_inclusive`) when classifying a struct as a range. The name-based fallback covering pre-lang-item code stays for safety. No behavior change — `is_range_ty` was already returning true for these types via the name check; the lang-item path now matches alumina-boot's mechanism.
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
  - `typeop_underlying_type_of` for Static / Const (currently enum + Closure). Closure now resolves to the underlying Fn ZST. Static / Const variants need item-as-type generic support, still TODO.
  - ~~`typeop_arguments_of` / `typeop_return_type_of` for `IrTyTag::Closure`.~~ Done in commit following this entry. Skips the env-pointer first parameter.
  - ~~`typeop_generic_args_of` for enums.~~ Moot — aluminac's grammar doesn't allow generic enum declarations (no `enum Name<T> { … }`). The typeop returns an empty tuple for any enum, which matches the only legal case.
- [DONE] **Dyn lang items** (`dyn`, `dyn_self`, `dyn_new`, `dyn_const_coerce`, `dyn_const_cast`, `dyn_data`, `dyn_vtable_index`). Acceptable `cfg(boot)` deviation: aluminac open-codes the dyn dispatch directly in `mono/lower.alu` and `codegen/`, so these lang items aren't required for aluminac to work. When unifying sysroot files that declare them, gate the declarations behind `#[cfg(boot)]`. (`#[lang(dyn)]` and `#[lang(dyn_self)]` ARE used by aluminac's resolve paths and have stubs in `sysroot-aluminac/std/builtins.alu`; the *callable* lang items above are the cfg-gated set.)
- [DONE] **Operator overload lang items** (`operator_eq`, `operator_neq`, `operator_lt`, `operator_lte`, `operator_gt`, `operator_gte`). Functionally covered via method-name dispatch — the sysroot lang-item wrappers delegate to those exact method names. See Language features.
- [TODO] **Reflection lang items** (`format_arg`, `enum_variant_new`, `field_descriptor_new`, `field_descriptor_new_unnamed`, `type_descriptor_new`). Required by `enum_variants` / `fields` intrinsics.
- [TODO] **`entrypoint_glue`.** See Language features.
- [DONE] **`static_for_iter`, `static_for_next`.** Aluminac's `lower_static_for` directly calls the type's `.iter()` and `.next()` methods (per the const-evaluated iterator protocol added in `a6b71e0c`). The sysroot's `static_for_iter` / `static_for_next` lang items are thin wrappers around exactly those calls, so the observable behavior matches alumina-boot. Going through the lang-item indirection would add a layer of inlining without functional change.
- [DONE] **Coroutine lang items** (`coroutine`, `coroutine_new`, `coroutine_yield`). Out of scope per `PORTING.md`.

## Stdlib modules

*(Goal: unify each `sysroot-aluminac/` file with its `sysroot/` counterpart into a single file under `sysroot/`. Track per-file. Files only in `sysroot/` are net-new for aluminac. Files only in `sysroot-aluminac/` are aluminac-local accommodations to be merged back.)*

### Already close to parity (small slices)

- [DONE] **`std/util.alu`** — unified.
- [TODO] **`std/mod.alu`** — module re-exports; aluminac-version still has cfg-gated sections; unifying breaks panicking test.
- [DONE] **`sysroot/mod.alu`** — root module. Identical content in both sysroots; verified via diff.
- [DONE] **`std/prelude.alu`** — unified.
- [DONE] **`std/option.alu`** — unified. The dispatch gap noted in the prior session was *not* a method-T shadowing issue; it was that aluminac's `visit_mixin_p1` only carried the *impl's* generic params into `PendingMixin` and silently dropped the mixin's own `<T>` params. Sysroot puts the `mixin<T: Equatable<T>> Equatable<Option<T>>` inside the *non-generic* `impl Option { ... }` block (line 468), where the impl-level gp ids are empty. With nothing recorded for T_mixin, `call_method_on_type` couldn't bind it to the dispatch type's args, and `Option<T_mixin>` resolved through whatever stale `type_map` entry was last set — producing wrong-element-type monos of `not_equals`. Fix: visit the mixin's own type-args under a fresh child scope, collect the resulting generic-param ids, and append to the PendingMixin's `impl_generic_param_ids`. Verified by `tests/aluminac/mixin_own_generics.alu` (focused regression for the polluted dispatch) and the embedded option/range/etc tests now passing under the unified file.

  Sysroot fix bundled with the port: `Option::compare` previously returned `Less` for `None.compare(None)` (a real reflexivity bug, undetected by sysroot's own tests but caught by `tests/aluminac/option_comparable.alu`). Now correctly returns `Equal`; alumina-boot still accepts the file and `make test-std` passes.

  Caveat: `Option::not_equals::<T>(...)` no longer matches the sysroot-aluminac signature with method-level T (since sysroot only has the protocol-mixin'd version with `Self: Option<T>`). `tests/aluminac/protocol_bound_debug.alu` updated to use the natural method-call form `o1.not_equals(&o2)`.

- [DONE] **`std/result.alu`** — unified. Both sysroots now share byte-identical content (verified via `diff -q`). The Self-uniformity refactor unblocked unification: `Result::unwrap` end-to-end works against the unified sysroot, panic chain compiles, all the previously-failing inference paths resolve. Two small additions to sysroot's version were needed to keep the existing aluminac tests green: `or_else` (dual of `and_then` for the error path) and the `AnyResult` type alias — both are pure additions accepted by alumina-boot too.

  Aluminac's `make test-std-aluminac` exercises the embedded test module (`test_result_basic`, `test_unwrap_or`, `test_map`, etc.) under the unified file. `make test-std` (alumina-boot against sysroot) still passes.

  Open follow-ups (now bundled under `std/panicking.alu` instead of result.alu):
  - `panicking::internal::PanicFormatter` segfault when given both `write_str` and `write_byte` directly — the symptom is a Formatter-conformance loop, separate from the result.alu work.
  - Panic-message richness uses DebugAdapter walking through reflection; stubs work, full version blocked on reflection lang items.
<!-- std/result.alu DONE — was previously PARTIAL -->

- [DONE] **`std/range.alu`** — unified. sysroot's range.alu now has fmt impls (additive for alumina-boot; needed by aluminac since sysroot-aluminac's assert_eq formats with `{}`). sysroot-aluminac/std/range.alu is byte-identical to sysroot/std/range.alu. The embedded test module (`test_range`, `test_range_inclusive`, `test_range_lower`, `test_equality`, `test_hash`) now runs under `make test-std-aluminac` (count grows from 18 → 23). The UFCS auto-ref fix landed earlier this session was the prerequisite for `test_hash` to dispatch correctly.

- [DONE] **UFCS auto-ref for methods taking `&T`.** Fixed `unify_type_for_inference` in `mono/lower.alu`: when the callee's parameter is `&T` (Pointer) and the argument is a non-Pointer value, recurse with `(T, arg_ty)` to bind T. Also fixed `try_ufcs_call`'s ref-take to skip when the receiver is already a Pointer (otherwise value-form and ref-form produced different IR — `&` vs `&&` — and dispatched via different mono paths). Verified by `tests/aluminac/ufcs_autoref.alu` (value-form vs ref-form produce identical hashes for Range, Tuple, Option). Closes the value-form UFCS gap.

  Caveat resolved: the prior "`(1..).hash_of()` returns the empty-hash sentinel under `--test --cfg test_std`" failure was a symptom of the mixin-own-generics gap — the mixin'd `not_equals` / `hash` substitution mis-resolved Self in the test runner's mono context. Fixed alongside the option.alu port (see "carry mixin's own generic params into dispatch" commit); `test_hash` now passes under `make test-std-aluminac` against the unified file.

- [DONE] **`std/ffi.alu`** — unified; aluminac test count grows with embedded ffi tests.
- [TODO] **`std/string/mod.alu`** — unifying breaks aluminac bootstrap (sysroot uses dyn-related `?` operator chains).
- [TODO] **`std/string/unicode.alu`** — unifying breaks the util_unicode test (need to investigate).
- [TODO] **`std/hash/mod.alu`** — unifying breaks hash_xxhash and string_extended tests.
- [TODO] **`std/hash/xxhash.alu`** — same; depends on hash/mod.alu unification.
- [DONE] **`std/collections/mod.alu`** — unified; aluminac test count grows with embedded collections tests.
- [TODO] **`std/collections/vector.alu`** — depends on dyn / iter combinator paths.
- [TODO] **`std/collections/deque.alu`** — depends on dyn / iter combinator paths.
- [TODO] **`std/collections/hashmap.alu`** — depends on dyn-via-Option::unwrap.
- [TODO] **`std/collections/hashset.alu`** — depends on dyn-via-Option::unwrap.
- [TODO] **`std/collections/heap.alu`** — depends on dyn / iter combinator paths.

### Medium slices (depend on a single language feature or lang-item set)

- [TODO] **`std/iter.alu` (and merge `sysroot-aluminac/std/iter/` directory back into the single file).** sysroot's iter.alu is large and uses the full iterator protocol; aluminac's has a reduced subset split into a directory. Recent commits worked on iterator protocol — confirm what's still missing.
- [TODO] **`std/typing.alu` (and merge `sysroot-aluminac/std/typing/` back).** Depends on dyn + reflection lang items.
- [TODO] **`std/cmp.alu`** — sysroot uses `DefaultEquatable` mixin + when-based type reflection. Depends on `when_type` and operator-overload lang items.
- [DONE] **`std/math.alu`** — unified. sysroot's version is identical content; the previous "depends on when-dispatch" concern turned out to be moot — sysroot's math.alu is generic but doesn't use complex when-based dispatch. The unified file's embedded test module (`test_abs`, `test_div_floor`, `test_various_math`) runs under aluminac via `make test-std-aluminac`.
- [DONE] **`std/macros.alu`** — unified. The previous blocker was `$m!(...)` inside a macro body where `$m` is a macro parameter: aluminac was storing the literal text `"$m"` as the invocation name and never substituting it. Fixed by recording the param idx on the `MacroInvocation` AST node when the name is a `MacroIdentifier` during body pre-parse, and substituting at expansion time (combining the substituted reference's bound args with the current call's args before resolving the underlying macro). Verified by `tests::test_bind_reduce` which exercises `map!(sum, bind!(times, N), 1, 2, 3)`.
- [DONE] **`std/intrinsics.alu`** — unified. Both sysroots now share byte-identical content. Aluminac-specific intrinsics (`llvm`, `stack_alloc`) live in a `#[cfg(not(boot))]` block in the unified file alongside the existing `#[cfg(boot)]` block for the C-codegen-only intrinsics (`codegen_func` / `codegen_const` / `codegen_type_func`). Each compiler sees only its block. The `slice_len` intrinsic was removed entirely — `mem.alu`'s `len` / `is_empty` now read `self._len` directly, matching sysroot. The remaining intrinsics aluminac needed but had stubbed (`attributed` / `fields` / `enum_variants` / `vtable` / `value_of` / `const_alloc` / `const_bake` / `const_free`) are recognised as no-ops that compile, with the broader semantic completion tracked under reflection-lang-items work.
- [TODO] **`std/builtins.alu`** — sysroot has 3× more impls + typeop lang items + type_descriptor lang item. Gated on the typeop and reflection lang items above.
- [TODO] **`std/mem.alu`** — sysroot has full slice ops + dyn casting. Gated on dyn + slice lang items.
- [TODO] **`std/fmt/mod.alu`** — sysroot has full formatting infrastructure (when-based dispatch on type). Gated on when_type, mixin, protocol bounds.

### Large slices (multiple blockers)

- [TODO] **`std/fmt/ryu/`** — float formatting (10 files). Needs full bit-twiddling intrinsics, when-dispatch, and large const tables. Net-new for aluminac.
- [TODO] **`std/panicking.alu`** — sysroot uses `panic!` macro + setjmp/longjmp via `jmp_buf`; aluminac has a different shape. Reconcile.
- [PARTIAL] **`std/time.alu`** — unification attempted 2026-05-11 then reverted (commits cb7f4380 / 7ec80c85). Switching `sysroot-aluminac/std/time.alu` to sysroot's version compiles cleanly but breaks `make test-std-aluminac` because the embedded `tests` module is then mono'd via aluminac's `test_cases!()` builtin and exposes two latent issues: (1) `test_monotonish` uses `thread::sleep` which sysroot-aluminac doesn't have (gated under `#[cfg(threading)]` upstream is one option), and (2) `test_artithmetic` runs `assert_eq!(start.duration_since(&start), Duration::zero())` on `Duration` values and fails fmt dispatch with "could not resolve method 'fmt' on type ''". The fmt resolution failure is the real blocker; the right fix is to debug why `assert_eq!`'s macro expansion can't dispatch fmt on a Duration value when the standalone `Duration::fmt` call works.
  Missing for unification (post-revert state):
  - Diagnose the `assert_eq!` → `eprintln!` → `static_format_args` → `$arg.fmt($fmt)` dispatch failure for Duration values.
  - Decide whether to keep `test_monotonish` (and any other thread::sleep users) gated under `#[cfg(threading)]` upstream, or to add a thread::sleep stub to sysroot-aluminac.
- [TODO] **`std/fs/mod.alu`** + **`std/fs/unix.alu`** — file abstraction + Unix syscall layer. Depends on closure traits for iteration, libc.
- [PARTIAL] **`std/io/mod.alu`** + **`std/io/unix.alu`** — `io/unix.alu` is already byte-identical between sysroots (the OS-syscall layer needs no aluminac-specific changes). `io/mod.alu` (the Read/Write protocol layer) still needs work — gated on protocol-trait design and dyn dispatch in the sysroot.
- [TODO] **`std/process/mod.alu`** + **`std/process/unix.alu`** — fork/exec/stdio plumbing. Depends on threads, closures, dyn traits.
- [TODO] **`std/runtime/mod.alu`** — backtrace + panic runtime. Depends on debug info + dyn.
- [TODO] **`std/runtime/backtrace.alu`** — uses libc + closures for frame iteration. Depends on debug info + closures verified.
- [DONE] **`std/runtime/minicoro.alu`** — minicoro coroutine glue. Out of scope per PORTING.md; gated under `cfg(coroutines)` in sysroot, never reached by aluminac.
- [TODO] **`std/random/mod.alu`** + **`std/random/ziggurat.alu`** — RNG trait + Gaussian. Depends on protocol traits + closures.
- [TODO] **`std/regex/mod.alu`** + **`std/regex/internal.alu`** — DFA regex engine. Depends on dyn + closures.
- [TODO] **`std/sync/mod.alu`** + **`std/sync/channel.alu`** — Mutex/RwLock/Arc + MPMC channels. Depends on threads + atomics.
- [TODO] **`std/thread/mod.alu`** + **`std/thread/pool.alu`** + **`std/thread/parker/`** — pthread-backed threads + thread pool + futex/pthread parking. Depends on closures for thread bodies.
- [TODO] **`std/net/mod.alu`** + **`std/net/address.alu`** + **`std/net/unix.alu`** — sockets + address parsing + syscall layer. Depends on closures, threads, complex address ops.

### Aluminac-only files (eliminate after parity)

- [DONE] **Delete `sysroot-aluminac/std/strbuf.alu`** — was a 64-byte vestigial stub; deleted.
- [TODO] **Merge `sysroot-aluminac/std/iter/` directory into single `sysroot/std/iter.alu`** (covered above).
- [TODO] **Merge `sysroot-aluminac/std/typing/` directory into single `sysroot/std/typing.alu`** (covered above).

### Libc

- [DONE] **`libc/mod.alu`** — unified. The sysroot version uses `use libc::bindings::*;` to wildcard-import everything, plus a small set of math externs and `errno_location` cfg-dispatched per-OS. Aluminac's `populate_host_cfgs` now sets `target_os` and `target_pointer_width` from the LLVM target triple so the `#[cfg(target_os = "linux")]` arms in sysroot resolve. All quality gates pass.
- [DONE] **`libc/bindings.alu`** — identical content in both sysroots; verified via diff.
- [DONE] **`libc/prelude.alu`** — identical content in both sysroots; verified via diff.

- [DONE] **Type-arg inference: `slice<Ptr>` from expected `&[T]` / `&mut [T]`.** Aluminac's expected-return-type inference path was Struct-only; now also handles the case where the function returns `slice<Ptr>` (the lang slice struct) and the call-site expects `IrTy::Slice`. Lets `slice::empty()` resolve `Ptr` from context. Verified via the unified-sysroot Vector usage in `tests/aluminac/unified_sysroot_basic.alu`.

- [DONE] **Protocol identity through generic-fn substitution.** `resolve_named_type` previously returned `void_ty` when the named item was a protocol, which collapsed protocol type-args at generic call sites — `typing::matches::<i32, Integer>()` mono'd to `i32 is void` and returned false. Now wraps protocols in a new `IrTyTag::Protocol` variant carrying the def-id; the TypeCheck handler recognises this when the AST `check_ty` is a Placeholder substituting to a Protocol IrTy. Verified by `tests/aluminac/unified_sysroot_basic.alu` (typing::matches against Integer / FloatingPoint / Signed).

- [DONE] **`*T` (deref-of) in type position.** Sysroot's `SliceIterator::next` returns `Option<*Ptr>` — `*Ptr` is the pointee type of the generic `Ptr` param. Aluminac's parser previously didn't handle `NodeKind::DerefOf` and silently returned `Ty::unresolved`, collapsing to void after substitution. So the iterator returned `Option<void>` instead of `Option<i32>`, and the for-loop on slices/arrays silently produced 0 iterations. Adds a `Ty::DerefOf` AST variant + parse_type case + resolve_type case (after substitution, derefs through the inner pointer type). Verified by `tests/aluminac/unified_sysroot_basic.alu` for-loops over a slice and an array.

- [DONE] **Slice method dispatch with two generic params.** `call_method_on_type` for slice methods passed only one type-arg (Ptr), but methods like `slice::equals<T, Ptr>` declare two — T (the pointee, bounded `Equatable<T>`) and Ptr (bounded `PointerOf<T>`). When `def.generic_params.len() == 2`, aluminac now passes `[elem_ty, ptr_ty]` instead of `[ptr_ty]`. Verified by string starts_with / ends_with which go through slice equality.

- [DONE] **Mixin's own generic params carried into dispatch.** `mixin<T: Bound> Proto<X<T>>;` introduces a fresh T scoped to the mixin alone. Aluminac previously only carried the *impl's* generic params into `PendingMixin` and silently dropped the mixin's own — which broke sysroot's `impl Foo { mixin<T> Equatable<Foo<T>>; }` pattern (Option / Result both use it). Fixed in `visit_mixin_p1` by parsing the mixin's type-args under a fresh child scope, collecting the resulting ids, and appending to `PendingMixin.impl_generic_param_ids`. Verified by `tests/aluminac/mixin_own_generics.alu`.

- [DONE] **Builtins satisfy user-defined protocols by method names.** `check_protocol_conformance` walks the type's struct/enum scope to verify each protocol method exists by name, but builtins (i32, u8, …) fell through with no scope — so `i32 is Formattable<i32, F>` returned false even though i32 has a `fmt` method on its lang-item-tagged struct. Now looks up `#[lang(builtin_X)] struct X {}`'s scope. Verified by `tests/aluminac/builtin_protocol_conformance.alu`.

- [DONE] **Default type-arg substitution.** `GenericParam.default_ty` was parsed but never consulted by mono. After explicit type_args setup in `mono_function`, walks declared generic params and substitutes `default_ty` for any slot that's missing or void. Required by sysroot signatures like `fn hash_of<T, H = DefaultHash>(val: &T)`. Verified by `tests/aluminac/default_type_arg.alu`.

- [DONE] **Grouped use list with nested paths.** `use outer::{shallow, inner::deep};` — the nested-path arm of a grouped use list ignored the outer prefix, so `deep` aliased to `[inner, deep]` rather than `[outer, inner, deep]`. Sysroot uses this in several places (notably `use mem::{size_of, slice::from_raw};` inside `builtins.alu`'s IntegerHashable). Verified by `tests/aluminac/use_grouped_nested_path.alu`.

- [DONE] **Tuple comparisons dispatch through `impl tuple<Tup>`.** `(a,b) < (c,d)` and friends used to bypass operator-overload eligibility (only Struct/Slice were accepted) and emit `icmp ult` on aggregate types. `find_method_in_scope` and `call_method_on_type` now route IrTyTag::Tuple through the `builtin_tuple` lang item; `lower_binop` accepts Tuple for comparison overloading; the mixin-substitution branch binds `Tup` (the tuple's single impl-generic) to the whole tuple type. Verified by `tests/aluminac/tuple_compare_dispatch.alu` (uses `--sysroot sysroot` since sysroot-aluminac/'s minimal tuple impl doesn't yet declare compare).

## Unified sysroot probe

- [PARTIAL] **Aluminac compiles dyn-free programs against `sysroot/`.** The slices in this branch (typeop dispatch, slice pseudo-fields, range type inference, fn-item type resolution, generic-fn skip-on-export, etc.) collectively let aluminac swallow non-trivial code against the unified sysroot — verified by `tests/aluminac/unified_sysroot_basic.alu`. The test exercises generics, Ordering, comparison-operator overload dispatch on a user struct, and works as a regression guard.

  `Option::unwrap` (and the rest of the panic chain — `Result::unwrap`, `panic!`, `dyn Formattable`-based `const_panic_impl`) compiles and runs end-to-end against `--sysroot sysroot`, verified by `tests/aluminac/unified_sysroot_unwrap.alu`. The wins:

  - Protocol type-args threaded through `IrTyTag::Protocol`.
  - Dyn vtable build assembles `[impl_struct.type_args..., proto.non_self_args...]` for impl methods.
  - Single-proto direct-Placeholder unification of `&dyn Proto<...>` in expected-return-type inference.
  - Expected element type propagated into array-literal lowering (panic path expands `format_args!` into an array of `dyn_format_arg(&...)` calls whose F must be solved from the array's expected type).
  - Codegen skips phi for zero-sized result types (LLVM 14 GlobalISel crashes on `phi {}` from `Result<T, ()>`-shaped flow).

  Missing:
  - Stdlib code that uses `dyn` directly (regex internal DFA, runtime backtrace, typing reflection, io/fs Read/Write protocols) — still unverified end-to-end. The **Protocol-method Self uniformity** gap that was the suspected blocker is resolved as of 2026-05-11; remaining failures are likely shallower per-feature work.
  - Macros that expand to references to coroutines / threading / panicking.
  - The actual panic *runtime* (setjmp/longjmp, backtrace) hasn't been exercised — only the compile-time chain.
  - `Result::unwrap` against `--sysroot sysroot` now works end-to-end (compile + run) following the Self-uniformity refactor — verified by `tests/aluminac/unified_sysroot_unwrap.alu` and a minimal repro that previously failed at `fmt/mod.alu:336` with "could not resolve method 'write_byte' on type ''".

- [DONE] **Macro expansion type inference for if/else expressions.** Reduced reproductions of "if-else where both arms produce Result<...>" pass under aluminac (verified locally). The original concern was about sysroot's bare format! returning the if/else inline; that's blocked behind sysroot/std/fmt/mod.alu unification on grounds other than this inference issue (the StringBuf/dyn dispatch chain). When that unification is attempted, re-investigate; for now the issue isn't a blocker.

- [DONE] **Array equality (`==` / `!=` on `[T; N]` value types).** Codegen unrolls into element-wise `icmp` (or `fcmp` for float elements) folded with AND (for ==) or OR (for !=). Verified via the milestone test.

- [DONE] **switch on bool / enum: phi-node and pattern-value bugs.** Two compounding bugs broke `switch b { true => x, false => y }`:
  1. Mono's switch-arm value extraction handled IntLit and Cast(IntLit) patterns but missed `BoolLit`, so `true` and `false` patterns both got value 0 — the second arm was deduplicated and dropped.
  2. Codegen's switch defaulted to merge_bb when there was no user default arm, making merge_bb a predecessor of itself for the LLVM switch instruction; the phi's incoming-block list then disagreed with the predecessor count. Now creates a synthetic `switch.default` block terminating in `unreachable` so merge_bb's predecessors match the arm count.
  Verified by `tests/aluminac/unified_sysroot_basic.alu` (bool switch with both true and false branches taken on different values).

## Test infrastructure

*(Running the alumina-boot test suites through aluminac. `tests/diag/` is **not** in scope — keep it passing under alumina-boot only.)*

- [TODO] **Add `make test-lang-aluminac`.** `tests/lang/lang.alu` is one module with ~35 `#[test]` functions; aluminac already supports `--cfg test --cfg test_std` for `make test-std-aluminac`, so a parallel target should be straightforward.
- [TODO] **Add `make test-libraries-aluminac`.** Compile `libraries/` with aluminac's `--test` flag. May require closure / dyn support for some libraries.
- [TODO] **Confirm `make test-std-aluminac` runs against the unified `sysroot/`** once feature gaps close; today it points at `sysroot-aluminac/`.
- [DONE] **`tests/aluminac/run_tests.sh` shell-driven runner** — fits the aluminac-specific suites, keep as-is. No work expected.
- [DONE] **`tests/diag/` and `make test-diag`** — alumina-boot only, no porting work; just don't break it on the boot side.
- [TODO] **`make test-docs`** — currently uses alumina-boot to compile generated `doctest.alu`. Bringing under aluminac is gated on full sysroot parity.

## Sysroot deletion (final)

- [TODO] Delete `sysroot-aluminac/` once the unified `sysroot/` compiles under both compilers, the aluminac → aluminac → aluminac bootstrap converges on `sysroot/`, and `make test-lang` / `make test-std` / `make test-libraries` pass under both compilers. Gated on the rest.
