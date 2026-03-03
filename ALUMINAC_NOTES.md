# aluminac vs alumina-boot: In-Depth Comparison

*Generated 2026-03-03. Based on reading both compiler codebases and auditing
real-world usage across common/, sysroot/, examples/, tools/, libraries/, and tests/.*

Note that some of the paths have been changed for aluminac, it is now in src/

## Table of Contents

1. [Architecture Overview](#1-architecture-overview)
2. [Missing Features -- Prioritized](#2-missing-features----prioritized)
3. [Implicit Coercions and Lang Item Machinery](#3-implicit-coercions-and-lang-item-machinery)
4. [Legitimate Implementation Differences](#4-legitimate-implementation-differences)
5. [Feature-by-Feature Deep Dive](#7-feature-by-feature-deep-dive)
6. [Real-World Usage Audit](#8-real-world-usage-audit)
7. [Source References](#appendix-source-references)

---

## 1. Architecture Overview

### File Structure

| Component | alumina-boot (Rust, ~18K lines) | aluminac (Alumina, ~15K lines) |
|---|---|---|
| Parser | `src/parser.rs` (165 lines, thin tree-sitter wrapper) | `lib/parser.alu` (3619 lines, all-in-one) |
| AST | `src/ast/*.rs` (8 files, ~5800 lines) | `lib/ast.alu` (926 lines) + `lib/node_kinds.alu` (915 lines) |
| Scope/Resolution | `src/src/*.rs` (4 files, ~1500 lines) | `lib/scope.alu` (401 lines) |
| IR/Mono | `src/ir/*.rs` (9 files, ~5600 lines) | `lib/mono.alu` (4369 lines) |
| Codegen | `src/codegen/*.rs` (4 files, ~2050 lines) | `lib/codegen.alu` (3155 lines) |
| Compiler driver | `src/compiler.rs` + `src/main.rs` (~510 lines) | `lib/compiler.alu` (755 lines) |
| Diagnostics | `src/diagnostics.rs` (590 lines) | `lib/diagnostics.alu` (164 lines) |
| Common | `src/common.rs` (585 lines) | `lib/common.alu` (63 lines) + `lib/arena.alu` (128 lines) |

### Pipeline Comparison

**alumina-boot**: Parse (tree-sitter) -> Pass1 (scope building) -> Pass2 (AST building with name resolution + for-loop/try desugaring) -> Mono (monomorphization + type inference + const eval) -> ZST Elision -> DCE -> Codegen (C text) -> C compiler

**aluminac**: Parse (tree-sitter) -> Pass1 (scope building) -> Pass2 (AST building) -> Mono (monomorphization + type inference + limited const eval + for-loop desugaring) -> Codegen (LLVM IR) -> LLVM backend

alumina-boot has separate ZST elision (613 lines) and DCE (215 lines) IR passes plus an IR fold/rewrite framework and IR inlining pass. These are largely unnecessary for aluminac since LLVM handles most of this. The exception is ZST elision -- we must guarantee no loads/stores are emitted for ZSTs (needs investigation whether LLVM handles this out of the box).

---

## 2. Missing Features -- Prioritized

### Tier 1: Essential (blocks compiling almost any real program)

#### 2.1. Full Const Evaluation

**This is the single most important missing feature.** Even basic enum definitions depend on const eval (e.g., enum variants with expressions like `FOO = BAR + 1`, or references to other enum values). The stdlib is riddled with const contexts.

**alumina-boot**: Full interpreter in `src/ir/const_eval.rs` (~1800 lines):
- Complete value representation: `Void`, `Bool`, all integer types up to `u128`/`i128`, `F32`, `F64`, `Bytes`, `Tuple`, `Array`, `Struct`, `FunctionPointer`, `Pointer(LValue)`, `LValue`
- Statement evaluation with goto/label support for loops
- Recursive function evaluation with depth limit (100) and iteration limit (1M)
- Full pointer arithmetic in const context
- `transmute` via byte roundtrip
- `const_alloc`/`const_free` for compile-time heap allocation
- `const_panic`/`const_warning`/`const_note` for compile-time diagnostics
- `const_bake` to force const evaluation and embed result

**aluminac**: Extremely limited `try_const_eval_u64()` in `mono.alu:1609-1703`:
- Only produces `u64` values (not full value types)
- Handles: int/bool literals, size_of, align_of, casts, binary ops, unary ops, blocks, void
- Can evaluate simple direct function calls by recursing into body
- **Missing**: pointer values, struct/tuple/array values, string values, assignments, loops, goto/labels, const_alloc/const_free, proper enum variant evaluation

**Enum variant evaluation** (`mono.alu:629-695`): ~~FIXED~~ Now uses two-pass approach matching alumina-boot: (1) evaluate all explicit variant values via `lower_expr` + `try_const_eval_u64`, supporting binary ops, casts, etc.; (2) auto-increment non-valued variants from 0, skipping taken values. Duplicate detection via HashSet. Test: `tests/aluminac/enum_const_eval.alu`.

**Usage**: 45 explicit `const_eval`/`const_bake` calls in sysroot, plus every enum definition, every `when` expression, every `static for`, and every `const` item.

#### 2.2. Builtin Macros

**Usage**: `println!`/`format_args!` alone have 318+ occurrences across 63 files.

**alumina-boot**: 11 builtin macros in `src/ast/macros.rs`:
1. `format_args!($fmt, $args...)` -- parses format string `"{} {0}"`, interleaves string pieces and argument references. Foundation for `println!`, `eprintln!`, `write!`, `writeln!`, `format!`, `assert!`, `panic!`.
2. `bind!($mac, $arg...)` -- partial application of macros (macro currying)
3. `reduce!($mac, $base, $arg...)` -- folds a macro over arguments
4. `stringify!($expr)` -- converts expression AST to string
5. `env!($var)` -- reads environment variable at compile time
6. `cfg!($flag)` -- checks cfg flag, returns bool literal
7. `include_bytes!($file)` -- reads file at compile time
8. `concat!($args...)` -- concatenates constant strings
9. `line!()` -- current source line number
10. `column!()` -- current source column
11. `file!()` -- current source file path

Each is declared with `#[builtin]` attribute in `sysroot/std/macros.alu` and `sysroot/std/mod.alu`.

**aluminac**: User-defined macros work. Builtin macro infrastructure implemented: the `#[builtin]` attribute is recognized on macro definitions, and the parser dispatches to specialized compile-time handlers. Currently implemented builtins:
1. `cfg!($flag)` -- checks cfg flag, returns bool literal
2. `line!()` -- current source line number
3. `column!()` -- current source column
4. `file!()` -- current source file path
5. `stringify!($expr)` -- converts expression source text to string
6. `env!($var)` -- reads environment variable at compile time
7. `concat!($a, $b)` -- concatenates constant strings
8. `include_bytes!($file)` -- reads file at compile time
9. `format_args!($wrapper, $fmt, $args...)` -- format string parsing with piece interleaving (basic support)

Also implemented: `bind!` (partial macro application), `reduce!` (fold macro over arguments), `count!` (count arguments), and **et cetera expansion** (`$arg$...`) for variadic macros. Variadic macro parameters (`$arg...`) capture remaining arguments, and `$arg$...` in argument lists expands the inner expression once per variadic arg. This enables the full `format_args!` → `reduce!` → fold chain used by `println!`, `write!`, etc.

Tests: `tests/aluminac/builtin_macros.alu`, `tests/aluminac/bind_reduce.alu`, `tests/aluminac/format_args.alu`.

#### 2.3. Complex `#[cfg()]` Evaluation

**Usage**: 2050+ occurrences across 50+ files. The entire sysroot is gated on cfg conditions.

**alumina-boot**: Full boolean cfg evaluation in `src/visitors.rs` (`CfgVisitor`):
- `#[cfg(flag)]` -- simple presence check
- `#[cfg(not(flag))]` -- negation
- `#[cfg(all(a, b, c))]` -- conjunction
- `#[cfg(any(a, b, c))]` -- disjunction
- `#[cfg(key = "value")]` -- key-value matching (e.g., `target_os = "linux"`)
- `#[cfg_attr(condition, attribute)]` -- conditional attribute application

**aluminac**: Implemented. Supports `#[cfg(flag)]`, `#[cfg(not(...))]`, `#[cfg(all(...))]`, `#[cfg(any(...))]`, `#[cfg(key = "value")]`, and arbitrary nesting. Evaluated during Pass 1 — items whose cfg condition is false are skipped entirely (not registered in scopes). Works on functions, structs, enums, protocols, type aliases, consts, statics, use declarations, impl blocks, macro definitions, and top-level blocks. Key-value matching uses `--cfg key=value` command-line syntax. Missing: `#[cfg_attr(condition, attribute)]`.

#### 2.4. For-Loop Iterator Desugaring

**Usage**: Every `for x in collection` loop in the language.

**alumina-boot** desugars in the parser (`src/ast/expressions.rs:1038-1205`) to:
```
for x in iterable { body }
// becomes:
{
    let _iter = iterable.iter();   // plain method call, NOT IntoIterator
    loop {
        let _result = _iter.next();  // plain method call
        if _result._is_some {        // direct field access on Option struct
            let x = _result._inner;  // direct field access on Option struct
            body
        } else {
            break;
        }
    }
}
```
No lang items, no `IntoIterator` protocol. Pure syntactic desugaring to `.iter()` + `.next()` + `_is_some`/`_inner` field access on the Option struct. Also supports tuple unpacking: `for (a, b) in pairs { ... }`.

Note: the desugaring also attempts to find a free function named `iter` in scope for UFCS (`expressions.rs:1117-1125`), but the primary mechanism is method call.

**aluminac**: Implemented. For struct types, calls `.iter()` on the iterable to get an iterator, then uses `.next()` + `is_none()` + `_inner` field access. Has fast-paths for slices and arrays (index-based iteration). Does not support tuple unpacking in for-loop variables or UFCS `iter` free function lookup.

#### 2.5. Try Operator (`?`)

**alumina-boot** (`src/ast/expressions.rs:728-734`): Desugars `expr?` to a `try!(expr)` macro invocation. The compiler constructs a path `"try"` and calls `visit_macro_invocation_impl`. The actual `try` macro must be in scope via `use`:
- `sysroot/std/result.alu:58-65`: `macro try($res) { ... return Result::err(res.unwrap_err()) ... }`
- `sysroot/std/option.alu:54-61`: `macro try($opt) { ... return Option::none() ... }`

This is user-extensible -- any `try` macro in scope works for custom types.

**aluminac** (`parser.alu:3349`): Now desugars `expr?` to `try!(expr)` macro invocation at parse time, matching alumina-boot's approach. The parser looks up the `try` macro in scope and expands it inline. If no `try` macro is in scope, falls back to a hardcoded `lower_try()` in mono that inspects struct layout (for backward compatibility with standalone tests). The `try` macros are defined in `sysroot-simple/std/result.alu` and `sysroot-simple/std/option.alu`, with the Result version imported via prelude (matching the full sysroot). Test: `tests/aluminac/try_operator.alu`.

#### 2.6. Closures with Captures

**alumina-boot**: Full closure implementation:
- `FnKind::Closure(&[ClosureBinding], ItemP)` AST variant (`src/ast/mod.rs:912`)
- Closure struct created with captured variables as fields
- Closure function takes the struct as implicit first argument
- Calling convention: extract function pointer from struct, pass struct as first arg
- Protocol conformance: closures satisfy `Callable` protocols
- `ClosureBinding` tracks: id, name, value expression, binding type (by-ref/by-value)

**aluminac**: Closures with captures implemented. Supports both by-value (`=var`) and by-reference (`&var`) captures. Closure struct created with captured values as fields; closure function receives implicit `&self` pointer as first parameter. Mixed captures (by-value + by-reference + regular params) work. Non-capturing lambdas still compile to bare function pointers. Protocol conformance for closures (e.g. `Callable`) is not yet implemented.

#### 2.7. Operator Overloading and Implicit Coercions

**Operator overloading**: Implemented for the 6 comparison operators (`==`, `!=`, `<`, `<=`, `>`, `>=`). When a comparison is applied to struct types, aluminac looks up the corresponding method (`equals`, `not_equals`, `less_than`, `less_than_or_equal`, `greater_than`, `greater_than_or_equal`) directly on the type's scope, creates references to both operands, and calls it. Also supports the lang item path (`operator_eq` etc.) with protocol redirect fallback. The approach differs from alumina-boot (which goes through lang items + inlining) but produces the same observable behavior.

See [Section 3](#3-implicit-coercions-and-lang-item-machinery) for implicit coercions (mostly still missing).

### Tier 2: Important (needed for full sysroot compilation)

#### 2.8. Dynamic Dispatch (`dyn`)

**Usage**: 53 occurrences across 14 files including `std::fmt`, `std::io`, `std::typing`, `std::panicking`.

**alumina-boot**: Full dyn dispatch:
- `Ty::Dyn(&[TyP], bool)` AST type variant
- VTable generation: `generate_vtable()` intrinsic creates array of function pointers
- Dyn object creation: `try_coerce()` creates `(data_ptr, vtable_ptr)` tuple
- Virtual call: `lower_virtual_call()` indexes into vtable, emits indirect call
- Dyn downcast: `lower_cast()` uses `TypeId` for safe casting
- 7 lang items: `Dyn`, `DynSelf`, `DynNew`, `DynConstCoerce`, `DynConstCast`, `DynData`, `DynVtableIndex`

**aluminac**: No dyn support whatsoever.

#### 2.9. Type Operators

**Usage**: Used throughout `sysroot/std/typing.alu` and `sysroot/std/builtins.alu`.

**alumina-boot**: 9 type operators:
- `ReturnTypeOf<Fn>`, `ArgumentsOf<Fn>`, `PointerWithMutOf<Ptr>`, `ArrayWithLengthOf<Arr>`, `GenericArgsOf<T>`, `ReplaceGenericArgsOf<T, Args>`, `FunctionPointerOf<T>`, `UnderlyingTypeOf<Enum>`, `UnderlyingFunctionOf<Closure>`

**aluminac**: No type operator support.

#### 2.10. Lang Items (97 in alumina-boot)

**alumina-boot** defines 97 lang items in `src/ast/lang.rs`:
- **Slice operations** (7): `Slice`, `SliceNew`, `SliceIndex`, `SliceRangeIndex`, `SliceConstCoerce`, `SliceConstCast`, `SliceSlicify`
- **Range types** (12): 6 range types + 6 constructors
- **Builtin protocols** (26): Primitive, Numeric, Integer, FloatingPoint, Signed, Unsigned, ZeroSized, Pointer, Array, Tuple, Range, Struct, Enum, Union, Callable, NamedFunction, FunctionPointer, Closure, Const, Static, ArrayOf, PointerOf, RangeOf, Meta, SameLayoutAs, SameBaseAs, Any, None
- **Builtin impls** (18+): One per primitive type, plus tuple/array/callable
- **Type operators** (9): see above
- **Dyn dispatch** (7): see above
- **Coroutines** (3): `Coroutine`, `CoroutineNew`, `CoroutineYield`
- **Operators** (6): `operator_eq`, `operator_neq`, `operator_lt`, `operator_lte`, `operator_gt`, `operator_gte`
- **Static for** (2): `StaticForIter`, `StaticForNext`
- **Misc**: `EntrypointGlue`, `FormatArg`, `EnumVariantNew`, `FieldDescriptorNew`, `FieldDescriptorNewUnnamed`, `TypeDescriptorNew`

**aluminac**: Recognizes `#[lang]` attribute and uses it for protocol method Self substitution (`mono.alu:207-217`), but the set of recognized lang items is much smaller.

#### 2.11. Memory Layout Attributes

| Attribute | alumina-boot | aluminac | Usage |
|---|---|---|---|
| `#[packed(N)]` | Yes, with custom pack values | No | 11 uses in tests, needed for FFI |
| `#[align(N)]` | Yes | Yes (parsed, but limited in codegen) | Used in sysroot |
| `#[transparent]` | Yes (single-field struct optimization) | No | 3 uses in sysroot (std::ffi, std::sync) |

These affect ABI compatibility and are needed for correct FFI.

#### 2.12. Missing Intrinsics

**alumina-boot**: 41 intrinsics. **aluminac**: ~20.

Key missing intrinsics (grouped by importance):

**Essential for static for to work with iterators:**
- `stop_iteration` -- signals end of iteration during const eval. Used by `static_for_next` lang item (`sysroot/std/iter.alu:1950-1958`). NOT related to coroutines -- it's the termination mechanism for `for const` loops that use the proper iterator protocol.

**Essential for stdlib:**
- `const_eval` / `const_bake` -- force compile-time evaluation (45 uses)
- `enum_variants` -- array of `{name, value}` descriptors (3 uses)
- `fields` -- struct field reflection descriptors (2+ uses)
- `tuple_invoke` -- call function with tuple-unpacked args (6 uses)
- `attributed` -- find all items with given attribute (3 uses, **test framework depends on this**)
- `vtable` -- generate vtable for type/protocol pair (3 uses, needed for dyn)
- `expect` -- branch prediction hint, maps to LLVM's `llvm.expect` intrinsic
- `module_path` -- get module path string

**NOT needed in aluminac** (alumina-boot C codegen specific):
- `codegen_const` -- inline C constant name (use LLVM intrinsics directly instead)
- `codegen_type_func` -- inline C function with type parameter (use LLVM intrinsics directly)

#### 2.13. Static For (Proper Implementation)

**alumina-boot**: Uses `StaticForIter` and `StaticForNext` lang items:
1. Calls `StaticForIter` (which calls `.iter()`) to get an iterator
2. Const-evaluates `StaticForNext` in a loop (which calls `.next()` and returns the value, or calls `stop_iteration()` when done)
3. `stop_iteration()` raises `ConstEvalErrorKind::StopIteration` which terminates the unrolling
4. Each iteration body is lowered with the loop variable bound to the const-evaluated value
5. Supports `StaticForLoopVariable::Tuple(&[Id])` for tuple unpacking

**aluminac** (`mono.alu:2205-2285`): Very basic. Only handles tuples and arrays by element count:
- Checks `IRTY_TUPLE` or `IRTY_ARRAY`, gets count from type
- Indexes into the value using `IR_FIELD_ACCESS` by index
- Does NOT use lang items, does NOT use const eval iterator protocol
- Does NOT handle ranges or any iterable beyond tuple/array

#### 2.14. Deferred Name Resolution

**alumina-boot**: `NameResolver` returns `ScopeResolution::Defered(Ty)` when resolution depends on a generic type parameter (e.g., `T::method` where T is generic). This allows the compiler to defer resolution until monomorphization.
- `Ty::Defered(Defered)` and `ExprKind::Defered(Defered)` AST types
- `Ty::Tag(&str, TyP)` for tagging deferred types with method names

**aluminac**: Resolves eagerly during parsing. Unresolvable names produce zero-ID placeholders or errors.

### Tier 3: Can Skip

#### 2.15. Coroutines / Yield

**Not important.** No stdlib machinery depends on them. The plan is to eventually switch to stackless coroutines, so implementing the current stackful model in aluminac would be wasted effort. Skip entirely.

---

## 3. Implicit Coercions and Lang Item Machinery

alumina-boot leans heavily on sysroot lang items for implicit coercions. This is a broader category than just operator overloading.

### 3.1. Coercion via `try_coerce()` (`ir/mono/mod.rs:~2876`)

| Coercion | Mechanism | Lang Item |
|---|---|---|
| `&mut [T]` -> `&[T]` | Calls lang item | `SliceConstCoerce` |
| `&[T; N]` -> `&[T]` | Constructs slice from ptr + len | `SliceNew` |
| `&mut [T; N]` -> `&mut [T]` | Same | `SliceNew` |
| `&mut dyn P` -> `&dyn P` | Calls lang item | `DynConstCoerce` |
| `&T` -> `&dyn Protocol` | Creates dyn object with vtable | `DynNew` |
| Named function -> fn pointer | Direct cast | (no lang item) |

**aluminac**: Handles `&[T; N]` -> `&[T]`, `&mut T` -> `&T`, and `&mut [T]` -> `&[T]` coercions. Dyn coercions are still missing.

### 3.1.1. `#[lang(builtin_X)]` Method Dispatch

**alumina-boot**: Methods on builtin types (i32, u8, etc.) are provided via `#[lang(builtin_X)]` structs. When resolving `x.method()` where `x` is a builtin type, the compiler looks up the corresponding lang item struct's scope to find the method. The struct itself resolves to the builtin type (not a real struct).

**aluminac**: Implemented. `resolve_named_type` intercepts `#[lang(builtin_X)]` struct definitions and returns the corresponding builtin type. `try_lower_method_call` looks up the lang item struct's scope for method resolution on builtin types. Supports both by-value (`self: i32`) and by-reference (`self: &i32`) methods.

### 3.2. Operator Overloading (`ir/mono/mod.rs:~3838`)

Only 6 comparison operators are overloadable: `==`, `!=`, `<`, `<=`, `>`, `>=`.

Mechanism: `lower_binary` first tries built-in type checking. If that fails with `InvalidBinOp` and the operator is one of the 6, it falls back to `invoke_custom_binary`, which:
1. Coerces RHS to LHS type
2. Takes references to both operands (`&lhs`, `&rhs`)
3. Calls the lang item `Operator(op)` with the value type and the two references

**aluminac**: Implemented. For struct types, directly looks up the method (`equals`, `less_than`, etc.) on the type's scope. Also supports lang item path with protocol redirect. Does not require `Equatable`/`Comparable` protocol conformance — just the presence of the method.

### 3.3. Indexing via Lang Items

| Operation | Lang Item | Description |
|---|---|---|
| `slice[i]` | `SliceIndex` | Single-element slice indexing |
| `slice[a..b]` | `SliceRangeIndex` | Range-based slice indexing |
| Slicifiable types | `SliceSlicify` | Auto-convert to slice before indexing |

**aluminac** (`mono.alu:2574-2652`): Hardcoded indexing behavior. For slices: extracts data pointer (field 0), indexes through it. For structs with slice-like fields: auto-dereferences. Does not go through lang items.

### 3.4. Callable Protocol

`Lang::ImplCallable` is used for calling closures and function objects. This interacts with `ProtoCallable` for protocol bound inference.

**aluminac**: No callable protocol support.

---

## 4. Legitimate Implementation Differences

These are areas where aluminac takes a different approach from alumina-boot. Neither approach is "wrong" -- they're implementation details, not language semantics.

### 4.1. Backend: C vs LLVM

alumina-boot emits C text and delegates to GCC/Clang. aluminac uses LLVM C API directly.

### 4.2. AST/IR Representation

alumina-boot uses Rust enums with named variants. aluminac uses flat tagged structs (necessary since Alumina lacks data-carrying enums). Both are valid representations.

### 4.3. Control Flow Lowering

alumina-boot lowers loops/breaks/continues/defers to labels and gotos. aluminac preserves structured control flow (`IR_WHILE`, `IR_LOOP`, `IR_BREAK`, `IR_CONTINUE`, `IR_DEFER`) and lets LLVM codegen create appropriate basic blocks. The aluminac approach is natural for LLVM.

### 4.4. Switch Statements

alumina-boot lowers `switch` to `if`/`goto` chains. aluminac emits native `LLVMBuildSwitch` with phi nodes (`codegen.alu:2776-2935`). The aluminac approach is better for LLVM.

### 4.5. Defer Implementation

alumina-boot lowers defers to goto/label during mono. aluminac uses a defer stack in codegen (`codegen.alu:1111-1112, 1232-1239`). Both should produce correct results, though the aluminac approach may have edge cases with defers in loops.

### 4.6. Mono Cache

alumina-boot uses `MonoKey(ItemP, &[TyP])` with reverse lookup. aluminac uses FNV-1a hashing. Implementation detail -- correctness is what matters.

### 4.7. IR Passes (ZST Elision, DCE, Fold, Inline)

alumina-boot needs ZST elision (613 lines), DCE (215 lines), IR fold (251 lines), and IR inlining (65 lines) because C codegen can't optimize these away. LLVM handles most of this automatically. **Exception**: we must verify that LLVM doesn't emit loads/stores for ZST values -- if it does, we need some level of ZST handling.

### 4.8. String Literals

alumina-boot emits C string literals with hex escaping. aluminac creates LLVM global constants with `LLVMConstStringInContext` and deduplicates via hash cache.

### 4.9. Struct Layout

alumina-boot computes explicit padding via `Layouter`. aluminac delegates to LLVM's `LLVMStructSetBody`. For unions, aluminac finds the largest field.

### 4.10. Diagnostics

alumina-boot has rich error reporting (~590 lines) with source spans, caret highlighting, notes, and suggestions. aluminac now has basic error reporting with file:line:column positions and errors for:
- Unresolved field access
- Unresolved method calls (suppresses redundant field error)
- Unresolved function references
- Unknown intrinsics
- Format message helper (`format_msg`) for building error strings in arena

Still missing vs alumina-boot: source line display, caret highlighting, notes/suggestions, multi-span errors.

---

## 5. Feature-by-Feature Deep Dive

### 5.1. Macro Expansion

**alumina-boot** (`src/ast/macros.rs`, ~800 lines):
- `MacroMaker`: Parses macro definitions, detects recursive macro calls
- `MacroExpander`: Substitutes arguments into macro body
- Et cetera (`...`) expansion in: function call args, tuple/array literals, block statements
- Local variables inside macros get fresh IDs to avoid name clashes
- Arguments can themselves be macros (higher-order macro patterns)
- Type substitution within macros
- 11 builtin macros (see 2.2)

**aluminac** (`parser.alu:3168-3278`):
- Inline expansion by swapping `macro_args` array and re-parsing body node
- Handles `universal_macro_invocation` (method-syntax macros: `obj.macro!(args)`)
- No fresh ID generation for macro locals (potential hygiene issues)
- No higher-order macro support
- No builtin macro infrastructure

### 5.2. When/Static If

Both handle `when` (compile-time if) similarly:
- Const-evaluate the condition
- Only monomorphize the taken branch
- alumina-boot: `ExprKind::StaticIf` + `Ty::When`
- aluminac: `EXPR_WHEN` + `TY_WHEN`, with `lower_when()` at `mono.alu:1966-1989`
- **Note**: aluminac defaults to false branch when const-eval fails (`mono.alu:1975-1976`). This is reasonable for now but could hide bugs.

### 5.3. Protocol Conformance

**alumina-boot**: Rich protocol checking:
- Cached results in `protocol_bound_cache`
- `ProtocolBounds` with `All`/`Any` semantics
- Negated bounds (`!Protocol`)
- Builtin protocol matching via lang items
- Deferred protocol checking for generic contexts

**aluminac** (`mono.alu:1772-1794`):
- Simple name-based: for each method in protocol, check if it exists in the type's scope
- Hardcoded builtin protocol names (`ZeroSized`, `Pointer`, `Primitive`, etc.) matched by string
- No caching, no negated bounds, no `All`/`Any` combinators

### 5.4. Type Inference

**alumina-boot**: Dedicated `TypeInferer` in `src/ir/infer.rs` (315 lines):
- Slot-based unification
- Protocol bound inference: `ProtoCallable`, `ProtoArrayOf`, `ProtoPointerOf`, `ProtoRangeOf`
- Callable matching across functions, closures, and function pointers
- Default generic parameter fallback

**aluminac** (`mono.alu:2978-3117`):
- Ad-hoc: direct placeholder matching from formal -> actual types
- Pointer/slice unwrapping for nested placeholder inference
- Return-type inference from expected type context
- No protocol bound inference
- No callable matching

### 5.5. Scope Resolution

| Feature | alumina-boot | aluminac |
|---|---|---|
| Impl blocks per type | Multiple (impl is a grouping, not a named item) | One item per name (last wins) |
| Cycle detection | `CycleGuardian` | None |
| `super::` path | Yes (`Scope::find_super()`) | No |
| Unused import warnings | Yes (`used_items` tracking) | No |
| Block-level shadowing | Preserves old items in `shadowed_items` | Overwrites with `HashMap::insert` |
| Star import resolution | Lazy (stores symbolic path) | Eager (resolves scope immediately) |
| Deferred resolution | `ScopeResolution::Defered(Ty)` for generics | Eagerly resolves or errors |

Note on impl blocks: A type can have multiple impl blocks, possibly with different generic parameters. An `impl` is not really a proper named item -- it's more of a group of methods with ambient generic placeholders that get inherited by the methods. In non-linear scopes (modules, structs, enums), items must be unique. In function bodies (linear scopes), shadowing applies.

### 5.6. AST Type Variants Missing from aluminac

| alumina-boot Ty variant | Purpose |
|---|---|
| `Ty::Dyn(&[TyP], bool)` | Dynamic dispatch type |
| `Ty::Deref(TyP)` | Deref type operator |
| `Ty::EtCetera(TyP)` | Variadic expansion type |
| `Ty::TupleIndex(TyP, ExprP)` | Compile-time tuple field type |
| `Ty::Tag(&str, TyP)` | Named deferred type |
| `Ty::Defered(Defered)` | Deferred resolution type |
| `Ty::FunctionProtocol` | Callable protocol type |

### 5.7. Integer Literal Representation

**alumina-boot**: `Lit::Int(bool, u128, Option<BuiltinType>)` where the bool is a negation flag. Handles `-1i8` directly as a literal. 128-bit capacity.

**aluminac**: `Expr.int_val: u64`. No negation flag.

With proper const evaluation, this distinction becomes less important. `-1i8` can be handled as `UnaryOp::Neg(IntLit(1, i8))` and const-evaluated. The only real issue is u128 literal values > 2^64, which are used in 104 places (mostly sysroot numeric impls).

### 5.8. Attributes Not Supported by aluminac

| Attribute | alumina-boot | aluminac | Usage |
|---|---|---|---|
| `#[builtin]` | Yes | No | 12 declarations (CRITICAL) |
| `#[packed(N)]` | Yes | No | 11 uses, FFI |
| `#[transparent]` | Yes | No | 3 uses in sysroot |
| `#[cfg_attr(...)]` | Yes | No | Used in sysroot |
| `#[returns_twice]` | Yes | No | 1 use (setjmp) |
| `#[const(always)]` / `#[const(never)]` | Yes | No | Rare |
| `Custom(...)` | Yes | No | Used by `attributed` intrinsic |
| `#[tuple_call]` | Yes | No | 0 uses |
| `#[diagnostic(must_use)]` | Yes | No | 0 uses |

---

## 6. Real-World Usage Audit

Feature usage across `common/`, `sysroot/`, `examples/`, `tools/`, `libraries/`, `tests/`:

### Tier 1: Blocks everything

| Feature | Occurrences | Key Files |
|---|---|---|
| Const eval (enum vals, consts, when) | Ubiquitous | Every enum, every const, every when |
| `#[cfg(not/all/any)]` | 2050+ across 50+ files | sysroot/*, every platform file (IMPLEMENTED) |
| `println!`/`format_args!` | 318+ across 63 files | Nearly every example and tool |
| For-loop desugaring (.iter()) | Every for-in loop | All user code |
| Try operator (macro desugar) | Every `?` use | Result/Option heavy code |
| Closures with captures | Throughout stdlib | Any closure that captures |
| Operator overloading (==, <, etc.) | Everywhere | Any user-defined type comparison (IMPLEMENTED) |
| Slice coercions (`&[T;N]` -> `&[T]`) | Everywhere | Any array-to-slice conversion |

### Tier 2: Needed for full sysroot

| Feature | Occurrences | Key Files |
|---|---|---|
| u128/i128 types | 104 across 15 files | std::builtins, std::time, std::random |
| `dyn` dispatch | 53 across 14 files | std::fmt, std::io, std::typing |
| `const_eval`/`const_bake` | 45 across 7 files | std::mem, std::mod, std::fmt |
| `#[builtin]` macros | 12 declarations | std::macros, std::mod, std::fmt |
| `#[packed]` | 11 across 3 files | Tests, FFI |
| `tuple_invoke` | 6 across 4 files | std::builtins, std::typing |
| `super::` paths | 0 in Alumina code | Not used in the Alumina language |
| `stop_iteration` intrinsic | In iter.alu | Static for with iterators |
| `attributed` intrinsic | 3 uses | Test framework discovery |
| `vtable` / `enum_variants` / `fields` | ~8 uses total | std::typing, reflection |

### Can skip entirely

| Feature | Status |
|---|---|
| Coroutines / yield | Skip (plan to redesign) |
| `@` capture bindings | 0 occurrences |
| `#[tuple_call]` | 0 occurrences |
| `#[const_only]` | 0 occurrences |
| `#[diagnostic]` | 0 occurrences |
| `codegen_const` / `codegen_type_func` | C codegen specific, not needed for LLVM |

---

## Appendix: Source References

### aluminac key locations
- AST types: `libraries/aluminac/lib/ast.alu`
- Parser: `libraries/aluminac/lib/parser.alu`
  - Pass1 (scope building): lines 420-1000
  - Pass2 (AST building): lines 1000-1980
  - ExprParser: lines 1985-3322
  - Macro expansion: lines 3168-3278
- Scope: `libraries/aluminac/lib/scope.alu`
- Monomorphization: `libraries/aluminac/lib/mono.alu`
  - Type resolution: lines 421-508
  - Expression lowering dispatch: lines 830-898
  - For-loop iterator: lines 1429-1603
  - Const eval: lines 1609-1703
  - Try operator: lines 1994-2170
  - Static for: lines 2205-2285
  - Type inference: lines 2978-3117
  - Protocol conformance: lines 1772-1794
  - Lambda lowering: lines 3543-3627
  - Intrinsics: lines 3629-3847
  - Entry point: lines 4219+
  - Enum mono: lines 629-684
- Codegen: `libraries/aluminac/lib/codegen.alu`
  - Type emission: lines 156-316
  - Function declaration: lines 475-550
  - Expression codegen: lines 784-2935
  - Main/test runner: lines 3030-3155
- LLVM bindings: `libraries/aluminac/lib/llvm.alu`

### alumina-boot key locations
- AST definitions: `src/alumina-boot/src/ast/mod.rs` (1048 lines)
- Expression building: `src/alumina-boot/src/ast/expressions.rs` (1835 lines)
  - For-loop desugaring: lines 1038-1205
  - Try operator desugaring: lines 728-734
- Macro expansion: `src/alumina-boot/src/ast/macros.rs` (799 lines)
  - Builtin macros: format_args (~614), bind (~641), reduce (~660), env (~686), cfg (~701), include_bytes (~708), concat (~730), line/column/file (~744-754), stringify (~774)
- Lang items: `src/alumina-boot/src/ast/lang.rs` (272 lines, 97 lang items)
- Scope resolution: `src/alumina-boot/src/src/scope.rs` (596 lines)
- Name resolver: `src/alumina-boot/src/src/resolver.rs` (220 lines)
- Monomorphization: `src/alumina-boot/src/ir/mono/mod.rs` (~6000 lines)
  - Coercion (try_coerce): ~2876
  - Operator overloading (invoke_custom_binary): ~3838
  - Static for: ~4172
- Intrinsics: `src/alumina-boot/src/ir/mono/intrinsics.rs` (1117 lines, 41 intrinsics)
- Type inference: `src/alumina-boot/src/ir/infer.rs` (315 lines)
- Const evaluation: `src/alumina-boot/src/ir/const_eval.rs` (~1800 lines)
- Layout computation: `src/alumina-boot/src/ir/layout.rs` (247 lines)
