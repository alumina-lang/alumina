# aluminac Code Improvements

Catalog of places where the aluminac codebase is unnecessarily spartan, not making
use of language features we already support, or could benefit from refactoring.

---

## 1. ~~Constants-as-enums~~ DONE

**Fixed:** Converted all ~190 tag constants to proper enum types:
- `ast.alu`: `TyTag`, `ExprTag`, `AttrTag`, `ItemTag`, `IrTyTag`, `IrTag`,
  `CallKind`, `BoundType`, `CValTag`, `CLVTag`
- `scope.alu`: `NamedItemTag`
- `const_eval.alu`: `CECode`

All struct tag fields changed from `i32` to the appropriate enum type.
~700 constant references updated across all files.

---

## 2. ~~if-else chains that should be `switch`~~ DONE

**Fixed:** Converted key dispatchers to `switch` statements:
- `mono.alu:resolve_type` — 12-branch type resolution (TyTag switch)
- `mono.alu:lower_expr` — 20+ branch expression dispatch (ExprTag switch)
- `parser.alu` — Attribute name dispatch (13-arm string switch)
- `parser.alu` — `parse_binop` and `parse_assign_op` (19+10 arm string switches)
- `codegen.alu:gen_expr` — 40-branch expression codegen (IrTag switch, ~550 lines)
- `codegen.alu:gen_lvalue` — 7-branch lvalue codegen (IrTag switch)
- `codegen.alu:gen_const_init` — 8-branch constant initializer (IrTag switch)
- `const_eval.alu:eval_inner` — 30+ branch const evaluator dispatch (IrTag switch)
- `const_eval.alu:irty_to_builtin` — 4-branch type mapping (IrTyTag switch)
- `layout.alu:compute_type_size` — 7-branch type size computation (IrTyTag switch)
- `layout.alu:compute_type_align` — 7-branch type alignment computation (IrTyTag switch)
- `parser.alu:expand_builtin_macro` — 13-branch builtin macro dispatch (string switch)

---

## 3. ~~Manual while-loops instead of `for i in 0..n`~~ DONE

**Fixed:** Converted 10 eligible while-loops to `for i in 0usize..n` syntax
across mono.alu (9 loops) and diagnostics.alu (1 loop). Also converted the
`equals` loop in sysroot-simple/std/mem.alu.

Remaining while-loops are NOT convertible: parser character-scanning loops
(non-uniform increments), arg parsing (consumes extra args), binary search,
reverse iteration, and i32-typed loops.

---

## 4. ~~`std::mem::zeroed` boilerplate~~ DONE

**Fixed:** Added `Ty::default()` and `IrTy::default()` that return zeroed
instances with empty slices/refs pre-filled. Simplified all 13 `Ty` constructors
and 11 `IrTy` constructors to one-liners. Also updated 3 ad-hoc Ty constructions
in parser.alu to use `Ty::default()`.

---

## 5. ~~IR node construction helpers~~ DONE

**Fixed:** Added 16 `mk_*` helper methods to `Mono` (mk_int_lit, mk_bool_lit,
mk_local, mk_field, mk_let, mk_let_uninit, mk_block, mk_block_void, mk_ref,
mk_deref, mk_assign, mk_binary, mk_cast, mk_call, mk_if, mk_index) and
applied them across mono.alu. Net reduction: ~670 lines.

---

## 6. ~~Magic numbers~~ MOSTLY DONE

**Fixed:**
- Added `SLICE_DATA_FIELD` / `SLICE_LEN_FIELD` constants in ast.alu, replaced
  ~17 occurrences across mono.alu and codegen.alu.
- Added `NO_VARIADIC` constant in parser.alu, replaced 6 sentinel assignments
  and 3 comparisons.
- Replaced `36u8` with `'$' as u8` (3 occurrences in parser.alu).

**Remaining:** Option field indices (`_is_some`/`_inner`) are already looked
up by name at runtime, so named constants aren't needed.

---

## 7. ~~Repeated Vector-to-arena-slice copy pattern~~ DONE

**Fixed:** Added `Arena::alloc_slice_copy<T>(src: &[T]) -> &mut [T]` helper
and applied it to ~30 pure-copy occurrences across parser.alu, mono.alu.
Remaining alloc+loop patterns do transformations during copy (resolve_type,
lower_expr, expand_macro_expr) and cannot use the helper.

---

## 8. `.is_some()` + `.unwrap()` chains (~60 occurrences)

Alumina doesn't have `if let`, but the pattern is still verbose:
```alumina
let result = map.get(&key);
if result.is_some() {
    let val = result.unwrap();
    // use val
}
```

No clean fix without language changes, but in many cases the value is
used exactly once and the unwrap could be inlined. Some cases are also
`is_none()` guard + `unwrap()` further down which is fragile.

---

## 9. ~~Duplicate code in for-loop lowering~~ DONE

**Fixed:** Extracted `build_for_indexed_loop` helper that contains the common
loop body (bindings, body lowering, increment, while construction). Both
`lower_for_slice` and `lower_for_array` now only handle collection-specific
setup (storing the collection, computing condition, element access) and
delegate to the shared helper. Net reduction: ~20 lines.

---

## 10. ~~BUG: aluminac switch on non-integer types~~ DONE

**Fixed:** Non-integer switch now desugars to if-else chains with `==`
comparisons at the IR level (in `mono.alu:lower_switch_as_if_else`).
Integer/enum switches still use LLVM `switch` instruction.

Also added `Equatable` protocol, `operator_eq` lang item, and slice
`equals` to sysroot-simple to enable string switch support.

---

## 11. Verbose char-to-byte comparisons

~20 occurrences of `c == '"' as u8` style comparisons. Minor, but could
define byte constants at the top of the file:
```alumina
const BYTE_QUOTE: u8 = '"' as u8;
const BYTE_DOLLAR: u8 = '$' as u8;
const BYTE_BACKSLASH: u8 = '\\' as u8;
```

---

## 12. ~~Unnecessary `as i32` casts for enum comparisons~~ DONE

**Fixed:** Removed ~60 occurrences of `x as i32 == Y::Variant as i32`
across all aluminac source files. Enums now support `==` directly via
the Equatable protocol. Also converted const_eval.alu binary op
dispatchers (int_bin_op, float_bin_op, bool_bin_op) to switch.

---

## 13. ~~Void main wrapper codegen bug~~ DONE

**Fixed:** When user's main returns void, `emit_main_wrapper` was
naming the void call result `"ret"`, which LLVM rejects. Now uses
an empty name for void returns.

---

## Priority Order

1. ~~**#10 (bug fix)** — Fix switch codegen for non-integer types~~ DONE
2. ~~**#5 (IR helpers)** — Biggest readability/LOC win, no risk~~ DONE
3. ~~**#1 + #2 (enums + switch)** — Large refactor but huge type safety win~~ DONE
4. ~~**#4 (default constructors)** — Reduce zeroed boilerplate~~ DONE
5. ~~**#3 (for loops)** — Mechanical cleanup~~ DONE
6. ~~**#6 (magic numbers)** — Quick wins~~ DONE
7. ~~**#7 (arena helper)** — Small utility addition~~ DONE
8. ~~**#9 (for-loop dedup)** — Moderate refactor~~ DONE
9. **#8, #11** — Minor quality-of-life
10. ~~**#12 (enum casts)** — Remove `as i32` casts~~ DONE
11. ~~**#13 (void main)** — Bug fix~~ DONE
