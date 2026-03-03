# aluminac Code Improvements

Catalog of places where the aluminac codebase is unnecessarily spartan, not making
use of language features we already support, or could benefit from refactoring.

---

## 1. Constants-as-enums (HIGH PRIORITY)

The entire codebase uses `const FOO: i32 = 0i32; const BAR: i32 = 1i32;` chains
for discriminated unions instead of proper `enum` types. This loses type safety
(any i32 can be used where a tag is expected) and makes `switch` less useful.

**~190 constants across 3 files that should be enums:**

| File | Constants | Suggested Enum |
|------|-----------|----------------|
| `ast.alu:127-139` | 13 `TY_*` constants | `enum TyTag` |
| `ast.alu:292-339` | 28 `EXPR_*` constants | `enum ExprTag` |
| `ast.alu:450-464` | 15 `ATTR_*` constants | `enum AttrTag` |
| `ast.alu:582-592` | 10 `ITEM_*` constants | `enum ItemTag` |
| `ast.alu:612-622` | 11 `IRTY_*` constants | `enum IrTyTag` |
| `ast.alu:778-818` | 20 `IR_*` constants | `enum IrTag` |
| `ast.alu:820-821` | 2 `CALL_*` constants | `enum CallKind` |
| `ast.alu:406-407` | 2 `BOUND_*` constants | `enum BoundType` |
| `ast.alu:950-961` | 12 `CVAL_*` constants | `enum CValTag` |
| `ast.alu:964-969` | 6 `CLV_*` constants | `enum CLVTag` |
| `scope.alu:9-25` | 16 `NIK_*` constants | `enum NamedItemTag` |
| `const_eval.alu:17-29` | 13 `CE_*` constants | `enum ConstEvalError` |

Converting these would enable proper `switch` exhaustiveness and catch
tag-mismatch bugs at compile time. This is a large but mechanical refactor.

---

## 2. if-else chains that should be `switch` (HIGH PRIORITY)

Many dispatchers use long if-else-if chains on integer tags. Once the tags are
enums (see #1), these become natural `switch` statements.

**Key locations:**

- **`mono.alu:426-519`** — Type resolution (~90 lines, 12 branches on `ty.tag`)
- **`mono.alu:877-945`** — Expression lowering dispatch (~70 lines, 20+ branches on `expr.tag`)
- **`mono.alu:173-221`** — Item processing (~50 lines, 6 branches on `ITEM_*`)
- **`codegen.alu` expression dispatch** — Similar pattern for IR codegen
- **`const_eval.alu` expression eval** — Similar pattern for const eval
- **`parser.alu:387-438`** — Attribute name dispatch (13 string comparisons)
- **`parser.alu:4452-4486`** — Binary/assign operator parsing (19+10 string comparisons)
- **`parser.alu:3665-3808`** — Builtin macro dispatch (12 string comparisons)

Note: String `switch` now works in aluminac (#10 fixed). These if-else chains
can be converted to `switch` statements for better readability.

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

## 9. Duplicate code in for-loop lowering

`lower_for_slice` and `lower_for_array` share ~80% of their code (the index
variable setup, the while loop structure, the increment). They differ only in
how the collection is stored and how length is obtained. Could be unified into
a single method that takes a "get element at index" callback or similar.

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

## Priority Order

1. ~~**#10 (bug fix)** — Fix switch codegen for non-integer types~~ DONE
2. ~~**#5 (IR helpers)** — Biggest readability/LOC win, no risk~~ DONE
3. **#1 + #2 (enums + switch)** — Large refactor but huge type safety win
4. ~~**#4 (default constructors)** — Reduce zeroed boilerplate~~ DONE
5. ~~**#3 (for loops)** — Mechanical cleanup~~ DONE
6. ~~**#6 (magic numbers)** — Quick wins~~ DONE
7. ~~**#7 (arena helper)** — Small utility addition~~ DONE
8. **#9 (for-loop dedup)** — Moderate refactor
9. **#8, #11** — Minor quality-of-life
