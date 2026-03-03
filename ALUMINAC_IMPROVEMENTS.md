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

Note: String `switch` works in alumina-boot (desugars to `==` chains) but
**aluminac has a codegen bug** — it emits LLVM `switch` instruction which only
works on integers. Needs fix before string switches can be used. See #10.

---

## 3. Manual while-loops instead of `for i in 0..n` (~24 occurrences)

Many places use manual index loops when `for` ranges are available:

```alumina
// Current (scattered across mono.alu, codegen.alu, diagnostics.alu):
let i = 0usize;
while i < n {
    // body
    i = i + 1;
}

// Should be:
for i in 0usize..n {
    // body
}
```

**Key locations in mono.alu:** lines 1052, 1868, 2449, 2617, 2747, 3820, 3829, 4030, 4075
**diagnostics.alu:** lines 130, 140

Some are genuine (loop variable modified inside body, or counting down), but
most are straightforward forward iterations.

---

## 4. `std::mem::zeroed` boilerplate (113 occurrences)

The flat struct representation forces every constructor to zero out unused fields:

```alumina
fn placeholder(id: Id) -> Ty {
    Ty { tag: TY_PLACEHOLDER, builtin: BuiltinType::Void, id: id,
         inner: std::mem::zeroed::<&Ty>(), is_const: false, array_size: 0,
         elems: &[], ret_ty: std::mem::zeroed::<&Ty>(),
         typeof_expr: std::mem::zeroed::<&Expr>() }
}
```

**Options:**
- Add a `Ty::default()` / `IrTy::default()` / `IrExpr::default()` that returns
  a fully-zeroed instance, then callers just set the fields they care about.
  `IrExpr::void_expr()` already does this for IR exprs — extend the pattern to
  `Ty` and `IrTy`.
- Alternatively, use `std::mem::zeroed::<Ty>()` as base and set fields.

The `IrExpr::void_expr(ty)` pattern already exists and is used ~274 times in
mono.alu — it's the right approach but `Ty` and `IrTy` don't have equivalents.

---

## 5. IR node construction helpers (MEDIUM PRIORITY)

mono.alu repeats the same 4-line patterns hundreds of times for constructing
IR nodes. Common patterns that should be helpers:

```alumina
// Pattern 1: Integer literal (~15 occurrences)
let lit = IrExpr::void_expr(ty);
lit.tag = IR_INT_LIT;
lit.int_val = value;
self.ctx.arena.alloc(lit) as &IrExpr

// Pattern 2: Local variable read (~40 occurrences)
let local = IrExpr::void_expr(ty);
local.tag = IR_LOCAL;
local.id = var_id;
self.ctx.arena.alloc(local) as &IrExpr

// Pattern 3: Field access (~15 occurrences)
let access = IrExpr::void_expr(field_ty);
access.tag = IR_FIELD_ACCESS;
access.lhs = obj;
access.field_idx = idx;
self.ctx.arena.alloc(access) as &IrExpr

// Pattern 4: Let binding (~20 occurrences)
let let_stmt = IrExpr::void_expr(self.ctx.void_ty);
let_stmt.tag = IR_LET;
let_stmt.id = var_id;
let_stmt.ir_ty = ty;
let_stmt.opt_expr = Option::some(init);
self.ctx.arena.alloc(let_stmt) as &IrExpr

// Pattern 5: Direct call target (~10 occurrences)
IrCallTarget { tag: CALL_DIRECT, fn_ref: fn_ref, callee: std::mem::zeroed::<&IrExpr>() }

// Pattern 6: Block (~15 occurrences)
let block = IrExpr::void_expr(self.ctx.void_ty);
block.tag = IR_BLOCK;
block.items = stmts;
self.ctx.arena.alloc(block) as &IrExpr

// Pattern 7: Ref (take address) (~10 occurrences)
let ref_expr = IrExpr::void_expr(self.ctx.make_ptr_ty(ty, false));
ref_expr.tag = IR_REF;
ref_expr.lhs = inner;
self.ctx.arena.alloc(ref_expr) as &IrExpr
```

Suggested helpers on `Mono`:
```alumina
fn mk_int_lit(&mut self, ty: &IrTy, val: u64) -> &IrExpr
fn mk_bool_lit(&mut self, val: bool) -> &IrExpr
fn mk_local(&mut self, id: Id, ty: &IrTy) -> &IrExpr
fn mk_field_access(&mut self, obj: &IrExpr, idx: u32, ty: &IrTy) -> &IrExpr
fn mk_let(&mut self, id: Id, ty: &IrTy, init: &IrExpr) -> &IrExpr
fn mk_block(&mut self, stmts: &[&IrExpr]) -> &IrExpr
fn mk_ref(&mut self, inner: &IrExpr, is_const: bool) -> &IrExpr
fn mk_assign(&mut self, lhs: &IrExpr, rhs: &IrExpr) -> &IrExpr
fn mk_binary(&mut self, op: BinOp, lhs: &IrExpr, rhs: &IrExpr, ty: &IrTy) -> &IrExpr
fn mk_direct_call_target(fn_ref: IrFnRef) -> IrCallTarget
```

This would cut mono.alu by ~500-800 lines.

---

## 6. Magic numbers

### Slice field indices
Used in ~10 places across mono.alu and codegen.alu:
```alumina
data_ptr.field_idx = 0u32;  // slice data pointer
len_access.field_idx = 1u32;  // slice length
```
Should be:
```alumina
const SLICE_DATA_FIELD: u32 = 0u32;
const SLICE_LEN_FIELD: u32 = 1u32;
```

### Option field indices
Used in iterator for-loop lowering:
```alumina
field0.field_idx = 0u32; // _is_some
unwrap_expr.field_idx = 1u32; // _inner
```
Should be:
```alumina
const OPTION_IS_SOME_FIELD: u32 = 0u32;
const OPTION_INNER_FIELD: u32 = 1u32;
```

### Sentinel values
```alumina
variadic_param_idx: i32,  // -1 if no variadic param
```
Should use a named constant: `const NO_VARIADIC: i32 = -1i32;`

### Raw byte literals
```alumina
name_text[0] == 36u8  // should be '$' as u8
```
Three occurrences in parser.alu (lines 1203, 1734, 2333).

---

## 7. Repeated Vector-to-arena-slice copy pattern

This 3-line pattern appears ~15 times:
```alumina
let result = self.ctx.arena.alloc_slice::<&Expr>(vec.len());
for i in 0usize..vec.len() {
    result[i] = vec[i];
}
```

Should add `Arena::alloc_slice_from<T>(src: &[T]) -> &mut [T]` or similar helper.

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

## 10. BUG: aluminac switch on non-integer types

aluminac's codegen emits LLVM `switch` instruction for all switch statements,
but LLVM switch only works on integer types. For struct/slice types (like
strings), it should fall back to if-else chains with `==` comparisons, which
is what alumina-boot does.

This blocks using `switch` on strings, which would clean up many if-else
chains in the parser (attribute dispatch, operator parsing, builtin macros).

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

1. **#10 (bug fix)** — Fix switch codegen for non-integer types
2. **#5 (IR helpers)** — Biggest readability/LOC win, no risk
3. **#1 + #2 (enums + switch)** — Large refactor but huge type safety win
4. **#4 (default constructors)** — Reduce zeroed boilerplate
5. **#3 (for loops)** — Mechanical cleanup
6. **#6 (magic numbers)** — Quick wins
7. **#7 (arena helper)** — Small utility addition
8. **#9 (for-loop dedup)** — Moderate refactor
9. **#8, #11** — Minor quality-of-life
