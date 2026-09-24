# aluminac Idiomatic-Alumina Backlog

## Executive summary

aluminac is written in a consistent hand-ported-C style. Across ~20 audited source files there are roughly **1,100+ `is_some`/`is_none`/`unwrap` calls**, **~200 manual `for i in 0..len` index loops**, and **zero uses of the `?` try-operator or Option combinators** — even though the sysroot that aluminac itself compiles uses `?`, `.map`, `.and_then`, `.unwrap_or`, `.any`, `.find`, iterators, and `fmt` adapters throughout. So every idiom proposed here is one aluminac can already compile.

The highest-leverage wins are **mechanical and bootstrap-safe**: delete confirmed dead code, swap hand-rolled helpers for stdlib equivalents (`starts_with`/`contains`/slice `==`), convert `!x.is_some()` → `is_none()`, collapse `if is_some { unwrap } else { default }` → `unwrap_or`, and replace index loops with `for-in` / `.enumerate()` / `.any()`.

**Order of attack:** start in leaf/small files (`arena.alu`, `common.alu`, `layout.alu`, `llvm.alu`, `diagnostics.alu`, `ast.alu`), then move to the procedural `mono/` and `codegen/` files, and **quarantine the genuinely bootstrap-sensitive refactors** (`ConstResult` → `Result`, `try_coerce` null-sentinel → `Option`, `lower_switch_as_if_else` multi-pass restructuring) into clearly-flagged late batches, each gated by its own serial `make bootstrap` + `s2==s3` byte-identity run.

Each batch below is independently applyable and verified by a single gate run: `make bootstrap test`, expecting **stage 2 and stage 3 to emit the same IR** and all tests green.

## Per-file spartan-score table

| File | Score | Dominant gap |
|---|---|---|
| `libraries/aluminac-common/common.alu` | 2 | dead `struct Error`, redundant `Result` import |
| `libraries/aluminac-common/arena.alu` | 2 | index copy loop → `copy_to_nonoverlapping`; dead `free`; stale comment |
| `src/aluminac/llvm.alu` | 2 | hand-rolled `triple_starts_with`; dead `initialize_all_targets` |
| `src/aluminac/ast.alu` | 3 | enum cast-to-i32 predicates; redundant rhs/cond arms |
| `src/aluminac/layout.alu` | 4 | index loops over `elems()`; duplicated max-fold |
| `src/aluminac/parser/mod.alu` | 5 | `is_some`/`unwrap` pairs; nested index loops; dead `format_num_small` |
| `src/aluminac/diagnostics.alu` | 6 | bespoke `_StderrFmt`; manual space/caret loops; double-pass |
| `src/aluminac/parser/pass1.alu` | 6 | pervasive `!is_none()`; manual concat loops |
| `src/aluminac/mono/intrinsics.alu` | 6 | `is_some`/`unwrap`; `!is_some()`; manual byte-compare loop |
| `src/aluminac/mono/mod.alu` | 6 | cache `is_some`/`unwrap`; index loops; duplicated lang-attr scan |
| `src/aluminac/scope.alu` | 7 | systematic `?`-avoidance; double-unwrap; index loops |
| `src/aluminac/main.alu` | 7 | `is_err`/`unwrap` pairs; reimplemented `contains`/`starts_with` |
| `src/aluminac/const_eval.alu` | 7 | hand-rolled `ConstResult` (36 `if !r.ok` guards) |
| `src/aluminac/parser/pass2.alu` | 7 | `if is_some {Some(f())} else {None}`; if-elif tag chains |
| `src/aluminac/codegen/mod.alu` | 7 | cache lookups; index loops; flag-accumulator loops |
| `src/aluminac/codegen/fn_codegen.alu` | 7 | `is_some/unwrap` pairs; index loops; `_data` access |
| `src/aluminac/parser/expr.alu` | 8 | 254 lines of `is_none/unwrap`; `.map`-eligible ternaries |
| `src/aluminac/mono/lower.alu` | 8 | 400+ `is_some/is_none/unwrap`; null sentinels; multi-pass scans |

## Ordered batches

### Batch 1 — Dead code & redundant imports/comments in leaf files (risk: low)
Files: `common.alu`, `arena.alu`, `llvm.alu`, `main.alu`, `parser/mod.alu`

Pure deletions; all confirmed zero-call-site by the auditors.
- `common.alu`: delete `struct Error {}`; `use std::result::{Result, try};` → `use std::result::try;`
- `arena.alu`: delete `ArenaNode::free`; fix/remove the contradictory `grow()` comment ("do not increase the increment" sits directly above `self.increment = self.increment * 2;`)
- `llvm.alu`: delete `initialize_all_targets` (no call sites)
- `main.alu`: delete `Compiler::format_num`
- `parser/mod.alu`: delete `format_num_small`

### Batch 2 — Replace hand-rolled string helpers with stdlib (risk: low)
Files: `llvm.alu`, `main.alu`, `parser/mod.alu`, `parser/pass2.alu`, `codegen/mod.alu`, `mono/intrinsics.alu`

```
// llvm.alu triple_starts_with — DELETE, replace call sites:
triple_slice.starts_with("x86_64")          // was: triple_starts_with(triple_slice, "x86_64")
// codegen/mod.alu CodegenCtx::new arch loop:
let is_x86_64 = triple_str.starts_with(prefix);   // was: manual byte loop
// main.alu — DELETE contains_subseq / matches_prefix:
triple.contains("linux")                     triple.starts_with(prefix)
// parser/mod.alu has_cfg inner loop & intrinsics attr-name loop:
if *s == flag { return true; }               // was: nested byte-equality loop
// UFCS everywhere:
attr.str_val().starts_with("builtin_")       // was: std::string::starts_with(attr.str_val(), "builtin_")
```

### Batch 3 — Negation & comparison cleanups (risk: low)
Files: `main.alu`, `const_eval.alu`, `parser/mod.alu`, `pass1.alu`, `expr.alu`, `intrinsics.alu`, `lower.alu`

Token-level, semantically inert:
```
if x.is_none() { ... }                       // was: if !x.is_some() { ... }   (~30 sites)
if self.options.optimize != OptLevel::O0 {   // was: ... as i32 != OptLevel::O0 as i32
self.steps_remaining -= 1;                    // was: = self.steps_remaining - 1;
if self.warning_msg.is_empty() { ... }        // was: .len() == 0
if !child.panic_msg.is_empty() { ... }        // was: .len() > 0
```

### Batch 4 — Collapse Option ternaries to `unwrap_or` / `map().unwrap_or` (risk: low)
Files: `const_eval.alu`, `mono/mod.alu`, `mono/intrinsics.alu`, `codegen/fn_codegen.alu`, `codegen/mod.alu`, `mono/lower.alu`

The most common spartan shape, ~70 sites:
```
// const_eval var_id / load_var:
self.remapped.get(&id._value).unwrap_or(id._value)
self.variables.get(&vid).unwrap_or(ConstValue::make_uninitialized())
// mono/mod get_lang_item:
self.lang_items.get(&hash)                    // just return the Option directly
// mono/mod is_lang_item:
self.get_lang_item(name).map(|lid: usize| -> bool { lid == id }).unwrap_or(false)
// fn_codegen gen_lvalue:
self.locals.get(&expr.id()._value).unwrap_or(LLVMGetUndef(self.ctx.ptr_type))
// lower.alu lower_when:
let cond_val = cond_result.unwrap_or(false);
// generic "if is_some {Some(f(x.unwrap()))} else {None}":
let init = sd.init.map(|e: &Expr| -> &IrExpr { mono.lower_expr(e) });
```

### Batch 5 — Index loops → `for-in` / `.enumerate()` / `.iter().rev()` (risk: low)
Files: `layout.alu`, `scope.alu`, `ast.alu`, `expr.alu`, `pass2.alu`, `mono/mod.alu`, `codegen/mod.alu`, `fn_codegen.alu`, `lower.alu`

```
// layout.alu:
for elem in ty.elems() { let s = compute_type_size(elem, pointer_size); ... }
// ast.alu is_zero_sized:
self.elems().iter().all(|e: &&IrTy| -> bool { e.is_zero_sized() })
// fn_codegen gen_defers (also removes ._data access):
for expr in self.defer_stack.iter_ref().rev() { self.gen_expr(*expr); }
// fn_codegen emit params (index needed for LLVMGetParam):
for (i, param) in self.ir_fn.params.iter().enumerate() { ... LLVMGetParam(self.llvm_fn, i as u32) ... }
```
Keep arena-fill loops that legitimately need the destination index (convert to `.enumerate()` at most).

### Batch 6 — Boolean-accumulator & linear-search loops → `.any()`/`.all()`/`.find()` (risk: medium)
Files: `diagnostics.alu`, `main.alu`, `const_eval.alu`, `expr.alu`, `pass1.alu`, `pass2.alu`, `codegen/mod.alu`, `fn_codegen.alu`, `lower.alu`

```
// main.alu --test branch:
if !options.cfg_flags.iter().any(|f: &&[u8]| -> bool { *f == "test" }) { options.cfg_flags.push("test"); }
// fn_codegen gen_switch:
let has_user_default = arms.iter().any(|arm: &IrSwitchArm| -> bool { arm.is_default });
let all_same = (1usize..phi_count as usize).all(|i: usize| -> bool { LLVMTypeOf(phi_vals[i]) == arm_ty });
// const_eval eval_global_ref:
let func = self.ir_functions.iter_ref().find(|f: &&IrFunction| -> bool { f.mangled_name == target_name });
// expr/pass2 macro params:
let param_idx = self.ctx.macro_param_names.iter().find_index(|n: &[u8]| -> bool { n == name });
```
**Caution:** several auditor notes warn the original loops lack `break` and overwrite with the LAST match (`lower_bound_value`, struct-lit field reorder in lower.alu). `.find()` selects the FIRST match — verify equivalence or keep the explicit loop at those sites.

### Batch 7 — `?` try-operator in functions that already return Option (risk: medium, partly bootstrap-path)
Files: `scope.alu`, `const_eval.alu`, `expr.alu`, `mono/lower.alu`

Add `use option::try;` at the relevant scope (mirroring sysroot), then:
```
// scope.alu resolve_raw tail call:
return self.resolve_raw(scope.parent?, name);
// const_eval materialize_to_ir:
items[i] = materialize_to_ir(arena, val.elems()[i], elem_ty, void_ty)?;
// lower.alu try_protocol_redirect / resolve_method_call_on_type:
let item = self.ctx.scopes.get(scope_idx).items.get(&method_name)?;
let def  = self.ctx.fn_defs.get(&fn_id._value)?;
```
Apply `scope.alu` + `const_eval` + `expr.alu` as a sub-commit and gate; then apply `lower.alu`'s ~47 sites separately and re-gate so any fixed-point break bisects cleanly.

### Batch 8 — `and_then`/`map` chains for nested Option lookups + double-unwrap elimination (risk: medium)
Files: `scope.alu`, `parser/mod.alu`, `pass1.alu`, `expr.alu`, `mono/intrinsics.alu`, `mono/lower.alu`

```
// lower.alu — the 6x copy-pasted two-level nest:
lang_id.and_then(|id: usize| -> Option<&StructDef> { self.ctx.struct_defs.get(&id) })
       .map(|sd: &StructDef| -> () { scope_idx = sd.scope_idx; });
// pass1 collect_generic_param_ids — store once, no double unwrap:
let item = resolved.unwrap(); if item.kind.tag == ... { ids.push(item.kind.id()); }
// intrinsics lower_enum_variants/lower_fields/lower_attributed:
let def_opt = m.ctx.get_lang_item("...").and_then(|id: u32| -> Option<&FnDef> { m.ctx.fn_defs.get(&id) });
```

### Batch 9 — Manual for/while → for-in/range, `.zip()`, and `copy_to_nonoverlapping` slice copies (risk: medium)
Files: `arena.alu`, `common.alu`, `diagnostics.alu`, `main.alu`, `scope.alu`, `parser/mod.alu`, `pass1.alu`, `mono/intrinsics.alu`, `mono/lower.alu`

```
// arena.alu alloc_slice_copy & common.alu reference:
src.copy_to_nonoverlapping(&dst[0]);          // was: for i in 0..len { dst[i] = src[i]; }
// pass1 use-path concat (x3):
prefix.copy_to_nonoverlapping(&combined[0]); own_segments.copy_to_nonoverlapping(&combined[prefix.len()]);
// lower.alu lower_static_for:
let result_items = self.ctx.arena.alloc_slice_copy::<&IrExpr>(stmts.as_slice());
// parser/mod share_macros parallel vectors:
for (id, entry) in all_ids.iter().zip(&all_entries.iter()) { if ctx.macro_defs.get(id).is_none() { ctx.macro_defs.insert(*id, *entry); } }
// main resolve_or_create_module_scope:
for s in std::string::split(module_path, "::") { if s.len() > 0 { current = self.ensure_module_scope(current, s); } }
// main parse_args '=' search:
switch arg.find_char('=') { Option::some(pos) => ..., Option::none() => ..., }
```
For each `copy_to_nonoverlapping` swap confirm `dst.len() >= src.len()` and non-overlap (arena allocations are always fresh).

### Batch 10 — fmt-adapter cleanups in `diagnostics.alu` (risk: medium, non-IR)
File: `diagnostics.alu`

Diagnostics affect only stderr rendering, never emitted IR, so this cannot break s2==s3 — but it CAN change diagnostic output, so it gets its own gate to eyeball formatting.
```
// Replace bespoke _StderrFmt with the existing StreamFormatter:
let stderr = io::StdioStream::stderr(); let f = fmt::StreamFormatter::new(&stderr);
// write_spaces / caret loops:
let _ = write!(f, "{}", ' '.char().repeat(n as usize));
let _ = write!(f, "{}", '^'.char().repeat(caret_len));
// render_snippet bool:
if diag.level != DiagLevel::Note { ... }
// compute_line_starts single pass:
let count = 1 + contents.iter().filter(|b: u8| -> bool { b == '\n' }).count();
for (i, byte) in contents.iter().enumerate() { if byte == '\n' { starts[idx] = (i + 1) as u32; idx += 1; } }
```

### Batch 11 — Structural de-duplication: switch consolidation, multi-value arms, extracted helpers (risk: medium)
Files: `layout.alu`, `main.alu`, `scope.alu`, `pass1.alu`, `pass2.alu`, `codegen/mod.alu`, `mono/mod.alu`

- `pass2.parse_type` / `collect_type_path_inner`: if-elif tag chains → `switch`; merge identical arms via multi-value arms (the file already does this at line 757)
- `codegen/mod.alu` `llvm_type_inner` / `create_di_type_inner`: if-elif → `switch`
- Extract helpers: `layout` max-fold / packed-struct-size; `main` `arena_copy(arena, s)` (x3 sites); `mono/mod` `register_lang_attrs` (x5 copies); `pass1` `collect_generic_params` tuple-return; `scope` `can_enter` predicate (x2)
- `mono/mod` `local_fn_ids: HashMap<usize, bool>` → `HashSet<usize>`

Verify each merged arm-set is exhaustive-equivalent to the original (especially the pass2 `TypeIdentifier`/`Identifier` superset merge, flagged medium by the auditor).

### Batch 12 — BOOTSTRAP-SENSITIVE: `ConstResult` → `Result<ConstValue, ConstEvalError>` + `?` (risk: high)
File: `const_eval.alu`

The single largest readability win in the file. Replace the hand-rolled `struct ConstResult { ok, value, error }` with stdlib `Result`, add `use result::try;`, and collapse all 36 `if !r.ok { return r; }` guards to `?`, `ConstResult::success(v)` → `Result::ok(v)`, `ConstResult::fail(e)` → `Result::err(e)`. Flagged **bootstrap_sensitive**: it changes a pervasive type that flows through every `eval_*` method; any short-circuit/ordering difference could alter constant-folding output and thus emitted IR. Own batch, own gate, full const-eval test pass.

### Batch 13 — BOOTSTRAP-SENSITIVE: `lower.alu` null-sentinel → `Option<&IrExpr>` and switch-pass restructuring (risk: high)
File: `mono/lower.alu`

Two auditor-flagged bootstrap_sensitive clusters in the central lowering engine, applied as **two separate gated commits**:
1. `try_coerce` / `build_dyn_vtable_ref` use `0usize as &IrExpr` null sentinels with `as &void as usize != 0` checks (~8 sites) → change return type to `Option<&IrExpr>`, use `?` / `.unwrap_or(val)`.
2. `lower_switch_as_if_else` makes 3–4 separate linear passes (O(N²) reverse fill) over `arms` → single `.enumerate()` pass collecting non-default indices into a `Vector<usize>`, then iterate `.rev()`.

Both change control-flow/temporary structure on the IR-emission path — highest risk of breaking s2==s3. Apply one, gate, then the other, gate; any `s2 != s3` means the lowering reordered IR — revert the offending sub-commit.

## Deliberately dropped / not worth doing

- **`diagnostics.alu` `CodeDiagnostic::fmt` arms and `emit_all` `let _ =` discards** — auditor explicitly notes these are *already idiomatic* (single write per arm needs no `?`; discarding fmt::Result to stderr is the accepted sysroot pattern, cf. `panicking.alu:282`). No change.
- **`parser/expr.alu` multi-Option guards** (`if left.is_none() || right.is_none() || op_node.is_none() { return void; }`) — the enclosing fns return `&Expr`, not Option, so `?` is off the table; the guard-then-unwrap form is the correct idiom. Auditor rates restructuring as medium-risk for negligible gain (short-circuit semantics). Leave as-is.
- **`parser/mod.alu` `ParseContext::new` field init** (`name: name`) — Alumina has no field shorthand; this is correct, not an anti-pattern.
- **`scope.alu` `module_path_for_scope` / `scope_name` Option-walk loops** — for non-Option-returning fns the `while is_some()/unwrap` walk is the honest idiomatic form (no `while let` in Alumina); auditor rates the gain "minor". Only the length-fold/reverse-join sub-parts are worth touching (folded into Batch 9).
- **`mono/mod.alu` `make_*_ty` cache early-returns** and **`codegen` cache `is_some {return unwrap}`** — these fns return concrete `&IrTy`/LLVM pointers, not Option, so the two-line early return is the appropriate Alumina form; auditor says "no change needed, flag for awareness only." They disappear only if the helpers are refactored to return `Option`, which is not worth the churn.
- **`ast.alu` `make_*` vs `mk_*` naming unification (12 sites)** and **`lower.alu` `lower_defered_call` → `lower_deferred_call` rename** — pure cosmetic naming preference, zero semantic impact, touches many call sites; low priority, do opportunistically if ever editing those functions anyway.
- **`pass2.alu` `process_*` helper extraction (6 fns)** — auditor flags closure-capture friction (`|=self|` would consume `Pass2`) making a clean shared helper awkward; medium risk for modest gain. Optional within Batch 11; skip if it fights the type system.
- **`lower.alu` `ir_type_name` manual string concatenation → `format!`** — there is no arena-backed `format!` wired up (the project uses a bespoke `format_usize`); the manual `copy_to_nonoverlapping` is currently the only arena-safe approach. Medium-risk, bootstrap_sensitive, and blocked on building an `arena_format!` helper first. Defer until that helper exists.
---
## Execution log (live)

- **Batch 1 ✅** dead code removed (5 files). Gate green.
- **Batch 2 ✅** hand-rolled string helpers → stdlib `starts_with`/`contains`/`==` (+ `use std::string` imports for UFCS). Gate green.
- **Batch 3 ✅** `!is_some()`→`is_none()`, enum `==`, `+=`, `.is_empty()` (7 files, ~150 sites). Gate green.
- **Batch 4a ✅** `unwrap_or` / direct-Option-return / double-lookup, no closures (~9 sites). Gate green.
- **Batch 4b ✅** `.map`/`unwrap_or_else` with explicit captures `|=self,..|` / `|&x,..|` (~7 sites). Gate green.
- **Batch 5 ✅ (partial)** index loops → `.iter()`/`.enumerate()`/`.iter_ref()`/`.rev()` (~80 sites across 8 files).
  - ⚠️ **mono/mod.alu Batch-5 DROPPED**: its `monomorphize`/`process_*` loops are worklist loops that append to
    the collection being iterated. `.iter()`/`.iter_ref()` snapshot the backing pointer → dangling ptr → **segfault**
    while self-compiling (s1 built, crashed building s2). Those loops must stay index-based. mono/mod keeps only its
    Batch-4 edits. Lesson recorded; applies to all future iterator conversions.

**Verified Alumina facts discovered during execution** (fold into future batches):
- UFCS on stdlib free fns (`slice.starts_with`) needs `use std::string::{...}`.
- Closures are non-capturing nested fns; capture explicitly `|=x,..|`(by value)/`|&x,..|`(by ref). `unwrap_or` is eager.
- `.iter()`/`.iter_ref()` snapshot the backing pointer — never convert loops over collections that grow during iteration.

### Continued execution log

- **Batch 6 ✅** search/accumulator loops → `.any`/`.all`/`.find`/`.find_index` (20 sites). First-match equivalence verified.
- **Batch 7 ✅** `?` try-operator on Option-returning fns (15 sites) — aluminac's first use of `?`.
- **Batch 8a ✅** repeated-`.unwrap()` CSE (28 sites). **8b ✅** `and_then`/`map` chains de-duplicating the 14 lang-item→struct_def lookups in lower.alu.
- **Batch 9 ✅ (minimal)** `arena.alloc_slice_copy` at 3 call sites. Direct `copy_to_nonoverlapping(&dst[OFF])` conversions dropped (empty-slice panic risk; see memory).
- **Batch 10 ✅** `compute_line_starts` via iterators. (fmt-adapter / StreamFormatter swap skipped: output-correctness risk, weak test coverage.)
- **Batch 11 ✅ (partial)** `local_fn_ids` HashMap<usize,bool> → HashSet<usize>. Remaining 11 items: `register_lang_attrs`×5 was the lang-item lookup duplication, already handled by Batch 8b; if-elif→`switch` consolidation deferred (medium-risk arm-exhaustiveness verification for marginal gain).
- **Batch 12 ✅** `ConstResult` → stdlib `Result<ConstValue, ConstEvalError>` (190 sites). Needed `fn fmt` on ConstEvalError+ConstValue (Result::unwrap's panic path needs Formattable payloads, else the broken generic DebugAdapter). No `?` introduced (error channel carries break/continue/return signals).

### Deferred (with reasons)
- **Batch 13 (both sub-parts)** — DEFERRED. (1) The null-sentinel cleanup is mostly AST-accessor-level (`expr.lhs()`/`expr.ty()` return nullable pointers) — Option-ifying needs an AST-layer rewrite, far out of scope; only the narrow build_dyn_vtable_ref return is IR-level. (2) `lower_switch_as_if_else` is already reasonably idiomatic after batches 1–12; the O(N²)→O(N) reverse-build restructure is high-risk on the IR-emission path (reordering → s2≠s3) for marginal perf gain. Both are the backlog's explicitly highest-risk items; not worth the bootstrap risk.
- **Batch 10 fmt-adapter swap, Batch 11 if-elif→switch** — deferred (see above).

### Discovered Alumina/aluminac pitfalls (saved to agent memory)
1. UFCS on stdlib free fns (`slice.starts_with`) needs a `use std::string::{...}` import.
2. Closures are non-capturing; capture explicitly `|=x,..|`/`|&x,..|`. `unwrap_or` is eager.
3. `.iter()`/`.iter_ref()` snapshot the backing pointer → segfault if the collection grows during iteration (worklist loops must stay index-based). Caught only at the bootstrap gate (s1 crashes building s2).
4. `copy_to_nonoverlapping(&dst[0])` panics on empty slices (`&dst[OFF]` is bounds-checked).
5. stdlib `Result`/`Option` `unwrap` formats its payload on the panic path; non-Formattable structs hit the broken generic DebugAdapter — add a minimal `fn fmt`.
