# Porting status

Live source of truth for the aluminac → alumina-boot parity work. See `PORTING.md` for the rules and workflow.

**Statuses:**

- `[DONE]` — implemented and verified by a test, plus `make bootstrap` passes.
- `[PARTIAL]` — work started, gaps remain. **Must include a `Missing:` block.**
- `[TODO]` — identified, not started.

**At session start:** prefer closing `[PARTIAL]` entries over picking up new `[TODO]` ones. Don't mark anything `[DONE]` without a test exercising it.

---

## [TODO] Initial audit

The first porting session must populate the categories below.

Audit covers:

- **Language features.** Compare `src/alumina-boot/src/` against `src/aluminac/`. Catalog parser/AST/type-system features that alumina-boot supports and aluminac doesn't (closures, full generic protocols, dyn, macros, mixins, etc. — see `docs/lang_guide.md` for the surface).
- **Const evaluation.** What const operations alumina-boot evaluates that aluminac doesn't.
- **Codegen.** Compare codegen surface — intrinsics, ABI edge cases, attributes (`#[align]`, `#[link_name]`, `#[thread_local]`, ...), debug info, panic/backtrace integration.
- **Lang items.** Compiler-known items in `sysroot/std/builtins.alu` and elsewhere.
- **Stdlib modules.** Files in `sysroot/std/` not yet in `sysroot-aluminac/`, plus files in both that need to converge.
- **Existing specialization gates.** `grep -rn 'cfg(boot)' sysroot/` and `grep -rn 'cfg(coroutines)' sysroot/` — these mark the natural specialization points.
- **Test infrastructure.** What it takes to run `make test-lang` / `make test-std` / `make test-libraries` through aluminac. `tests/diag/` is out of scope (alumina-boot only) — see `PORTING.md`.

Produce 30–60 concrete entries across the categories below. Each entry must be specific enough that "done" is unambiguous (e.g. *"Port `sysroot/std/string.alu` to compile under aluminac and pass `tests/std/string.alu`"*, not *"port stdlib"*).

When the audit is done, replace this section with a `[DONE]` marker like:

```
## [DONE] Initial audit
Completed YYYY-MM-DD. Categories below populated; see git log for the audit commit.
```

The audit may itself span more than one session — if so, keep it as `[PARTIAL]` with a `Missing:` listing of which categories still need to be enumerated.

---

## Language features

*(Parser/AST/type system features in alumina-boot but not aluminac.)*

## Const evaluation

## Codegen

*(LLVM IR coverage: intrinsics, ABI, attributes, debug info, panic/backtrace.)*

## Lang items

## Stdlib modules

*(Goal: unify each `sysroot-aluminac/` file with its `sysroot/` counterpart into a single file under `sysroot/`. Track per-file.)*

## Test infrastructure

*(Running the alumina-boot test suites through aluminac. `tests/diag/` is **not** in scope — keep it passing under alumina-boot only.)*

## Sysroot deletion (final)

- [TODO] Delete `sysroot-aluminac/` once the unified `sysroot/` compiles under both compilers, the aluminac → aluminac → aluminac bootstrap converges on `sysroot/`, and `make test-lang` / `make test-std` / `make test-libraries` pass under both compilers. Gated on the rest.
