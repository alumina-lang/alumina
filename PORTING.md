# Aluminac → alumina-boot parity

## Goal

Bring aluminac to behavioral parity with alumina-boot so that:

1. aluminac accepts the unified `sysroot/` directly, with minimal `#[cfg(boot)]` gating.
2. `sysroot-aluminac/` is deleted from the repo.
3. The aluminac → aluminac → aluminac bootstrap converges on `sysroot/` (byte-identical stage 2 == stage 3).
4. Language and stdlib tests pass on **both** alumina-boot and aluminac:
   - `make test-lang` (`tests/lang/`)
   - `make test-std` (sysroot embedded tests)
   - `make test-libraries` (`libraries/` embedded tests)
   - `make test-aluminac` and `make test-std-aluminac` (aluminac-specific suites; keep passing)
5. Diagnostics tests (`tests/diag/`, `make test-diag`) **continue to pass on alumina-boot**. They are out of scope for aluminac — we are not porting them, but we are also not breaking alumina-boot's coverage.

## Out of scope

- **Coroutines.** Used by almost no code; aluminac itself doesn't depend on them. Eventually we'll add LLVM stackless coroutines as a replacement for the minicoro-based implementation; until then, coroutine code in `sysroot/` should be gated so aluminac never sees it. Use `#[cfg(coroutines)]` (the existing flag in alumina-boot) or `#[cfg(boot)]`.
- **`std::intrinsics::codegen_func` and other C-output-only intrinsics.** Replace with LLVM equivalents or gate with `#[cfg(boot)]`.
- **Diagnostics tests for aluminac.** `tests/diag/` exercises alumina-boot's error reporting. Don't port; don't break in alumina-boot.

## Specialization: `#[cfg(boot)]`

`#[cfg(boot)]` is set only when alumina-boot is the compiler. Use it for genuine C-vs-LLVM divergences. **Keep usage minimal**: prefer one implementation that both compilers can compile, and if divergence is unavoidable, isolate it in the smallest possible block. Prefer dispatching through a lang item or intrinsic so the rest of the sysroot stays clean.

When you add a `cfg(boot)` gate, justify it in the commit message. It's minor architectural debt; we may revisit later.

## Quality bar — "better and more beautiful"

The aim isn't merely a self-hosted compiler that limps to parity. The aim is one that's better than the old one. While porting:

- Push logic into the sysroot via lang items rather than hardcoding it in the compiler whenever it's reasonable. The sysroot is testable, hackable, and shared by both compilers; compiler-internal magic is none of those.
- We are not porting the warts. Legitimate small cleanups in `sysroot/` are welcome (renames, simpler implementations, removed dead code) **provided alumina-boot still accepts the result and the existing tests still pass**. Major architectural departures (restructuring modules, breaking public API) are not — they expand scope and risk.
- Notice opportunities for compiler-level improvements while you're in there (e.g. now that the sysroot exposes a primitive, the hardcoded compiler path can be deleted). Take them when the slice naturally invites them; otherwise note them in `ALUMINAC_FUTURE.md`.
- If you find yourself running the same multi-step command repeatedly, add a Makefile target for it.

## The cardinal rule

> **Better to have ten things explicitly at 80% than ten things silently at 80%.**

Punting to a higher-bang-for-buck task is fine and encouraged. Punting *silently* is the failure mode we're guarding against. When you stop work on something:

- If it works end-to-end and a test proves it → mark `[DONE]`.
- Otherwise → mark `[PARTIAL]` with a precise `Missing:` enumeration.

When in doubt, downgrade. A feature you "think works" stays `[PARTIAL]` until a test proves it. Never delete a `[PARTIAL]` entry without either upgrading it to `[DONE]` or noting in the commit message that the feature is being abandoned (with reason).

A test is the evidence of completeness. **No test, no `[DONE]`.**

## Source of truth: `PORTING_STATUS.md`

Live, structured state of the parity work. **Read it at the start of every session and update it before every commit.**

Each entry has one of three statuses:

- `[DONE]` — implemented and verified by a test or test suite, plus bootstrap passes.
- `[PARTIAL]` — work started, gaps remain. **Must include a `Missing:` block listing exactly what's left.** Never `[PARTIAL]` without that list.
- `[TODO]` — identified but not started.

### Examples of well-formed entries

Bad (silently 80%):

```
- [DONE] Port std::string
```

…when actually some methods aren't ported. This is the failure mode we're guarding against.

Good (explicitly 80%):

```
- [PARTIAL] Port std::string
  Missing:
  - StringBuilder::extend with iterator argument (needs iterator-protocol bridge in aluminac)
  - char-boundary checks in slicing (needs const-evaluable UTF-8 helpers)
  - tests/std/string.alu cases #4 and #11 fail at runtime (cause unknown — investigate)
```

The `Missing:` list must be specific enough that anyone (including future-you, after a compaction) can pick it up and finish. "TODO: edge cases" is not acceptable; list the edge cases.

## The porting loop (run continuously)

Each iteration is one commit. After each commit, **immediately start the next iteration** — the user is AFK and not gating anything.

1. **Read `PORTING_STATUS.md`.** Pick the next slice. **Prefer `[PARTIAL]` over `[TODO]`** — closing partials is what prevents the "ten things at 80%" failure.
2. **Define the slice's success criterion** before starting. Usually: "test X passes under aluminac" or "sysroot file Y is unified into a single version under `sysroot/` that both compilers compile, and its existing alumina-boot tests still pass".
3. **If the slice needs new language features in aluminac** (parser, type system, codegen), implement them first:
   - Study how alumina-boot does it (`src/alumina-boot/src/`). Don't guess semantics — alumina-boot is the spec; the lang guide is secondary.
   - Implement in aluminac. Push logic into the sysroot via lang items where reasonable.
   - Add a focused test in `tests/aluminac/` that exercises just the new feature.
4. **Port / unify the sysroot file(s).** The end state is one file under `sysroot/` that both compilers compile. If alumina-boot has a wart in the file, you may clean it up provided the existing tests pass. Don't refactor module structure or public API.
5. **Run the quality gates** (see below). All must pass.
6. **Update `PORTING_STATUS.md`.** Mark anything now `[DONE]`. Add `[PARTIAL]` entries with `Missing:` lists for anything you started but didn't finish. Add new follow-ups discovered during the work as `[TODO]`. Note non-parity refactor ideas in `ALUMINAC_FUTURE.md`.
7. **Commit.** One logical change per commit. Match existing commit-message style (`feat(aluminac):`, `fix(aluminac):`, `port(aluminac):`, `refactor(aluminac):`). Reference the `PORTING_STATUS.md` entry when it maps cleanly to one.
8. **Loop to step 1.** Don't ask "should I continue?" — continue.

## Quality gates (non-negotiable, every commit)

Run before every commit:

- `make test-aluminac` — must pass.
- `make test-std-aluminac` — must pass.
- `make bootstrap` — must pass (stage 2 == stage 3).
- If sysroot files moved or unified: `make test-libraries` and (if the file lives under `sysroot/`) `make test-std` to confirm alumina-boot still compiles them.
- `make test-diag` — must pass on alumina-boot (any change to error reporting in alumina-boot must keep it green).

Do not stack work on a knowingly-broken bootstrap. Fix it first. The only exception is if the commit message *explicitly* says "WIP: bootstrap broken, next commit fixes" and the very next commit does fix it.

## When stuck

1. **Verify the assumption** against alumina-boot before patching aluminac. The Rust source is the spec; the lang guide is incomplete.
2. **Punt explicitly** if another `[TODO]` is higher-leverage. Write a `[PARTIAL]` entry with the `Missing:` list, commit what's working, move on. Encouraged for bang-for-buck reasons. But never silently — a feature that's punted with no `[PARTIAL]` entry is the failure mode.
3. **Ask the user** only for genuine judgment calls (e.g. "this requires either a `cfg(boot)` divergence or a major sysroot refactor — which?"). Don't ask for permission to continue between slices.
4. Note non-parity follow-up ideas (style, refactors) in `ALUMINAC_FUTURE.md`, not `PORTING_STATUS.md`.

## Definition of project-level done

- aluminac compiles all of `sysroot/` with no `#[cfg(boot)]` gates beyond a small allowlist agreed upon with the user.
- `sysroot-aluminac/` deleted from the repo.
- Bootstrap converges on the unified `sysroot/` (aluminac → aluminac → aluminac, byte-identical).
- `make test-lang`, `make test-std`, `make test-libraries`, `make test-aluminac`, `make test-std-aluminac` all pass under both compilers (where applicable — the aluminac-specific suites just need to keep passing under aluminac).
- `make test-diag` passes under alumina-boot. Not ported to aluminac.
- Coroutines remain out of scope; LLVM stackless coroutines is a separate follow-up project.

## Anti-laziness notes (read at every session start)

This project will run across many sessions and many context compactions. Treat your future self as a stranger:

- A `Missing:` list with three concrete items is worth more than vague guidance like "needs more work on edge cases".
- If you're tempted to write "should also handle X" in a commit message instead of in `PORTING_STATUS.md`, redirect — commit messages don't get re-read each session, the status file does.
- If you find yourself simplifying a test to make it pass ("I'll come back and add the harder cases"), **stop and add the harder cases to a `[PARTIAL]` entry first.** Otherwise they vanish.
- Periodically scan `[PARTIAL]` entries; if any have been sitting for many commits without progress, surface that — it may be that the design is wrong, not that the work is hard.
- "Continue without asking" applies between slices, not within them. If a slice itself reveals a real ambiguity — a design choice with non-obvious tradeoffs — that's a legitimate stop, not laziness.

## Stay-on-track notes (lessons from prior sessions)

Specific failure modes observed in this project. Read before starting work.

### Verify framings against alumina-boot, not against `PORTING_STATUS.md`

`PORTING_STATUS.md` is descriptive of past investigations — not authoritative, and entries go stale. Several entries here have turned out to be wrong:

- `enum_variants` / `fields` / `attributed` were tagged "blocked on `const_alloc`" across multiple sessions. They're not — alumina-boot's `intr_enum_variants` is a plain `array_of(...)` expression of lang-item calls, no heap. Verified by reading `src/alumina-boot/src/ir/mono/intrinsics.rs`.
- DWARF was tagged `[TODO]` for an unknown number of sessions. Aluminac actually has DWARF emission via `LLVMDIBuilder*` calls. Verified by grepping `src/aluminac/llvm.alu` and `codegen/mod.alu`.

**Rule:** before you adopt a framing like "X is blocked on Y" from a status entry, spend 5 minutes verifying against the actual source. If the status entry is wrong, fix it in the same commit as your work.

### Recognize structural-asymmetry signals

If you find yourself adding a "fifth branch" to handle a new shape of input that the existing four don't cover, **stop**. Two or more patches in a row to the same dispatch site usually means the underlying model is asymmetric and the right fix is upstream of where you're touching.

Concrete example from 2026-05-11: the dyn vtable builder has four branches matching `def.generic_params.len()` against combinations of `impl_args.len()` and `proto_non_self_count`. Each new case "needed another branch". Real cause was that `pass2.alu`'s two FnDef-building paths produce structurally different `generic_params` shapes (one includes Self, the other doesn't). A fifth branch wouldn't have fixed it; uniform construction will.

### When the obvious next slice is large, the obvious next slice is the slice

Don't drift into reading 6 different `[PARTIAL]` entries looking for a smaller one. If the headline blocker is large, read alumina-boot's solution shape first, then attempt it. If genuinely stuck, ask the user a specific design question rather than swapping to an unrelated small slice and shipping a `feat:` commit that doesn't move the headline.

Symptoms of slice-shopping drift: reading several modules in a row, opening files just to gauge size, multiple "let me check if this works" experiments without committing. Each minute spent here is a minute not spent on the actual blocker.

### Don't propagate prose between sessions without verifying it

Long-form prose ages worst. If an entry's first sentence says "alumina-boot does X, aluminac does Y" — that's a snapshot, possibly wrong now. Periodically (e.g. when touching an adjacent entry) re-read for staleness. The "Highest-leverage remaining work" section in `PORTING_STATUS.md` is meant to be the high-signal summary; if it disagrees with a per-feature entry, the per-feature entry is probably the stale one.

### Architectural debt should be tracked, not patched around forever

Some gaps are bandage-able with targeted fixes (the 2026-05-11 type_map snapshot/restore). Bandages buy time but compound: the same architectural shape will surface in new symptoms. When you ship a bandage, **also write an entry naming the underlying architectural debt** so the next session can decide between another bandage and the real fix. The "Highest-leverage remaining work" section is the right home for these — item #4 there is the type_map example.
