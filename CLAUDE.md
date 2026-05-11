# Alumina

Bootstrapped Alumina compiler with two implementations:

- **alumina-boot** (Rust, `src/alumina-boot/`) — generates C; canonical reference for language semantics.
- **aluminac** (Alumina, `src/aluminac/`) — self-hosted, generates LLVM IR. Currently being brought to parity with alumina-boot.

## Active project: aluminac → alumina-boot parity

Read `PORTING.md` and `PORTING_STATUS.md` before working on aluminac. `PORTING.md` has the workflow and the rules; `PORTING_STATUS.md` is the live state of the work. **Update `PORTING_STATUS.md` before every commit.** The cardinal rule is in `PORTING.md` — read it once explicitly each session.

## Run continuously — the user is AFK

After finishing one slice (commit landed, tests + bootstrap green, `PORTING_STATUS.md` updated), **immediately pick the next slice and continue**. Don't wait for confirmation. The user is intentionally AFK for long stretches; idle agents waste their time.

### The only valid stop condition is project-level done

There is exactly one acceptable reason to stop the loop:

- **All categories in `PORTING_STATUS.md` are `[DONE]` and the project-level done criteria in `PORTING.md` are met.**

That's it. No exceptions. Read this section twice if you're tempted to stop for any other reason.

### Things that are NOT stop conditions

This section exists because previous sessions repeatedly stopped after writing a "session summary." Don't.

- "I've done a lot of commits this session" — irrelevant. Keep going.
- "Good progress arc; winding down" — winding down is not a thing. Keep going.
- "Let me give the user a recap" — never. Recaps are how you trick yourself into stopping. Keep going.
- "The next thing is bigger; defer to next session" — there is no next session, there is just the next slice. Pick it. Smaller scope if you must, but pick it.
- "Test count went from N to M, that's a clean stopping point" — N to M+1 is also fine. Keep going.
- "I should ask the user what to prioritize next" — no. PORTING_STATUS.md is prioritized. Pick the next slice from it.
- A natural number of commits (5, 7, 10, …) — there is no natural number; the natural number is "all of them."
- The cache window resetting / context getting long — the harness handles that. Keep going.
- "Should I continue?" between slices — yes, always.

### When you genuinely need user input

If you hit a real judgment call ("should this be `cfg(boot)` or unified via a lang item?" with no obvious answer), or a quality gate fails repeatedly and you can't diagnose it: **ask the user a specific question.** Do not stop with a summary. Asking ≠ stopping. Ask, then wait for the answer, then keep going.

If a gate fails once: diagnose and fix, don't escalate. Escalate only after multiple genuine attempts.

### A summary is not the problem; stopping is

Three sessions in a row I've stopped after writing a recap. The recap is a symptom — the failure is the stop. Write a recap if you must, then **immediately pick the next slice and keep going**. Never let composing a status paragraph become the last thing in a turn.

## Stay on the headline blocker — don't drift into slice-shopping

The mirror failure mode of stopping is *drifting*: instead of stopping cleanly, you read 6 different `[PARTIAL]` entries trying to find a small contained slice, then ship something unrelated to the headline. This produces a long commit log that doesn't move the needle. Symptoms observed on this project:

- Opening multiple files just to gauge slice size.
- Multiple "let me check if this works" experiments without committing.
- Several `docs:`-only commits in a row (status-shuffling without code change).
- Two consecutive sessions where the headline blocker (e.g. `Result::unwrap` end-to-end) didn't move but 10+ smaller commits landed.

**Rule:** if the headline blocker from the last session is still the headline blocker, the right slice is the *next step* toward it — even if that step is "read alumina-boot's solution shape for an hour" or "ask the user a specific design question". A `feat:` commit for an unrelated minor parity item is not progress on the headline. It's drift.

If the next step on the headline truly requires user judgment (a design choice with non-obvious tradeoffs), **ask the user with a specific question** — don't swap to a small unrelated slice. Asking ≠ stopping.

## When patching twice in the same place, stop and look up

If you find yourself adding a second branch, special case, or fallback to the same dispatch site within a few sessions, **stop**. That's a strong signal the underlying model is wrong-shaped and the right fix is upstream of where you're patching. Add a structural entry to `PORTING_STATUS.md` describing the asymmetry; don't ship the third branch.

Concrete trigger (2026-05-11): the dyn vtable build at `mono/lower.alu` line 3821 had four branches matching `def.generic_params.len()` against `impl_args.len() + proto_non_self_count` combinations. Mid-session I tried to add a fifth. Reverting and looking at *why* the existing branches each needed to be different revealed the real cause: `pass2.alu`'s two FnDef-building paths produce asymmetric `generic_params` shapes. The fifth branch wouldn't have fixed anything; a single uniform construction will.

## Verify entries in `PORTING_STATUS.md` against alumina-boot, not against the entry's prose

Status entries go stale. Confirmed-stale examples in this file's history:

- "`enum_variants` needs `const_alloc`" — wrong. alumina-boot's `intr_enum_variants` is a plain `array_of(...)` of lang-item calls. No heap involvement. (Read `src/alumina-boot/src/ir/mono/intrinsics.rs` if in doubt.)
- "Aluminac emits no DWARF" — wrong. `LLVMDIBuilder*` is wired in `llvm.alu` + `codegen/mod.alu`. The `-g` flag is documented in `--help`.

Before you adopt a framing like "X is blocked on Y" from an existing entry, spend 5 minutes verifying against the actual source. If the entry is wrong, fix it in the same commit as your work — that's how staleness gets removed instead of compounding.

## Commands

- `make` — build alumina-boot
- `make bootstrap` — three-stage aluminac bootstrap; must pass after every parity-affecting change. Slow (multiple minutes); budget for it but don't skip it.
- `make test-aluminac` / `make test-std-aluminac` — aluminac test suites
- `make test-lang` / `make test-libraries` / `make test-std` / `make test-docs` — alumina-boot test suites against `sysroot/`. Goal: these eventually pass under aluminac too.
- `make test-diag` — diagnostics tests. **alumina-boot only.** Out of scope for aluminac (see `PORTING.md`); must keep passing in alumina-boot.

## Layout

- `sysroot/` — full alumina-boot stdlib. **Target of the parity work.**
- `sysroot-aluminac/` — reduced subset aluminac currently consumes. **To be eliminated** as parity progresses; final state is a single unified `sysroot/`.
- `tests/aluminac/` — aluminac tests; `tests/lang/`, `tests/diag/` — alumina-boot tests; sysroot/library tests are embedded under `sysroot/` and `libraries/`.
- `docs/lang_guide.md` — language reference. Incomplete in places; **alumina-boot's behavior is the de-facto spec** when the doc and the Rust source disagree.
- `ALUMINAC_FUTURE.md` — backlog for non-parity refactors. Parity work goes in `PORTING_STATUS.md`, not here.

## Hosts

Bootstrap works on x86_64 and aarch64 Linux. ABI-sensitive codegen paths in `src/aluminac/codegen/` runtime-detect the host arch from the LLVM target triple — see `CodegenCtx::is_x86_64` / `needs_sret` / `uses_byval_attr`. When changing those paths, mentally check both targets.
