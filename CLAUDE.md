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

### Anti-pattern: end-of-session prose

If you find yourself writing a paragraph that:
- Lists what you did this session, or
- Says "winding down" / "stopping here" / "good arc" / "let me wrap up", or
- Starts with "**Audit + hygiene (N commits):**" or any similar recap structure,

**stop typing that prose, delete it, and pick the next slice instead.** That prose is the failure mode. The user does not want it; they want the next commit.

The user has corrected this twice. Don't make it three.

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
