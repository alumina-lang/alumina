# Alumina

Bootstrapped Alumina compiler with two implementations:

- **alumina-boot** (Rust, `src/alumina-boot/`) — generates C; canonical reference for language semantics.
- **aluminac** (Alumina, `src/aluminac/`) — self-hosted, generates LLVM IR. Currently being brought to parity with alumina-boot.

## Active project: aluminac → alumina-boot parity

Read `PORTING.md` and `PORTING_STATUS.md` before working on aluminac. `PORTING.md` has the workflow and the rules; `PORTING_STATUS.md` is the live state of the work. **Update `PORTING_STATUS.md` before every commit.** The cardinal rule is in `PORTING.md` — read it once explicitly each session.

## Run continuously — the user is AFK

After finishing one slice (commit landed, tests + bootstrap green, `PORTING_STATUS.md` updated), **immediately pick the next slice and continue**. Don't wait for confirmation. The user is intentionally AFK for long stretches; idle agents waste their time.

Stop and ask only when:

- You hit genuine ambiguity that needs a user judgment call (e.g. "should this be `cfg(boot)` or unified via a lang item?" with no obvious answer).
- A quality gate fails repeatedly and you can't diagnose it.
- All categories in `PORTING_STATUS.md` are `[DONE]` and the project-level done criteria in `PORTING.md` are met.

"Should I continue?" between slices is **not** a reason to stop. Just continue.

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
