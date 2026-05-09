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

### Anti-pattern: recap prose (any time, not just at "end")

The user has corrected this three times. The previous version of this rule only forbade end-of-session summaries; the third failure was a mid-session recap written immediately after a green-gate run, framed as an innocent progress note. So: **any** turn that summarises recent work is the failure mode, regardless of whether you're "stopping."

After a commit lands, the next text you emit must point forward, not backward. Two acceptable shapes:

- A one-sentence forward statement about what you're doing next ("Trying X next."), then immediately a tool call.
- Nothing at all — go straight to the next tool call.

Anything else is a recap. In particular, do **not** emit any of these, even mid-session:

- A list of what landed in recent commits.
- Numbers ("N TODO, M PARTIAL", "X tests pass", "Y commits this session"). The status file already tracks numbers.
- "All gates pass. Continuing." — the gates passing is implied by the next slice starting; saying it adds nothing.
- "Bug fixes that landed", "key wins", "remaining blockers" — these are restating PORTING_STATUS.md prose at the user, who doesn't need it.
- Any paragraph that opens with "The session …", "Quality gates are …", or similar.

#### The inner monologue is also the failure

The visible recap is downstream of the reasoning. Watch for these in your own thinking and treat them as red flags — when one appears, immediately pick the next slice instead:

- "Let me wrap up", "let me end this session", "let me stop here".
- "Diminishing returns", "every remaining slice is too big".
- "The session has been productive / has made progress".
- "I've done a lot this session".
- "Let me check the final state".
- "Per the user's instruction to continue, I should keep going. But …" — the "but" is the tell.

Once you start composing a final-state-of-the-world thought, you've already half-written the recap. Cut it before the colon.

#### Why this keeps happening

Your training pushes you to summarise before terminating a turn. You have to actively suppress that instinct here. The cardinal rule is **forward-only output**: after a commit, the next emission is the next slice's first action, not a status sentence about the previous slice.

If you're three commits past the last user message and still feel a pull toward a recap, you are right on the edge of the failure mode. Stop, delete whatever recap-shaped text is composing, and write the next tool call instead.

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
