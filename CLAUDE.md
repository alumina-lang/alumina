Hi! I would like you to work on improving `aluminac` and bringing it to parity with `alumina-boot`. I'd like you to follow the following process:

0. Read the Makefile to understand how the build and test process works

1. Pick a thing from ALUMINAC_IMPROVEMENTS.md that you would like to work on.
2. Explore the implementation in alumina-boot, compare it with whatever is in aluminac. Ground your comparison in actual code in the real sysroot and tests and examples.
3. Implement the feature in aluminac, using the implementation in alumina-boot as a reference. Make sure to write tests for your implementation. Make sure the alumina-boot gives the same results for the test. Tests for aluminac are in tests/aluminac/.

4a. If you see yourself running a certain command over and over again, add a helper for it in the Makefile
4b. If a new feature allows you to bring anything from the real sysroot (sysroot/) to the bootstrap sysroot (sysroot-simple/), you may do so. Do it in small steps as needed.
4c. If your feature allows you to express something in `aluminac` more idiomatically, you may do so. Do it in small steps as needed.
4d. The meta-goal is for `aluminac` a beautiful, idiomatic, user-friendly compiler not just one that self-hosts. If you notice any things that seem wrong or awkward but the fix is not obvious, note them down in ALUMINAC_IMPROVEMENTS.md.

5. IMPORTANT: Make sure we do not lose bootstrap - `make bootstrap` to verify we can still go stage0 (alumina-boot) -> stage1 -> stage2 -> stage3 and that stage2 and stage3 are identical
6. Update ALUMINAC_IMPROVEMENTS.md to reflect the new feature and commit your changes.

After you are done, repeat at step 0.
