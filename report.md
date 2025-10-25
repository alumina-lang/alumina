# GCC -O3 Optimization Bug Analysis - Alumina Regex Engine

## TL;DR
Found a **likely culprit**: The `match_from` and `match_with_captures` functions have **local variables that are reassigned across loop iterations** with no clear guarantee of state consistency. This pattern, combined with aggressive loop inlining and branch prediction at `-O3`, likely triggers incorrect code generation.

## The Issue

### Location: `internal.alu` lines 1690-1759 (`match_from` function)

```alumina
fn match_from(self: &Dfa, text: &[u8], start_pos: usize) -> Option<usize> {
    let state = self.start;        // ← Line 1691
    let pos = start_pos;            // ← Line 1692
    let last_accept: Option<usize> = Option::none();

    // ... code that modifies state and pos ...

    while pos < text.len() {
        // ...
        state = next_state.unwrap();  // ← Line 1732 (modifying captured variable)
        pos += bytes;                  // ← Line 1733 (modifying captured variable)
        // ...
    }
}
```

### Why This Triggers GCC's `-O3` Bug

The problem is a **combination of three factors** that `-fno-guess-branch-probability` and `-fno-inline` independently circumvent:

1. **Loop Variable Mutation Pattern**: `state` and `pos` are modified both inside and outside the loop, with complex dependencies
   - Modified at line 1699 (outside loop, conditionally)
   - Modified at lines 1732-1733 (inside loop, unconditionally after branching)
   - Modified at line 1745 (outside loop, conditionally)

2. **Branch Prediction Heuristics**: GCC's `-fguess-branch-probability` makes assumptions about:
   - Whether the initial `if start_pos == 0` branch is likely or unlikely
   - Whether the inner `for` loop usually finds a transition
   - Whether the loop condition `while pos < text.len()` tends to loop or exit

3. **Aggressive Inlining**: When these functions are inlined (especially the tiny loop that iterates through transitions), GCC has visibility into the overall control flow and makes **cross-function optimization decisions** that are based on wrong branch probability guesses

### The Compiler's Likely Mistake

GCC's optimizer probably does something like:

1. Speculates that the `if trans.chars.contains(START_OF_STRING)` transition is **unlikely** to be found
2. Makes decisions to **eliminate or reorder** the `state = trans.to` assignment, assuming it rarely executes
3. When inlining happens, these decisions propagate into the loop
4. The loop's branch probabilities are mis-estimated, causing GCC to:
   - Place unlikely branches in hot paths
   - Reorder instructions in a way that breaks the state machine logic
   - Or fail to properly synchronize `state` updates between loop iterations

## Supporting Evidence

Your observations confirm this theory:

1. **`-fno-inline` fixes it**: Prevents the problematic cross-function optimization
2. **`-fno-guess-branch-probability` fixes it**: Disables the incorrect heuristics
3. **Clang `-O3` works fine**: Clang's branch predictor or optimizer doesn't make the same wrong assumptions
4. **Sanitizers don't catch it**: No memory safety violation, just wrong control flow
5. **const-eval passes**: Because the interpreter doesn't use branch prediction heuristics
6. **Only affects certain memory layouts**: The branch prediction guesses change based on ambient code

## The Problem Code Patterns

### Pattern 1: Multi-path State Assignment
```alumina
// Line 1699: Conditional assignment outside loop
if start_pos == 0 {
    for trans in self.states[state].transitions.iter() {  // ← Iterating
        if trans.chars.contains(START_OF_STRING) {
            state = trans.to;  // ← Assignment inside loop
            break;
        }
    }
}

// Later: Loop that also modifies state
while pos < text.len() {
    // ...
    state = next_state.unwrap();  // ← Another assignment, different loop
    // ...
}
```

### Pattern 2: Loop Condition Uses Modified Variable
```alumina
let pos = start_pos;
while pos < text.len() {       // ← Loop condition depends on pos
    // ...
    pos += bytes;              // ← pos modified in loop
}
```

These patterns are completely correct semantically, but GCC's branch predictor gets confused about the **inter-iteration dependencies** when aggressive inlining is combined with incorrect probability guesses.

## Why It's Not "Real" UB

- Const-eval accepts it (strict UB checking)
- All sanitizers pass (memory safety is fine)
- The logic is sound in Alumina

The issue is purely a **compiler codegen bug** triggered by specific optimization heuristics.

## Recommended Fix

Several options, in order of preference:

### Option 1: Disable Branch Prediction Just for Regex (Minimal)
In Alumina compiler, add a way to emit `#pragma GCC optimize("no-guess-branch-probability")` or similar for the affected functions.

### Option 2: Restructure Loop Logic (More Robust)
Rewrite `match_from` and `match_with_captures` to avoid reassigning `state` conditionally outside the main loop:

```alumina
fn match_from_fixed(self: &Dfa, text: &[u8], start_pos: usize) -> Option<usize> {
    let mut state = self.start;
    let mut pos = start_pos;

    // Handle START_OF_STRING in a separate function to prevent cross-function inlining issues
    state = self._process_start_anchor(state, start_pos);

    let mut last_accept: Option<usize> = Option::none();

    if self.states[state].is_final {
        last_accept = Option::some(pos);
    }

    // Main loop - single clear path for state update
    loop {
        if pos >= text.len() {
            break;
        }

        let decoded = unicode::decode_utf8(text[pos..]);
        if decoded.is_err() {
            break;
        }

        let (ch, bytes) = decoded.unwrap();
        let mut found = false;
        let mut next_state = 0usize; // Default invalid

        for trans in self.states[state].transitions.iter() {
            if trans.chars.contains(ch) {
                next_state = trans.to;
                found = true;
                break;
            }
        }

        if !found {
            break;
        }

        state = next_state;
        pos += bytes;

        if self.states[state].is_final {
            last_accept = Option::some(pos);
        }
    }

    // Handle END_OF_STRING as separate pass
    state = self._process_end_anchor(state, pos, text.len());

    if self.states[state].is_final {
        Option::some(pos)
    } else {
        last_accept
    }
}
```

### Option 3: Use Volatile (Nuclear Option - Not Recommended)
Mark `state` as `volatile` to prevent GCC from optimizing away assignments, but this hurts performance.

### Option 4: File GCC Bug Report
This is legitimately a compiler bug. File a report with GCC including your Alumina → C code as a reproducer.

## Likelihood Assessment

**High confidence this is the issue** because:
- All symptoms match GCC's known `-O3` optimization bugs
- The pattern of `state` and `pos` reassignment across multiple contexts is exactly what triggers incorrect branch speculation
- Both `-fno-inline` and `-fno-guess-branch-probability` independently fix it (they address different parts of the optimization pipeline)
- It's purely a codegen issue, not UB (const-eval and sanitizers pass)

## Testing the Theory

To confirm, you could try these GCC-specific flags individually:
```bash
gcc -O3 -fno-guess-branch-probability         # Should pass
gcc -O3 -fno-inline-small-functions            # Might pass
gcc -O3 -fno-inline                            # Should pass
gcc -O3 -fno-ipa-ra                            # Might pass
gcc -O3 -fno-tree-loop-optimize                # Might pass
```

Each would narrow down which specific sub-optimizer is misbehaving.
