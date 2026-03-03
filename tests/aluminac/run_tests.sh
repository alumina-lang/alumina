#!/bin/bash
# Test runner for aluminac (self-hosted compiler) feature tests.
#
# Each .alu file in this directory is compiled with aluminac and executed.
# Exit code 0 = pass, non-zero = fail. Compile failures also count as fails
# unless the filename contains "compile_fail".
#
# Usage:
#   ./tests/aluminac/run_tests.sh [path-to-aluminac] [filter]
#
# Examples:
#   ./tests/aluminac/run_tests.sh build/fast-debug/aluminac
#   ./tests/aluminac/run_tests.sh build/fast-debug/aluminac mixin

set -u

ALUMINAC="${1:-build/fast-debug/aluminac}"
FILTER="${2:-}"
TESTDIR="$(dirname "$0")"
TMPDIR="${TMPDIR:-/tmp}"
PASS=0
FAIL=0
SKIP=0
FAILURES=""

if [ ! -x "$ALUMINAC" ]; then
    echo "error: $ALUMINAC not found or not executable"
    echo "hint: make FAST_DEBUG=1 build/fast-debug/aluminac"
    exit 1
fi

for src in "$TESTDIR"/*.alu; do
    name="$(basename "$src" .alu)"

    # Filter
    if [ -n "$FILTER" ] && [[ "$name" != *"$FILTER"* ]]; then
        SKIP=$((SKIP + 1))
        continue
    fi

    printf "test %-40s ... " "$name"

    out="$TMPDIR/aluminac_test_$name"

    # Extract extra flags from test file (// ALUMINAC_FLAGS: ...)
    extra_flags=""
    flags_line=$(grep -m1 '^// ALUMINAC_FLAGS:' "$src" || true)
    if [ -n "$flags_line" ]; then
        extra_flags="${flags_line#// ALUMINAC_FLAGS:}"
    fi

    # Extract expected exit code (// EXPECTED_EXIT: N), default 0
    expected_rc=0
    exit_line=$(grep -m1 '^// EXPECTED_EXIT:' "$src" || true)
    if [ -n "$exit_line" ]; then
        expected_rc=$(echo "${exit_line#// EXPECTED_EXIT:}" | tr -d ' ')
    fi

    # Compile
    if ! $ALUMINAC "$src" -o "$out" $extra_flags 2>/dev/null; then
        if [[ "$name" == *"compile_fail"* ]]; then
            echo "ok (expected compile failure)"
            PASS=$((PASS + 1))
        else
            echo "FAIL (compile error)"
            FAIL=$((FAIL + 1))
            FAILURES="$FAILURES\n  $name: compile error"
            # Show compiler output for diagnosis
            $ALUMINAC "$src" -o "$out" $extra_flags 2>&1 | head -5 | sed 's/^/    /'
        fi
        continue
    fi

    # Run
    "$out"
    rc=$?
    rm -f "$out"

    if [ "$rc" -eq "$expected_rc" ]; then
        echo "ok"
        PASS=$((PASS + 1))
    else
        echo "FAIL (exit $rc, expected $expected_rc)"
        FAIL=$((FAIL + 1))
        FAILURES="$FAILURES\n  $name: exit code $rc (expected $expected_rc)"
    fi
done

echo ""
echo "test result: $PASS passed; $FAIL failed; $SKIP filtered out"

if [ "$FAIL" -gt 0 ]; then
    echo -e "\nfailures:$FAILURES"
    exit 1
fi
