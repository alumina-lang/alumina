#!/usr/bin/env bash
#
# Cross-check the aluminac feature tests against alumina-boot, the reference
# compiler: every test must behave the same when compiled by alumina-boot
# (a compile_fail test must fail to compile, any other test must compile
# and exit with its expected code). A divergence means either the test is
# not valid Alumina, or one of the compilers has a bug.
#
# Usage:
#   ./tests/aluminac/cross_check.sh [path-to-alumina-boot] [filter]

set -u

ALUMINA_BOOT="${1:-build/alumina-boot}"
FILTER="${2:-}"
TESTDIR="$(dirname "$0")"
TMPDIR="${TMPDIR:-/tmp}"
CC="${CC:-cc}"
PASS=0
FAIL=0
KNOWN=0
FAILURES=""

for src in "$TESTDIR"/*.alu; do
    name="$(basename "$src" .alu)"
    if [ -n "$FILTER" ] && [[ "$name" != *"$FILTER"* ]]; then
        continue
    fi

    # Same flags as for aluminac, minus the ones alumina-boot spells
    # differently or does not have.
    flags=""
    flags_line=$(grep -m1 '^// ALUMINAC_FLAGS:' "$src" || true)
    if [ -n "$flags_line" ]; then
        flags="${flags_line#// ALUMINAC_FLAGS:}"
    fi
    flags="$(echo "$flags" | sed -e 's/--sysroot [^ ]*//')"
    # alumina-boot always needs the sysroot (entry point, lang items), even
    # for tests aluminac compiles freestanding.
    sysroot="--sysroot sysroot"

    diverges_line=$(grep -m1 '^// BOOT_DIVERGES:' "$src" || true)
    if [ -n "$diverges_line" ]; then
        printf "test %-40s ... known divergence:%s\n" "$name" "${diverges_line#// BOOT_DIVERGES:}"
        KNOWN=$((KNOWN + 1))
        continue
    fi

    expected_rc=0
    exit_line=$(grep -m1 '^// EXPECTED_EXIT:' "$src" || true)
    if [ -n "$exit_line" ]; then
        expected_rc=$(echo "${exit_line#// EXPECTED_EXIT:}" | tr -d ' ')
    fi

    printf "test %-40s ... " "$name"
    c_out="$TMPDIR/crosscheck_$name.c"
    bin_out="$TMPDIR/crosscheck_$name"

    if ! "$ALUMINA_BOOT" $sysroot $flags -o "$c_out" "$src" >/dev/null 2>&1; then
        if [[ "$name" == *"compile_fail"* ]]; then
            echo "ok (expected compile failure)"
            PASS=$((PASS + 1))
        else
            echo "FAIL (alumina-boot rejects it)"
            FAIL=$((FAIL + 1))
            FAILURES="$FAILURES\n  $name: rejected by alumina-boot"
            "$ALUMINA_BOOT" $sysroot $flags -o "$c_out" "$src" 2>&1 | grep -m2 -A1 '^error' | sed 's/^/    /'
        fi
        continue
    fi
    if [[ "$name" == *"compile_fail"* ]]; then
        echo "FAIL (alumina-boot accepts it)"
        FAIL=$((FAIL + 1))
        FAILURES="$FAILURES\n  $name: accepted by alumina-boot"
        continue
    fi

    helper=""
    if [ -f "$TESTDIR/c/$name.c" ]; then
        helper="$TESTDIR/c/$name.c"
    fi
    if ! $CC -o "$bin_out" "$c_out" $helper -lm >/dev/null 2>&1; then
        echo "FAIL (C compilation)"
        FAIL=$((FAIL + 1))
        FAILURES="$FAILURES\n  $name: C compilation failed"
        continue
    fi
    "$bin_out" >/dev/null 2>&1
    rc=$?
    rm -f "$bin_out" "$c_out"
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
echo "cross-check result: $PASS agree; $FAIL diverge; $KNOWN known divergences"
if [ "$FAIL" -gt 0 ]; then
    echo -e "\ndivergences:$FAILURES"
    exit 1
fi
