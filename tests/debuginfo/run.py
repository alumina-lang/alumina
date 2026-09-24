#!/usr/bin/env python3

"""
Debug info tests: programs compiled with `aluminac -g`, run under lldb.

Each test (tests/debuginfo/*.alu) says what to do in comments:

    let x = 5; // #break        a breakpoint on this line
    // setup: b main::f         an lldb command before `run`
    // lldb: frame variable x   an lldb command (in order, after `run`)
    // check: (i32) x = 5       text the output must contain, after the
                                previous check's
    // check-not: __            text that must not be in the output between
                                the checks around it

The program is run to its first breakpoint first, with the formatters
(tools/lldb/alumina_lldb.py) loaded. Before that, `llvm-dwarfdump --verify`
checks the DWARF (with --dwarfdump or LLVM_DWARFDUMP).

Usage: run.py [--lldb LLDB] [--dwarfdump LLVM_DWARFDUMP] ALUMINAC [FILTER]
"""

import argparse
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TEST_DIR = os.path.join(ROOT, "tests", "debuginfo")
FORMATTERS = os.path.join(ROOT, "tools", "lldb", "alumina_lldb.py")
SYSROOT = os.path.join(ROOT, "sysroot")

DIRECTIVE = re.compile(r"//\s*(setup|lldb|check|check-not):\s?(.*)$")


def parse(path):
    breakpoints, setup, commands, checks = [], [], [], []
    with open(path) as f:
        for number, line in enumerate(f, 1):
            if re.search(r"//\s*#break\b", line):
                breakpoints.append(number)
            match = DIRECTIVE.search(line)
            if match:
                kind, text = match.group(1), match.group(2).rstrip()
                {"setup": setup, "lldb": commands}.get(kind, checks).append((kind, text))
    return breakpoints, setup, commands, checks


def match_checks(output, checks):
    """FileCheck-style: `check`s in order; `check-not`s between them."""
    position, pending_not = 0, []
    for kind, text in checks:
        if kind == "check-not":
            pending_not.append(text)
            continue
        found = output.find(text, position)
        if found < 0:
            return "expected `%s` (after offset %d)" % (text, position)
        for forbidden in pending_not:
            if forbidden in output[position:found]:
                return "unexpected `%s` before `%s`" % (forbidden, text)
        pending_not, position = [], found + len(text)
    for forbidden in pending_not:
        if forbidden in output[position:]:
            return "unexpected `%s`" % forbidden
    return None


def run_test(args, path, work):
    name = os.path.splitext(os.path.basename(path))[0]
    binary = os.path.join(work, name)
    compile_cmd = [args.aluminac, "-g", "--sysroot", SYSROOT, "-o", binary, "main=" + path]
    result = subprocess.run(compile_cmd, capture_output=True, text=True)
    if result.returncode != 0:
        return "compile failed:\n" + result.stdout + result.stderr, ""

    # (On macOS the DWARF is in the .dSYM bundle aluminac makes.)
    dwarf = binary + ".dSYM" if platform.system() == "Darwin" else binary
    if args.dwarfdump:
        result = subprocess.run([args.dwarfdump, "--verify", "--quiet", dwarf], capture_output=True, text=True)
        if result.returncode != 0:
            return "llvm-dwarfdump --verify failed:\n" + result.stdout + result.stderr, ""

    breakpoints, setup, commands, checks = parse(path)
    script = ["settings set auto-confirm true", "command script import " + FORMATTERS]
    script += ["breakpoint set --file %s --line %d" % (os.path.basename(path), line) for line in breakpoints]
    script += [command for _, command in setup]
    script += ["run"] + [command for _, command in commands] + ["kill"]
    script_path = os.path.join(work, name + ".lldb")
    with open(script_path, "w") as f:
        f.write("\n".join(script) + "\n")

    result = subprocess.run(
        [args.lldb, "--batch", "--no-lldbinit", "--source", script_path, binary],
        capture_output=True,
        text=True,
        timeout=120,
    )
    output = result.stdout + result.stderr
    return match_checks(output, checks), output


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("aluminac")
    parser.add_argument("filter", nargs="?", default="")
    parser.add_argument("--lldb", default=os.environ.get("LLDB") or shutil.which("lldb-22") or shutil.which("lldb"))
    parser.add_argument("--dwarfdump", default=os.environ.get("LLVM_DWARFDUMP"))
    parser.add_argument("-v", "--verbose", action="store_true", help="print lldb's output")
    args = parser.parse_args()

    if not args.lldb:
        print("error: lldb not found (set LLDB, or install lldb-22)")
        return 1
    if args.dwarfdump and not shutil.which(args.dwarfdump):
        print("error: %s not found" % args.dwarfdump)
        return 1

    tests = sorted(
        os.path.join(TEST_DIR, entry)
        for entry in os.listdir(TEST_DIR)
        if entry.endswith(".alu") and args.filter in entry
    )
    failures = []
    with tempfile.TemporaryDirectory(prefix="alumina-debuginfo-") as work:
        for path in tests:
            name = os.path.basename(path)
            error, output = run_test(args, path, work)
            if args.verbose or error:
                print(output)
            if error:
                print("FAIL %s: %s" % (name, error))
                failures.append(name)
            else:
                print("PASS %s" % name)

    print("\n%d passed, %d failed" % (len(tests) - len(failures), len(failures)))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
