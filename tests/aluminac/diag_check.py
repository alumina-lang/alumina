#!/usr/bin/env python3
"""
Check aluminac's diagnostics against alumina-boot's diagnostics tests
(tests/diag/*.alu, annotated with `// diag: level(kind): "message"`).

For every expected error and warning, aluminac should report a diagnostic of
the same level on that line: the diagnostic's own location if it is in the
test file, otherwise the first instantiation note in it (as alumina-boot's
harness attributes a diagnostic to the first frame of its backtrace in the
file). Errors aluminac reports on other lines are "unexpected". Messages are
not compared (the wording differs between the compilers), but are printed
for mismatches.

Usage: tests/aluminac/diag_check.py [aluminac] [filter]
"""

import json
import os
import re
import subprocess
import sys
import tempfile

ALUMINAC = sys.argv[1] if len(sys.argv) > 1 else "build/debug/aluminac"
FILTER = sys.argv[2] if len(sys.argv) > 2 else ""
DIAG_DIR = "tests/diag"

DIAG_RE = re.compile(r'([a-z]+)\(([a-z0-9_]+)\): ("(.*?)(?<!\\)")')


def expected_diagnostics(contents):
    expected = {}
    for line_num, line in enumerate(contents.split("\n"), start=1):
        m = re.fullmatch(r"^.*\s*// diag: (.*)$", line)
        if not m:
            continue
        for level, kind, message, _ in DIAG_RE.findall(m[1]):
            if level in ("error", "warning"):
                expected.setdefault(line_num, []).append((level, kind, json.loads(message)))
    return expected


def aluminac_diagnostics(output, path):
    """(level, message, line, column) of each error/warning, located in `path`."""
    diags = []
    current = None
    for line in output.split("\n"):
        m = re.match(r"^(error|warning): (.*)$", line)
        if m:
            current = {"level": m[1], "message": m[2], "places": []}
            diags.append(current)
            continue
        m = re.match(r"^\s*--> (.*):(\d+):(\d+)$", line)
        if m and current is not None:
            if os.path.normpath(m[1]) == os.path.normpath(path):
                current["places"].append((int(m[2]), int(m[3])))
    return [(d["level"], d["message"], *d["places"][0]) for d in diags if d["places"]]


def main():
    passed, failed = 0, []
    for name in sorted(os.listdir(DIAG_DIR)):
        if not name.endswith(".alu") or FILTER not in name:
            continue
        path = os.path.join(DIAG_DIR, name)
        with open(path) as f:
            contents = f.read()
        directives = dict(re.findall(r"^//!\s*([a-zA-Z0-9_]+):\s*(.*)$", contents, flags=re.MULTILINE))
        extra = [a for a in json.loads(directives.get("extra_args", "[]")) if not a.startswith("-Z")]
        expected = expected_diagnostics(contents)

        with tempfile.TemporaryDirectory() as tmp:
            proc = subprocess.run(
                [ALUMINAC, "--sysroot", "sysroot", "-o", os.path.join(tmp, "out"), *extra, f"main={path}"],
                stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=300,
            )
        got = aluminac_diagnostics(proc.stderr, path)

        problems = []
        # (Each diagnostic is given once, as alumina-boot's.)
        for diag in sorted(set(got)):
            if got.count(diag) > 1:
                problems.append(f"  line {diag[2]}: {diag[0]} given {got.count(diag)} times: {diag[1]}")
        got = [(level, message, line) for level, message, line, _ in got]
        for line, diags in sorted(expected.items()):
            for level, kind, message in diags:
                if not any(g[0] == level and g[2] == line for g in got):
                    problems.append(f"  line {line}: missing {level}({kind}): {message}")
        for level, message, line in got:
            if level == "error" and not any(e[0] == "error" for e in expected.get(line, [])):
                problems.append(f"  line {line}: unexpected error: {message}")
        expects_failure = int(directives.get("exit_code", "0")) != 0
        if expects_failure != (proc.returncode != 0) and not problems:
            problems.append(f"  exit code {proc.returncode} (alumina-boot: {directives.get('exit_code', '0')})")

        if problems:
            failed.append(name)
            print(f"{name}: FAIL")
            print("\n".join(problems))
        else:
            passed += 1

    print(f"\ndiag check: {passed} match alumina-boot; {len(failed)} differ")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
