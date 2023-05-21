#!/usr/bin/env python3

"""
Test runner for compile-time (diagnostics) tests. It takes the expected compile errors/warnings/notes from comments
in source files and matches them against the actual compilation results.
"""

import sys
import re
import subprocess
import argparse
import json
import logging
import sys
import dataclasses
import functools

from collections import defaultdict

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@functools.total_ordering
@dataclasses.dataclass
class Diagnostic:
    level: str
    kind: str
    message: str

    def __eq__(self, other):
        return self.level == other.level and self.kind == other.kind

    def __lt__(self, other):
        return self.level < other.level or (self.level == other.level and self.kind < other.kind)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", help="File to test")
    parser.add_argument(
        "--fix",
        action="store_true",
        help="Fix files instead of checking them",
    )
    parser.add_argument("cmd", nargs=argparse.REMAINDER, help="Command to run the compiler")
    args = parser.parse_args()

    with open(args.file) as f:
        contents = f.read().strip()

    extra_args = []

    directives = re.findall(r"^//!\s*([a-zA-Z0-9_]+):\s*(.*)$", contents, flags=re.MULTILINE)
    expected_exit_code = 0

    for key, value in directives:
        if key == "extra_args":
            extra_args.extend(json.loads(value))
        if key == "exit_code":
            expected_exit_code = json.loads(value)

    command = [*args.cmd, "-Zdiag-report", *extra_args, f"main={args.file}"]

    logger.debug(f"Executing {command}")
    proc = subprocess.run(
        command,
        stdin=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        stdout=subprocess.DEVNULL,
    )

    errors = defaultdict(list)

    try:
        results = json.loads(proc.stderr)
    except:
        logger.error(proc.stderr)
        sys.exit(1)

    for error in results:
        for span in error["backtrace"]:
            if span["file"] == args.file:
                errors[span["line"] - 1].append(
                    Diagnostic(error["level"], error["kind"], error["message"])
                )
                break

    for k in errors:
        errors[k].sort()

    if args.fix:
        contents = re.sub(r"\s*// diag: .*$", "", contents, flags=re.MULTILINE)
        with open(args.file, "w") as f:
            if extra_args:
                f.write(f"//! extra_args: {json.dumps(extra_args)}\n")

            f.write(f"//! exit_code: {proc.returncode}\n")

            for line_num, s in enumerate(contents.split("\n")):
                if re.match(r"^//!\s*([a-zA-Z0-9_]+):\s*(.*)$", s):
                    continue

                f.write(s)
                if errors[line_num]:
                    diags = ", ".join(
                        f"{diag.level}({diag.kind}): {json.dumps(diag.message)}"
                        for diag in errors[line_num]
                    )
                    f.write(f"  // diag: {diags}")
                f.write("\n")
    else:
        success = True
        if proc.returncode != expected_exit_code:
            print(
                f"{args.file}: exit code mismatch ({proc.returncode} != {expected_exit_code})",
                file=sys.stderr,
            )
            success = False

        for line_num, s in enumerate(contents.split("\n")):
            if match := re.fullmatch(r"^.*\s*// diag: (.*)$", s):
                diags = list(
                    sorted(
                        Diagnostic(vals[0], vals[1], json.loads(vals[2]))
                        for vals in re.findall(
                            r'([a-z]+)\(([a-z0-9_]+)\): ("(.*?)(?<!\\)")', match[1]
                        )
                    )
                )
            else:
                diags = []

            if errors[line_num] != diags:
                print(
                    f"{args.file}:{line_num+1} expected: {errors[line_num]}, got: {diags}",
                    file=sys.stderr,
                )
                success = False

        if not success:
            sys.exit(1)


if __name__ == "__main__":
    main()
