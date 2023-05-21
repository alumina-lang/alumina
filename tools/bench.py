#!/usr/bin/env python3

"""
Simple benchmarking tool that collects timings from the compiler run multiple
times and prints the per-stage results.
"""

import sys
import re
import subprocess
import argparse

from collections import defaultdict

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "-n", "--num-runs", type=int, default=10,
        help="Number of times to run the compiler",
    )
    parser.add_argument(
        "-m", "--markdown", action="store_true", help="Output in markdown format"
    )
    parser.add_argument(
        "cmd", nargs=argparse.REMAINDER, help="Command to run the compiler"
    )
    args = parser.parse_args()

    timings = defaultdict(list)

    for i in range(args.num_runs):
        print(f"Running {i+1}/{args.num_runs}...")

        proc = subprocess.run(
            args.cmd,
            stdin=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            stdout=subprocess.DEVNULL,
        )
        if proc.returncode != 0:
            print(f"Compiler failed with code {proc.returncode}")
            sys.exit(1)

        for line in proc.stderr.decode("utf-8").splitlines():
            m = re.search(r"(\w+) took (\d+)ms", line)
            if m:
                stage = m.group(1)
                timing = int(m.group(2))
                if stage == "TOTAL" and args.markdown:
                    stage = "**TOTAL**"

                timings[stage].append(timing)

    if args.markdown:
        print(
            "| Stage | Median time (ms) | Min time (ms) | Max time (ms) | Average time (ms) | Standard deviation (ms) |"
        )
        print(
            "| --- | --: | --: | --: | --: | --: |"
        )

    for stage, times in timings.items():
        times = sorted(times)

        p50 = times[len(times) // 2]
        min = times[0]
        max = times[-1]
        avg = sum(times) / len(times)
        stddev = (sum((x - avg) ** 2 for x in times) / len(times)) ** 0.5

        if args.markdown:
            print(f"| {stage} | {p50} | {min} | {max} | {avg:.2f} | {stddev:.2f} |")
        else:
            print(
                f"{stage}: {p50}ms (min {min}ms, max {max}ms, avg {avg:.2f}ms, stddev {stddev:.2f}ms)"
            )


if __name__ == "__main__":
    main()
