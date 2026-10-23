#!/usr/bin/env python3
"""Runs the unit tests of ci/ (`test_check_*.py`), each module in a process
of its own, as many at once as there are CPUs: what
`python3 -m unittest discover -s ci -p 'test_check_*.py'` runs, a few times
faster. Exits non-zero if any module fails, printing its output.

    python3 ci/run_unit_tests.py [-j N] [PATTERN]

`PATTERN` selects the modules as `discover -p` does (default
`test_check_*.py`).
"""

import argparse
import concurrent.futures
import os
import pathlib
import re
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
CI = ROOT / "ci"
SUMMARY = re.compile(r"^Ran (\d+) tests? in", re.M)


def run(path: pathlib.Path) -> tuple[pathlib.Path, int, str, float]:
    start = time.monotonic()
    p = subprocess.run(
        [sys.executable, "-m", "unittest", "discover", "-s", "ci", "-p", path.name],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    return path, p.returncode, p.stdout, time.monotonic() - start


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("-j", "--jobs", type=int, default=os.cpu_count() or 1)
    parser.add_argument("pattern", nargs="?", default="test_check_*.py")
    args = parser.parse_args()
    # Largest first, a rough guess at the slowest, so that none starts last.
    paths = sorted(CI.glob(args.pattern), key=lambda p: -p.stat().st_size)
    if not paths:
        print(f"no module matches {args.pattern}", file=sys.stderr)
        return 1
    failed, tests = [], 0
    start = time.monotonic()
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        for path, code, out, secs in pool.map(run, paths):
            m = SUMMARY.search(out)
            tests += int(m.group(1)) if m else 0
            if code:
                failed.append(path.name)
                print(f"=== {path.name} failed ({secs:.1f}s)\n{out}", file=sys.stderr)
    print(f"Ran {tests} tests in {len(paths)} modules in {time.monotonic() - start:.1f}s")
    if failed:
        print(f"FAILED: {', '.join(failed)}", file=sys.stderr)
        return 1
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
