#!/usr/bin/env python3
"""Compare one integration test in two checkouts, with interleaved native runs."""

import argparse
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import time


def build(root, target, env):
    result = subprocess.run(
        ["cargo", "test", "--locked", "--test", "tests", "--no-run", "--message-format=json"],
        cwd=root, env={**env, "CARGO_TARGET_DIR": str(target)},
        check=True, text=True, stdout=subprocess.PIPE,
    )
    binaries = []
    for line in result.stdout.splitlines():
        item = json.loads(line)
        if item.get("reason") == "compiler-artifact" and item.get("executable") and item["target"]["name"] == "tests":
            binaries.append(Path(item["executable"]))
    if len(binaries) != 1:
        raise RuntimeError(f"expected one integration-test binary, found {binaries}")
    return binaries[0]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base", type=Path)
    parser.add_argument("head", type=Path)
    parser.add_argument("--test", required=True)
    parser.add_argument("--vectors", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=6)
    parser.add_argument("--output", type=Path, default=Path("test-compare"))
    parser.add_argument("--summary", type=Path)
    args = parser.parse_args()
    if args.rounds < 2:
        parser.error("use at least two interleaved comparison rounds")
    vectors = args.vectors.resolve()
    if not (vectors / "testvectors_v1").is_dir():
        parser.error("--vectors must contain testvectors_v1")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    # Match CI's test build. The assembly dependencies retain Cargo.toml's
    # opt-level=3; parsing, test setup and teardown stay in the measured scope.
    env = {**os.environ, "CARGO_PROFILE_TEST_DEBUG": "0", "WYCHEPROOF_ROOT": str(vectors)}
    roots = {"base": args.base.resolve(), "head": args.head.resolve()}
    binaries = {side: build(root, output / f"target-{side}", env) for side, root in roots.items()}
    command = [args.test, "--exact", "--test-threads=1"]
    for side, binary in binaries.items():
        listing = subprocess.check_output([str(binary), args.test, "--exact", "--list"], env=env, text=True)
        if f"{args.test}: test" not in listing or "1 test, 0 benchmarks" not in listing:
            raise RuntimeError(f"{side}: expected exactly the requested test: {listing}")
    samples = {"base": [], "head": []}

    def run(side, label):
        start = time.perf_counter()
        result = subprocess.run([str(binaries[side]), *command], env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True)
        elapsed = time.perf_counter() - start
        (output / f"{label}-{side}.log").write_text(result.stdout)
        # A skipped Wycheproof test returns success too; insist that vectors
        # were enabled above and that the requested test actually ran.
        if "1 passed; 0 failed" not in result.stdout:
            raise RuntimeError(f"{side}: unexpected test result: {result.stdout}")
        print(f"{label} {side}: {elapsed:.6f} s", flush=True)
        return elapsed

    for side in roots:
        run(side, "warmup")
    for round_index in range(args.rounds):
        order = ("base", "head") if round_index % 2 == 0 else ("head", "base")
        for side in order:
            samples[side].append(run(side, f"round-{round_index + 1}"))
    results = {
        "test": args.test, "metric": "native elapsed seconds, complete test process",
        "revisions": {side: subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
                      for side, root in roots.items()},
        "vectors_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=vectors, text=True).strip(),
        "platform": platform.platform(), "logical_cpus": os.cpu_count(),
        "available_cpus": subprocess.check_output(["nproc"], text=True).strip(),
        "cpuinfo": Path("/proc/cpuinfo").read_text().split("\n\n", 1)[0],
        "affinity": sorted(os.sched_getaffinity(0)),
        "rustc": subprocess.check_output(["rustc", "-vV"], text=True),
        "rustflags": env.get("RUSTFLAGS", ""), "profile": "test; CARGO_PROFILE_TEST_DEBUG=0",
        "samples": samples,
    }
    stats = {side: {"median": statistics.median(values), "mean": statistics.mean(values),
                    "stdev": statistics.stdev(values), "min": min(values), "max": max(values)}
             for side, values in samples.items()}
    results["statistics"] = stats
    delta = 100 * (stats["base"]["median"] - stats["head"]["median"]) / stats["base"]["median"]
    results["median_elapsed_reduction_percent"] = delta
    (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    lines = [f"### `{args.test}`", "", f"{args.rounds} interleaved samples per revision, after one warm-up each.",
             "", "| Revision | Median (s) | Mean (s) | Std. dev. (s) | Min–max (s) |",
             "|---|---:|---:|---:|---:|"]
    for side, stat in stats.items():
        lines.append(f"| {side} `{results['revisions'][side][:12]}` | {stat['median']:.4f} | {stat['mean']:.4f} | "
                     f"{stat['stdev']:.4f} | {stat['min']:.4f}–{stat['max']:.4f} |")
    lines += ["", f"Median elapsed-time reduction: **{delta:.2f}%**.", "",
              "Includes parsing, all key sizes and checks, the test's parallel workers, startup and teardown.",
              f"Runner: `{results['platform']}`, {results['available_cpus']} available CPUs.",
              f"Wycheproof: `{results['vectors_revision']}`.", ""]
    summary = "\n".join(lines)
    print(summary)
    if args.summary:
        with args.summary.open("a") as stream:
            stream.write(summary)


if __name__ == "__main__":
    main()
