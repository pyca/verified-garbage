"""Measures this checkout next to OpenSSL and aws-lc-rs, every library alike,
for numbers to publish.

    python3 ci/bench_copies.py --json results.json [--benches "sha256 x25519"] [--copies 5]

`ci/bench_compare.py` compares two checkouts of this library: it takes the
fastest of several copies of each side's binary for the groups whose time
depends on where the binary's pages land (its `FRESH_COPIES`), and runs
OpenSSL and aws-lc-rs once, as a reference. That is right for finding a
slowdown of this library, and wrong for comparing the libraries: one of
them gets the best of eight draws and the others one.

This runs every benchmark selected, of every library, from `--copies` fresh
copies of the benchmark binary, one after the other (each a new file, so
new pages for all three libraries' code and tables), with Criterion's
warm-up and measurement the same for all, and reports for each benchmark
the median over the copies of Criterion's median estimate. Every copy's
time is in the results file (`samples`), and in `--csv` with the spread,
(max - min) / median, of each benchmark.

`--benches` names the benchmarks to run (`BENCHES` entries of
bench/benches/primitives/main.rs, its files' names; all of them by
default), each in a process of its own, which sets up only that one.
`--filter` is a regular expression over the benchmark ids
(`<group>/<library>/<size>`) for Criterion, e.g. `/64$`. `--features` are
the benchmark crate's (`openssl-mldsa,openssl-mlkem` with OpenSSL 3.5 or
later; `OPENSSL_DIR` and `OPENSSL_STATIC=1` in the environment build
against an OpenSSL other than the system's). `--cpu` pins the runs to
one CPU (Linux, with `taskset`).

The results file (`ci/bench_report.py`'s format, which its page charts)
records what was measured: the commit, the machine, the versions of OpenSSL
(as the binary reports it), aws-lc-rs and aws-lc-sys (bench/Cargo.lock's),
and the settings. `--out` keeps each copy's Criterion directory and output.
"""

import argparse
import csv
import json
import os
import pathlib
import platform
import shutil
import statistics
import subprocess
import sys
import time
import tomllib

import bench_report
from bench_compare import cpu_model

ROOT = pathlib.Path(__file__).resolve().parent.parent


def build(features):
    """Builds the benchmarks, returning the binary's path."""
    cmd = ["cargo", "bench", "--no-run", "--message-format=json-render-diagnostics"]
    if features:
        cmd += ["--features", features]
    out = subprocess.run(cmd, cwd=ROOT / "bench", check=True, stdout=subprocess.PIPE, text=True).stdout
    for line in out.splitlines():
        msg = json.loads(line)
        if msg.get("reason") == "compiler-artifact" and msg.get("executable") and msg["target"]["name"] == "primitives":
            return pathlib.Path(msg["executable"])
    raise SystemExit("no benchmark binary built")


def bench_names(listing):
    """The benchmarks (`BENCHES` entries) that have a benchmark id, from the
    binary's `--list` output with `VG_BENCH_NAMES` set, in its order."""
    names, bench = [], None
    for line in listing.splitlines():
        if line.endswith(": bench"):
            bench = line.removesuffix(": bench")
        elif line.endswith(": benchmark") and bench is not None and bench not in names:
            names.append(bench)
    return names


def openssl_version(listing):
    """OpenSSL's version, from the binary's output with `VG_BENCH_VERSIONS`
    set (None from a binary that does not print it)."""
    for line in listing.splitlines():
        if line.startswith("openssl: "):
            return line.removeprefix("openssl: ")
    return None


def locked(lock, name):
    """The version of the crate `name` in the parsed Cargo.lock `lock`
    (every version, comma-separated, if it has several; None without it)."""
    return ", ".join(sorted(p["version"] for p in lock.get("package", []) if p["name"] == name)) or None


def aws_lc_version(lock):
    """aws-lc-rs's and aws-lc-sys's versions in the parsed Cargo.lock `lock`
    (the version of aws-lc-sys is that of the AWS-LC it builds)."""
    rs, sys_ = locked(lock, "aws-lc-rs"), locked(lock, "aws-lc-sys")
    return f"aws-lc-rs {rs} (aws-lc-sys {sys_})" if rs and sys_ else None


def aggregate(copies):
    """Each benchmark's times over `copies` (each a list of
    `bench_report.read_criterion`'s results), as `(group, library, size)` to
    the list of its times, one per copy. A benchmark that a copy lacks is an
    error: its median would be of fewer draws than the others'."""
    times = {}
    for i, copy in enumerate(copies):
        for group, library, size, t in copy:
            times.setdefault((group, library, size), [None] * len(copies))[i] = t
    for key, ts in times.items():
        if None in ts:
            raise SystemExit(f"{'/'.join(map(str, key))}: not measured in every copy")
    return dict(sorted(times.items(), key=lambda kv: (bench_report.natural(kv[0][0]),
                                                      bench_report.natural(str(kv[0][2])), kv[0][1])))


def spread(ts):
    """How far a benchmark's times `ts` are apart: (max - min) / median."""
    return (max(ts) - min(ts)) / statistics.median(ts)


def write_csv(path, times, copies):
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["group", "library", "size", *(f"copy{i + 1}_ns" for i in range(copies)), "median_ns", "spread"])
        for (group, library, size), ts in times.items():
            w.writerow([group, library, size, *(f"{t:.3f}" for t in ts),
                        f"{statistics.median(ts):.3f}", f"{spread(ts):.4f}"])


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--json", type=pathlib.Path, required=True, help="the results file to write")
    p.add_argument("--csv", type=pathlib.Path, help="every copy's time of each benchmark, and their spread")
    p.add_argument("--out", type=pathlib.Path, default=pathlib.Path("bench-copies"),
                   help="where each copy's Criterion directory and output go")
    p.add_argument("--copies", type=int, default=5)
    p.add_argument("--benches", default="", help="space-separated; only these benchmarks (default: all)")
    p.add_argument("--filter", default="", help="a regular expression over benchmark ids, for Criterion")
    p.add_argument("--features", default="", help="the benchmark crate's features, comma-separated")
    p.add_argument("--cpu", type=int, help="pin the runs to this CPU (Linux)")
    p.add_argument("--warm-up-time", type=float, default=1)
    p.add_argument("--measurement-time", type=float, default=2)
    p.add_argument("--meta", action="append", metavar="KEY=VALUE", help="a field of the run (repeatable)")
    args = p.parse_args(argv)
    if args.copies < 1:
        p.error("--copies must be at least 1")
    if args.out.exists() and any(args.out.iterdir()):
        p.error(f"{args.out} is not empty: its results would be read as this run's")

    binary = build(args.features)
    started = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    env = {**os.environ, "VG_BENCHES": args.benches}
    listing = subprocess.run([binary, "--bench", "--list"], env={**env, "VG_BENCH_NAMES": "1"},
                             check=True, stdout=subprocess.PIPE, text=True).stdout
    names = bench_names(listing)
    if not names:
        raise SystemExit("no benchmark selected")
    versions = subprocess.run([binary, "--bench", "--list"], env={**env, "VG_BENCH_VERSIONS": "1"},
                              check=True, stdout=subprocess.PIPE, text=True).stdout
    pin = ["taskset", "-c", str(args.cpu)] if args.cpu is not None else []

    for n in range(1, args.copies + 1):
        d = args.out / f"copy-{n}"
        d.mkdir(parents=True)
        # A new file: the page cache holds a file's pages by inode, so this
        # copy's code and tables are read into newly chosen physical pages.
        copy = d / "primitives"
        shutil.copyfile(binary, copy)
        copy.chmod(0o755)
        for name in names:
            print(f"copy {n}/{args.copies}: {name}", file=sys.stderr)
            cmd = [*pin, str(copy.resolve()), "--bench", "--warm-up-time", str(args.warm_up_time),
                   "--measurement-time", str(args.measurement_time)]
            with open(d / f"{name}.out", "w") as out:
                subprocess.run(cmd + ([args.filter] if args.filter else []), check=True, stdout=out,
                               stderr=subprocess.STDOUT,
                               env={**os.environ, "VG_BENCHES": name, "CRITERION_HOME": str((d / "criterion").resolve())})
        copy.unlink()

    times = aggregate([bench_report.read_criterion(args.out / f"copy-{n}" / "criterion")
                       for n in range(1, args.copies + 1)])
    if not times:
        raise SystemExit("nothing was measured: does --filter match a benchmark id?")
    commit = bench_report.commit_of(ROOT)
    results = [bench_report.record(group, library, size, statistics.median(ts), samples=ts, commit=commit)
               for (group, library, size), ts in times.items()]
    context = {
        "arch": bench_report.arch_name(),
        "os": platform.system(),
        "cpu": cpu_model(),
        "cpu_features": os.environ.get("VG_CPU_FEATURES", ""),
        "ref": bench_report.git(ROOT, "rev-parse", "--abbrev-ref", "HEAD"),
        "date": started,
        "source": "local",
        "openssl": openssl_version(versions),
        "aws_lc": aws_lc_version(tomllib.loads((ROOT / "bench/Cargo.lock").read_text())),
        "method": f"Criterion, {args.warm_up_time:g} s warm-up, {args.measurement_time:g} s measurement; "
                  f"median of {args.copies} fresh copies of the binary",
        **bench_report.parse_meta(args.meta),
    }
    args.json.write_text(json.dumps(bench_report.document(context, results), indent=1) + "\n")
    if args.csv:
        write_csv(args.csv, times, args.copies)
    spreads = sorted(spread(ts) for ts in times.values())
    print(f"{args.json}: {len(results)} benchmarks, the median of {args.copies} copies; "
          f"their spread: median {statistics.median(spreads):.1%}, largest {spreads[-1]:.1%}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
