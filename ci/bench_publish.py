r"""Benchmarks this checkout against OpenSSL and aws-lc-rs, for numbers to
publish: every run, their results and the report, in one command.

    python3 ci/bench_publish.py OUT [options] BENCH[=FILTER] ... [rustls]

Each BENCH is a benchmark of bench/benches/primitives (a file's name, a
`BENCHES` entry of its main.rs), with, after `=`, a regular expression over
its benchmark ids (`<group>/<library>/<size>`) for Criterion; `rustls` is
the rustls provider's suite (crates/rustls-verified-garbage/bench/run.sh),
against aws-lc-rs, of `--rustls-rounds` rounds. The
`benchmarking` skill has the command of the published run.

Unlike `ci/bench_compare.py`, which looks for a slowdown of this library,
every library is measured alike. The benchmark binary is copied to
`--copies` new files, one after the other (which physical pages a file's
code and tables are read into moves some benchmarks by several percent, for
every library: see bench_compare.py), and each copy runs every benchmark
selected, of every library, with Criterion's default 100 samples after
`--warm-up-time` and over `--measurement-time`. A benchmark's time is the
median, over the copies, of Criterion's median estimate.

What is measured:

* This checkout, with every CPU feature it detects.
* The OpenSSL that the `openssl` crate finds: `OPENSSL_DIR`'s (linked
  statically with `OPENSSL_STATIC=1`), which is built beforehand, or the
  system's. `--features` are the benchmark crate's, which add the
  comparisons that need a newer OpenSSL (`openssl-mlkem`, ...).
* The aws-lc-rs (and aws-lc-sys, so AWS-LC) of bench/Cargo.lock. The
  rustls checkout's is set to the same versions.

Run it on a machine doing nothing else, with `--cpu` (Linux), and check
`run.log`'s load averages. It needs cargo, a C compiler and cmake. In OUT:

    primitives.json, rustls.json   results files (ci/bench_report.py's format)
    primitives.csv                 every copy's time of each benchmark, and
                                   their spread, (max - min) / median
    report.html                    `ci/bench_report.py html` of them, with
                                   this command's `--rename`s, `--chart`s
                                   and `--title`
    environment.txt                the machine, and every version measured
    run.log                        each run's time and the load average
    raw/                           each copy's Criterion directory and
                                   output; rustls-bench's rows
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
import bench_run

ROOT = pathlib.Path(__file__).resolve().parent.parent
RUSTLS = ROOT / "crates/rustls-verified-garbage"

def sh(*cmd, cwd=None, env=None, out=None):
    """Runs `cmd`, which must succeed, returning its output (or, with `out`,
    writing its output and errors there)."""
    print("+", *cmd, file=sys.stderr)
    cmd = [str(c) for c in cmd]
    if out is None:
        return subprocess.run(cmd, cwd=cwd, env=env, check=True, stdout=subprocess.PIPE, text=True).stdout
    with open(out, "a") as f:
        subprocess.run(cmd, cwd=cwd, env=env, check=True, stdout=f, stderr=subprocess.STDOUT)


def locked(lock, name):
    """The version of the crate `name` in the Cargo.lock at `lock`: the one
    version, since two would be two libraries under one name."""
    versions = [p["version"] for p in tomllib.loads(lock.read_text())["package"] if p["name"] == name]
    if len(versions) != 1:
        raise SystemExit(f"{lock}: {name} is locked at {versions or 'no version'}, not at one")
    return versions[0]


def primitives(binary, benches, args, raw, log):
    """Runs `benches` (name to Criterion filter) from each copy of `binary`,
    returning each benchmark's times, one per copy."""
    pin = ["taskset", "-c", args.cpu] if args.cpu is not None else []
    times = {}
    for n in range(args.copies):
        d = raw / f"copy-{n + 1}"
        d.mkdir(parents=True)
        copy = bench_run.fresh_copy(binary, d / "primitives")
        for name, pattern in benches.items():
            log(f"copy {n + 1}/{args.copies}: {name}")
            proc = bench_run.criterion(copy, d / "criterion", args.warm_up_time, args.measurement_time,
                                       [pattern] if pattern else [], {**os.environ, "VG_BENCHES": name}, pin)
            (d / f"{name}.out").write_text(proc.stdout + proc.stderr)
            if proc.returncode:
                raise SystemExit(f"{name}: the benchmarks failed: see {d / f'{name}.out'}")
        copy.unlink()
        for group, library, size, t in bench_report.read_criterion(d / "criterion"):
            times.setdefault((group, library, size), []).append(t)
    log("primitives: done")
    short = [key for key, ts in times.items() if len(ts) != args.copies]
    if short or not times:
        raise SystemExit(f"not measured in every copy: {short or 'anything'}")
    return dict(sorted(times.items(), key=lambda kv: (bench_report.natural(kv[0][0]),
                                                      bench_report.natural(str(kv[0][2])), kv[0][1])))


def rustls(args, out, lock, env, log):
    """Runs the rustls provider's benchmarks, with the aws-lc-rs of `lock`,
    returning the results file."""
    checkout = ROOT / "target/rustls"
    if not checkout.is_dir():
        sh(RUSTLS / "rustls/setup.sh", checkout)
    sh("cargo", "update", "-p", "aws-lc-rs", "--precise", locked(lock, "aws-lc-rs"), cwd=checkout)
    sh("cargo", "update", "-p", "aws-lc-sys", "--precise", locked(lock, "aws-lc-sys"), cwd=checkout)
    log("rustls")
    sh(RUSTLS / "bench/run.sh", args.rustls_rounds, out=out / "raw/rustls.out",
       env={**env, "BENCH_OUT": str(out / "raw/rustls"), **({"BENCH_CPU": args.cpu} if args.cpu is not None else {})})
    log("rustls: done")
    # Again, to name what aws-lc-rs was measured.
    sh(sys.executable, RUSTLS / "bench/results.py", out / "raw/rustls",
       "--meta", f"aws_lc=aws-lc-rs {locked(lock, 'aws-lc-rs')} (aws-lc-sys {locked(lock, 'aws-lc-sys')})")
    return out / "raw/rustls/rustls-bench.json"


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("out", type=pathlib.Path, help="a new directory for everything the run writes")
    p.add_argument("benches", nargs="+", metavar="BENCH[=FILTER]", help="benchmarks to run, or `rustls`")
    p.add_argument("--cpu", help="pin every run to this CPU (Linux)")
    p.add_argument("--copies", type=int, default=5)
    p.add_argument("--warm-up-time", default="1")
    p.add_argument("--measurement-time", default="2")
    p.add_argument("--rustls-rounds", default="5")
    p.add_argument("--features", default="", help="the benchmark crate's features, comma-separated")
    p.add_argument("--title", help="the report's (default: the libraries' versions and the CPU)")
    p.add_argument("--rename", action="append", default=[], metavar="PATTERN=GROUP/SIZE",
                   help="as `ci/bench_report.py html`'s, for the report (repeatable)")
    p.add_argument("--chart", action="append", default=[], metavar="PATTERNS",
                   help="as `ci/bench_report.py html`'s, for the report (repeatable)")
    args = p.parse_args(argv)
    out = args.out.resolve()
    if (out / "raw").exists():
        p.error(f"{out} has a run's results already")
    benches = dict(b.partition("=")[::2] for b in args.benches)
    with_rustls = benches.pop("rustls", None) is not None
    (out / "raw").mkdir(parents=True)

    def log(what):
        load = os.getloadavg() if hasattr(os, "getloadavg") else ()
        line = f"{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())} {what} load={' '.join(f'{x:.2f}' for x in load)}"
        print(line, file=sys.stderr)
        with open(out / "run.log", "a") as f:
            f.write(line + "\n")

    # The `openssl` command of the OpenSSL that is linked, for its version.
    env, tool = dict(os.environ), "openssl"
    if prefix := os.environ.get("OPENSSL_DIR"):
        tool = pathlib.Path(prefix) / "bin/openssl"
        env["LD_LIBRARY_PATH"] = f"{prefix}/lib:{prefix}/lib64"
    lock = ROOT / "bench/Cargo.lock"
    aws_lc = f"aws-lc-rs {locked(lock, 'aws-lc-rs')} (aws-lc-sys {locked(lock, 'aws-lc-sys')})"
    openssl_version = sh(tool, "version", env=env).strip()
    context = {
        "arch": bench_report.arch_name(),
        "os": platform.system(),
        "cpu": bench_run.cpu_model(),
        "cpu_features": "",
        "ref": bench_report.git(ROOT, "rev-parse", "--abbrev-ref", "HEAD"),
        "date": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "source": "local",
        "openssl": openssl_version,
        "aws_lc": aws_lc,
        "method": f"Criterion, {args.warm_up_time} s warm-up, {args.measurement_time} s measurement;"
                  f" median of {args.copies} fresh copies of the binary",
    }
    commit = bench_report.commit_of(ROOT)
    (out / "environment.txt").write_text("\n".join([
        f"verified-garbage: {commit} ({bench_report.git(ROOT, 'status', '--short') or 'clean'})",
        f"cpu: {context['cpu']}",
        f"platform: {platform.platform()}",
        f"aws-lc: {aws_lc}",
        f"rust: {sh('rustc', '-vV')}",
        f"cc: {sh('cc', '--version')}",
        f"openssl: {sh(tool, 'version', '-a', env=env)}",
    ]))
    shutil.copy(lock, out / "bench-Cargo.lock")

    files = []
    if benches:
        times = primitives(bench_run.build(ROOT / "bench", env, args.features), benches, args, out / "raw", log)
        results = [bench_report.record(group, library, size, statistics.median(ts), samples=ts, commit=commit)
                   for (group, library, size), ts in times.items()]
        (out / "primitives.json").write_text(json.dumps(bench_report.document(context, results), indent=1) + "\n")
        files.append(out / "primitives.json")
        with open(out / "primitives.csv", "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["group", "library", "size", *(f"copy{i + 1}_ns" for i in range(args.copies)),
                        "median_ns", "spread"])
            for (group, library, size), ts in times.items():
                median = statistics.median(ts)
                w.writerow([group, library, size, *(f"{t:.3f}" for t in ts), f"{median:.3f}",
                            f"{(max(ts) - min(ts)) / median:.4f}"])
    if with_rustls:
        shutil.copy(rustls(args, out, lock, env, log), out / "rustls.json")
        shutil.copy(ROOT / "target/rustls/Cargo.lock", out / "rustls-Cargo.lock")
        files.append(out / "rustls.json")

    title = args.title or f"verified-garbage, {openssl_version.split(' (')[0]} and {aws_lc}: {context['cpu']}"
    return bench_report.main(["html", *map(str, files), "-o", str(out / "report.html"), "--title", title,
                              *(a for r in args.rename for a in ("--rename", r)),
                              *(a for c in args.chart for a in ("--chart", c))])


if __name__ == "__main__":
    sys.exit(main())
