#!/usr/bin/env python3
"""rustls-bench's results as a results file of ci/bench_report.py's format.

    python3 bench/results.py --start DIR
    python3 bench/results.py DIR [-o FILE] [--meta KEY=VALUE ...]

`--start` records a run's context in DIR/context.json: this machine, the
checkout's commit, the time, and the CPU features the libraries are
restricted to. bench/run.sh records it before it runs rustls-bench, so
that the results file describes what was measured, wherever and whenever
it is written.

Without `--start`, it reads bench/run.sh's output in DIR
(`rustls-bench-<provider>-<round>.tsv`) and that context, and writes, for
each scenario and provider, the median of its runs, as a time:
nanoseconds per handshake, or per megabyte for bulk transfers.
(rustls-bench runs a bulk transfer once for each key type its suite
allows, which its rows do not name: those are runs of the same scenario.)
A scenario's size is its `max_fragment_size` (bulk) or its resumption
(handshakes), and its other parameters are its group, e.g.
`rustls-bulk-TLSv1_3-TLS13_AES_128_GCM_SHA256-send` of size 10000, or
`rustls-handshakes-TLSv1_3-EcdsaP256-TLS13_AES_128_GCM_SHA256-client-mutual`
of size `tickets`. `python3 ci/bench_report.py html` charts it, each group
relative to aws-lc-rs.
"""

import argparse
import collections
import json
import os
import pathlib
import platform
import re
import statistics
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "ci"))

import bench_report  # noqa: E402
from bench_compare import cpu_model  # noqa: E402

FILE = re.compile(r"rustls-bench-(?P<library>.+)-(?P<round>\d+)\.tsv")


def scenario(fields):
    """A rustls-bench row's group and size, from its parameters."""
    if fields[0] == "bulk":
        *params, fragment, direction = fields
        size = bench_report.bench_size(fragment.removeprefix("max_fragment_size:"))
        return "-".join(["rustls", *params, direction]), size
    *params, resumption = fields
    return "-".join(["rustls", *params]), resumption


def read(out):
    """Each scenario's rates (per second) in DIR, by (group, size, library)."""
    rates = collections.defaultdict(list)
    for path in sorted(pathlib.Path(out).iterdir()):
        m = FILE.fullmatch(path.name)
        if not m:
            continue
        for line in path.read_text().splitlines():
            *fields, rate, _unit = line.split("\t")
            group, size = scenario(fields)
            rates[group, size, m["library"]].append(float(rate))
    return rates


def context():
    """The context of a run starting now, with the checkout's commit."""
    return {
        "arch": bench_report.arch_name(),
        "os": platform.system(),
        "cpu": cpu_model(),
        "cpu_features": os.environ.get("VG_CPU_FEATURES", ""),
        "openssl_ia32cap": os.environ.get("OPENSSL_ia32cap"),
        "ref": bench_report.git(ROOT, "rev-parse", "--abbrev-ref", "HEAD"),
        "commit": bench_report.commit_of(ROOT),
        "date": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "source": "local",
    }


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("out", type=pathlib.Path, help="bench/run.sh's output directory")
    p.add_argument("--start", action="store_true", help="record the context of a run starting now")
    p.add_argument("-o", "--output", type=pathlib.Path)
    p.add_argument("--meta", action="append", metavar="KEY=VALUE", help="a field of the run (repeatable)")
    args = p.parse_args(argv)

    recorded = args.out / "context.json"
    if args.start:
        args.out.mkdir(parents=True, exist_ok=True)
        recorded.write_text(json.dumps(context(), indent=1) + "\n")
        return 0
    if not recorded.is_file():
        p.error(f"{recorded}: no context recorded (bench/run.sh records it with --start)")
    run = json.loads(recorded.read_text())
    commit = run.pop("commit", None)
    results = []
    for (group, size, library), rates in read(args.out).items():
        times = [1e9 / r for r in rates]
        results.append(bench_report.record(group, library, size, statistics.median(times),
                                           samples=times, commit=commit))
    if not results:
        p.error(f"{args.out}: no rustls-bench results")
    doc = bench_report.document({**run, **bench_report.parse_meta(args.meta)}, results)
    output = args.output or args.out / "rustls-bench.json"
    output.write_text(json.dumps(doc, indent=1) + "\n")
    print(f"{output}: {len(results)} results", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
