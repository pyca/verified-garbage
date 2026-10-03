"""Compares the performance of two checkouts of this repository.

    python3 ci/bench_compare.py BASE HEAD [--summary FILE]

Both are built with HEAD's `bench/` crate (copied into BASE, so the two run
the same benchmark code against different library code); if that doesn't
build against BASE (it benchmarks an API BASE doesn't have yet), BASE uses
its own `bench/` crate, and HEAD's other benchmarks show as new. Their benchmark
binaries are run alternately on this machine, a few rounds each, keeping the
fastest time of each benchmark on each side: interleaving cancels out slow
drift in the machine's speed, and the minimum discards runs slowed by
interference, both of which are common on shared CI runners.

Writes a Markdown table of the results to stdout (and appends it to
`--summary`, e.g. `$GITHUB_STEP_SUMMARY`), and exits with status 1 if any
verified-garbage benchmark got slower by more than `--threshold`.

OpenSSL's code is the same on both sides, so its benchmarks run just once,
with HEAD's binary, as a reference point for HEAD's times; and only without
`VG_CPU_FEATURES`, which does not change OpenSSL's code either.

`VG_CPU_FEATURES` in the environment (see src/cpu.rs) restricts the CPU
features both sides use, and is named in the report. Each side is passed
only the features its own src/cpu.rs knows (base may predate one), since it
cannot use the others anyway.

`--modules` runs only the benchmarks of those library modules (see
`bench_arches.py`), and `--shard i/n` only the i-th of n shares of them,
whose groups (`<primitive>`s) are dealt out by HEAD's list of them, balanced
by their number of benchmarks.
"""

import argparse
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys

from bench_arches import bench_catalog

# Criterion filters (regexes over benchmark ids, which are
# `<primitive>/<library>/<bytes>`, see bench/benches/primitives/main.rs).
VG = "verified-garbage"
OPENSSL = "openssl"


# Every build shares one target directory, so the dependencies (criterion,
# rust-openssl), which are the same on both sides, are compiled only once.
TARGET = pathlib.Path("bench-target").resolve()


def build(bench):
    """Builds the benchmark crate `bench`, returning the binary's path."""
    out = subprocess.run(
        [
            "cargo",
            "bench",
            "--no-run",
            "--message-format=json-render-diagnostics",
        ],
        cwd=bench,
        env={**os.environ, "CARGO_TARGET_DIR": str(TARGET)},
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout
    for line in out.splitlines():
        msg = json.loads(line)
        if msg.get("reason") == "compiler-artifact" and msg.get("executable"):
            if msg["target"]["name"] == "primitives":
                # A copy, which the next build can't overwrite.
                binary = TARGET / f"primitives-{len(list(TARGET.glob('primitives-*')))}"
                shutil.copy2(msg["executable"], binary)
                return str(binary)
    raise RuntimeError(f"no benchmark binary built in {bench}")


def build_base(base, head):
    """Builds BASE's benchmarks (see the module docstring), returning the
    binary's path and a note on which benchmark code it runs, or no path
    if neither builds."""
    if base == head:
        return build(head / "bench"), None, head
    # A sibling of BASE's own `bench/`, so its `path = ".."` is BASE too.
    copy = base / "bench-head"
    shutil.rmtree(copy, ignore_errors=True)
    shutil.copytree(head / "bench", copy, ignore=shutil.ignore_patterns("target"))
    try:
        return build(copy), None, head
    except subprocess.CalledProcessError:
        pass
    if (base / "bench").is_dir():
        try:
            return build(base / "bench"), "Head's benchmarks don't build against base, so base ran its own.", base
        except subprocess.CalledProcessError:
            pass
    return None, "Base has no benchmarks that build, so head ran alone.", base


NAMES = re.compile(r"const NAMES: \[&str; \d+\] = \[(.*?)\];", re.DOTALL)


def cpu_features(checkout):
    """`VG_CPU_FEATURES` without the features `checkout`'s src/cpu.rs does
    not know (which it rejects)."""
    features = os.environ.get("VG_CPU_FEATURES", "")
    if features in ("", "none"):
        return features
    known = re.findall(r'"([^"]+)"', NAMES.search((checkout / "src/cpu.rs").read_text())[1])
    return ",".join(f for f in features.split(",") if f in known) or "none"


def selected_modules(checkout, requested):
    if not requested.strip():
        return ""  # Explicit full-suite selection.
    catalog = bench_catalog(root=str(checkout))
    if catalog is None:
        return None
    return " ".join(sorted(set(requested.split()) & set().union(*catalog.values()))) or None


def list_groups(binary, modules):
    """The benchmark groups (`<primitive>`s) of verified-garbage that
    `binary` runs for `modules`, with how many benchmarks each has."""
    out = subprocess.run(
        [binary, "--bench", "--list", f"/{VG}/"],
        env={**os.environ, "VG_BENCH_MODULES": modules},
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout
    groups = {}
    for line in out.splitlines():
        if line.endswith(": benchmark"):
            group = line.split("/", 1)[0]
            groups[group] = groups.get(group, 0) + 1
    return groups


def shard_groups(groups, shard, shards):
    """The groups of the `shard`-th (from 1) of `shards` shares: each, largest
    first, goes to the share with the fewest benchmarks so far."""
    load = [0] * shards
    mine = []
    for group in sorted(groups, key=lambda g: (-groups[g], g)):
        i = load.index(min(load))
        load[i] += groups[group]
        if i == shard - 1:
            mine.append(group)
    return sorted(mine)


def run(binary, home, library, args, checkout, modules, groups=None):
    """Runs the benchmarks of `checkout` once (only those of `groups`, if
    given), returning each one's median time (ns)."""
    pattern = f"/{library}/"
    if groups is not None:
        pattern = f"^(?:{'|'.join(map(re.escape, groups))})/{library}/"
    subprocess.run(
        [
            binary,
            "--bench",
            "--noplot",
            "--warm-up-time",
            str(args.warm_up_time),
            "--measurement-time",
            str(args.measurement_time),
            # Only the median is used, not the bootstrapped confidence
            # intervals, whose default 100000 resamples cost more than a
            # short measurement.
            "--nresamples",
            "1000",
            pattern,
        ],
        env={
            **os.environ,
            "CRITERION_HOME": str(home),
            "VG_BENCH_MODULES": modules,
            "VG_CPU_FEATURES": cpu_features(checkout),
        },
        check=True,
        stdout=subprocess.DEVNULL,
    )
    times = {}
    for est in home.glob(f"*/{library}/*/new/estimates.json"):
        primitive, _, size = est.relative_to(home).parts[:3]
        times[primitive, int(size)] = json.loads(est.read_text())["median"]["point_estimate"]
    return times


def vs_openssl(ours, theirs):
    """How head's time compares with OpenSSL's, in words."""
    if ours > theirs * 1.05:
        return f"{ours / theirs:.1f}× slower"
    if theirs > ours * 1.05:
        return f"{theirs / ours:.1f}× faster"
    return "about the same"


def fmt_time(ns):
    for unit, scale in (("ms", 1e6), ("µs", 1e3)):
        if ns >= scale:
            return f"{ns / scale:.2f} {unit}"
    return f"{ns:.0f} ns"


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("base", type=pathlib.Path)
    p.add_argument("head", type=pathlib.Path)
    p.add_argument("--summary", type=pathlib.Path)
    p.add_argument("--rounds", type=int, default=3)
    p.add_argument("--threshold", type=float, default=0.35)
    p.add_argument("--warm-up-time", type=float, default=0.2)
    p.add_argument("--measurement-time", type=float, default=0.5)
    p.add_argument("--work-dir", type=pathlib.Path, default=pathlib.Path("bench-compare"))
    p.add_argument("--modules", default="", help="space-separated; only benchmark these modules")
    p.add_argument("--shard", default="", help="i/n: only the i-th of n shares of the benchmarks")
    args = p.parse_args()
    shard, shards = map(int, (args.shard or "1/1").split("/"))
    if not 1 <= shard <= shards:
        p.error("--shard must be i/n with 1 <= i <= n")

    base, head = args.base.resolve(), args.head.resolve()
    modules = {"head": selected_modules(head, args.modules), "base": selected_modules(base, args.modules)}
    if modules["head"] is None or (args.modules and set(modules["head"].split()) != set(args.modules.split())):
        p.error("head's benchmark registry does not use the selected modules")
    binaries = {"head": build(head / "bench"), "base": None}
    note = "Base has no selected benchmarks; head/OpenSSL results are new."
    if modules["base"] is not None:
        binaries["base"], note, source = build_base(base, head)
        if binaries["base"] is not None:
            modules["base"] = selected_modules(source, args.modules)

    # Both sides run the same groups, which head's list of them decides.
    groups = None
    if shards > 1:
        groups = shard_groups(list_groups(binaries["head"], modules["head"]), shard, shards)

    shutil.rmtree(args.work_dir, ignore_errors=True)
    best = {"base": {}, "head": {}}
    for r in range(args.rounds):
        # Alternate which side goes first, so neither always runs warmer.
        for side in ("base", "head") if r % 2 == 0 else ("head", "base"):
            if binaries[side] is None:
                continue
            print(f"round {r + 1}/{args.rounds}: {side}", file=sys.stderr)
            checkout = base if side == "base" else head
            times = run(binaries[side], args.work_dir.resolve() / f"{side}-{r}", VG, args, checkout, modules[side],
                        groups)
            for bench_id, t in times.items():
                best[side][bench_id] = min(t, best[side].get(bench_id, t))
    cpu_features = os.environ.get("VG_CPU_FEATURES", "")
    openssl = {}
    if not cpu_features:
        print("OpenSSL", file=sys.stderr)
        openssl = run(binaries["head"], args.work_dir.resolve() / "openssl", OPENSSL, args, head, modules["head"],
                      groups)

    title = ", ".join([*([f"VG_CPU_FEATURES={cpu_features}"] if cpu_features else []),
                       *([f"shard {shard}/{shards}"] if shards > 1 else [])])
    lines = [
        f"## Benchmarks ({title})" if title else "## Benchmarks",
        "",
        f"Fastest of {args.rounds} interleaved runs of each side on this runner;"
        f" a slowdown of more than {args.threshold:.0%} fails."
        + (" OpenSSL (through rust-openssl) ran once, for reference." if not cpu_features
           else " OpenSSL ran only in the configuration without VG_CPU_FEATURES."),
        *(
            [
                f"Changed modules: {args.modules}. Only the benchmarks that use them ran"
                ". Base received only modules present in its benchmark registry."
            ]
            if args.modules.strip()
            else []
        ),
        *([f"{note}"] if note else []),
        "",
        "| Benchmark | Base | Head | Change | OpenSSL | Head vs OpenSSL |",
        "|---|--:|--:|--:|--:|--:|",
    ]
    regressions = []
    for primitive, size in sorted(best["head"]):
        bench_id = f"{primitive}/{size}"
        b, h = best["base"].get((primitive, size)), best["head"][primitive, size]
        if b is None:
            change = "new"
        else:
            change = f"{h / b - 1:.1%} slower" if h > b else f"{1 - h / b:.1%} faster"
            if h / b - 1 > args.threshold:
                regressions.append(bench_id)
                change += " 🚨"
        o = openssl.get((primitive, size))
        vs = vs_openssl(h, o) if o else "–"
        o = fmt_time(o) if o else "–"
        b = fmt_time(b) if b else "–"
        lines.append(f"| `{bench_id}` | {b} | {fmt_time(h)} | {change} | {o} | {vs} |")
    lines.append("")
    if regressions:
        lines.append(f"🚨 {len(regressions)} benchmark(s) slowed down by more than {args.threshold:.0%}.")
    else:
        lines.append(f"No benchmark slowed down by more than {args.threshold:.0%}.")
    report = "\n".join(lines) + "\n"

    print(report)
    if args.summary:
        with args.summary.open("a") as f:
            f.write(report)
    return 1 if regressions else 0


if __name__ == "__main__":
    sys.exit(main())
