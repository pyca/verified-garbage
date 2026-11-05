#!/usr/bin/env python3
"""Interleave preserved VG binaries against OpenSSL 4.x with matched x86 masks.

Build bench/ with OPENSSL_DIR and OPENSSL_STATIC=1 first. The benchmark itself
prints its linked OpenSSL version; --openssl must name the matching CLI build.
Each binary must use the same AES-CBC benchmark source and Criterion settings.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import statistics
import subprocess

# LV0: CPUID.1 EDX:ECX; LV1: CPUID.7.0 EBX:ECX. Clear AVX or SSSE3
# when VG cannot select them; a zero LV1 also zeroes subsequent vectors.
# Positive masks only retain features detected on this CPU (checked below).
PROFILES = {
    "scalar": ("none", "~0x1200020000000000:0"),
    "aesni": ("aes", "~0x1000020000000000:0"),
    "aesni-avx2": ("aes,ssse3,avx,avx2,bmi1,bmi2,adx", ":0x80128"),
    "vaes256": ("aes,avx,avx2,vaes", "~0x20000000000:0x20000000020"),
    "vaes512f": ("aes,avx,avx2,vaes,avx512f", "~0x20000000000:0x20000010020"),
    "native": (None, None),
}


def capture(command, env):
    return subprocess.check_output(command, env=env, text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", action="append", required=True, metavar="LABEL=PATH")
    parser.add_argument("--openssl", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--profiles", nargs="+", choices=PROFILES, default=["aesni", "vaes256", "native"])
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--nresamples", type=int, default=10000)
    parser.add_argument("--samples", type=int, default=40)
    parser.add_argument("--measurement-time", type=float, default=0.5)
    parser.add_argument("--warm-up-time", type=float, default=0.1)
    parser.add_argument("--cpu", type=int, help="optionally pin both libraries to one allowed CPU")
    parser.add_argument("--filter", default="^aes-cbc-")
    args = parser.parse_args()
    if args.repeats < 1 or args.samples < 10:
        parser.error("need at least one repetition and ten samples")
    if args.cpu is not None:
        os.sched_setaffinity(0, {args.cpu})
    binaries = {}
    for entry in args.binary:
        label, separator, path = entry.partition("=")
        if not separator or not label or label in binaries or Path(label).name != label:
            parser.error("--binary requires a unique simple LABEL=PATH")
        binaries[label] = Path(path).resolve(strict=True)
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    for name in ["OPENSSL_ia32cap", "VG_CPU_FEATURES"]:
        env.pop(name, None)
    version = capture([str(args.openssl), "version", "-a"], env)
    if not version.startswith("OpenSSL 4."):
        parser.error("--openssl must be an OpenSSL 4.x build")
    cpuinfo = Path("/proc/cpuinfo").read_text()
    flags = set(next(line for line in cpuinfo.splitlines() if line.startswith("flags")).split(":", 1)[1].split())
    required = {
        "scalar": set(), "native": set(), "aesni": {"aes"},
        "aesni-avx2": {"aes", "ssse3", "avx", "avx2", "bmi1", "bmi2", "adx"},
        "vaes256": {"aes", "avx", "avx2", "vaes"},
        "vaes512f": {"aes", "avx", "avx2", "vaes", "avx512f"},
    }
    for profile in args.profiles:
        missing = required[profile] - flags
        if missing:
            parser.error(f"{profile} requires unavailable CPU features: {','.join(sorted(missing))}")
    metadata = {
        "affinity": sorted(os.sched_getaffinity(0)),
        "platform": platform.platform(), "cpuinfo": cpuinfo.split("\n\n")[0],
        "openssl": version, "settings": vars(args) | {"binary": None, "openssl": str(args.openssl), "out": str(out)},
        "binaries": {label: {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()} for label, path in binaries.items()},
        "profiles": {},
    }
    hashes = [entry["sha256"] for entry in metadata["binaries"].values()]
    if len(hashes) != len(set(hashes)):
        raise RuntimeError("comparison binaries are identical; check that every build succeeded")
    results = []
    rng = random.Random(0)
    for profile in args.profiles:
        features, caps = PROFILES[profile]
        runenv = env.copy()
        if features is not None:
            runenv["VG_CPU_FEATURES"] = features
        if caps is not None:
            runenv["OPENSSL_ia32cap"] = caps
        runenv["VG_BENCHES"] = "aes_cbc"
        metadata["profiles"][profile] = {
            "VG_CPU_FEATURES": features, "OPENSSL_ia32cap": caps,
            "observed_openssl_caps": capture([str(args.openssl), "info", "-cpusettings"], runenv),
        }
        for repetition in range(args.repeats):
            order = list(binaries)
            rng.shuffle(order)
            for label in order:
                directory = out / profile / str(repetition) / label
                directory.mkdir(parents=True, exist_ok=False)
                runenv["CRITERION_HOME"] = str(directory / "criterion")
                command = [str(binaries[label]), "--bench", args.filter, "--noplot",
                           "--sample-size", str(args.samples), "--nresamples", str(args.nresamples), "--warm-up-time", str(args.warm_up_time),
                           "--measurement-time", str(args.measurement_time)]
                print(f"{profile} {repetition + 1}/{args.repeats} {label}", flush=True)
                with (directory / "run.log").open("w") as log:
                    subprocess.run(command, env=runenv, stdout=log, stderr=subprocess.STDOUT, check=True)
                if "AES-CBC comparison: OpenSSL 4." not in (directory / "run.log").read_text():
                    raise RuntimeError(f"{label} did not report linking OpenSSL 4.x; rebuild with the current CBC benchmark")
                estimates = list(directory.glob("criterion/**/new/estimates.json"))
                if not estimates:
                    raise RuntimeError(f"{label} produced no samples; check --filter")
                for estimate in estimates:
                    benchmark = json.loads((estimate.parent / "benchmark.json").read_text())["full_id"]
                    mean = json.loads(estimate.read_text())["mean"]
                    results.append({"profile": profile, "repetition": repetition, "binary": label,
                                    "benchmark": benchmark, "mean_ns": mean["point_estimate"],
                                    "confidence_interval": mean["confidence_interval"]})
    (out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    (out / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    lines = ["| Profile | Binary | Benchmark | Median ns | Run range ns |", "|---|---|---|---:|---:|"]
    keys = sorted({(r["profile"], r["binary"], r["benchmark"]) for r in results})
    for profile, label, benchmark in keys:
        values = [r["mean_ns"] for r in results if (r["profile"], r["binary"], r["benchmark"]) == (profile, label, benchmark)]
        lines.append(f"| {profile} | {label} | {benchmark} | {statistics.median(values):.2f} | {min(values):.2f}–{max(values):.2f} |")
    (out / "report.md").write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
