#!/usr/bin/env python3
"""Interleave single-process A/B runs; do not run other builds/tests alongside."""

import argparse
import csv
import os
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--samples", type=int, default=7)
    parser.add_argument("--profile", choices=["release", "debug"], default="release")
    parser.add_argument("--phases-only", action="store_true")
    parser.add_argument("--candidate-wipe", choices=["chunks", "bulk"], default="bulk")
    args = parser.parse_args()
    if args.samples < 1:
        parser.error("samples must be positive")
    args.output.mkdir(parents=True, exist_ok=True)
    roots = {"baseline": args.baseline.resolve(), "candidate": args.candidate.resolve()}
    with (args.output / "kernels.csv").open("w") as output:
        writer = csv.writer(output, lineterminator="\n")
        writer.writerow(["side", "round", "kind", "n", "r", "iterations", "sample", "seconds", "checksum"])
        cases = [("blockmix", 2, r, 500000) for r in [1, 2, 8, 16]]
        cases += [("romix", n, 8, 1) for n in [16384, 131072, 1048576]]
        if args.phases_only:
            cases = []
        for kind, n, r, iterations in cases:
            for sample in range(args.samples):
                order = ["baseline", "candidate"] if sample % 2 == 0 else ["candidate", "baseline"]
                hashes = []
                for side in order:
                    command = [str(roots[side] / "kernel"), str(n), str(r), str(iterations), "1", str(int(kind == "blockmix"))]
                    row = next(csv.reader(subprocess.check_output(command, text=True).splitlines()))
                    hashes.append(row[-1])
                    writer.writerow([side, sample, *row])
                    output.flush()
                assert hashes[0] == hashes[1], "kernel outputs differ"
    with (args.output / "phases.csv").open("w") as output:
        writer = csv.writer(output, lineterminator="\n")
        writer.writerow(["side", "round", "n", "r", "p", "sample", "allocation_s", "derivation_s", "wipe_s", "free_s", "public_api_s"])
        for n, r, p in [(1024, 1, 1), (16384, 2, 1), (16384, 16, 1), (1024, 8, 16), (16384, 8, 1), (131072, 8, 1), (1048576, 8, 1)]:
            for sample in range(args.samples):
                order = ["baseline", "candidate"] if sample % 2 == 0 else ["candidate", "baseline"]
                for side in order:
                    env = os.environ.copy()
                    env["SCRYPT_WIPE_MODE"] = args.candidate_wipe if side == "candidate" else "chunks"
                    env["LLVM_PROFILE_FILE"] = str(args.output.resolve() / f"{side}-%p.profraw")
                    command = [str(roots[side] / f"target/{args.profile}/phases"), str(n), str(r), str(p), "1"]
                    row = next(csv.reader(subprocess.check_output(command, env=env, text=True).splitlines()))
                    writer.writerow([side, sample, *row])
                    output.flush()


if __name__ == "__main__":
    main()
