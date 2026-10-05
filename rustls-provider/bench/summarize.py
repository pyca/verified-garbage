#!/usr/bin/env python3
"""Summarizes bench/run.sh's results: verified-garbage / aws-lc-rs ratios
(below 1 is slower) for rustls-bench, by scenario and as geometric means
by category, and the medians of the timing tables (where above 1 is
slower)."""

import collections
import glob
import math
import os
import re
import statistics
import sys


def rustls_bench(out, provider):
    runs = collections.defaultdict(list)
    for f in sorted(glob.glob(os.path.join(out, f"all-{provider}-*.tsv"))):
        for line in open(f):
            parts = line.rstrip("\n").split("\t")
            if len(parts) >= 3:
                runs[tuple(parts[:-2])].append(float(parts[-2]))
    return {k: statistics.median(v) for k, v in runs.items()}


def category(key):
    if key[0] == "bulk":
        aead = "ChaCha20-Poly1305" if "CHACHA" in key[2] else "AES-GCM"
        return f"bulk {key[1]} {aead} {key[3]}"
    # handshakes, version, key type, suite, side, auth, resumption
    return f"handshakes {key[1]} {key[2]} {key[4]} {key[5]} {key[6]}"


def tables(out, pattern):
    """Medians of the rows of the timing tables `pattern` (name, aws-lc,
    verified-garbage, ratio)."""
    rows = collections.defaultdict(lambda: ([], []))
    order = []
    for f in sorted(glob.glob(os.path.join(out, pattern))):
        for line in open(f):
            m = re.match(r"^(.*?)\s+(\d+)\s+(\d+)\s+[\d.]+x$", line.rstrip())
            if not m:
                continue
            name = m.group(1).strip()
            if name not in rows:
                order.append(name)
            rows[name][0].append(float(m.group(2)))
            rows[name][1].append(float(m.group(3)))
    for name in order:
        a, v = (statistics.median(x) for x in rows[name])
        print(f"{name:<52} {a:>11.0f} {v:>11.0f} {v / a:>7.2f}x")


def main():
    out = sys.argv[1]
    aws = rustls_bench(out, "aws-lc-rs")
    vg = rustls_bench(out, "verified-garbage")
    common = [k for k in aws if k in vg]

    print("== rustls-bench: verified-garbage / aws-lc-rs, geometric means\n")
    cats = collections.defaultdict(list)
    for k in common:
        cats[category(k)].append(vg[k] / aws[k])
    for c, rs in sorted(cats.items()):
        g = math.exp(sum(map(math.log, rs)) / len(rs))
        print(f"{g:5.2f}  (n={len(rs):2}, {min(rs):.2f}-{max(rs):.2f})  {c}")

    print("\n== rustls-bench: each scenario (aws-lc-rs, verified-garbage, ratio)\n")
    for k in common:
        print(f"{vg[k] / aws[k]:5.2f}  {aws[k]:10.1f} {vg[k]:10.1f}  {' '.join(k)}")

    for title, pattern in [
        ("provider-primitives: ns per operation", "primitives-*.txt"),
        ("aws-lc-compare: ns per operation", "aws-lc-compare-*.txt"),
        ("aws-lc-compare: AEAD sizes", "sweep-*.txt"),
    ]:
        print(f"\n== {title} (aws-lc-rs, verified-garbage, ratio)\n")
        tables(out, pattern)


main()
