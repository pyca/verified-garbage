#!/usr/bin/env python3
"""Splits a CPU's runs in CI's `rust-cpu-features` job across its shards.

A CPU's `runs` are lines of `<VG_CPU_FEATURES> | <tests>`, each a `cargo
test` (see ci.yml). A CPU whose runs take long has several matrix entries,
its shards, with the same `runs` and a `shard` of `i/n`: each job runs its
share of the lines. The lines are dealt out by the CPU time each took in
`main`'s last run (from a cache `main` saves), largest first, each to the
shard with the least time so far, so that a slow line (e.g. Wycheproof's RSA
tests under SDE) does not share a runner with another when it need not. A
line without a time (new, or before `main` saved any) counts as the median
of the CPU's known lines, or 1 if none is known. Every shard computes the
same split from the same times (which the plan job hands to all of them), so
each line runs in exactly one.

A runner's CPU decides how fast SDE emulates another: one without AVX-512
emulates `-icx`'s AVX-512 instructions several times slower, and the shards
of one run may land on different ones. So the times are kept per class of
host (`HOSTS`), each line's latest in each, and a split uses one class's
times only: the slow hosts', which are the runs worth balancing, if they
time every line, or else the class that times the most lines (the slow
hosts' on a tie).

  cpu_shards.py pick CPU SHARD TIMES  of the `runs` on stdin, the lines of
                                      SHARD (`i/n`, or empty for every
                                      line) of CPU, slowest first, as
                                      `<features>|<tests>`, by the times
                                      in the JSON TIMES (`{}` for none)
  cpu_shards.py times CPU HOST FILE   the times (seconds of CPU, `user sys`)
                                      of FILE's lines (`<features>\t<user>
                                      <sys>`), on a host of class HOST, as
                                      JSON for CPU
  cpu_shards.py merge FILE...         the times of FILEs (from `times`, or
                                      earlier merges), merged, later files'
                                      winning, as JSON
"""

import json
import statistics
import sys

# The classes of host, slowest first: whether its CPU has AVX-512
# (`/proc/cpuinfo`'s `avx512f`).
HOSTS = ["no-avx512f", "avx512f"]


def cpu_key(cpu):
    """A CPU's key in the times: its matrix entry's chip, arch and os, which
    may be empty."""
    return " ".join(cpu.split())


def parse_runs(text):
    """The lines of `runs` that have tests, as (features, tests); a value of
    `VG_CPU_FEATURES` on two lines is an error, so that a CPU never runs one
    twice."""
    lines = []
    seen = set()
    for raw in text.splitlines():
        features, _, tests = raw.partition("|")
        features, tests = " ".join(features.split()), " ".join(tests.split())
        if not tests:
            continue
        if features in seen:
            raise SystemExit(f"VG_CPU_FEATURES={features} twice: put its tests on one line")
        seen.add(features)
        lines.append((features, tests))
    return lines


def parse_shard(shard):
    """`i/n` as (i, n); empty for the only shard."""
    if not shard:
        return 1, 1
    i, _, n = shard.partition("/")
    i, n = int(i), int(n)
    if not 1 <= i <= n:
        raise SystemExit(f"shard {shard}: not between 1/{n} and {n}/{n}")
    return i, n


def split(lines, times, shards):
    """`lines` dealt out to `shards` shards by `times` (features to seconds):
    for each shard, its lines, slowest first."""
    known = [times[f] for f, _ in lines if f in times]
    default = statistics.median(known) if known else 1.0
    cost = {f: times.get(f, default) for f, _ in lines}
    load = [0.0] * shards
    out = [[] for _ in range(shards)]
    # Ties keep the order of `runs`, so that the split is the same in every shard.
    for _, (features, tests) in sorted(enumerate(lines), key=lambda e: (-cost[e[1][0]], e[0])):
        i = load.index(min(load))
        load[i] += cost[features]
        out[i].append((features, tests))
    return out


def host_times(lines, by_host):
    """Of `by_host` (a host class to features to seconds), the times of the
    one class a split uses for `lines`."""
    features = [f for f, _ in lines]
    known = {h: sum(f in by_host.get(h, {}) for f in features) for h in HOSTS}
    if known[HOSTS[0]] == len(features):
        return by_host[HOSTS[0]]
    # `max` keeps the first, the slowest, of the classes that time as many.
    return by_host.get(max(HOSTS, key=lambda h: known[h]), {})


def pick(cpu, shard, times, runs):
    lines = parse_runs(runs)
    i, n = parse_shard(shard)
    if n > len(lines):
        raise SystemExit(f"{n} shards for {len(lines)} lines: some would run nothing")
    return split(lines, host_times(lines, times.get(cpu_key(cpu), {})), n)[i - 1]


def times(cpu, host, text):
    """`<features>\t<user> <sys>` lines as {cpu: {host: {features: seconds}}}."""
    if host not in HOSTS:
        raise SystemExit(f"host {host}: not one of {', '.join(HOSTS)}")
    out = {}
    for raw in text.splitlines():
        if not raw.strip():
            continue
        features, _, cpu_time = raw.partition("\t")
        out[" ".join(features.split())] = round(sum(float(t) for t in cpu_time.split()), 2)
    return {cpu_key(cpu): {host: out}}


def merge(parts):
    out = {}
    for part in parts:
        for cpu, hosts in part.items():
            for host, lines in hosts.items():
                out.setdefault(cpu, {}).setdefault(host, {}).update(lines)
    return out


def main(argv):
    if argv[:1] == ["pick"] and len(argv) == 4:
        for features, tests in pick(argv[1], argv[2], json.loads(argv[3] or "{}"), sys.stdin.read()):
            print(f"{features}|{tests}")
    elif argv[:1] == ["times"] and len(argv) == 4:
        with open(argv[3]) as f:
            print(json.dumps(times(argv[1], argv[2], f.read()), sort_keys=True))
    elif argv[:1] == ["merge"]:
        parts = []
        for path in argv[1:]:
            with open(path) as f:
                parts.append(json.load(f))
        print(json.dumps(merge(parts), sort_keys=True, separators=(",", ":")))
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
