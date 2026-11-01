"""Compares the performance of two checkouts of this repository.

    python3 ci/bench_compare.py BASE HEAD [--summary FILE] [--openssl]

Both are built with HEAD's `bench/` crate (so the two run the same
benchmark code against different library code), each at the same path
(`STAGE`); if that doesn't build against BASE (it benchmarks an API BASE
doesn't have yet), BASE uses its own `bench/` crate, and HEAD's other
benchmarks show as new. Their benchmark
binaries are run on this machine `--rounds` times each (keeping the fastest
time of each benchmark on each side, if more than one): one round, with a
short warm-up and measurement, is the default, since the check fails only
on a slowdown of more than `--threshold`, far beyond the noise between two
runs of the same code (in an A/A run on CI, with two rounds of 0.2 s and
0.5 s: 99% of benchmarks within 3%, the largest 12%).

The two sides are interleaved: each round runs one benchmark (a `BENCHES`
entry of bench/benches/primitives/main.rs, selected by `VG_BENCHES`) on
base, then on head, then the next one on head, then on base, and so on, so
that a few slow seconds of the runner (an A/A run of one round, with each
side's benchmarks all run one after the other, found three neighbouring
benchmarks 35% slower) hit both sides of a benchmark, or neither, rather
than a stretch of one side's. Each run sets up only its own benchmark
(generating RSA keys, …), so this costs no more than running each side's
benchmarks at once; only the processes' start, a few milliseconds each.
When BASE runs its own `bench/` crate, whose benchmarks need not be HEAD's,
each side runs all of its benchmarks at once, alternately, as before.

The benchmarks still over the threshold after the rounds run again, base
and head alternately, `--confirm` more times each: a slowdown fails only if
it is still there in the fastest time of every run.

Writes a Markdown table of the results to stdout (and appends it to
`--summary`, e.g. `$GITHUB_STEP_SUMMARY`), and exits with status 1 if any
verified-garbage benchmark got slower by more than `--threshold`. If BASE
does not exist, HEAD runs alone, next to OpenSSL and aws-lc-rs.

OpenSSL's and aws-lc-rs's code is the same on both sides, so their
benchmarks are only a reference point for HEAD's times, not part of the
comparison: they run once, with HEAD's binary, with `--openssl` or when BASE
does not exist; and only without `VG_CPU_FEATURES`, which does not change
their code either, unless `--openssl-with-features` asks for them under it
too (`OPENSSL_ia32cap` in the environment then masks their own x86 CPU
features: OpenSSL and aws-lc both read it). aws-lc-rs has no benchmark where
it lacks the primitive.

`VG_CPU_FEATURES` in the environment (see src/cpu.rs) restricts the CPU
features both sides use, and is named in the report. Each side is passed
only the features its own src/cpu.rs knows (base may predate one), since it
cannot use the others anyway. If it names a feature this runner's CPU does
not have, the library stops the benchmarks (they would measure another
configuration's code under its name): the report then says what was not
measured, with a warning, and the exit status is 0, since another runner,
from a re-run, may have the feature.

The groups that read a large table of constants (`FRESH_COPIES`: the
combs of hundreds of kilobytes) are slower or faster by up to about 7%
depending on which physical pages hold the table, which the kernel picks
when it first reads that file into its page cache, and keeps until it drops
it: identical copies of one binary measured 104.5–110.4 µs for a P-521
signature, each copy within 0.3% of itself from run to run. So one run of
each side would compare two draws of that, not the code; these groups also
run from `--copies - 1` fresh copies of each side's binary (each a new
file, so new pages), and each of their times is the fastest of the copies
(as of the rounds): the time with the table where it collides least, which
the code decides, while the median of five draws still moved by 1–2%
between two sides of the same code. The report shows the spread.
ChaCha20-Poly1305's groups depend on the draw too, on AMD's Zen 3 and Zen 5
(its code of up to about 100 KB a function, rather than a table): eight
copies of one binary on an EPYC 7763 sealed 4096 bytes in 2.05–2.51 µs and
16384 in 7.15–9.21 µs, and one run of each side of an unchanged function
reported it up to 46% slower, so they run from copies as well. So do
AES-GCM's (not AES-GCM-SIV's): eight copies of one binary on an x86-64
runner spread by up to 35% (`aes-256-gcm-tls-open` at 1025 bytes), 29%
(`aes-128-gcm-encrypt-out-of-place` at 64) and 28% (the TLS seal at 4095).
So do the SHA-512 family's digests and PBKDF2's: eight copies of one binary
on an EPYC 9V74 spread by up to 9% (`pbkdf2-hmac-sha512-256`, 23.33–25.49 µs
at 64 bytes; `pbkdf2-hmac-sha384` 6.9%, `sha512` at 64 bytes 11%), and one
run of each side of unchanged PBKDF2 code reported it 5% slower on an EPYC
7763, three times out of three, where the fastest copies of the two sides
were within 0.1%. So do ML-KEM's: eight copies of one binary spread by
up to 9.4% on an EPYC 9V74 and 4.6% on an EPYC 7763 for
`mlkem1024_keygen` (17.18–18.81 µs), and up to 14% for `mlkem768_decaps`,
and one run of each side of a change that left `keygen_mul` byte for byte
the same reported ML-KEM-1024's key generation 4–5% slower or faster,
where the fastest copies of the two sides were within 0.3%. So do SHA-256's
and SHA-224's digests, HMACs and PBKDF2's: eight copies of one binary on an
Arm Neoverse N2 spread by up to 3.5% for `sha256` at 32 bytes
(47.22–48.85 ns), 2.1% for `sha224` at 32, 8.6% for `pbkdf2-hmac-sha224`
at 64 (5.16–5.60 µs) and 1.6% for `hmac-sha256` at 32, more than the 0.7%
by which a pull request's code layout already moves them. So do HMAC's
with the SHA-512 family's hashes, which run the same compression function
as their digests: on an EPYC 9V45, one function's 16 KiB time (HMAC-SHA-384,
-512, -512/224 or -512/256) sat at 13.55–13.64 µs from some call sites and
at 14.00–14.28 µs from others in one binary, and the other side's binary
drew only the slower level (14.04–14.18 µs at every call site), 3–4% slower,
where the PBKDF2 groups' fastest copies were within 0.4%; in a second run
on an EPYC 9V45 every call site of both sides was within 1%.

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
# The libraries benchmarked for reference, with their names in the report.
REFERENCES = {"openssl": "OpenSSL", "aws-lc-rs": "aws-lc-rs"}


# Every build shares one target directory, so the dependencies (criterion,
# rust-openssl, aws-lc-rs), which are the same on both sides, are compiled
# only once.
TARGET = pathlib.Path("bench-target").resolve()

# The benchmark groups (`<primitive>`s) whose time depends on the physical
# pages that hold the binary (see the module docstring): those that read a
# comb's table of hundreds of kilobytes, ChaCha20-Poly1305's, AES-GCM's,
# the SHA-512 family's digests, HMAC's and PBKDF2's, ML-KEM's, and SHA-256's and
# SHA-224's digests, HMACs and PBKDF2's.
# They run from `--copies` copies of each binary.
FRESH_COPIES = re.compile(
    r"^(?:ec_p521_public_key|ecdsa_p521_|chacha20poly1305|aes-(?:128|256)-gcm-(?!siv)"
    r"|pbkdf2-hmac-sha(?:384|512)|sha(?:384|512)(?:-224|-256)?$|mlkem(?:768|1024)_"
    r"|hmac-sha(?:384|512)(?:-224|-256)?(?:-verify)?$"
    r"|sha(?:224|256)$|(?:hmac|pbkdf2-hmac)-sha(?:224|256)(?:-verify)?$)")
# The `VG_BENCH_MODULES` of the copies' runs when the sides are not
# interleaved (which select each benchmark by `VG_BENCHES`): the modules
# whose benchmarks hold those groups. The binary sets up every selected
# benchmark before criterion's filter applies (RSA keys of up to 4096 bits
# among them), which took about 110 s of each copy's run with every module.
FRESH_COPIES_MODULES = "ecdsa_p521 chacha20poly1305 aes_gcm sha512 mlkem sha256"

# How src/cpu.rs stops a run whose `VG_CPU_FEATURES` names features this CPU
# does not have.
LACKING = re.compile(r"VG_CPU_FEATURES names (\S+), which this CPU does not have")


class Lacking(Exception):
    """A run stopped by `LACKING`, with the features the CPU lacks."""


# Where each side is built, one after the other: the same path for both,
# since Cargo derives the library's symbol hashes from its path, and with
# them the order the linker lays out its code and tables in, so the same
# code built in two checkouts put P-521's comb table at a different offset
# in a page (0x700 and 0x740 on x86-64), and an A/A run measured P-521
# signatures 5% slower on one side.
STAGE = pathlib.Path("bench-src").resolve()


def stage(checkout, bench=None):
    """Copies what building `checkout`'s benchmarks reads to `STAGE`, with
    the benchmark crate `bench` (`checkout`'s own by default), returning
    the staged crate. Copies get new modification times, so Cargo rebuilds
    the library, which the last side's build would otherwise seem to be."""
    shutil.rmtree(STAGE, ignore_errors=True)
    # (Run from a checkout, as `bench_compare.py main-checkout .`, STAGE,
    # TARGET and the work directory are in it.)
    top = {".git", "lean", "target", "bench", "bench-head", STAGE.name, TARGET.name, "bench-compare"}
    skip = lambda d, names: top & set(names) if pathlib.Path(d) == pathlib.Path(checkout) else []
    shutil.copytree(checkout, STAGE, ignore=skip, copy_function=shutil.copy)
    shutil.copytree(bench or checkout / "bench", STAGE / "bench",
                    ignore=shutil.ignore_patterns("target"), copy_function=shutil.copy)
    return STAGE / "bench"


def build(checkout, bench=None):
    """Builds `checkout`'s library with the benchmark crate `bench`
    (`checkout`'s own by default) at `STAGE`, returning the binary's path."""
    out = subprocess.run(
        [
            "cargo",
            "bench",
            "--no-run",
            "--message-format=json-render-diagnostics",
        ],
        cwd=stage(checkout, bench),
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
    raise RuntimeError(f"no benchmark binary built for {checkout}")


# The executable format of each `--arch` (ci/bench_arches.py's platforms):
# ELF's class (32 or 64 bits) and `e_machine`, or Mach-O's `cputype`.
EXECUTABLES = {
    "x86_64": ("ELF", 64, 62),
    "aarch64": ("ELF", 64, 183),
    "x86": ("ELF", 32, 3),
    "arm": ("ELF", 32, 40),
    "thumb": ("ELF", 32, 40),
    "powerpc64": ("ELF", 64, 21),
    "riscv64": ("ELF", 64, 243),
    "aarch64-apple": ("Mach-O", 64, 0x0100000C),
}


def executable(binary):
    """`binary`'s format, word size and machine, as in `EXECUTABLES`."""
    with open(binary, "rb") as f:
        header = f.read(20)
    if header[:4] == b"\x7fELF":
        return "ELF", 32 * header[4], int.from_bytes(header[18:20], "little")
    if header[:4] == b"\xcf\xfa\xed\xfe":
        return "Mach-O", 64, int.from_bytes(header[4:8], "little")
    return None


def check_arch(binary, arch):
    """Stops unless `binary` is code of `arch`: ARMv7's benchmarks are
    cross-compiled on an AArch64 host (ci/bench_arches.py), so a build that
    lost its target would otherwise measure AArch64's code as ARMv7's."""
    if executable(binary) != EXECUTABLES[arch]:
        raise SystemExit(f"{binary} is {executable(binary)}, not {arch}'s {EXECUTABLES[arch]}")


def fresh_copy(binary, i):
    """A copy of `binary` in a new file: the page cache holds a file's pages
    by inode, so the copy's table is read into newly chosen physical pages."""
    copy = TARGET / f"{pathlib.Path(binary).name}-copy-{i}"
    shutil.copyfile(binary, copy)
    copy.chmod(0o755)
    return copy


def build_base(base, head):
    """Builds BASE's benchmarks (see the module docstring), returning the
    binary's path and a note on which benchmark code it runs, or no path
    if neither builds."""
    if base == head:
        return build(head), None, head
    try:
        return build(base, head / "bench"), None, head
    except subprocess.CalledProcessError:
        pass
    if (base / "bench").is_dir():
        try:
            return build(base), "Head's benchmarks don't build against base, so base ran its own.", base
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
    `binary` runs for `modules`, with how many benchmarks each has, and the
    benchmark (`BENCHES` entry) each is in, in the order they run (None if
    the binary does not name them)."""
    # Without `VG_CPU_FEATURES`: listing runs no benchmark, and the library
    # stops at its start if this CPU lacks a feature it names, which the
    # runs report.
    env = {k: v for k, v in os.environ.items() if k != "VG_CPU_FEATURES"}
    out = subprocess.run(
        [binary, "--bench", "--list", f"/{VG}/"],
        env={**env, "VG_BENCH_MODULES": modules, "VG_BENCH_NAMES": "1"},
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout
    return parse_list(out)


def parse_list(out):
    """`list_groups`'s results from the binary's `--list` output."""
    groups, owner, bench, shared = {}, {}, None, False
    for line in out.splitlines():
        if line.endswith(": bench"):
            bench = line.removesuffix(": bench")
        elif line.endswith(": benchmark"):
            group = line.split("/", 1)[0]
            groups[group] = groups.get(group, 0) + 1
            if bench is not None:
                # A group in two benchmarks cannot run with either alone.
                shared |= owner.setdefault(group, bench) != bench
    return groups, (owner if bench is not None and not shared else None)


def units(groups, owner):
    """The runs each round consists of, as `(bench, groups)`: with `owner`
    (each group's benchmark), one per benchmark, of its groups among
    `groups`, in the order the benchmarks run; without, one run of all of
    `groups` (None: every group)."""
    if owner is None:
        return [(None, groups)]
    runs, wanted = {}, set(groups)
    for group, bench in owner.items():
        if group in wanted:
            runs.setdefault(bench, []).append(group)
    return list(runs.items())


def interleaved(runs, binaries, start=0):
    """The order to run `runs` (`units`) in on the sides that have a binary,
    as `(side, bench, groups)`: each run on both sides, one after the other,
    alternating which goes first, from base for `start` even."""
    for k, (bench, groups) in enumerate(runs):
        for side in ("base", "head") if (start + k) % 2 == 0 else ("head", "base"):
            if binaries[side] is not None:
                yield side, bench, groups


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


def run(binary, home, library, args, checkout, modules, groups=None, bench=None):
    """Runs the benchmarks of `checkout` once (only those of `groups`, if
    given, in the benchmark `bench`, if given), returning each one's median
    time (ns)."""
    pattern = f"/{library}/"
    if groups is not None:
        pattern = f"^(?:{'|'.join(map(re.escape, groups))})/{library}/"
    proc = subprocess.run(
        [
            binary,
            "--bench",
            "--noplot",
            "--warm-up-time",
            str(args.warm_up_time),
            "--measurement-time",
            str(args.measurement_time),
            # Criterion's default 100 samples cannot fit in a short
            # measurement once an iteration takes more than a few
            # milliseconds (PBKDF2 at 16384 iterations, signatures), so
            # those overran it with a warning; faster benchmarks take as
            # long either way, with more iterations per sample.
            "--sample-size",
            "25",
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
            "VG_BENCHES": bench or "",
            "VG_CPU_FEATURES": cpu_features(checkout),
        },
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        text=True,
    )
    sys.stderr.write(proc.stderr)
    if proc.returncode:
        if m := LACKING.search(proc.stderr):
            raise Lacking(m[1])
        raise subprocess.CalledProcessError(proc.returncode, binary)
    times = {}
    for est in home.glob(f"*/{library}/*/new/estimates.json"):
        primitive, _, size = est.relative_to(home).parts[:3]
        times[primitive, int(size)] = json.loads(est.read_text())["median"]["point_estimate"]
    return times


def cpu_model():
    """This machine's CPU model, from /proc/cpuinfo (or, on macOS, `sysctl`),
    or None."""
    try:
        cpuinfo = pathlib.Path("/proc/cpuinfo").read_text()
    except OSError:
        try:
            out = subprocess.run(["sysctl", "-n", "machdep.cpu.brand_string"], capture_output=True,
                                 text=True, check=True).stdout.strip()
        except (OSError, subprocess.CalledProcessError):
            return None
        return out or None
    m = re.search(r"^model name\s*:\s*(.+)$", cpuinfo, re.M)
    return m[1].strip() if m else None


def not_measured(cpu_features, lacking, model):
    """The report of a run that this CPU, without the features `lacking`,
    cannot measure."""
    return (f"## Benchmarks (VG_CPU_FEATURES={cpu_features})\n\n"
            f"Not measured: this runner's CPU{f' ({model})' if model else ''} does not have {lacking},"
            " which this configuration names; a re-run may get a runner with them.\n")


def vs_reference(ours, theirs):
    """How head's time compares with a reference library's, in words."""
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
    p.add_argument("--rounds", type=int, default=1)
    p.add_argument("--copies", type=int, default=8,
                   help="copies of each binary that run the groups of FRESH_COPIES (1: only the binary)")
    p.add_argument("--confirm", type=int, default=2,
                   help="runs of each side again for the benchmarks over the threshold")
    p.add_argument("--threshold", type=float, default=0.35)
    p.add_argument("--warm-up-time", type=float, default=0.1)
    p.add_argument("--measurement-time", type=float, default=0.3)
    p.add_argument("--openssl", action="store_true",
                   help="also run OpenSSL's and aws-lc-rs's benchmarks, for reference")
    p.add_argument("--openssl-with-features", action="store_true",
                   help="run them even under VG_CPU_FEATURES (with --openssl, or without a base)")
    p.add_argument("--work-dir", type=pathlib.Path, default=pathlib.Path("bench-compare"))
    p.add_argument("--modules", default="", help="space-separated; only benchmark these modules")
    p.add_argument("--shard", default="", help="i/n: only the i-th of n shares of the benchmarks")
    p.add_argument("--arch", choices=EXECUTABLES, help="fail unless the binaries are this architecture's")
    args = p.parse_args()
    shard, shards = map(int, (args.shard or "1/1").split("/"))
    if not 1 <= shard <= shards:
        p.error("--shard must be i/n with 1 <= i <= n")

    base, head = args.base.resolve(), args.head.resolve()
    modules = {"head": selected_modules(head, args.modules), "base": selected_modules(base, args.modules)}
    if modules["head"] is None or (args.modules and set(modules["head"].split()) != set(args.modules.split())):
        p.error("head's benchmark registry does not use the selected modules")
    binaries = {"head": build(head), "base": None}
    note = "Base has no selected benchmarks; head's and the references' results are new."
    if not base.is_dir():
        note = "No base to compare with, so head ran alone."
    elif modules["base"] is not None:
        binaries["base"], note, source = build_base(base, head)
        if binaries["base"] is not None:
            modules["base"] = selected_modules(source, args.modules)
    if args.arch:
        for binary in filter(None, binaries.values()):
            check_arch(binary, args.arch)

    # Both sides run the same groups, which head's list of them decides. It
    # also says which benchmark has each group, so that the sides can run
    # one benchmark at a time, if both binaries have head's benchmarks.
    listed, owner = list_groups(binaries["head"], modules["head"])
    if note is not None and binaries["base"] is not None:
        owner = None
    groups = None
    if shards > 1:
        groups = shard_groups(listed, shard, shards)
    # Run-only scope: changed out-of-place APIs and an in-place control.
    focused = {"aes-128-gcm-encrypt-out-of-place", "aes-128-gcm-encrypt-two-pieces",
               "aes-128-gcm-tls-seal", "aes-256-gcm-tls-seal", "aes-128-gcm-encrypt"}
    groups = sorted(set(listed) & focused)
    if set(groups) != focused:
        raise RuntimeError("focused GCM groups missing from the benchmark registry")
    print("Focused GCM groups: " + ", ".join(groups), file=sys.stderr)
    # Interleaved, every group is named (base's runs of a benchmark it lacks
    # measure nothing); otherwise, unsharded, each side runs all of its own.
    selected = groups if groups is not None or owner is None else sorted(listed)

    work = args.work_dir.resolve()
    shutil.rmtree(work, ignore_errors=True)

    def measure(order, binary_of, home, modules_of, into):
        """Runs `order` (`interleaved`), adding each benchmark's times to
        `into[side]`, a list of them per benchmark."""
        for side, bench, unit in order:
            print(f"{home(side)}{f': {bench}' if bench else ''}", file=sys.stderr)
            checkout = base if side == "base" else head
            times = run(binary_of(side), work / home(side) / (bench or "all"), VG, args, checkout,
                        modules_of(side, bench), unit, bench)
            for bench_id, t in times.items():
                into[side].setdefault(bench_id, []).append(t)

    def keep_fastest(runs):
        for side, times in runs.items():
            for bench_id, ts in times.items():
                best[side][bench_id] = min(*ts, best[side].get(bench_id, ts[0]))

    best = {"base": {}, "head": {}}
    rounds = units(selected, owner)
    try:
        for r in range(args.rounds):
            # Alternate which side goes first, so neither always runs warmer.
            runs = {"base": {}, "head": {}}
            measure(interleaved(rounds, binaries, r), binaries.get, lambda side, r=r: f"{side}-{r}",
                    lambda side, _bench: modules[side], runs)
            keep_fastest(runs)
    except Lacking as e:
        # The first run of either side stops, before any other.
        report = not_measured(os.environ.get("VG_CPU_FEATURES", ""), e.args[0], cpu_model())
        print(f"::warning::{report.splitlines()[-1]}")
        print(report)
        if args.summary:
            with args.summary.open("a") as f:
                f.write(report)
        return 0

    # The groups that depend on where the kernel puts their table run again
    # from fresh copies of each binary, alternately, and keep the fastest
    # time of the copies (the rounds above counting as the first copy).
    copied = []
    if args.copies > 1:
        copied = sorted(g for g in (groups if groups is not None else listed) if FRESH_COPIES.match(g))
    spread = {"base": {}, "head": {}}
    if copied:
        for side in spread:
            spread[side] = {i: [t] for i, t in best[side].items() if i[0] in copied}
        copy_modules = (lambda side, _bench: modules[side]) if owner is not None else (
            lambda _side, _bench: FRESH_COPIES_MODULES)
        for c in range(1, args.copies):
            print(f"copy {c + 1}/{args.copies} of {len(copied)} group(s)", file=sys.stderr)
            copies = {side: fresh_copy(b, c) if b is not None else None for side, b in binaries.items()}
            try:
                measure(interleaved(units(copied, owner), copies, c), lambda side: str(copies[side]),
                        lambda side, c=c: f"{side}-copy-{c}", copy_modules, spread)
            finally:
                for copy in copies.values():
                    if copy is not None:
                        copy.unlink()
        for side, times in spread.items():
            for bench_id, ts in times.items():
                best[side][bench_id] = min(ts)

    def suspects():
        """The groups (`<primitive>`s) of the benchmarks over the threshold."""
        return sorted({p for (p, size), h in best["head"].items()
                       if (p, size) in best["base"] and h / best["base"][p, size] - 1 > args.threshold})

    # A slowdown over the threshold is confirmed: its groups run again on
    # both sides, alternately, and keep their fastest times.
    # (Not the groups that ran from copies, already the fastest of as many
    # runs.)
    confirmed = [g for g in suspects() if g not in copied] if binaries["base"] is not None else []
    for r in range(args.confirm if confirmed else 0):
        runs = {"base": {}, "head": {}}
        print(f"confirming {len(confirmed)} group(s), {r + 1}/{args.confirm}", file=sys.stderr)
        measure(interleaved(units(confirmed, owner), binaries, r + 1), binaries.get,
                lambda side, r=r: f"{side}-confirm-{r}", lambda side, _bench: modules[side], runs)
        keep_fastest(runs)
    cpu_features = os.environ.get("VG_CPU_FEATURES", "")
    references = {}
    with_references = (args.openssl or binaries["base"] is None) and (not cpu_features or args.openssl_with_features)
    ia32cap = os.environ.get("OPENSSL_ia32cap", "")
    if with_references:
        for library, name in REFERENCES.items():
            print(name, file=sys.stderr)
            references[library] = run(binaries["head"], args.work_dir.resolve() / library, library, args, head,
                                       modules["head"], groups)

    title = ", ".join([*([f"VG_CPU_FEATURES={cpu_features}"] if cpu_features else []),
                       *([f"shard {shard}/{shards}"] if shards > 1 else [])])
    runs = (f"Fastest of {args.rounds} runs of each side" if args.rounds > 1 else "One run of each side")
    runs += (", interleaved benchmark by benchmark" if owner is not None
             else ", each side's benchmarks at once, alternately")
    lines = [
        f"## Benchmarks ({title})" if title else "## Benchmarks",
        "",
        f"{runs} on this runner; a slowdown of more than {args.threshold:.0%} fails."
        + (" OpenSSL (through rust-openssl) and aws-lc-rs ran once, for reference"
           + (f", with OPENSSL_ia32cap={ia32cap}" if ia32cap
              else ", with all of this CPU's features" if cpu_features else "") + "." if with_references
           else " OpenSSL and aws-lc-rs ran only in the configuration without VG_CPU_FEATURES." if cpu_features
           else " OpenSSL and aws-lc-rs did not run (they do with `--openssl`, the workflow's `openssl` input)."),
        *(
            [
                f"Changed modules: {args.modules}. Only the benchmarks that use them ran"
                ". Base received only modules present in its benchmark registry."
            ]
            if args.modules.strip()
            else []
        ),
        *([f"{note}"] if note else []),
        *(
            [
                f"From {args.copies} copies of each binary (each a new file, so the kernel reads it into new"
                " physical pages, on which these groups' tables of constants make them up to about 7% faster or"
                f" slower), the fastest of the copies: {', '.join(f'`{g}`' for g in copied)}."
                " Their spread is below the table."
            ]
            if copied
            else []
        ),
        *(
            [
                f"Over the threshold after the first run, so run {args.confirm} more time(s) on each side,"
                f" alternately, keeping the fastest: {', '.join(f'`{g}`' for g in confirmed)}."
            ]
            if confirmed and args.confirm
            else []
        ),
        "",
        "| Benchmark | Base | Head | Change |"
        + "".join(f" {name} | Head vs {name} |" for name in REFERENCES.values() if with_references),
        "|---|--:|--:|--:|" + "--:|--:|" * len(references),
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
        b = fmt_time(b) if b else "–"
        row = f"| `{bench_id}` | {b} | {fmt_time(h)} | {change} |"
        for times in references.values():
            o = times.get((primitive, size))
            row += f" {fmt_time(o) if o else '–'} | {vs_reference(h, o) if o else '–'} |"
        lines.append(row)
    if copied:
        lines += ["", "| Benchmark | Base copies | Head copies |", "|---|--:|--:|"]
        for bench_id in sorted(spread["head"]):
            cells = []
            for side in ("base", "head"):
                ts = spread[side].get(bench_id)
                cells.append(f"{fmt_time(min(ts))} – {fmt_time(max(ts))} ({max(ts) / min(ts) - 1:.1%})" if ts else "–")
            lines.append(f"| `{bench_id[0]}/{bench_id[1]}` | {cells[0]} | {cells[1]} |")
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
