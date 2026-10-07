#!/usr/bin/env python3
"""Pilot: what would it cost to record per-declaration profiles in every
Lean build, and would they point at the right declarations?

Lake keeps each module's build log in its `.trace` file (the `log` field),
and the CI cache (`ghcr.io/pyca/vg-lean-cache`) ships those files. So if the build itself printed a compact profile, every
restored cache would already carry one for every module, with no separate
profiling build. Lean's `profiler` option prints one line per step over
`profiler.threshold` milliseconds (`type checking took 609ms`, `simp took
890ms`), each a message at the position of its declaration under `--json`
(as Lake runs Lean). Setting it in `leanOptions` changes every module's
trace, so it must be measured before it is proposed. (Lake also replays a
module's stored log on every later `lake build` that finds it up to date,
info messages included, unless run with `--log-level=warning` or `-q`.)

For each module, this runs Lean the way `lake build` does (its setup file,
`-j2`, `--json`, writing `.olean`, `.ilean` and `.c` to a scratch directory)
in three configurations, interleaved, `--runs` times each:

  base   the build as it is
  prof   + `-Dprofiler=true -Dprofiler.threshold=T` (the candidate)
  ref    + `-DElab.async=false` as well, as CLAUDE.md's profiling recipes
         run, a second opinion on the candidate's attribution (its own
         coverage varies with the threshold, so it is no ground truth)

and reports, per module and in total: the median wall and CPU time of each
configuration and the candidate's overhead over `base`; whether `prof`
wrote byte-identical `.olean`, `.ilean` and `.c` files (the option must not
change what is checked or emitted); the bytes of profile it adds to the
build log; the share of the module's kernel time (Lean's own cumulative
`type checking`) its lines attribute to declarations, the measure of
whether the profile finds the cost; and the declarations it attributes the
most time to, against `ref`'s.

Run it from `lean/` after restoring the CI cache and building the modules
(`lake build +Module` for each; nothing is rebuilt if the cache matches):

  python3 ../ci/lean_profile_pilot.py [--runs N] [--threshold MS] \
      [--json OUT] [MODULE ...]

Without modules it measures `DEFAULT_MODULES`, a mix of the build's
shapes (symbolic execution, `taint_decide`, literals, registration files).
Compare overheads on the runner CI builds on: times depend on the machine.
"""

import argparse
import json
import os
import pathlib
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

LEAN = pathlib.Path(__file__).resolve().parent.parent / "lean"

DEFAULT_MODULES = [
    # Symbolic execution with `run_block` (ARMv7).
    "VerifiedGarbage.Proof.MlKem.Arm.Mul",
    # Large constant-time checks (`taint_decide`).
    "VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CT",
    "VerifiedGarbage.Proof.Scrypt.Arm.RoMixCT",
    # Long functional-correctness proofs.
    "VerifiedGarbage.Proof.Poly1305.X86.Blocks",
    "VerifiedGarbage.Proof.MdStream.X86.Finalize",
    "VerifiedGarbage.Proof.Argon2.AArch64.InitFill",
    # Framework: many small lemmas.
    "VerifiedGarbage.Proof.Framework.X86_64.Taint",
    # A registration file (`spSafe`, `ofApi`'s checks).
    "VerifiedGarbage.Artifacts.Sha256.X86_64",
]

CONFIGS = ("base", "prof", "ref")

# `profiler` lines: `<what> took <n>ms` or `<n>s`.
TOOK = re.compile(r"^(.*) took ([0-9.]+)(ms|s)\s*$")
# A line of the summary Lean prints at the end (`\ttype checking 3.12s`).
CUMULATIVE = re.compile(r"^\t(.*) ([0-9.]+)(ms|s)$")
# A declaration's name at the start of a line (after modifiers).
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|"
    r"nonrec|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|"
    r"axiom|example|materialize_code|materialize_table|materialize_value)"
    r"(?:\s+([^\s:({\[]+))?"
)


def lean_cmd():
    return ["lake", "env", "lean"]


def setup_file(mod):
    return LEAN / ".lake/build/ir" / (mod.replace(".", "/") + ".setup.json")


def source_file(mod):
    return LEAN / (mod.replace(".", "/") + ".lean")


def run(mod, config, threshold, outdir):
    """Runs Lean on `mod` as Lake does, in `config`. Returns its measurements
    and messages."""
    args = ["--setup", str(setup_file(mod)), "-j2", "--json"]
    if config in ("prof", "ref"):
        args += ["-Dprofiler=true", f"-Dprofiler.threshold={threshold}"]
    if config == "ref":
        args += ["-DElab.async=false"]
    out = pathlib.Path(outdir)
    args += [
        "-o", str(out / "m.olean"), "-i", str(out / "m.ilean"),
        "-c", str(out / "m.c"),
        str(source_file(mod).relative_to(LEAN)),
    ]
    # Lean prints `profiler` lines outside messages (`parsing took`, the
    # cumulative summary) to stderr, which would split the JSON messages on
    # stdout if the two were one stream: keep them apart, as Lake does.
    with tempfile.TemporaryFile() as err:
        start = time.monotonic()
        proc = subprocess.Popen(
            lean_cmd() + args, cwd=LEAN, stdout=subprocess.PIPE, stderr=err)
        stdout = proc.stdout.read()
        _, status, usage = os.wait4(proc.pid, 0)
        wall = time.monotonic() - start
        err.seek(0)
        stderr = err.read()
    text = stdout.decode("utf-8", "replace")
    if os.waitstatus_to_exitcode(status) != 0:
        sys.exit(f"{mod} ({config}) failed:\n{text[-4000:]}"
                 f"{stderr.decode('utf-8', 'replace')[-4000:]}")
    messages, other = [], stderr.decode("utf-8", "replace").splitlines()
    for line in text.splitlines():
        if line.startswith("{"):
            try:
                messages.append(json.loads(line))
            except ValueError:
                sys.exit(f"{mod} ({config}): unparsable message: {line[:200]}")
        else:
            other.append(line)
    outputs = {p: (out / p).read_bytes() for p in ("m.olean", "m.ilean", "m.c")}
    return {
        "wall": wall, "cpu": usage.ru_utime + usage.ru_stime,
        "rss_mb": usage.ru_maxrss / 1024, "log_bytes": len(stdout) + len(stderr),
        "messages": messages, "other": other, "outputs": outputs,
    }


def decl_names(path):
    """Maps each line number of `path` to the declaration it is in. A
    declaration's doc comment and attributes are part of its command, where
    Lean places its messages without `Elab.async` (with it, at its name)."""
    names, current, header = {}, None, None
    for n, line in enumerate(path.read_text().splitlines(), 1):
        m = DECL.match(line)
        if m:
            current = m.group(1) or line.split()[0]
            for k in range(header or n, n):
                names[k] = current
            header = None
        elif header is None and line.startswith(("/--", "@[")):
            header = n
        names[n] = current
    return names


def attribution(messages, names):
    """Time per declaration, per kind of step, from `profiler` messages."""
    decls = {}
    for m in messages:
        if not m.get("pos"):
            continue
        # Without `Elab.async`, one message holds all of a command's lines.
        for line in m.get("data", "").splitlines():
            t = TOOK.match(line.strip())
            if not t:
                continue
            what, n, unit = t.group(1), float(t.group(2)), t.group(3)
            secs = n / 1000 if unit == "ms" else n
            # `blocked`: an async task waiting for another (e.g. the kernel
            # checking a lemma it uses), not work of its own.
            kind = ("kernel" if what == "type checking" else
                    "blocked" if what.startswith("blocked") else "elab")
            decl = names.get(m["pos"]["line"]) or f"line {m['pos']['line']}"
            d = decls.setdefault(
                decl, {"kernel": 0.0, "elab": 0.0, "blocked": 0.0})
            d[kind] += secs
    return decls


def kernel_coverage(run, decls):
    """The share of the module's kernel time (Lean's cumulative `type
    checking`) that its `profiler` lines attribute to declarations."""
    total = None
    for line in run["other"]:
        m = CUMULATIVE.match(line.rstrip("\n"))
        if m and m.group(1) == "type checking":
            total = float(m.group(2)) / (1000 if m.group(3) == "ms" else 1)
    if not total:
        return None
    return sum(d["kernel"] for d in decls.values()) / total


def top(decls, n=5):
    return sorted(decls, key=lambda d: -(decls[d]["kernel"] + decls[d]["elab"]))[:n]


def pct(x):
    return "n/a" if x is None else f"{100 * x:.0f}%"


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("modules", nargs="*", default=DEFAULT_MODULES)
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--threshold", type=int, default=1,
                        help="profiler.threshold, in ms (default 1)")
    parser.add_argument("--json", help="write the full results here")
    args = parser.parse_args()
    if not shutil.which("lake"):
        sys.exit("lake is not on PATH")
    for mod in args.modules:
        if not setup_file(mod).exists():
            sys.exit(f"no setup file for {mod}: run `lake build +{mod}` first")

    results = {}
    for mod in args.modules:
        names = decl_names(source_file(mod))
        samples = {c: [] for c in CONFIGS}
        identical, profile_bytes, decls = True, [], {}
        coverage = {"prof": [], "ref": []}
        with tempfile.TemporaryDirectory() as tmp:
            dirs = {c: pathlib.Path(tmp, c) for c in CONFIGS}
            for d in dirs.values():
                d.mkdir()
            for _ in range(args.runs):
                runs = {}
                for c in CONFIGS:
                    runs[c] = run(mod, c, args.threshold, dirs[c])
                    samples[c].append(runs[c])
                identical &= runs["prof"]["outputs"] == runs["base"]["outputs"]
                profile_bytes.append(
                    runs["prof"]["log_bytes"] - runs["base"]["log_bytes"])
                for c in ("prof", "ref"):
                    run_decls = attribution(runs[c]["messages"], names)
                    cov = kernel_coverage(runs[c], run_decls)
                    if cov is not None:
                        coverage[c].append(cov)
                    for d, v in run_decls.items():
                        acc = decls.setdefault(c, {}).setdefault(
                            d, {k: [] for k in v})
                        for k in v:
                            acc[k].append(v[k])
        med = {
            c: {k: statistics.median(s[k] for s in samples[c])
                for k in ("wall", "cpu", "rss_mb")}
            for c in CONFIGS
        }
        attr = {
            c: {d: {k: sum(v[k]) / args.runs for k in v} for d, v in ds.items()}
            for c, ds in decls.items()
        }
        results[mod] = {
            "median": med, "identical_outputs": identical,
            "profile_bytes": statistics.median(profile_bytes),
            "attribution": attr,
            "kernel_coverage": {c: statistics.median(v) if v else None
                                for c, v in coverage.items()},
            "top_overlap": len(set(top(attr.get("prof", {})))
                               & set(top(attr.get("ref", {})))),
        }
        b, p = med["base"], med["prof"]
        print(f"{mod}\n"
              f"  base {b['wall']:.2f}s wall {b['cpu']:.2f}s cpu  "
              f"prof {p['wall']:.2f}s wall {p['cpu']:.2f}s cpu  "
              f"({100 * (p['wall'] / b['wall'] - 1):+.1f}% wall, "
              f"{100 * (p['cpu'] / b['cpu'] - 1):+.1f}% cpu)  "
              f"ref {med['ref']['wall']:.2f}s wall\n"
              f"  outputs identical: {identical}  "
              f"profile: {results[mod]['profile_bytes']:.0f} bytes\n"
              f"  kernel time attributed: "
              f"{pct(results[mod]['kernel_coverage']['prof'])} "
              f"(ref {pct(results[mod]['kernel_coverage']['ref'])})  "
              f"top 5 shared with ref: {results[mod]['top_overlap']}\n"
              f"  top (prof): {top(attr.get('prof', {}))}\n"
              f"  top (ref):  {top(attr.get('ref', {}))}", flush=True)

    tot = {c: {k: sum(r["median"][c][k] for r in results.values())
               for k in ("wall", "cpu")} for c in CONFIGS}
    print(f"\ntotal: base {tot['base']['wall']:.1f}s wall "
          f"{tot['base']['cpu']:.1f}s cpu, prof {tot['prof']['wall']:.1f}s "
          f"wall {tot['prof']['cpu']:.1f}s cpu "
          f"({100 * (tot['prof']['wall'] / tot['base']['wall'] - 1):+.1f}% wall, "
          f"{100 * (tot['prof']['cpu'] / tot['base']['cpu'] - 1):+.1f}% cpu); "
          f"outputs identical: "
          f"{all(r['identical_outputs'] for r in results.values())}")
    if args.json:
        pathlib.Path(args.json).write_text(json.dumps(results, indent=1))


if __name__ == "__main__":
    main()
