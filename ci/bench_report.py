"""Benchmark results as JSON, and the interactive page that charts them.

    python3 ci/bench_report.py collect [CRITERION_DIR] [-o FILE] [--meta KEY=VALUE ...]
    python3 ci/bench_report.py html FILE_OR_DIR ... [-o FILE] [--title TITLE] [--chart PATTERNS ...]

`collect` reads the results of a local `cargo bench` (Criterion's
directory, by default `bench/target/criterion`) into a results file:
the median time of each benchmark, by `<group>/<library>/<size>` (the ids of
bench/benches/primitives/main.rs), with what this machine and checkout were
(architecture, CPU model, `VG_CPU_FEATURES`, commit). `ci/bench_compare.py
--json` writes the same format for the Benchmarks workflow, with each
benchmark's side (`base` or `head`) and every run's time. `--meta` adds
fields of the run (a label to tell runs apart, say), which the page offers
like any other.

`html` writes `bench_report.html` (the page; open it alone to load results
files by hand) with the results files given, or every `*.json` in the
directories given, built in, so that the one file is the whole report.
Each `--chart` is a chart the page starts with, combining the benchmarks
that its space-separated regular expressions match, each a whole group's
name (`ecdh_p(256|384|521)`: every size of each) or a whole `group/size`
(`ecdsa_p256_sha256_sign/64`: the chart starts with the group's other sizes
hidden). E.g. ECDH and ECDSA signatures of 64 bytes, by curve:

    python3 ci/bench_report.py html results/ \
      --chart 'ecdh_p(256|384|521) ecdsa_p(256_sha256|384_sha384|521_sha512)_sign/64'

A pattern that matches nothing is skipped, with a warning (a run need not
have measured every benchmark).

A results file is

    {"format": "verified-garbage-bench", "version": 1,
     "id": "...",                        # unique per run, to skip a file loaded twice
     "context": {"arch": "x86_64", ...}, # the run's fields: strings or numbers
     "results": [{"group": "ecdh_p256", "library": "verified-garbage", "size": 32,
                  "side": "head", "commit": "...", "time_ns": 12345.6,
                  "samples": [12345.6, ...]}, ...]}

and the page also reads a list of them (`{"files": [...]}`, what `html`
builds in) and another report's page, whose built-in results it takes.
"""

import argparse
import hashlib
import json
import os
import pathlib
import platform
import re
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
TEMPLATE = pathlib.Path(__file__).resolve().parent / "bench_report.html"
FORMAT = "verified-garbage-bench"
VERSION = 1
# Where the page reads its built-in results from: the template's is empty.
DATA = re.compile(r'(<script type="application/json" id="bench-data">)(.*?)(</script>)', re.S)
# And the charts it starts with (`--chart`).
VIEW = re.compile(r'(<script type="application/json" id="bench-view">)(.*?)(</script>)', re.S)


def bench_size(size):
    """A benchmark's parameter, from its directory name: the number for a
    size (`1024`), the name itself for anything else (`mul_acc4`)."""
    return int(size) if size.isdecimal() else size


def record(group, library, size, time_ns, samples=None, side=None, commit=None):
    """One benchmark's result, in a results file's `results`."""
    r = {"group": group, "library": library, "size": size, "time_ns": time_ns}
    if samples and len(samples) > 1:
        r["samples"] = samples
    if side is not None:
        r["side"] = side
    if commit is not None:
        r["commit"] = commit
    return r


def document(context, results):
    """A results file of `results` (`record`s), measured in `context`."""
    context = {k: v for k, v in context.items() if v is not None}
    digest = hashlib.sha256(json.dumps([context, results], sort_keys=True).encode()).hexdigest()
    return {"format": FORMAT, "version": VERSION, "id": digest[:16], "context": context, "results": results}


def parse_meta(pairs):
    """`--meta KEY=VALUE` arguments as a dict."""
    meta = {}
    for pair in pairs or []:
        key, sep, value = pair.partition("=")
        if not sep or not key:
            raise SystemExit(f"--meta {pair!r}: expected KEY=VALUE")
        meta[key] = value
    return meta


def git(checkout, *args):
    """A `git` command's output in `checkout`, or None where it fails."""
    try:
        # (A job in a container owns no checkout: git refuses it as unsafe.)
        out = subprocess.run(["git", "-c", "safe.directory=*", "-C", str(checkout), *args],
                             capture_output=True, text=True, check=True)
    except (OSError, subprocess.CalledProcessError):
        return None
    return out.stdout.strip() or None


def commit_of(checkout):
    """`checkout`'s commit, or None if it is no git checkout."""
    return git(checkout, "rev-parse", "HEAD")


def arch_name():
    """This machine's architecture, by ci/bench_arches.py's names."""
    machine = platform.machine().lower()
    return {"amd64": "x86_64", "arm64": "aarch64", "i386": "x86", "i686": "x86",
            "ppc64le": "powerpc64"}.get(machine, machine)


def read_criterion(home):
    """Each benchmark's median time (ns) under the Criterion directory
    `home`, as `(group, library, size, time)`."""
    found = []
    for est in sorted(pathlib.Path(home).glob("*/*/*/new/estimates.json")):
        group, library, size = est.relative_to(home).parts[:3]
        found.append((group, library, bench_size(size), json.loads(est.read_text())["median"]["point_estimate"]))
    return found


def collect(home, meta, cpu_model=None):
    """The results file of a local run's Criterion directory `home`."""
    commit = commit_of(ROOT)
    results = [record(g, lib, size, t, commit=commit) for g, lib, size, t in read_criterion(home)]
    context = {
        "arch": arch_name(),
        "os": platform.system(),
        "cpu": cpu_model,
        "cpu_features": os.environ.get("VG_CPU_FEATURES", ""),
        "ref": git(ROOT, "rev-parse", "--abbrev-ref", "HEAD"),
        "date": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "source": "local",
        **meta,
    }
    return document(context, results)


def load(paths):
    """The results files at `paths` (each a file, or a directory of
    `*.json`), as a list, skipping any loaded twice."""
    files, seen = [], set()
    for path in map(pathlib.Path, paths):
        for p in sorted(path.rglob("*.json")) if path.is_dir() else [path]:
            doc = json.loads(p.read_text())
            docs = doc["files"] if isinstance(doc, dict) and "files" in doc else doc if isinstance(doc, list) else [doc]
            for d in docs:
                if not isinstance(d, dict) or d.get("format") != FORMAT:
                    raise SystemExit(f"{p}: not a {FORMAT} results file")
                if d.get("id") in seen:
                    continue
                seen.add(d.get("id"))
                # A workflow's results files are all `bench-results.json`, each
                # in a directory named for its job's artifact: name them by it.
                d.setdefault("name", p.parent.name if path.is_dir() and p.parent != path else p.name)
                files.append(d)
    return files


def natural(s):
    """A sort key for names with numbers in them (p256 before p1024)."""
    return [int(t) if t.isdigit() else t for t in re.split(r"(\d+)", s)]


def charts(specs, files):
    """The charts that `--chart`s ask for, of the benchmarks in `files`:
    for each, its groups, and the `group/size`s it starts with hidden."""
    sizes = {}
    for f in files:
        for r in f["results"]:
            sizes.setdefault(str(r["group"]), set()).add(str(r["size"]))
    out, taken = [], set()
    for spec in specs:
        try:
            regexes = [re.compile(p) for p in spec.split()]
        except re.error as e:
            raise SystemExit(f"--chart {spec!r}: {e}")
        groups, shown = [], {}
        for rx in regexes:
            found = False
            for g in sorted(sizes, key=natural):
                picked = sizes[g] if rx.fullmatch(g) else {s for s in sizes[g] if rx.fullmatch(f"{g}/{s}")}
                if not picked:
                    continue
                found = True
                if g in taken:
                    raise SystemExit(f"--chart {spec!r}: {g} is in an earlier chart already")
                if g not in shown:
                    groups.append(g)
                    shown[g] = set()
                shown[g] |= picked
            if not found:
                print(f"warning: --chart {rx.pattern!r} matches no benchmark (a group's name, or a group/size)",
                      file=sys.stderr)
        if groups:
            taken.update(groups)
            out.append({"groups": groups,
                        "hide": [f"{g}/{s}" for g in groups for s in sorted(sizes[g] - shown[g], key=natural)]})
    return out


def script_json(value):
    """`value` as JSON to put in a script element: `</` would end it early,
    and in JSON `<\\/` is the same string."""
    return json.dumps(value, separators=(",", ":")).replace("</", "<\\/")


def embed(template, files, title=None, view=None):
    """The page `template` with `files` built in (and, if given, `title`,
    and the charts it starts with, `view`)."""
    data = script_json({"files": files})
    page, n = DATA.subn(lambda m: m[1] + data + m[3], template, count=1)
    if n != 1:
        raise SystemExit(f"{TEMPLATE}: no bench-data script element to fill")
    if view:
        page, n = VIEW.subn(lambda m: m[1] + script_json({"charts": view}) + m[3], page, count=1)
        if n != 1:
            raise SystemExit(f"{TEMPLATE}: no bench-view script element to fill")
    if title:
        escaped = title.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
        page = re.sub(r"<title>.*?</title>", lambda _: f"<title>{escaped}</title>", page, count=1)
    return page


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = p.add_subparsers(dest="command", required=True)
    c = sub.add_parser("collect", help="a results file from a local run's Criterion directory")
    c.add_argument("criterion", nargs="?", type=pathlib.Path, default=ROOT / "bench/target/criterion")
    c.add_argument("-o", "--output", type=pathlib.Path, default=pathlib.Path("bench-results.json"))
    c.add_argument("--meta", action="append", metavar="KEY=VALUE", help="a field of the run (repeatable)")
    h = sub.add_parser("html", help="the report page, with results files built in")
    h.add_argument("inputs", nargs="+", type=pathlib.Path)
    h.add_argument("-o", "--output", type=pathlib.Path, default=pathlib.Path("benchmarks.html"))
    h.add_argument("--title")
    h.add_argument("--chart", action="append", default=[], metavar="PATTERNS",
                   help="a chart to start with: space-separated regular expressions, each matching a whole "
                        "group name or group/size (repeatable)")
    args = p.parse_args(argv)

    if args.command == "collect":
        if not args.criterion.is_dir():
            p.error(f"{args.criterion}: no Criterion directory (run `cargo bench` in bench/ first)")
        from bench_compare import cpu_model
        doc = collect(args.criterion, parse_meta(args.meta), cpu_model())
        if not doc["results"]:
            p.error(f"{args.criterion}: no benchmark results")
        args.output.write_text(json.dumps(doc, indent=1) + "\n")
        print(f"{args.output}: {len(doc['results'])} results", file=sys.stderr)
    else:
        files = load(args.inputs)
        args.output.write_text(embed(TEMPLATE.read_text(), files, args.title, charts(args.chart, files)))
        n = sum(len(f["results"]) for f in files)
        print(f"{args.output}: {n} results from {len(files)} file(s)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
