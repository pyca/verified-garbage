"""Benchmark results as JSON, and the interactive page that charts them.

    python3 ci/bench_report.py collect [CRITERION_DIR] [-o FILE] [--meta KEY=VALUE ...]
    python3 ci/bench_report.py html FILE_OR_DIR ... [-o FILE] [--title TITLE]

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
                d.setdefault("name", p.name)
                files.append(d)
    return files


def embed(template, files, title=None):
    """The page `template` with `files` built in (and, if given, `title`)."""
    # `</` would end the script element early; in JSON, `<\/` is the same string.
    data = json.dumps({"files": files}, separators=(",", ":")).replace("</", "<\\/")
    page, n = DATA.subn(lambda m: m[1] + data + m[3], template, count=1)
    if n != 1:
        raise SystemExit(f"{TEMPLATE}: no bench-data script element to fill")
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
        args.output.write_text(embed(TEMPLATE.read_text(), files, args.title))
        n = sum(len(f["results"]) for f in files)
        print(f"{args.output}: {n} results from {len(files)} file(s)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
