#!/usr/bin/env python3
"""Opt-in generated Lean projects for testing import plans against the compiler.

Unlike the normal unit suite, this deliberately spends seconds per project.
It compiles baseline and edited sources and, for instance-order projects,
compares evaluated values. No Lake build or repository proof edit is needed.

  python3 ci/stress_lean_imports.py --kind instances --projects 40 --output /tmp/import-stress
  python3 ci/stress_lean_imports.py --kind phases --projects 160 --seed 7312931 --output /tmp/import-phases
  python3 ci/stress_lean_imports.py --kind initializers --projects 40 --output /tmp/import-initializers
  python3 ci/stress_lean_imports.py --kind macro-initializers --projects 40 --output /tmp/import-macro-initializers

Each case saves sources, reader answers, a replay snapshot, the plan and its
outcome. Stop at the first failure; its seed and case number reproduce the
generated project.
"""

import argparse
from dataclasses import asdict
import json
import pathlib
import random
import sys
import time
import traceback
from unittest import mock

import check_lean_public_imports as check
import lean_import_replay as replay
from test_check_lean_import_integration import LEAN, LeanImports


def effect_project(fixture, rng, initializers=False, generated=False):
    fixture.write("E", "public initialize counter : IO.Ref Nat ← IO.mkRef 0\n" if initializers else
                  "@[expose] public section\nclass Chosen where\n  value : Nat\n"
                  "def chosen [Chosen] : Nat := Chosen.value\n")
    fixture.compile("E")
    if generated:
        fixture.write("D", "public meta import Lean\npublic import VerifiedGarbage.E\n"
                      'macro "append_digit " digit:num : command =>\n'
                      '  `(initialize counter.modify fun n => n * 10 + $digit)\n')
        fixture.compile("D")
    children = [f"VerifiedGarbage.C{i}" for i in range(5)]
    for i, mod in enumerate(children):
        body = (f"import VerifiedGarbage.D\nappend_digit {i + 1}\n" if generated else
                f"initialize counter.modify fun n => n * 10 + {i + 1}\n" if initializers else
                f"public instance choice{i} : Chosen := ⟨{i}⟩\n")
        fixture.write_module(mod, "public import VerifiedGarbage.E\n" + body)
        fixture.compile_module(mod)
    shims = [f"VerifiedGarbage.S{i}" for i in range(3)]
    for mod in shims:
        # import-all can make a dependency's initializer executable while
        # constructing this shim. Supply its shared runtime prerequisite
        # explicitly, so random visibility combinations have valid baselines.
        lines = ["meta import VerifiedGarbage.E\n"] if initializers else []
        for dep in rng.sample(children, len(children)):
            if rng.random() < .65:
                public, meta = rng.choice([True, False]), rng.choice([True, False])
                all_ = not public and rng.random() < .2
                lines.append(("public " if public else "") + ("meta " if meta else "")
                             + "import " + ("all " if all_ else "") + dep + "\n")
        fixture.write_module(mod, "".join(lines))
        fixture.compile_module(mod)
    prerequisite = "meta import VerifiedGarbage.E\n" if initializers else ""
    fixture.write("U", prerequisite + "".join("public import " + m + "\n" for m in rng.sample(children, len(children))))
    fixture.compile("U")
    roots = rng.sample(shims, len(shims)) + ["VerifiedGarbage.U"]
    evaluation = ("#eval counter.get\n" if initializers else
                  "@[expose] public def chosenValue : Nat := chosen\n#eval chosenValue\n")
    fixture.write("A", ("public import VerifiedGarbage.E\n" + prerequisite if initializers else "")
                  + "".join("public import " + m + "\n" for m in roots)
                  + "".join("meta import " + m + "\n" for m in roots)
                  + evaluation)
    fixture.compile("A")
    return ["VerifiedGarbage.E", *(["VerifiedGarbage.D"] if generated else []),
            *children, *shims, "VerifiedGarbage.U", "VerifiedGarbage.A"], "VerifiedGarbage.A"


def phase_project(fixture, rng):
    modules = [f"VerifiedGarbage.M{i}" for i in range(8)]
    for i, mod in enumerate(modules):
        edges = []
        for dep in modules[:i]:
            if rng.random() < .45:
                for _ in range(rng.choice([1, 1, 1, 2])):
                    public, meta = rng.choice([False, True]), rng.choice([False, False, True])
                    all_ = not public and rng.random() < .12
                    edges.append(("public " if public else "") + ("meta " if meta else "")
                                 + "import " + ("all " if all_ else "") + dep + "\n")
        fixture.write_module(mod, "".join(edges))
    graph = check.Graph([fixture.root])
    for i, mod in enumerate(modules):
        def values(owners, prefix):
            return [prefix + m.rpartition("M")[2] for m in sorted(owners) if m in modules]

        def pick(options):
            return rng.choice(options) if options and rng.random() < .85 else str(i)

        public, private = graph.passes(mod) - {mod}, graph.reads(mod)
        meta_public, meta_private = graph.meta_exports(mod), graph.reads(mod, True)
        body = (f"\n@[expose] public def v{i} : Nat := {pick(values(public, 'v'))}\n"
                f"public meta def m{i} : Nat := {pick(values(public, 'm') + values(meta_public, 'v'))}\n"
                f"private def p{i} : Nat := {pick(values(private, 'v'))}\n"
                f"private meta def q{i} : Nat := {pick(values(private, 'm') + values(meta_private, 'v'))}\n")
        path = check.graph_path(mod)
        path.write_text(path.read_text() + body)
    for mod in modules:
        fixture.compile_module(mod)
    return modules, None


def sources(root):
    return {".".join(path.relative_to(root).with_suffix("").parts): path.read_text()
            for path in sorted((root / "VerifiedGarbage").rglob("*.lean"))}


def run_case(kind, rng, output, seed, number):
    fixture = LeanImports()
    record = {"kind": kind, "seed": seed, "case": number, "status": "started"}
    started = time.monotonic()
    evidence = None
    try:
        fixture.setUp()
        with mock.patch.object(check, "LEAN", fixture.root), mock.patch.object(check, "ROOT", fixture.root.parent):
            record["phase"] = "baseline"
            modules, evaluated = (phase_project(fixture, rng) if kind == "phases" else
                                  effect_project(fixture, rng, initializers=kind.endswith("initializers"),
                                                 generated=kind == "macro-initializers"))
            record["before"] = sources(fixture.root)
            if evaluated:
                path = check.graph_path(evaluated)
                record["baseline_value"] = fixture.run_lean(path).strip()
            record["phase"] = "planning"
            graph = check.Graph([fixture.root])
            evidence = replay.Evidence(fixture.uses, 4)
            shaken = replay.discover(modules, {}, graph, evidence)
            plan = check.analyze(modules, shaken, graph, uses=evidence, library=modules)
            record["edits"] = [asdict(e) for e in plan.edits]
            record["deferred"] = plan.deferred
            replay.save(output / f"{number:04}-evidence.json.gz",
                        replay.capture(modules, modules, graph, {}, evidence, {}, True))
            record["phase"] = "editing"
            check.fix(plan)
            record["after"] = sources(fixture.root)
            record["phase"] = "verification"
            for mod in modules:
                fixture.compile_module(mod)
            if evaluated:
                record["edited_value"] = fixture.run_lean(path).strip()
                if record["baseline_value"] != record["edited_value"]:
                    raise AssertionError(f"evaluated value changed: {record['baseline_value']} -> {record['edited_value']}")
            record["status"] = "passed"
    except BaseException:
        record["status"] = "failed"
        record["error"] = traceback.format_exc()
        if hasattr(fixture, "root"):
            record["failure_sources"] = sources(fixture.root)
        raise
    finally:
        record["elapsed_seconds"] = time.monotonic() - started
        if evidence is not None:
            record["evidence"] = evidence.data
        replay.save(output / f"{number:04}.json", record)
        fixture.doCleanups()
    return record


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--kind", choices=["phases", "instances", "initializers", "macro-initializers"],
                        default="instances")
    parser.add_argument("--projects", type=int, default=40)
    parser.add_argument("--seed", type=int, default=7312941)
    parser.add_argument("--output", type=pathlib.Path, required=True)
    args = parser.parse_args(argv)
    if not LEAN:
        parser.error("Lean is required; put the repository's toolchain on PATH")
    if args.projects < 1:
        parser.error("--projects must be positive")
    if args.output.exists() and any(args.output.iterdir()):
        parser.error("--output must be empty so earlier failure evidence is preserved")
    args.output.mkdir(parents=True, exist_ok=True)
    rng = random.Random(args.seed)
    records = []
    try:
        for number in range(args.projects):
            row = run_case(args.kind, rng, args.output, args.seed, number)
            records.append(row)
            print(f"PASS {number}: {len(row['edits'])} operations; {row['elapsed_seconds']:.2f}s", flush=True)
    finally:
        replay.save(args.output / "summary.json", {
            "kind": args.kind, "seed": args.seed, "requested_projects": args.projects,
            "analyzer": replay.analyzer_key(), "lean": LEAN,
            "passed_projects": len(records), "verified_operations": sum(len(r["edits"]) for r in records),
            "elapsed_seconds": sum(r["elapsed_seconds"] for r in records),
        })
    return 0


if __name__ == "__main__":
    sys.exit(main())
