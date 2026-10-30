"""Portable evidence and build-free replay for the import planner.

Snapshots contain the source/graph and declaration evidence actually consulted,
not a claim that a plan builds. Missing evidence is an error, never an empty use
set. Replaying may use a newer planner without trusting its old conclusions.
"""

from dataclasses import asdict
from collections import Counter
import hashlib
import gzip
import json
import pathlib

import check_lean_public_imports as check
import lean_profile
import lean_shards

SCHEMA = 1


def evidence_keys() -> dict[str, str]:
    base = pathlib.Path(check.__file__).parent
    toolchain = check.LEAN / "lean-toolchain"
    version = toolchain.read_bytes() if toolchain.is_file() else b""
    return {
        "shake": hashlib.sha256(b"shake-schema-1:--force:--only" + version).hexdigest(),
        "declarations": hashlib.sha256(b"uses-schema-1" + version + (base / "lean_module_uses.lean").read_bytes()).hexdigest(),
        "index": hashlib.sha256(b"index-schema-1" + version + (base / "lean_source_evidence.py").read_bytes()).hexdigest(),
    }


class MissingEvidence(ValueError):
    pass


def analyzer_key() -> str:
    paths = [pathlib.Path(__file__), pathlib.Path(check.__file__),
             pathlib.Path(check.__file__).with_name("lean_module_uses.lean"),
             pathlib.Path(check.__file__).with_name("lean_source_evidence.py"),
             pathlib.Path(check.__file__).with_name("lean_import_build.py"),
             pathlib.Path(check.__file__).with_name("lean_import_graph.py"),
             pathlib.Path(check.__file__).with_name("check_lean_imports.py"),
             pathlib.Path(check.__file__).with_name("trim_lean_imports.py")]
    toolchain = check.LEAN / "lean-toolchain"
    return hashlib.sha256(b"".join(p.read_bytes() for p in paths + [toolchain] if p.is_file())).hexdigest()


class Evidence:
    def __init__(self, read, batch: int):
        self.read = read
        self.batch = batch
        self.data: dict[str, dict[str, list[str]]] = {}

    def __call__(self, mods: list[str], view: str) -> dict[str, set[str]]:
        table = self.data.setdefault(view, {})
        todo = sorted(set(mods) - table.keys())
        # Metadata reads only each file's exported data, without importing its
        # dependency environment. A small root batch need not spawn a process
        # for every few providers; retain a separate bounded file batch.
        batch = 32 if view in ("effects", "namespace_exports") else self.batch
        for k in range(0, len(todo), batch):
            part = todo[k:k + batch]
            result = self.read(part, view)
            missing = set(part) - result.keys()
            if missing:
                raise MissingEvidence(f"{view} uses not returned for: {', '.join(sorted(missing))}")
            table.update({m: sorted(result[m]) for m in part})
        return {m: set(table[m]) for m in mods}


class DiscoverySuggestions(dict):
    """Candidates plus direct-use evidence that ruled out other hypotheses."""
    def __init__(self, values):
        super().__init__(values)
        self.retained: dict[tuple[str, str, str], str] = {}


def discover(mods: list[str], shaken: dict, graph: check.Graph, uses) -> dict:
    """Add hypotheses independently of shake; all still require build verification.

    Ordinary and private meta project imports are considered.
    The planner independently checks declaration uses and unknown side effects.
    """
    check.prepare_effects(graph, {x for m in mods for x, _, _, _ in check.header(graph.text(m))}, uses)
    public = uses(mods, "public")
    private = uses(mods, "private")
    meta_mods = [m for m in mods if any(meta and not pub and not all_ and graph.project(x) and not graph.kept(x)
                                      for x, pub, meta, all_ in check.header(graph.text(m)))]
    meta_private = uses(meta_mods, "meta_private") if meta_mods else {}
    result = DiscoverySuggestions({f: (list(rem), list(add)) for f, (rem, add) in shaken.items()})
    for mod in mods:
        rem, add = result.setdefault(str(check.graph_path(mod)), ([], []))
        for x, pub, meta, all_ in check.header(graph.text(mod)):
            if (meta and pub) or all_ or not graph.project(x) or graph.kept(x):
                continue
            action = "demote" if pub else "remove_meta" if meta else "remove"
            if meta and x not in meta_private[mod]:
                candidate = f"meta import {x}"
            elif meta:
                result.retained[mod, x, action] = "direct_meta_dependency"
                continue
            elif pub and x not in public[mod]:
                candidate = f"public import {x}"
            elif not pub and x not in private[mod]:
                # A transitive use may have another provider. Rejecting the
                # entire closure here hides redundant imports (and every
                # closure contains implicitly imported Init). analyze checks
                # actual visibility losses against all evidence and effects.
                candidate = f"import {x}"
            else:
                result.retained[mod, x, action] = (
                    "public_declaration_dependency" if pub else "direct_private_dependency")
                continue
            if candidate not in rem:
                rem.append(candidate)
            # Shake may disagree: independent hypotheses are deliberately not
            # vetoed by it. Public uses/keep markers are checked by the planner.
            add[:] = [s for s in add if s != candidate]
    return result


def profile_cost(mods: list[str]) -> dict[str, float]:
    """Recorded profiled work, excluding blocked time; not elapsed build time."""
    result = {}
    build = check.LEAN / ".lake/build/lib/lean"
    stored = lean_profile.stored_logs(build)
    for mod in mods:
        path = build / pathlib.Path(*mod.split(".")).with_suffix(".trace")
        try:
            trace = json.loads(path.read_text())
        except (OSError, ValueError):
            continue
        steps = list(lean_profile.steps(lean_profile.trace_log(trace, stored.get(mod))))
        if steps:
            result[mod] = sum(seconds for _, _, kind, seconds in steps if kind != "blocked")
    return result


def cost(plan: check.Plan, graph: check.Graph, library: list[str], profile: dict[str, float]) -> dict:
    """Conservative verification scope on a warm build, with shared work once."""
    edited = sorted({e.module for e in plan.edits})
    targets = set(edited)
    ranked = []
    for mod in edited:
        affected = {mod} | graph.importers(mod, library)
        targets.update(affected)
        ranked.append({"module": mod, "affected_modules": len(affected),
                       "known_profile_work_seconds": sum(profile.get(m, 0) for m in affected),
                       "unprofiled_modules": len(affected - profile.keys())})
    return {"edited_modules": edited, "verification_targets": sorted(targets),
            "affected_modules": len(targets),
            "known_profile_work_seconds": sum(profile.get(m, 0) for m in targets),
            "unprofiled_modules": len(targets - profile.keys()),
            "ranked": sorted(ranked, key=lambda r: (r["affected_modules"], r["known_profile_work_seconds"], r["module"])),
            "basis": "conservative library reverse closure; warm dependencies; profile work is not wall time"}


def visibility_impact(plan: check.Plan, graph: check.Graph, targets: list[str]) -> dict:
    """Model exposure changes, without presenting them as build-time savings."""
    basis = "ordinary/meta visibility in the affected library scope; not a recompilation or wall-time prediction"
    if len(targets) > 250:
        return {"evaluated": False, "basis": basis, "reason": "scope exceeds 250 modules; select a smaller batch"}
    after = check.Planned(graph, plan.edits)
    measurements = {
        "ordinary_reads": (graph.reads, after.reads),
        "meta_reads": (lambda m: graph.reads(m, True), lambda m: after.reads(m, True)),
        "ordinary_reexports": (graph.passes, after.passes),
        "meta_reexports": (graph.meta_exports, after.meta_exports),
    }
    totals, losses, gains = {}, {}, {}
    for kind, (before, planned) in measurements.items():
        lost, gained = Counter(), Counter()
        for mod in targets:
            old, new = before(mod), planned(mod)
            lost.update(old - new)
            gained.update(new - old)
        totals[kind] = {"removed_pairs": sum(lost.values()), "added_pairs": sum(gained.values())}
        losses[kind], gains[kind] = lost, gained
    dependencies = set().union(*(table.keys() for table in losses.values()), *(table.keys() for table in gains.values()))
    ranked = [{"dependency": dep, **{kind: {"removed_readers": losses[kind][dep], "added_readers": gains[kind][dep]}
                                    for kind in measurements}} for dep in dependencies]
    ranked.sort(key=lambda x: tuple(-(x[k]["removed_readers"] + x[k]["added_readers"]) for k in measurements)
                + (x["dependency"],))
    return {"evaluated": True, "basis": basis, "scope_modules": len(targets), "totals": totals,
            "largest_changes": ranked[:20], "dependencies_with_changes": len(ranked)}


def rebuild_impact(plan: check.Plan, graph: check.Graph, targets: list[str]) -> dict:
    """Compare project source dependencies in Lake traces, not declaration access."""
    basis = "Lake source dependencies, including meta IR; excludes native libraries and wall time"
    if len(targets) > 250:
        return {"evaluated": False, "basis": basis, "reason": "scope exceeds 250 modules; select a smaller batch"}

    def dependencies(view):
        imps, vis, modes = {}, {}, {}
        pending = list(targets)
        while pending:
            mod = pending.pop()
            if mod in imps:
                continue
            edges = [edge for edge in view.imports(mod) if graph.project(edge[0])]
            imps[mod] = list(dict.fromkeys(i for i, _, _, _ in edges))
            vis[mod] = ([i for i, public, _, _ in edges if public],
                        [i for i, _, _, all_ in edges if all_]) if check.is_module(graph.text(mod)) else None
            modes[mod] = {"meta": [i for i, _, meta, _ in edges if meta],
                          "public_meta": [i for i, public, meta, _ in edges if public and meta]}
            pending.extend(imps[mod])
        return lean_shards.reads(imps, lean_shards.closures(imps), vis, modes)

    before = dependencies(graph)
    after = dependencies(check.Planned(graph, plan.edits))
    lost, gained = Counter(), Counter()
    for mod in targets:
        lost.update(before[mod] - after[mod])
        gained.update(after[mod] - before[mod])
    return {"evaluated": True, "basis": basis, "scope_modules": len(targets),
            "removed_pairs": sum(lost.values()), "added_pairs": sum(gained.values()),
            "largest_changes": [{"dependency": dep, "removed_readers": lost[dep], "added_readers": gained[dep]}
                                for dep in sorted(lost.keys() | gained.keys(),
                                                  key=lambda d: (-(lost[d] + gained[d]), d))[:20]]}


def report(plan: check.Plan, estimate: dict, graph: check.Graph | None = None) -> dict:
    result = {"build_verified": False, "edits": [asdict(e) for e in plan.edits],
            "findings": plan.messages, "blocked": plan.blocked, "deferred": plan.deferred,
            "decisions": plan.decisions, "cost": estimate}
    if graph is not None:
        for key, measure in (("visibility_impact", visibility_impact), ("rebuild_impact", rebuild_impact)):
            try:
                result[key] = measure(plan, graph, estimate["verification_targets"])
            except MissingEvidence as error:
                # Old captures need not contain optional diagnostic evidence.
                result[key] = {"evaluated": False, "reason": "optional impact evidence was not captured",
                               "detail": str(error)}
    return result


def bounded(plan: check.Plan, shaken: dict, graph: check.Graph, uses, library: list[str],
            limit: int, profile: dict[str, float] | None = None) -> check.Plan:
    """Select primary source modules within a shared verification budget.

    Repairs aren't independent candidates. Replan the chosen sources together,
    so every repair follows the subset's actual combined visibility losses.
    """
    if plan.blocked:
        return plan
    profile = profile or {}
    candidates = {e.module for e in plan.edits if e.action in check.NARROWING}
    scopes = {m: {m} | graph.importers(m, library) for m in candidates}
    ordered = sorted(candidates, key=lambda m: (len(scopes[m]), len(scopes[m] - profile.keys()),
                                               sum(profile.get(j, 0) for j in scopes[m]), m))
    selected, targets, deferred = [], set(), []
    for mod in ordered:
        if len(targets | scopes[mod]) <= limit:
            selected.append(mod)
            targets.update(scopes[mod])
        else:
            deferred.append({"module": mod, "reason": "verification target budget", "limit": limit,
                             "candidate_targets": len(scopes[mod])})
    if not deferred:
        return plan
    result = check.analyze(selected, shaken, graph, uses=uses, library=library) if selected else check.Plan()
    for item in plan.deferred + deferred:
        if item not in result.deferred:
            result.deferred.append(item)
    kept = {e.module for e in result.edits if e.action in check.NARROWING}
    identity = lambda d: (d["module"], d["dependency"], d["action"], d["meta"], d["import_all"])
    known = {identity(d) for d in result.decisions}
    for decision in plan.decisions:
        key = identity(decision)
        if key not in known:
            decision = dict(decision)
            if decision["status"] == "proposed" and decision["module"] not in kept:
                decision.update(status="deferred", reason="verification_target_budget", evidence={"limit": limit})
            result.decisions.append(decision)
    result.decisions.sort(key=identity)
    return result


def save(path: pathlib.Path, data: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    if path.suffix == ".gz":
        output = gzip.open(tmp, "wt", encoding="utf-8", compresslevel=3)
    else:
        output = tmp.open("w")
    with output:
        json.dump(data, output, sort_keys=True, indent=2)
        output.write("\n")
    tmp.replace(path)


def load(path: pathlib.Path) -> dict:
    with (gzip.open(path, "rt", encoding="utf-8") if path.suffix == ".gz" else path.open()) as source:
        return json.load(source)


def capture(mods: list[str], library: list[str], graph: check.Graph, shaken: dict,
            evidence: Evidence, profile: dict[str, float], independent: bool, max_affected: int | None = None) -> dict:
    # Paths are stored as module identities plus project membership, so a
    # snapshot can be moved between checkouts without retaining absolute paths.
    sources = {m: {"project": graph.project(m), "text": t} for m, t in list(graph.texts.items())}
    modules = {m: None if p is None else graph.project(m) for m, p in list(graph.files.items())}
    return {"schema": SCHEMA, "analyzer": analyzer_key(), "modules": modules, "sources": sources,
            "selected": mods, "library": library, "independent": independent,
            "shake": {m: shaken.get(str(check.graph_path(m)), ([], [])) for m in mods},
            "uses": evidence.data, "users": {m: sorted(js) for m, js in (graph.users or {}).items()},
            "profile": profile, "max_affected": max_affected}


class ReplayGraph(check.Graph):
    def __init__(self, data: dict):
        super().__init__([])
        self.data = data
        self.users = {m: set(js) for m, js in data["users"].items()}

    def path(self, mod: str) -> pathlib.Path | None:
        if mod not in self.data["modules"]:
            raise MissingEvidence(f"source availability of {mod} was not captured")
        project = self.data["modules"][mod]
        if project is None:
            return None
        root = check.LEAN if project else check.ROOT / "captured-dependencies"
        return root.joinpath(*mod.split(".")).with_suffix(".lean")

    def text(self, mod: str) -> str:
        if mod not in self.data["sources"]:
            raise MissingEvidence(f"source of {mod} was not captured")
        return self.data["sources"][mod]["text"]


def replay(data: dict, independent: bool | None = None, max_affected: int | None = None) -> dict:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported import snapshot schema")
    graph = ReplayGraph(data)

    def uses(mods, view):
        table = data["uses"].get(view, {})
        missing = set(mods) - table.keys()
        if missing:
            raise MissingEvidence(f"{view} evidence missing for {', '.join(sorted(missing))}; recapture with this analysis")
        return {m: set(table[m]) for m in mods}

    shaken = {str(check.graph_path(m)): v for m, v in data["shake"].items()}
    discover_independently = data["independent"] if independent is None else independent
    if discover_independently:
        shaken = discover(data["selected"], shaken, graph, uses)
    plan = check.analyze(data["selected"], shaken, graph, uses=uses, library=data["library"])
    limit = data.get("max_affected") if max_affected is None else max_affected
    if limit is not None:
        plan = bounded(plan, shaken, graph, uses, data["library"], limit, data["profile"])
    return report(plan, cost(plan, graph, data["library"], data["profile"]), graph)
