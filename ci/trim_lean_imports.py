#!/usr/bin/env python3
"""Trims the import headers of many modules at once: the bulk form of
`check_lean_public_imports.py --fix`, for a change too large for it (a
refactor touching thousands of modules) or a sweep of the library.

Round after round, it finds every import of the modules to change (not only
those a change added): a `public import` used only privately, made plain,
with the module importing publicly what it used through it and the modules
importing it given what they used; a plain import nothing uses, removed.
It applies them, builds what it edited and every module importing those,
and undoes the edits of a file that then fails, nearest first. It stops
when a round finds nothing, or makes no change that builds.

  trim_lean_imports.py -m MOD...        those modules
  trim_lean_imports.py --base REV       the modules changed since REV
  trim_lean_imports.py --all            every module of the library
  … --batch N       modules per `lake shake` call (default 1000): shake loads
                    every module it is given at once, about 3 GB per 1,000
  … --rounds N      at most N rounds (default 5)
  … --capture FILE  analyze once and save replayable evidence; no edits
  … --dry-run       report operations and conservative verification scope
  … --discover      also consider declaration-based hypotheses shake missed
  … --no-shake      with --discover, skip shake (still check selected builds)
  … --max-affected N  select a subset within N verification targets
  trim_lean_imports.py --replay FILE [--report FILE]  no Lake calls

It never edits registrations or variants (`Artifacts/`, `Generic/`,
`Variants/`). Its state is in `lean/.lake/trim-imports.json`: each module's
`lake shake` suggestions and uses, keyed by the hash Lake records of the
module's inputs and outputs (its `.trace`), so a round or a rerun analyses
again only the modules whose build changed. Analyzer/toolchain changes
invalidate that state. Rejected batches are retried only when their context
changes. Run it after building; it prints its phases and
writes its builds' output to `lean/.lake/check-imports-build.log`.
"""

import argparse
import hashlib
import json
import pathlib
import subprocess
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).parent))
import check_lean_public_imports as check  # noqa: E402
import lean_import_replay as replay  # noqa: E402

STATE = check.LEAN / ".lake" / "trim-imports.json"


def trace_key(mod: str) -> str | None:
    """Lake's hash of the module's inputs (its source, its imports' outputs,
    the options) and its outputs' hashes, from its `.trace`; None without a
    build."""
    path = check.LEAN / ".lake/build/lib/lean" / pathlib.Path(*mod.split(".")).with_suffix(".trace")
    try:
        trace = json.loads(path.read_text())
    except (OSError, ValueError):
        return None
    if not isinstance(trace, dict) or "depHash" not in trace or not trace.get("outputs"):
        return None
    return hashlib.sha256(json.dumps([trace["depHash"], trace["outputs"]], sort_keys=True).encode()).hexdigest()


def source_key(mod: str) -> str | None:
    trace = trace_key(mod)
    try:
        source = check.graph_path(mod).read_bytes()
    except OSError:
        return None
    if trace is None:
        return None
    return hashlib.sha256(trace.encode() + hashlib.sha256(source).digest()).hexdigest()


class State:
    """What earlier rounds and runs found, by module and trace key."""

    def __init__(self, path: pathlib.Path):
        self.path = path
        try:
            data = json.loads(path.read_text())
        except (OSError, ValueError):
            data = {}
        self.analyzer = replay.analyzer_key()
        self.keys = replay.evidence_keys()
        if not isinstance(data, dict):
            data = {}
        previous = data.get("keys", {})
        self.shake: dict = data.get("shake", {}) if previous.get("shake") == self.keys["shake"] else {}
        self.uses: dict = {view: table for view, table in data.get("uses", {}).items()
                          if previous.get("index" if view in ("references", "namespaces") else "declarations")
                          == self.keys["index" if view in ("references", "namespaces") else "declarations"]}
        self.undone: set[str] = set(data.get("undone", [])) if data.get("analyzer") == self.analyzer else set()
        self.module_rejections: dict[str, dict[str, dict]] = (data.get("module_rejections", {})
                                                            if data.get("analyzer") == self.analyzer else {})
        self.current: dict[str, str | None] = {}

    def save(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        replay.save(self.path, {"analyzer": self.analyzer, "keys": self.keys, "shake": self.shake,
                               "uses": self.uses, "undone": sorted(self.undone),
                               "module_rejections": self.module_rejections})


def shaken(mods: list[str], state: State, batch: int, skip: bool = False,
           timeout: float | None = None) -> dict[str, tuple[list[str], list[str]]]:
    """`lake shake`'s suggestions for `mods`, by file, from `state` where the
    module's build is the one they were found for; the others in batches."""
    for k in range(0, len(mods), batch):
        if timeout is None:
            check.build_modules(mods[k:k + batch])
        else:
            check.build_modules(mods[k:k + batch], timeout)
    state.current.update({m: source_key(m) for m in mods})
    if skip:
        return {str(check.graph_path(m)): ([], []) for m in mods}
    keys = {m: trace_key(m) for m in mods}
    todo = [m for m in mods if keys[m] is None or state.shake.get(m, [None])[0] != keys[m]]
    check.progress(f"lake shake: {len(todo)} of {len(mods)} modules changed since their last analysis")
    for k in range(0, len(todo), batch):
        part = todo[k:k + batch]
        found = check.suggestions(check.shake(part, built=True, timeout=timeout))
        by_path = {check.shake_path(f): v for f, v in found.items()}
        for m in part:
            rem, add = by_path.get(check.graph_path(m).resolve(), ([], []))
            state.shake[m] = [keys[m], rem, add]
        state.save()
    return {str(check.graph_path(m)): tuple(state.shake[m][1:]) for m in mods}


def cached_uses(state: State, timeout: float | None = None, read_timeout: float | None = None):
    """`check.module_uses`, from `state` where the module's build is the one
    they were read for."""
    def uses(mods: list[str], view: str) -> dict[str, set[str]]:
        if view in check.DECLARATION_VIEWS:
            # A downstream module can become stale when a selected module's
            # public output changes, even if its own source/header is intact.
            # Refresh each queried root once per analysis round before trusting
            # declaration/index evidence, including persistent cache hits.
            warm = [m for m in mods if source_key(m) is None or state.current.get(m) != source_key(m)]
            if warm:
                check.build_modules(warm, timeout)
                state.current.update({m: source_key(m) for m in warm})
        table = state.uses.setdefault(view, {})
        keys = {m: source_key(m) for m in mods}
        todo = sorted(m for m in mods if keys[m] is None or table.get(m, [None])[0] != keys[m])
        if todo:
            if view in check.DECLARATION_VIEWS:
                result = check.module_evidence(todo) if read_timeout is None else check.module_evidence(todo, read_timeout)
                missing = set(todo) - result.keys()
                if missing:
                    raise replay.MissingEvidence(f"{view} reader omitted: {', '.join(sorted(missing))}")
                for m, views in result.items():
                    for v in check.DECLARATION_VIEWS:
                        state.uses.setdefault(v, {})[m] = [keys[m], sorted(views[v])]
                state.save()
                return {m: set(state.uses[view][m][1]) for m in mods}
            result = check.module_uses(todo, view)
            missing = set(todo) - result.keys()
            if missing:
                raise replay.MissingEvidence(f"{view} reader omitted: {', '.join(sorted(missing))}")
            for m, us in result.items():
                table[m] = [keys[m], sorted(us)]
            state.save()
        return {m: set(table[m][1]) for m in mods if m in table}
    return uses


def trial_context(targets: list[str], graph: check.Graph) -> dict:
    return {"traces": {m: trace_key(m) for m in targets},
            "sources": {m: hashlib.sha256(graph.text(m).encode()).hexdigest() for m in targets}}


def module_trial_key(mod: str, plan: check.Plan, graph: check.Graph, library: list[str], context: dict) -> str:
    """A failed file trial, including changes that could alter its consumers.

    Unrelated successful edits shouldn't reopen it. Receiver sources, build
    outputs, importer scope and planned edits anywhere in their dependency DAG
    do reopen it, so interactions remain eligible for a new trial.
    """
    graph.importers(mod, library)  # initialize the original reverse index
    users = dict(graph.users or {})
    for edit in plan.edits:
        if edit.action.startswith("add"):
            users[edit.dependency] = set(users.get(edit.dependency, ())) | {edit.module}
    scope = {mod} | check.reverse_closure(mod, users)
    planned = check.Planned(graph, plan.edits)
    relevant = set(scope)
    pending = list(scope)
    while pending:
        current = pending.pop()
        for dep, _, _, _ in graph.imports(current) + planned.imports(current):
            if dep not in relevant:
                relevant.add(dep)
                pending.append(dep)
    data = {"module": mod, "traces": {m: context["traces"].get(m) for m in sorted(scope)},
            "sources": {m: context["sources"].get(m) for m in sorted(scope)},
            "edits": [(e.module, e.action, e.dependency) for e in sorted(plan.edits) if e.module in relevant]}
    return hashlib.sha256(json.dumps(data, sort_keys=True).encode()).hexdigest()


def trim(mods: list[str], library: list[str], rounds: int, batch: int, state: State,
         independent: bool = False, max_affected: int | None = None, skip_shake: bool = False,
         timeout: float | None = None, max_attempts: int = 3, audit: dict | None = None,
         read_batch: int = 32, read_timeout: float | None = None, verify_batch: int = 32) -> dict[str, int]:
    """Rounds of findings, fixes and builds until nothing is left to change."""
    totals = {"rounds": 0, "applied": 0, "undone": 0}
    if audit is not None:
        audit.update({"totals": totals, "rounds": []})
    uses = cached_uses(state, timeout, read_timeout)
    for r in range(1, rounds + 1):
        check.progress(f"round {r}")
        totals["rounds"] = r
        state.current.clear()
        graph = check.Graph(check.dependency_roots())
        evidence = replay.Evidence(uses, min(batch, read_batch))
        suggestions = shaken(mods, state, batch, skip=skip_shake, timeout=timeout)
        raw_suggestions = {f: (list(rem), list(add)) for f, (rem, add) in suggestions.items()}
        if independent:
            suggestions = replay.discover(mods, suggestions, graph, evidence)
        eligible, cached_deferred, cached_decisions = list(mods), [], []
        while True:
            plan = check.analyze(eligible, suggestions, graph, uses=evidence, library=library) if eligible else check.Plan()
            estimate = replay.cost(plan, graph, library, {})
            profile = replay.profile_cost(estimate["verification_targets"])
            if max_affected is not None and estimate["affected_modules"] > max_affected:
                plan = replay.bounded(plan, suggestions, graph, evidence, library, max_affected, profile)
            estimate = replay.cost(plan, graph, library, profile)
            context = trial_context(estimate["verification_targets"], graph)
            primary = {e.module for e in plan.edits if e.action in check.NARROWING}
            known = {}
            for mod in primary & state.module_rejections.keys():
                trial = module_trial_key(mod, plan, graph, library, context)
                if trial in state.module_rejections[mod]:
                    known[mod] = state.module_rejections[mod][trial]
            if not known:
                break
            cached_deferred.extend({"module": m, "reason": "unchanged rejected module trial",
                                    "previous_verification": known[m].get("manifest"),
                                    "rejection_evidence": known[m].get("evidence")} for m in sorted(known))
            for d in plan.decisions:
                if d["module"] in known:
                    d = dict(d)
                    if d["status"] == "proposed":
                        d.update(status="deferred", reason="unchanged_rejection")
                    cached_decisions.append(d)
            eligible = [m for m in eligible if m not in known]
        plan.deferred.extend(cached_deferred)
        plan.decisions.extend(cached_decisions)
        baseline_context = context
        round_record = {"round": r, "plan": replay.report(plan, estimate, graph), "status": "planned"}
        if audit is not None:
            audit["rounds"].append(round_record)
        # Rejections apply to an exact batch and its context, not an English
        # finding forever. A changed source/build/analyzer permits a retry.
        context = json.dumps({"edits": [(e.module, e.action, e.dependency) for e in plan.edits],
                              "traces": {m: trace_key(m) for m in estimate["verification_targets"]},
                              "sources": {m: hashlib.sha256(t.encode()).hexdigest() for m, t in graph.texts.items()},
                              "users": {m: sorted(js) for m, js in (graph.users or {}).items()}},
                             sort_keys=True)
        key = hashlib.sha256(context.encode()).hexdigest()
        check.progress(f"round {r}: {len(plan.edits)} operations, up to {estimate['affected_modules']} affected modules")
        if plan.blocked:
            check.progress("; ".join(plan.blocked))
            round_record["status"] = "blocked"
            break
        if plan.deferred:
            check.progress(f"{len(plan.deferred)} candidates deferred by policy or verification budget")
        if not plan.edits or key in state.undone:
            round_record["status"] = ("deferred" if plan.deferred else "no_changes") if not plan.edits else "cached_rejection"
            break
        if max_affected is not None and estimate["affected_modules"] > max_affected:
            check.progress(f"deferred: exceeds --max-affected {max_affected}; inspect a --dry-run report or select fewer modules")
            round_record["status"] = "deferred"
            break
        verification = {}
        round_record["verification"] = verification
        kept, undone = [], []
        try:
            kept, undone = check.fix_and_verify(plan, library, timeout=timeout, max_attempts=max_attempts,
                                               audit=verification, verify_batch=verify_batch)
        finally:
            if undone or verification.get("status") in ("aborted", "rejected"):
                # Freeze the already-collected, pre-edit evidence. A failed
                # trial should be debuggable without another Lean build.
                folder = pathlib.Path(verification["manifest"]).parent if verification.get("manifest") else (
                    check.LEAN / ".lake/import-rejections" / str(time.time_ns()))
                path = folder / "evidence.json.gz"
                try:
                    snapshot = replay.capture(mods, library, graph, raw_suggestions, evidence,
                                              profile, independent, max_affected)
                    snapshot["verification"] = dict(verification)
                    replay.save(path, snapshot)
                    round_record["rejection_evidence"] = str(path)
                    check.progress(f"replayable rejection evidence: {path}")
                except (OSError, ValueError) as error:
                    round_record["evidence_error"] = str(error)
                    check.progress(f"could not save rejection evidence: {error}")
        round_record["status"] = verification.get("status", "finished")
        totals["applied"] += len(kept)
        totals["undone"] += len(undone)
        if undone:
            state.undone.add(key)
            for mod in set(undone) & primary:
                state.module_rejections.setdefault(mod, {})[module_trial_key(mod, plan, graph, library, baseline_context)] = {
                    "manifest": verification.get("manifest"), "evidence": round_record.get("rejection_evidence"),
                    "status": verification.get("status"),
                    "failures": sorted({m for a in verification.get("attempts", []) for m in a.get("failures", [])})}
        state.save()
        if not kept:
            break
    return totals


@check.lean_import_build.interruptible
def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    what = parser.add_mutually_exclusive_group(required=True)
    what.add_argument("-m", "--modules", nargs="+")
    what.add_argument("--base", help="the modules changed since this git revision")
    what.add_argument("--all", action="store_true", help="every module of the library")
    what.add_argument("--replay", type=pathlib.Path, help="replan captured evidence without Lake or source access")
    parser.add_argument("--batch", type=int, default=1000)
    parser.add_argument("--read-batch", type=int, default=32, help="maximum modules per declaration-reader process (default 32)")
    parser.add_argument("--read-timeout", type=float, default=120, help="seconds per declaration-reader process (default 120)")
    parser.add_argument("--rounds", type=int, default=5)
    parser.add_argument("--dry-run", action="store_true", help="analyze and estimate cost without editing or verification builds")
    parser.add_argument("--capture", type=pathlib.Path, help="save portable analysis evidence; implies --dry-run")
    parser.add_argument("--report", type=pathlib.Path, help="write the dry-run/replay plan and costs as JSON")
    discovery = parser.add_mutually_exclusive_group()
    discovery.add_argument("--discover", action="store_true", default=None, help="also test hypotheses independent of lake shake")
    discovery.add_argument("--shake-only", dest="discover", action="store_false", default=None,
                           help="replay only shake's hypotheses, even if discovery was captured")
    parser.add_argument("--no-shake", action="store_true", help="skip lake shake; requires --discover (selected modules are still built)")
    parser.add_argument("--max-affected", type=int, help="verify a low-cost subset within N affected modules; defer the rest")
    parser.add_argument("--build-timeout", type=float, help="seconds per analysis/baseline/verification build; stops Lean children on timeout")
    parser.add_argument("--verify-attempts", type=int, default=3, help="maximum verification passes before restoring a batch (default 3)")
    parser.add_argument("--verify-batch", type=int, default=32, help="targets per baseline/verification build; stop a pass at its first failing chunk (default 32)")
    parser.add_argument("--retry-rejected", action="store_true", help="retry selected modules' unchanged failed trials without discarding raw evidence caches")
    args = parser.parse_args(argv)
    if (args.batch < 1 or args.read_batch < 1 or args.read_timeout <= 0 or args.rounds < 1
            or args.verify_attempts < 1 or args.verify_batch < 1
            or (args.max_affected is not None and args.max_affected < 1)
            or (args.build_timeout is not None and args.build_timeout <= 0)):
        parser.error("batch sizes, timeouts, rounds, max-affected and verify-attempts must be positive")
    if args.no_shake and (not args.discover or args.replay):
        parser.error("--no-shake requires --discover and live analysis")
    if args.retry_rejected and (args.replay or args.dry_run or args.capture):
        parser.error("--retry-rejected requires live verification")
    if args.replay:
        if args.capture:
            parser.error("--capture cannot be combined with --replay")
        result = replay.replay(replay.load(args.replay), args.discover, args.max_affected)
        return show_report(result, args.report)
    library = check.library_modules(
        ".".join(f.relative_to(check.LEAN).with_suffix("").parts) for f in (check.LEAN / check.LIBRARY).rglob("*.lean"))
    if args.modules:
        names = args.modules
    elif args.base:
        out = subprocess.run(["git", "-C", str(check.ROOT), "diff", "--name-only", args.base, "--", "lean/" + check.LIBRARY],
                             capture_output=True, text=True, check=True).stdout.split()
        names = [".".join(pathlib.Path(f).relative_to("lean").with_suffix("").parts) for f in out if f.endswith(".lean")]
    else:
        names = library
    mods = sorted(m for m in check.library_modules(names) if not check.reviewed(m))
    check.progress(f"{len(mods)} modules to trim")
    state = State(STATE)
    if args.retry_rejected:
        state.undone.clear()
        for mod in mods:
            state.module_rejections.pop(mod, None)
        state.save()
    if args.dry_run or args.capture:
        graph = check.Graph(check.dependency_roots())
        graph.users = check.reverse_index(library)
        evidence = replay.Evidence(cached_uses(state, args.build_timeout, args.read_timeout), min(args.batch, args.read_batch))
        suggestions = shaken(mods, state, args.batch, skip=args.no_shake, timeout=args.build_timeout)
        # Preserve raw shake evidence so a replay can compare discovery modes.
        raw = {f: (list(rem), list(add)) for f, (rem, add) in suggestions.items()}
        if args.discover:
            suggestions = replay.discover(mods, suggestions, graph, evidence)
        plan = check.analyze(mods, suggestions, graph, uses=evidence, library=library)
        scope = replay.cost(plan, graph, library, {})["verification_targets"]
        profile = replay.profile_cost(scope)
        if args.max_affected is not None and len(scope) > args.max_affected:
            plan = replay.bounded(plan, suggestions, graph, evidence, library, args.max_affected, profile)
        result = replay.report(plan, replay.cost(plan, graph, library, profile), graph)
        if args.capture:
            replay.save(args.capture, replay.capture(mods, library, graph, raw, evidence, profile, bool(args.discover), args.max_affected))
        return show_report(result, args.report)
    audit = {}
    try:
        totals = trim(mods, library, args.rounds, args.batch, state, bool(args.discover), args.max_affected, args.no_shake,
                      args.build_timeout, args.verify_attempts, audit, args.read_batch, args.read_timeout, args.verify_batch)
    except BaseException as error:
        audit["error"] = f"{type(error).__name__}: {error}"
        raise
    finally:
        audit["build_verified"] = ("error" not in audit and any(
            r.get("verification", {}).get("build_verified") for r in audit.get("rounds", [])))
        if args.report:
            replay.save(args.report, audit)
    print(f"{totals['rounds']} rounds: {totals['applied']} changes kept, {totals['undone']} files' changes undone")
    return 0


def show_report(result: dict, path: pathlib.Path | None) -> int:
    if path:
        replay.save(path, result)
    cost = result["cost"]
    print(f"Unverified plan: {len(result['edits'])} operations in {len(cost['edited_modules'])} modules; "
          f"up to {cost['affected_modules']} affected modules")
    print(f"Recorded profile work: {cost['known_profile_work_seconds']:.1f} s; "
          f"{cost['unprofiled_modules']} modules without profiles (not a wall-time estimate)")
    impact = result.get("visibility_impact", {})
    if impact.get("evaluated"):
        totals = impact["totals"]
        change = lambda kind: totals[kind]["added_pairs"] - totals[kind]["removed_pairs"]
        print(f"Modelled dependency exposure: {change('ordinary_reads'):+d} ordinary, {change('meta_reads'):+d} meta; "
              f"{change('ordinary_reexports'):+d} public ordinary re-exports (not a timing estimate)")
    for item in cost["ranked"][:10]:
        print(f"  {item['affected_modules']:6} affected: {item['module']}")
    for message in result["blocked"]:
        print("blocked:", message)
    if result.get("deferred"):
        print(f"Deferred {len(result['deferred'])} candidates by policy or verification budget")
    return 0


if __name__ == "__main__":
    sys.exit(main())
