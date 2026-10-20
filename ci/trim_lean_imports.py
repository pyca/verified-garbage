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

It never edits registrations or variants (`Artifacts/`, `Generic/`,
`Variants/`). Its state is in `lean/.lake/trim-imports.json`: each module's
`lake shake` suggestions and uses, keyed by the hash Lake records of the
module's inputs and outputs (its `.trace`), so a round or a rerun analyses
again only the modules whose build changed, and the findings it undid, which
it does not try again. Run it after building; it prints its phases and
writes its builds' output to `lean/.lake/check-imports-build.log`.
"""

import argparse
import json
import pathlib
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).parent))
import check_lean_public_imports as check  # noqa: E402

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
    outputs = trace.get("outputs", {})
    return f"{trace.get('depHash')}:{','.join(outputs.get('o', []))}"


class State:
    """What earlier rounds and runs found, by module and trace key."""

    def __init__(self, path: pathlib.Path):
        self.path = path
        try:
            data = json.loads(path.read_text())
        except (OSError, ValueError):
            data = {}
        self.shake: dict = data.get("shake", {})
        self.uses: dict = data.get("uses", {})
        self.undone: set[str] = set(data.get("undone", []))

    def save(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.write_text(json.dumps({"shake": self.shake, "uses": self.uses, "undone": sorted(self.undone)},
                                        sort_keys=True))


def shaken(mods: list[str], state: State, batch: int) -> dict[str, tuple[list[str], list[str]]]:
    """`lake shake`'s suggestions for `mods`, by file, from `state` where the
    module's build is the one they were found for; the others in batches."""
    for k in range(0, len(mods), batch):
        check.build_modules(mods[k:k + batch])
    keys = {m: trace_key(m) for m in mods}
    todo = [m for m in mods if keys[m] is None or state.shake.get(m, [None])[0] != keys[m]]
    check.progress(f"lake shake: {len(todo)} of {len(mods)} modules changed since their last analysis")
    for k in range(0, len(todo), batch):
        part = todo[k:k + batch]
        found = check.suggestions(check.shake(part))
        by_path = {pathlib.Path(f).resolve(): v for f, v in found.items()}
        for m in part:
            rem, add = by_path.get(check.graph_path(m).resolve(), ([], []))
            state.shake[m] = [keys[m], rem, add]
        state.save()
    return {str(check.graph_path(m)): tuple(state.shake[m][1:]) for m in mods}


def cached_uses(state: State):
    """`check.module_uses`, from `state` where the module's build is the one
    they were read for."""
    def uses(mods: list[str], view: str) -> dict[str, set[str]]:
        table = state.uses.setdefault(view, {})
        keys = {m: trace_key(m) for m in mods}
        todo = sorted(m for m in mods if keys[m] is None or table.get(m, [None])[0] != keys[m])
        if todo:
            for m, us in check.module_uses(todo, view).items():
                table[m] = [keys[m], sorted(us)]
            state.save()
        return {m: set(table[m][1]) for m in mods if m in table}
    return uses


def reviewed(mod: str) -> bool:
    return any(f".{d}." in f".{mod}." for d in check.REVIEWED)


def usable(finding: str, state: State) -> bool:
    """Whether to apply a finding: not one undone before, and not one that
    would have a registration or variant import what it used (they are never
    edited: the import stays public)."""
    if finding in state.undone:
        return False
    if "where it is used: " in finding:
        users = check.re.findall(r"(\S+) uses ", finding.split("where it is used: ", 1)[1])
        if any(reviewed(j) for j in users):
            return False
    return True


def trim(mods: list[str], library: list[str], rounds: int, batch: int, state: State) -> dict[str, int]:
    """Rounds of findings, fixes and builds until nothing is left to change."""
    totals = {"rounds": 0, "applied": 0, "undone": 0}
    uses = cached_uses(state)
    for r in range(1, rounds + 1):
        check.progress(f"round {r}")
        totals["rounds"] = r
        check._USERS.clear()  # headers changed: read the reverse index again
        graph = check.Graph(check.dependency_roots())
        found = check.problems(mods, shaken(mods, state, batch), graph, None, None, uses, library)
        found = [f for f in found if f.startswith("lean/") and ": and keep passing on" not in f]
        todo = [f for f in found if usable(f, state)]
        check.progress(f"round {r}: {len(found)} findings, {len(todo)} to apply")
        if not todo:
            break
        kept, undone = check.fix_and_verify(todo, library)
        totals["applied"] += len(kept)
        totals["undone"] += len(undone)
        gone = {str(check.graph_path(m).relative_to(check.ROOT)) for m in undone}
        state.undone.update(f for f in todo if f.split(":", 1)[0] in gone)
        state.save()
        if not kept:
            break
    return totals


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    what = parser.add_mutually_exclusive_group(required=True)
    what.add_argument("-m", "--modules", nargs="+")
    what.add_argument("--base", help="the modules changed since this git revision")
    what.add_argument("--all", action="store_true", help="every module of the library")
    parser.add_argument("--batch", type=int, default=1000)
    parser.add_argument("--rounds", type=int, default=5)
    args = parser.parse_args(argv)
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
    mods = sorted(m for m in check.library_modules(names) if not reviewed(m))
    check.progress(f"{len(mods)} modules to trim")
    totals = trim(mods, library, args.rounds, args.batch, State(STATE))
    print(f"{totals['rounds']} rounds: {totals['applied']} changes kept, {totals['undone']} files' changes undone")
    return 0


if __name__ == "__main__":
    sys.exit(main())
