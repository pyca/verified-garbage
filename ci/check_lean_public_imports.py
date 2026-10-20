#!/usr/bin/env python3
"""Checks that the modules a change edits import privately what they use only
privately (CLAUDE.md, "Lean modules"). Run in CI after the Lean build, which
`lake shake` reads; exits non-zero naming each import to change.

A module's `public import X` makes every module importing it read `X`'s
outputs too (`lean_shards.reads`): a change to `X`'s statements then rebuilds
all of them. Imported privately, `X` rebuilds only the module itself, whose
outputs come out as they were, and Lake stops there. So a `public import` of a
module of the project that the module's own statements and exposed
definitions do not use (as `lake shake` finds from the module's `.olean`) must
be a plain `import`; the modules that use `X` import it themselves.

`lake shake` sees the declarations, instances, syntax and attributes a module
uses, not the effects of a module that only changes how others elaborate
(an `attribute [...]`, a `macro_rules`, a `seal`, a `materialize_*` literal
that `lit_decide` reads: `side_effects`). The check never asks to stop
re-exporting such a module: where making `X` private would hide one (or a
module of a dependency) from the importers, it names the `public import`s
that keep passing it on. An import that must stay public for another reason
says so after it: `public import X -- shake: keep`, which `lake shake` then
leaves alone.

  check_lean_public_imports.py PLAN       the modules of `edited` in the plan
                                          (`lean_shards.py plan`)
  check_lean_public_imports.py -m M...    the modules M
  … --base REV                            only the public imports they added
                                          since REV (CI: the pull request's
                                          base), so that an edit is not held to
                                          imports it did not touch
"""

import argparse
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"
# The library the check covers, and its one file that is not a module.
LIBRARY = "VerifiedGarbage"
NOT_MODULES = {"VerifiedGarbage.Artifacts"}
# More edited modules than this (a missing manifest, which makes every module
# edited) would take `lake shake` minutes: the check then covers none.
MAX_MODULES = 3000
IMPORT = re.compile(r"^(public\s+)?(meta\s+)?import\s+(all\s+)?(\S+)")
# Commands whose effect on the modules importing a module no declaration of
# it records: global attributes, syntax, sealing, unification hints,
# instance priorities, and the literals of `materialize_*` and summaries of
# `taint_summary`, which tactics read without naming them.
SIDE_EFFECTS = re.compile(
    r"^\s*(attribute \[|seal |unseal |register_simp_attr|macro_rules|macro |elab |syntax |notation|infix|"
    r"prefix|postfix|declare_syntax_cat|elab_rules|@\[(term_)?elab|@\[macro|@\[tactic|@\[simproc|@\[dsimproc|"
    r"(builtin_)?d?simproc |unif_hint|instance \(priority|scoped|@\[default_instance|materialize_|taint_summary|"
    r"local_notation)",
    re.M,
)


def header(text: str) -> list[tuple[str, bool, bool, bool]]:
    """The imports of a source's header: (module, public, meta, all)."""
    out, comment = [], False
    for line in text.split("\n"):
        s = line.strip()
        if comment:
            comment = not s.endswith("-/")
            continue
        if s.startswith("/-") and not s.startswith("/-!"):
            comment = not s.endswith("-/")
            continue
        if not s or s.startswith("--") or s in ("module", "prelude"):
            continue
        m = IMPORT.match(s)
        if not m:
            break
        out.append((m.group(4), bool(m.group(1)), bool(m.group(2)), bool(m.group(3))))
    return out


def is_module(text: str) -> bool:
    comment = False
    for line in text.split("\n"):
        s = line.strip()
        if comment:
            comment = not s.endswith("-/")
        elif s.startswith("/-") and not s.startswith("/-!"):
            comment = not s.endswith("-/")
        elif s == "module":
            return True
        elif s and not s.startswith("--"):
            return False
    return False


class Graph:
    """The imports of the project's modules and its dependencies' (read
    lazily, from the sources Lake builds them from)."""

    def __init__(self, roots: list[pathlib.Path]):
        self.roots = roots
        self.files: dict[str, pathlib.Path | None] = {}
        self.texts: dict[str, str] = {}
        self.passed: dict[str, frozenset[str]] = {}

    def path(self, mod: str) -> pathlib.Path | None:
        if mod not in self.files:
            rel = pathlib.Path(*mod.split(".")).with_suffix(".lean")
            self.files[mod] = next((r / rel for r in self.roots if (r / rel).is_file()), None)
        return self.files[mod]

    def text(self, mod: str) -> str:
        if mod not in self.texts:
            p = self.path(mod)
            self.texts[mod] = p.read_text(errors="replace") if p else ""
        return self.texts[mod]

    def imports(self, mod: str) -> list[tuple[str, bool, bool, bool]]:
        text = self.text(mod)
        module = is_module(text)
        return [(i, p or not module, me, a) for i, p, me, a in header(text) if self.path(i)]

    def project(self, mod: str) -> bool:
        p = self.path(mod)
        return p is not None and p.is_relative_to(LEAN / LIBRARY)

    def kept(self, mod: str) -> bool:
        """Whether every importer must keep reading `mod` as it does: a module
        of a dependency, or one with side effects."""
        return not self.project(mod) or bool(SIDE_EFFECTS.search(self.text(mod)))

    def passes(self, mod: str) -> frozenset[str]:
        """`mod` and the modules it passes on to its importers, transitively."""
        stack = [mod]
        while stack:
            m = stack[-1]
            if m in self.passed:
                stack.pop()
                continue
            on = [i for i, p, _, _ in self.imports(m) if p]
            todo = [i for i in on if i not in self.passed]
            if todo:
                stack += todo
                continue
            stack.pop()
            self.passed[m] = frozenset({m}).union(*(self.passed[i] for i in on))
        return self.passed[mod]


def shake(mods: list[str]) -> str:
    """`lake shake`'s suggestions for `mods`, which must be built."""
    args = ["lake", "shake", "--force"]
    for m in mods:
        args += ["--only", m]
    out = subprocess.run(args + mods, cwd=LEAN, capture_output=True, text=True)
    # It exits non-zero when it has suggestions.
    if "error:" in out.stderr:
        raise SystemExit(f"lake shake failed:\n{out.stderr}")
    return out.stdout


def suggestions(text: str) -> dict[str, tuple[list[str], list[str]]]:
    """Of `lake shake`'s output, the imports it would remove and add, per
    file (as `public import X`, `meta import X`, …)."""
    out = {}
    for f, body in re.findall(r"^(\S+\.lean):\n((?:  .*\n)*)", text, re.M):
        rem, add = [], []
        for line in body.splitlines():
            m = re.match(r"\s*(remove|add) #\[(.*)\]", line)
            if m:
                (rem if m.group(1) == "remove" else add).extend(x.strip() for x in m.group(2).split(",") if x.strip())
        out[f] = (rem, add)
    return out


def new_public(mod: str, base: str | None) -> set[str] | None:
    """The modules `mod` imports publicly but did not at the git revision
    `base` (None: every one, without a base or for a new file)."""
    if base is None:
        return None
    rel = pathlib.Path("lean", *mod.split(".")).with_suffix(".lean").as_posix()
    old = subprocess.run(["git", "-C", str(ROOT), "show", f"{base}:{rel}"], capture_output=True, text=True)
    if old.returncode:
        return None
    path = LEAN / pathlib.Path(*mod.split(".")).with_suffix(".lean")
    was = {i for i, p, me, _ in header(old.stdout) if p and not me}
    return {i for i, p, me, _ in header(path.read_text()) if p and not me} - was


def problems(mods: list[str], shaken: dict[str, tuple[list[str], list[str]]], graph: Graph,
             new: dict[str, set[str] | None] | None = None) -> list[str]:
    """What to change, for each of `mods`: a `public import` of a module of the
    project that `lake shake` (`shaken`) finds used only privately, of those
    the change made public (`new`, by module; all of them where None)."""
    out = []
    for mod in mods:
        path = graph.path(mod)
        rem, add = next((v for f, v in shaken.items() if pathlib.Path(f).resolve() == path.resolve()), ([], []))
        public_after = {x.split()[-1] for x in add if x.startswith("public import ")}
        made = (new or {}).get(mod)
        private = sorted(
            x.split()[-1] for x in rem
            if x.startswith("public import ") and x.split()[-1] not in public_after
            and graph.project(x.split()[-1]) and not graph.kept(x.split()[-1])
            and (made is None or x.split()[-1] in made)
        )
        if not private:
            continue
        imps = graph.imports(mod)
        before = set().union(*(graph.passes(i) for i, p, _, _ in imps if p))
        after = set().union(*(graph.passes(i) for i, p, _, _ in imps if p and i not in private))
        lost = {x for x in before - after if graph.kept(x)}
        keep = sorted(x for x in lost if not any(x in graph.passes(y) for y in lost if y != x))
        lines = graph.text(mod).split("\n")
        for x in private:
            n = next(i for i, l in enumerate(lines) if re.match(rf"^public\s+import\s+{re.escape(x)}\s*$", l)) + 1
            out.append(f"lean/{path.relative_to(LEAN)}:{n}: `public import {x}`: {mod} uses it only privately: "
                       f"make it `import {x}`, and import it where the modules importing {mod} use it")
        if keep:
            out.append(f"lean/{path.relative_to(LEAN)}: and keep passing on what those passed on that "
                       f"the check cannot see the uses of: " + ", ".join(f"`public import {x}`" for x in keep))
    return out


def library_modules(names) -> list[str]:
    out = []
    for m in names:
        p = LEAN / pathlib.Path(*m.split(".")).with_suffix(".lean")
        if m.split(".")[0] == LIBRARY and m not in NOT_MODULES and p.is_file() and is_module(p.read_text()):
            out.append(m)
    return sorted(out)


def dependency_roots() -> list[pathlib.Path]:
    """Where Lake finds the sources of the project and its dependencies."""
    prefix = subprocess.run(["lake", "env", "lean", "--print-prefix"], cwd=LEAN, capture_output=True,
                            text=True, check=True).stdout.strip()
    packages = sorted(p for p in (LEAN / ".lake/packages").iterdir() if p.is_dir())
    return [LEAN, pathlib.Path(prefix) / "src/lean", *packages]


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("plan", nargs="?", type=pathlib.Path)
    parser.add_argument("-m", "--modules", nargs="+", default=[])
    parser.add_argument("--base", help="check only the public imports added since this git revision")
    args = parser.parse_args(argv)
    names = list(args.modules)
    if args.plan:
        plan = json.loads(args.plan.read_text())
        if "edited" not in plan:
            print("The plan has no edited modules (no manifest of a last build): nothing to check.")
            return 0
        names += plan["edited"]
    mods = library_modules(names)
    if len(mods) > MAX_MODULES:
        print(f"{len(mods)} modules edited, more than {MAX_MODULES}: not checked.")
        return 0
    if not mods:
        print("Public imports OK (no module edited)")
        return 0
    new = {m: new_public(m, args.base) for m in mods}
    mods = [m for m in mods if new[m] is None or new[m]]
    if not mods:
        print("Public imports OK (no public import added)")
        return 0
    found = problems(mods, suggestions(shake(mods)), Graph(dependency_roots()), new)
    for p in found:
        print(p, file=sys.stderr)
    if not found:
        print(f"Public imports OK ({len(mods)} modules)")
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main())
