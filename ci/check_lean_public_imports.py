#!/usr/bin/env python3
"""Checks that the modules a change edits import privately what they use only
privately, and import nothing they do not use (CLAUDE.md, "Lean modules").
Run it before pushing, after building the modules, which `lake shake` reads;
it exits non-zero naming each import to change, and `--fix` changes them.
Not run in CI: `lake shake` alone takes most of a minute.

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
import time

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
    """`lake shake`'s suggestions for `mods`, built first (Lake skips what is
    up to date): shake reads their `.olean`s."""
    progress(f"building {len(mods)} modules (what is up to date is skipped)")
    built = subprocess.run(["lake", "build", "--log-level=error", *("+" + m for m in mods)],
                           cwd=LEAN, capture_output=True, text=True)
    if built.returncode:
        raise SystemExit(f"the modules do not build; fix that first:\n{(built.stdout + built.stderr)[-3000:]}")
    progress(f"lake shake on {len(mods)} modules")
    args = ["lake", "shake", "--force"]
    for m in mods:
        args += ["--only", m]
    out = subprocess.run(args + mods, cwd=LEAN, capture_output=True, text=True)
    # It exits non-zero when it has suggestions.
    if "error:" in out.stderr:
        raise SystemExit(f"lake shake failed:\n{out.stderr}")
    return out.stdout


_T0 = time.time()


def progress(msg: str) -> None:
    """A phase, with the time since the start, on stderr (the findings go
    there too, after)."""
    print(f"[{time.time() - _T0:6.1f} s] {msg}", file=sys.stderr, flush=True)


def module_uses(mods: list[str], view: str) -> dict[str, set[str]]:
    """The modules each of `mods` uses (`ci/lean_module_uses.lean`, which
    reads their builds): `public`, what Lean checks as public uses (statements
    and exposed bodies, with the proofs elaborated as part of them); `private`,
    everything."""
    if not mods:
        return {}
    progress(f"reading {len(mods)} modules' {view} uses")
    out = subprocess.run(["lake", "env", "lean", "--run", str(ROOT / "ci/lean_module_uses.lean"), view, *mods],
                         cwd=LEAN, capture_output=True, text=True)
    if out.returncode:
        raise SystemExit(f"lean_module_uses.lean failed:\n{out.stderr}{out.stdout}")
    return {m: set(us) for m, us in json.loads(out.stdout).items()}


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


def new_imports(mod: str, base: str | None, public: bool) -> set[str] | None:
    """The modules `mod` imports (publicly, or plainly) but did not so at the
    git revision `base` (None: every one, without a base or for a new file).
    `meta` imports are left out."""
    if base is None:
        return None
    rel = pathlib.Path("lean", *mod.split(".")).with_suffix(".lean").as_posix()
    old = subprocess.run(["git", "-C", str(ROOT), "show", f"{base}:{rel}"], capture_output=True, text=True)
    if old.returncode:
        return None
    path = LEAN / pathlib.Path(*mod.split(".")).with_suffix(".lean")
    was = {i for i, p, me, _ in header(old.stdout) if p == public and not me}
    return {i for i, p, me, _ in header(path.read_text()) if p == public and not me} - was


def new_public(mod: str, base: str | None) -> set[str] | None:
    """The modules `mod` imports publicly but did not at `base`."""
    return new_imports(mod, base, True)


def new_plain(mod: str, base: str | None) -> set[str] | None:
    """The modules `mod` imports plainly but did not at `base`."""
    return new_imports(mod, base, False)


class Demoted(Graph):
    """`graph`, but for the modules of `pairs` importing those privately:
    `Demoted(graph, mod, x)`, or `Demoted(graph, pairs={(mod, x), …})`."""

    def __init__(self, graph: Graph, mod: str | None = None, x: str | None = None, pairs=None):
        super().__init__(graph.roots)
        self.files, self.texts = graph.files, graph.texts
        self.pairs = set(pairs or ()) | ({(mod, x)} if mod is not None else set())

    def imports(self, mod: str) -> list[tuple[str, bool, bool, bool]]:
        imps = super().imports(mod)
        return [(i, p and (mod, i) not in self.pairs, me, a) for i, p, me, a in imps]


def reads(graph: Graph, mod: str) -> set[str]:
    """What `mod` sees: what it imports, and what those pass on."""
    return set().union(*(graph.passes(i) for i, _, _, _ in graph.imports(mod)))


def problems(mods: list[str], shaken: dict[str, tuple[list[str], list[str]]], graph: Graph,
             new: dict[str, set[str] | None] | None = None, plain: dict[str, set[str] | None] | None = None,
             uses=None, library: list[str] | None = None) -> list[str]:
    """What to change, for each of `mods`:

    * a `public import` of a module of the project that `lake shake`
      (`shaken`) finds used only privately, of those the change made public
      (`new`, by module; all of them where None), unless what Lean checks as
      public uses it (`uses(mods, "public")`: proofs inside exposed definitions,
      which shake counts as private), naming the modules of `library` that
      used what it passed on (`uses(mods, "private")`), which must import it
      themselves;
    * a plain import of a module of the project that shake finds unused, of
      those the change added (`plain`; all of them where None).
    """
    # Pass 1: shake's candidates, per module.
    found = []  # (mod, rel, lines, private, unused)
    for mod in mods:
        path = graph.path(mod)
        rel = f"lean/{path.relative_to(LEAN)}"
        rem, add = next((v for f, v in shaken.items() if pathlib.Path(f).resolve() == path.resolve()), ([], []))
        public_after = {x.split()[-1] for x in add if x.startswith("public import ")}
        added_after = {x.split()[-1] for x in add if not x.startswith("meta ") and " meta " not in x}
        made = (new or {}).get(mod)
        private = sorted(
            x.split()[-1] for x in rem
            if x.startswith("public import ") and x.split()[-1] not in public_after
            and graph.project(x.split()[-1]) and not graph.kept(x.split()[-1])
            and (made is None or x.split()[-1] in made)
        )
        added = (plain or {}).get(mod)
        unused = sorted(
            x.split()[-1] for x in rem
            if x.startswith("import ") and x.split()[-1] not in added_after
            and graph.project(x.split()[-1]) and not graph.kept(x.split()[-1])
            and (added is None or x.split()[-1] in added)
        )
        if private or unused:
            found.append((mod, rel, graph.text(mod).split("\n"), private, unused))
    # Pass 2: what Lean checks as public uses, for every module with a
    # candidate at once (proofs inside exposed definitions count).
    if uses is not None:
        pub = uses([f[0] for f in found if f[3]], "public") if any(f[3] for f in found) else {}
        kept_found = []
        for mod, rel, lines, private, unused in found:
            direct = {i for i, p, _, _ in graph.imports(mod) if p}
            used = pub.get(mod, set())
            # A module imports directly what it uses (CLAUDE.md): it keeps
            # `public import X` if it publicly uses X itself; otherwise X
            # becomes a plain import, and the module imports publicly, itself,
            # what it publicly used of what X passed on. Each finding depends
            # only on the module's own uses and imports: they hold together.
            demote = []
            for x in private:
                if x in used:
                    continue
                need = {y for y in used & graph.passes(x) if y not in direct}
                need = {y for y in need if not any(y != z and y in graph.passes(z) for z in need)}
                demote.append((x, sorted(need)))
            kept_found.append((mod, rel, lines, demote, unused))
        found = kept_found
    else:
        found = [(mod, rel, lines, [(x, []) for x in private], unused) for mod, rel, lines, private, unused in found]
    # Pass 2b: an import shake would remove, whose declarations the source
    # names (in a tactic, `simp [f]`, a field: uses that leave nothing in
    # the `.olean` shake reads), stays.
    if uses is not None and any(f[4] for f in found):
        # Against the planned result: every demotion applied, and none of the
        # module's other removal candidates counted as providing anything
        # (each would justify the other).
        planned = Demoted(graph, pairs={(mod, x) for mod, _, _, private, _ in found for x, _ in private})
        provided = {}
        for mod, _, _, _, unused in found:
            imps = graph.imports(mod)
            for x in unused:
                others = set().union(*(planned.passes(i) for i, _, _, _ in imps if i != x and i not in unused))
                provided[mod, x] = {y for y in planned.passes(x) - others if graph.project(y)}
        names = uses(sorted(set().union(*provided.values())), "names") if provided else {}
        kept_found = []
        for mod, rel, lines, private, unused in found:
            text = "\n".join(lines)
            words, opened = source_words(text), opened_namespaces(text)
            keep = []
            for x in unused:
                declared = set().union(*(names.get(y, set()) for y in provided[mod, x]))
                named = words & {d.rpartition(".")[2] for d in declared}
                spaces = {d.rpartition(".")[0] for d in declared}
                opens = {ns for ns in opened if any(s == ns or s.endswith("." + ns) or s.startswith(ns + ".") for s in spaces)}
                if not named and not opens:
                    keep.append(x)
            kept_found.append((mod, rel, lines, private, keep))
        found = kept_found
    # Pass 3: the importers that lose a module, for every finding; then what
    # each uses, all at once.
    losing = {}
    if uses is not None and library:
        for mod, _, _, private, _ in found:
            for x, _ in private:
                losing[mod, x] = importers_losing(mod, x, graph, library)
        everyone = sorted(set().union(*(set(v) for v in losing.values()))) if losing else []
        used = uses(everyone, "private") if everyone else {}
    out = []
    for mod, rel, lines, private, unused in found:
        imps = graph.imports(mod)
        if private:
            names = [x for x, _ in private]
            before = set().union(*(graph.passes(i) for i, p, _, _ in imps if p))
            after = set().union(*(graph.passes(i) for i, p, _, _ in imps if p and i not in names))
            lost = {x for x in before - after if graph.kept(x)}
            keep = sorted(x for x in lost if not any(x in graph.passes(y) for y in lost if y != x))
            for x, need in private:
                n = next(i for i, l in enumerate(lines) if re.match(rf"^public\s+import\s+{re.escape(x)}\s*(--.*)?$", l)) + 1
                msg = f"{rel}:{n}: `public import {x}`: {mod} uses it only privately: make it `import {x}`"
                if need:
                    msg += ", import publicly itself what it used through it: " + ", ".join(f"`public import {y}`" for y in need)
                if (mod, x) not in losing:
                    msg += f", and import it where the modules importing {mod} use it"
                else:
                    users = {}
                    for j, gone in losing[mod, x].items():
                        need = gone & used.get(j, set())
                        need = {y for y in need if not any(y != z and y in graph.passes(z) for z in need)}
                        if need:
                            users[j] = need
                    if users:
                        msg += ", and import what it passed on where it is used: " + "; ".join(
                            f"{j} uses {', '.join(sorted(need))}" for j, need in sorted(users.items()))
                out.append(msg)
            if keep:
                out.append(f"{rel}: and keep passing on what those passed on that "
                           f"the check cannot see the uses of: " + ", ".join(f"`public import {x}`" for x in keep))
        for x in unused:
            n = next((i for i, l in enumerate(lines) if re.match(rf"^import\s+{re.escape(x)}\s*(--.*)?$", l)), None)
            if n is not None:
                out.append(f"{rel}:{n + 1}: `import {x}`: {mod} does not use it: remove it")
    return out


WORD = re.compile(r"[^\W\d][\w'!?₀-₉]*")


def source_words(text: str) -> set[str]:
    """The identifiers' last components in a source, comments left out."""
    text = re.sub(r"/-.*?-/|--[^\n]*", " ", text, flags=re.S)
    return {w.rpartition(".")[2] for w in WORD.findall(text)}


OPEN = re.compile(r"^\s*(?:@\[[^\]\n]*\]\s*)?open\s+(?:scoped\s+)?([^\n(]*)", re.M)


def opened_namespaces(text: str) -> set[str]:
    """The namespaces a source opens (`open A B`, `open A (x y)`), comments left out."""
    text = re.sub(r"/-.*?-/|--[^\n]*", " ", text, flags=re.S)
    return {ns for l in OPEN.findall(text) for ns in l.split() if ns[:1].isupper() and ns != "in"}


def header_imports(path: pathlib.Path) -> list[str]:
    """The modules a source imports, reading only its header."""
    lines = []
    with open(path, errors="replace") as f:
        for line in f:
            s = line.strip()
            if s and not (IMPORT.match(s) or s.startswith("--") or s.startswith("/-") or s in ("module", "prelude")):
                break
            lines.append(line)
    return [m for m, _, _, _ in header("".join(lines))]


_USERS: dict[tuple[str, ...], dict[str, set[str]]] = {}


def importers_of(mod: str, library: list[str]) -> set[str]:
    """The modules of `library` that import `mod`, directly or not (the
    reverse index is read once per library)."""
    key = tuple(library)
    if key not in _USERS:
        users: dict[str, set[str]] = {}
        for j in library:
            for i in header_imports(LEAN / pathlib.Path(*j.split(".")).with_suffix(".lean")):
                users.setdefault(i, set()).add(j)
        _USERS[key] = users
    users = _USERS[key]
    out, todo = set(), [mod]
    while todo:
        for j in users.get(todo.pop(), ()):
            if j not in out:
                out.add(j)
                todo.append(j)
    return out


def importers_losing(mod: str, x: str, graph: Graph, library: list[str]) -> dict[str, set[str]]:
    """The modules importing `mod` (of `library`) that would no longer see
    modules of the project if `mod` imported `x` privately, with those."""
    demoted = Demoted(graph, mod, x)
    lost = {}
    for j in sorted(importers_of(mod, library)):
        gone = {y for y in reads(graph, j) - reads(demoted, j) if graph.project(y)}
        if gone:
            lost[j] = gone
    return lost


EVALUATES = re.compile(r"#guard|#eval|run_cmd|materialize_|taint_decide|taint_summary")


def fix(found: list[str]) -> list[str]:
    """Apply `problems`' findings to the sources: make the imports plain,
    import what importers used through them, remove unused imports (with a
    `meta import` for each import added to a file that evaluates code, as
    CLAUDE.md asks). Returns what it changed."""
    edits: dict[pathlib.Path, list[tuple[str, str]]] = {}
    adds: dict[str, set[str]] = {}
    for f in found:
        m = re.match(r"^(lean/\S+\.lean):\d+: `public import (\S+)`: \S+ uses it only privately", f)
        if m:
            edits.setdefault(ROOT / m.group(1), []).append(("demote", m.group(2)))
            if "import publicly itself what it used through it: " in f:
                own = f.split("import publicly itself what it used through it: ", 1)[1].split(", and import", 1)[0]
                edits[ROOT / m.group(1)].extend(("add_public", y) for y in re.findall(r"`public import (\S+)`", own))
            for j, need in re.findall(r"(\S+) uses ([^;]+)", f.split("where it is used: ", 1)[1] if "where it is used: " in f else ""):
                adds.setdefault(j, set()).update(x.strip() for x in need.split(","))
            continue
        m = re.match(r"^(lean/\S+\.lean):\d+: `import (\S+)`: \S+ does not use it", f)
        if m:
            edits.setdefault(ROOT / m.group(1), []).append(("remove", m.group(2)))
    for j, need in adds.items():
        edits.setdefault(LEAN / pathlib.Path(*j.split(".")).with_suffix(".lean"), []).extend(("add", x) for x in sorted(need))
    done = []
    for path, ops in sorted(edits.items()):
        lines = path.read_text().split("\n")
        imps = [k for k, l in enumerate(lines) if IMPORT.match(l.strip())]
        last = imps[-1] if imps else next(k for k, l in enumerate(lines) if l.strip() == "module")
        have = {l.strip() for l in lines[:last + 1]}
        evaluates = bool(EVALUATES.search("\n".join(lines[last + 1:])))
        new_lines = []
        for op, x in ops:
            if op == "demote":
                lines = [f"import {x}" if re.match(rf"^public\s+import\s+{re.escape(x)}\s*$", l) else l for l in lines]
            elif op == "remove":
                lines = [l for l in lines if not re.match(rf"^import\s+{re.escape(x)}\s*(--.*)?$", l)]
            elif op == "add_public":
                lines = [l for l in lines if l.strip() != f"import {x}"]
                if f"public import {x}" not in have:
                    new_lines.append(f"public import {x}")
                    if evaluates and f"public meta import {x}" not in have and f"meta import {x}" not in have:
                        new_lines.append(f"meta import {x}")
            elif f"import {x}" not in have and f"public import {x}" not in have:
                new_lines.append(f"import {x}")
                if evaluates and f"meta import {x}" not in have:
                    new_lines.append(f"meta import {x}")
            done.append(f"{path.relative_to(ROOT)}: {op} {x}")
        if new_lines:
            imps = [k for k, l in enumerate(lines) if IMPORT.match(l.strip())]
            at = (imps[-1] if imps else next(k for k, l in enumerate(lines) if l.strip() == "module")) + 1
            lines[at:at] = new_lines
        path.write_text("\n".join(lines))
    return done


BUILT = re.compile(r"^✖ \[\d+/\d+\] \w+ ([^\s:]+)", re.M)


BUILD_LOG = LEAN / ".lake" / "check-imports-build.log"


def build_failures(mods: list[str]) -> set[str]:
    """The modules that fail when `mods` are built (with what they import).
    Lake's output goes to `BUILD_LOG` as it builds, to follow with `tail -f`."""
    progress(f"build log: {BUILD_LOG}")
    BUILD_LOG.parent.mkdir(parents=True, exist_ok=True)
    with open(BUILD_LOG, "w") as log:
        code = subprocess.run(["lake", "build", "--log-level=warning", *("+" + m for m in mods)],
                              cwd=LEAN, stdout=log, stderr=subprocess.STDOUT).returncode
    return set(BUILT.findall(BUILD_LOG.read_text())) if code else set()


def fix_and_verify(found: list[str], library: list[str]) -> tuple[list[str], list[str]]:
    """`fix`, then build what it edited and every module importing those, and
    undo the edits of a file whose build fails, or of an edited module a
    failing one imports, until the rest builds. Returns (kept, undone)."""
    def mod_of(path: pathlib.Path) -> str:
        return ".".join(path.relative_to(LEAN).with_suffix("").parts)
    files = {ROOT / f.split(":", 1)[0] for f in found if f.startswith("lean/")}
    for f in found:
        for j in re.findall(r"(\S+) uses ", f.split("where it is used: ", 1)[1]) if "where it is used: " in f else []:
            files.add(LEAN / pathlib.Path(*j.split(".")).with_suffix(".lean"))
    saved = {path: path.read_text() for path in files if path.is_file()}
    done = fix(found)
    edited = {mod_of(path): path for path in saved if path.read_text() != saved[path]}
    undone = []
    for _ in range(10):
        targets = sorted(set(edited) | set().union(*(importers_of(m, library) for m in edited)))
        progress(f"fix: building {len(targets)} modules ({len(edited)} edited, and what imports them)")
        failing = build_failures(targets) if targets else set()
        if failing:
            progress(f"fix: {len(failing)} fail; undoing the nearest edits")
        if not failing:
            break
        def closure(m, seen=None):
            seen = set() if seen is None else seen
            for i in header_imports(LEAN / pathlib.Path(*m.split(".")).with_suffix(".lean")):
                if i not in seen and i.startswith(LIBRARY + "."):
                    seen.add(i)
                    closure(i, seen)
            return seen
        # Nearest first: a failing module's own edits, else those of the
        # edited modules it imports directly, else of any it imports.
        culprits = {m for m in edited if m in failing}
        if not culprits:
            direct = set().union(*(set(header_imports(LEAN / pathlib.Path(*f.split(".")).with_suffix(".lean")))
                                   for f in failing))
            culprits = {m for m in edited if m in direct}
        if not culprits:
            culprits = {m for m in edited if any(m in closure(f) for f in failing)}
        if not culprits:
            break
        for m in culprits:
            edited[m].write_text(saved[edited[m]])
            undone.append(m)
            del edited[m]
    kept = [d for d in done if not any(d.startswith(str(saved_path.relative_to(ROOT)) + ":")
                                       for saved_path in (LEAN / pathlib.Path(*m.split(".")).with_suffix(".lean")
                                                          for m in undone))]
    return kept, sorted(undone)


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
    parser.add_argument("--base", help="check only the imports added since this git revision")
    parser.add_argument("--fix", action="store_true",
                        help="apply the findings to the sources (then build and run the check again)")
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
    plain = {m: new_plain(m, args.base) for m in mods}
    mods = [m for m in mods if new[m] is None or new[m] or plain[m] is None or plain[m]]
    if not mods:
        print("Public imports OK (no import added)")
        return 0
    library = library_modules(
        ".".join(f.relative_to(LEAN).with_suffix("").parts) for f in (LEAN / LIBRARY).rglob("*.lean"))
    found = problems(mods, suggestions(shake(mods)), Graph(dependency_roots()), new, plain, module_uses, library)
    for p in found:
        print(p, file=sys.stderr)
    if not found:
        print(f"Imports OK ({len(mods)} modules)")
        return 0
    if args.fix:
        kept, undone = fix_and_verify(found, library)
        for d in kept:
            print("fixed:", d)
        for m in undone:
            print(f"undone (did not build with the change): {m}")
        print(f"{len(kept)} changes kept, building; {len(undone)} files' changes undone. "
              "Run the check again to see what is left.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
