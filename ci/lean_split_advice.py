#!/usr/bin/env python3
"""Finds the modules worth splitting: those that modules import for a few
declarations, whose other declarations make the importers build much more
than what they use needs. No builds.

A module imports a whole module even when it uses one lemma of it, and so
waits for (and a CI shard builds) everything that module imports. Narrowing
import headers (`trim_lean_imports.py`) cannot help there: the import is
used. Moving the declarations the importers use into a module of their own
can: the importers then import that module, whose closure is what those
declarations need.

For each module X of the project, this reads (`lean_decl_deps.lean`) what
each of X's declarations needs outside X, and which of X's declarations each
module importing X uses. It groups the importers that use only light
declarations of X (those whose own needs are a small part of X's closure),
and estimates what moving those declarations into a new module X' (which X
then imports) would take out of the closures of every module of the project:
the work of the modules, by their time in the build cache's profile
(`lean_profile.py`), that each module's closure no longer contains, summed
over all modules ("closure work"). It never proposes splitting registrations,
variants (reviewed by hand), `TCB/` or `Spec/` (trusted), and never moves an
importer that is one of those to X'.

The estimate is a ranking, not a proof: X' also needs the tactics and
notation X's proofs use (it counts X's imports with side effects that X uses
no declaration of, `check_lean_public_imports.SIDE_EFFECTS`), and a
declaration's attributes, `open`s and `variable`s move by hand. Build the
split and compare with `lean_closure.py score`.

  lean_split_advice.py read [-m MOD... | --prefix P...] [--jobs N] [--batch N]
      read the declarations of those modules (default: every module of the
      library) into the cache, `lean/.lake/split-advice.json.gz`, keyed by
      each module's Lake trace: a module whose build did not change is not
      read again
  lean_split_advice.py advise [--prefix P...] [--top N] [--json FILE]
                              [--min-saving S] [--jobs N] [--batch N]
      read what the cache lacks, then rank candidate splits of the modules
      under the prefixes (default: every module), each with the
      declarations to move, the imports of the new module and the importers
      to switch to it, and the closure work it saves

Run it after restoring the CI build cache (`lean/README.md`): it reads the
built modules. Reading the whole library takes about half an hour on four
cores the first time; later runs read only the modules whose builds changed.
"""

import argparse
import concurrent.futures
import gzip
import hashlib
import json
import os
import pathlib
import subprocess
import sys
import threading
import time

import check_lean_public_imports as check
import lean_closure
import lean_profile
import lean_shards as shards
import lean_source_evidence

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"
BUILD = LEAN / ".lake/build/lib/lean"
READER = ROOT / "ci/lean_decl_deps.lean"
CACHE = LEAN / ".lake/split-advice.json.gz"
LIBRARY = "VerifiedGarbage"
# What a module takes beyond its declarations' profile (`lean_closure.py`).
IMPORT_TIME = 1.25
# Directories never split: reviewed by hand, or trusted.
PROTECTED = ("Artifacts", "Generic", "Variants", "TCB", "Spec")


def progress(msg: str) -> None:
    print(msg, file=sys.stderr, flush=True)


def protected(mod: str) -> bool:
    parts = mod.split(".")
    return len(parts) < 2 or parts[0] != LIBRARY or parts[1] in PROTECTED or mod in check.NOT_MODULES


def trace_key(mod: str) -> str | None:
    """Lake's hash of the module's inputs and outputs, from its `.trace`;
    None without a build."""
    try:
        trace = json.loads((BUILD / pathlib.Path(*mod.split("."))).with_suffix(".trace").read_text())
        return hashlib.sha256(json.dumps([trace["depHash"], trace["outputs"]], sort_keys=True).encode()).hexdigest()
    except (OSError, ValueError, KeyError, TypeError):
        return None


def reader_key() -> str:
    toolchain = (LEAN / "lean-toolchain").read_text()
    return hashlib.sha256(READER.read_bytes() + toolchain.encode()).hexdigest()


def profile_time(mod: str) -> float | None:
    """The module's declarations' time in its build's profile (not time
    blocked on others), as `lean_import_replay.profile_cost` reads it."""
    try:
        trace = json.loads((BUILD / pathlib.Path(*mod.split("."))).with_suffix(".trace").read_text())
    except (OSError, ValueError):
        return None
    return sum(s for _, _, kind, s in lean_profile.steps(trace.get("log", [])) if kind != "blocked")


class Cache:
    """Each module's declarations, needs and uses, with its time, by the
    trace of the build they were read from."""

    def __init__(self, path: pathlib.Path = CACHE):
        self.path = path
        self.key = reader_key()
        try:
            with gzip.open(path, "rt") as f:
                data = json.load(f)
        except (OSError, ValueError, EOFError):
            data = {}
        if data.get("reader") != self.key:
            data = {}
        self.modules: dict[str, dict] = data.get("modules", {})
        self.lock = threading.Lock()

    def fresh(self, mod: str, key: str | None) -> bool:
        return key is not None and self.modules.get(mod, {}).get("key") == key

    def save(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        tmp = self.path.with_suffix(".tmp")
        with gzip.open(tmp, "wt", compresslevel=3) as f:
            json.dump({"reader": self.key, "modules": self.modules}, f, separators=(",", ":"))
        os.replace(tmp, self.path)


def run_reader(mods: list[str], timeout: float) -> dict:
    out = subprocess.run(["lake", "env", "lean", "--run", str(READER), *mods], cwd=LEAN,
                         capture_output=True, text=True, timeout=timeout)
    if out.returncode != 0:
        raise RuntimeError(out.stderr.strip()[-500:] or f"reader exited {out.returncode}")
    return json.loads(out.stdout)


def store(cache: Cache, data: dict, keys: dict[str, str | None]) -> None:
    """Keep the project modules of a reader's output, by name."""
    table = data["modules"]
    with cache.lock:
        for mod, row in data["results"].items():
            decls = {}
            for name, d in row["decls"].items():
                owners = sorted({table[i] for i in d["owners"]} - {mod})
                decls[name] = [[o for o in owners if o.startswith(LIBRARY + ".")], d["with"]]
            cache.modules[mod] = {"key": keys[mod], "time": profile_time(mod), "size": row["size"],
                                  "decls": decls, "uses": row["uses"]}


def read(cache: Cache, mods: list[str], jobs: int, batch: int, timeout: float = 1800) -> list[str]:
    """Read the modules of `mods` the cache lacks, in batches, `jobs` at a
    time. Modules that define the same names (one per target) cannot be
    loaded together: a batch that fails is read again in halves. Returns the
    modules that could not be read."""
    keys = {m: trace_key(m) for m in mods}
    unbuilt = [m for m in mods if keys[m] is None]
    todo = sorted(m for m in mods if keys[m] is not None and not cache.fresh(m, keys[m]))
    if unbuilt:
        progress(f"{len(unbuilt)} modules are not built; build them first: {', '.join(unbuilt[:5])}…")
    if not todo:
        return unbuilt
    # Keep each target's modules together, which share names less often.
    targets = ("X86_64", "X86", "AArch64", "Arm", "PPC64LE")
    todo.sort(key=lambda m: (next((t for t in targets if t in m.split(".")), ""), m))
    progress(f"reading {len(todo)} modules' declarations ({jobs} at a time)")
    failed: list[str] = []
    done = [0]
    start = time.monotonic()
    last_save = [start]

    def work(part: list[str]) -> list[list[str]]:
        try:
            store(cache, run_reader(part, timeout), keys)
        except (RuntimeError, ValueError, subprocess.TimeoutExpired) as error:
            if len(part) == 1:
                with cache.lock:
                    failed.append(part[0])
                progress(f"could not read {part[0]}: {error}")
                return []
            half = len(part) // 2
            return [part[:half], part[half:]]
        with cache.lock:
            done[0] += len(part)
            now = time.monotonic()
            if now - last_save[0] > 120:
                last_save[0] = now
                cache.save()
        progress(f"  {done[0]}/{len(todo)} read ({time.monotonic() - start:.0f} s)")
        return []

    with concurrent.futures.ThreadPoolExecutor(jobs) as pool:
        pending = {pool.submit(work, todo[i:i + batch]) for i in range(0, len(todo), batch)}
        while pending:
            finished, pending = concurrent.futures.wait(pending, return_when=concurrent.futures.FIRST_COMPLETED)
            for f in finished:
                pending |= {pool.submit(work, part) for part in f.result()}
    cache.save()
    return unbuilt + failed


class Graph:
    """The project's imports, with each module's closure as a bit set."""

    def __init__(self, imps: dict[str, list[str]]):
        self.imps = imps
        self.order = topological(imps)
        self.index = {m: i for i, m in enumerate(self.order)}
        self.closure: dict[str, int] = {}
        for m in self.order:
            c = 1 << self.index[m]
            for i in imps[m]:
                c |= self.closure[i]
            self.closure[m] = c
        self.users: dict[str, list[str]] = {m: [] for m in imps}
        for m, deps in imps.items():
            for i in deps:
                self.users[i].append(m)

    def members(self, bits: int) -> list[str]:
        out, i = [], 0
        while bits:
            low = bits & -bits
            i = low.bit_length() - 1
            out.append(self.order[i])
            bits ^= low
        return out

    def downstream(self, mods) -> set[str]:
        seen, stack = set(mods), list(mods)
        while stack:
            for u in self.users[stack.pop()]:
                if u not in seen:
                    seen.add(u)
                    stack.append(u)
        return seen


def topological(imps: dict[str, list[str]]) -> list[str]:
    order, done = [], set()
    for root in sorted(imps):
        stack = [(root, False)]
        while stack:
            m, ready = stack.pop()
            if ready:
                if m not in done:
                    done.add(m)
                    order.append(m)
            elif m not in done:
                stack.append((m, True))
                stack += [(i, False) for i in imps[m] if i not in done]
    return order


class Weights:
    """Sums the time of the modules of a bit set."""

    def __init__(self, graph: Graph, time: dict[str, float]):
        self.graph = graph
        self.time = [time.get(m, 0.0) for m in graph.order]
        # Sum a byte of the set at a time.
        self.tables = []
        for base in range(0, len(self.time), 8):
            row = [0.0] * 256
            for b in range(256):
                row[b] = sum(self.time[base + k] for k in range(8) if b >> k & 1 and base + k < len(self.time))
            self.tables.append(row)

    def __call__(self, bits: int) -> float:
        total = 0.0
        data = bits.to_bytes((bits.bit_length() + 7) // 8, "little")
        tables = self.tables
        for i, b in enumerate(data):
            if b:
                total += tables[i][b]
        return total


def side_effects(text: str) -> bool:
    code = lean_source_evidence.code_only(text)
    return bool(check.SIDE_EFFECTS.search(code) or check.INSTANCE_DECLS.search(code)
                or check.INITIALIZER_DECLS.search(code))


def candidates(graph: Graph, weights: Weights, cache: Cache, texts: dict[str, str], scope: set[str],
               min_saving: float) -> list[dict]:
    """Splits of the modules of `scope`, ranked by the closure work they
    save the modules they switch (exact for all modules: `evaluate`)."""
    effects = {}

    def has_effects(m):
        if m not in effects:
            effects[m] = side_effects(texts.get(m, ""))
        return effects[m]

    out = []
    for x in sorted(scope):
        info = cache.modules.get(x)
        users = [m for m in graph.users.get(x, []) if not protected(m)]
        if not info or protected(x) or not users or not info["decls"]:
            continue
        own_uses = set(info["uses"])
        # What X' needs besides its declarations' owners: X's imports that
        # change elaboration and that X uses no declaration of.
        tactics = [i for i in graph.imps[x] if i not in own_uses and has_effects(i)]
        base = 0
        for t in tactics:
            base |= graph.closure[t]
        whole = graph.closure[x]
        groups = []
        for m in users:
            row = cache.modules.get(m)
            used = sorted(set(row["uses"].get(x, []))) if row else []
            if not used or any(u not in info["decls"] for u in used):
                continue  # nothing recorded, or a private declaration
            moved = set(used)
            for u in used:
                moved.update(info["decls"][u][1])
            owners = set()
            for d in moved:
                owners.update(info["decls"].get(d, [[], []])[0])
            need = base
            for o in owners:
                if o in graph.closure:
                    need |= graph.closure[o]
            rest = 0
            for i in graph.imps[m]:
                if i != x:
                    rest |= graph.closure[i]
            saved = whole & ~need & ~rest & ~(1 << graph.index[x])
            groups.append((weights(need), m, moved, owners, need, rest, saved))
        if not groups:
            continue
        # Switch importers lightest first, while that saves more.
        groups.sort(key=lambda g: (g[0], g[1]))
        best, moved, owners, need, switched = None, set(), set(), base, []
        for _, m, mv, ow, nd, _, _ in groups:
            moved |= mv
            owners |= ow
            need |= nd
            switched.append(m)
            if len(moved) >= len(info["decls"]):
                break  # moving everything is renaming
            saving = 0.0
            for g in groups:
                if g[1] in switched:
                    saving += weights(whole & ~need & ~g[5] & ~(1 << graph.index[x]))
            if best is None or saving > best["local_saving"]:
                best = {"module": x, "local_saving": saving, "switch": list(switched), "moved": sorted(moved),
                        "owners": sorted(owners), "tactics": tactics, "new_closure_work": weights(need),
                        "closure_work": weights(whole), "decls": len(info["decls"]), "size": info["size"],
                        "importers": len(users)}
        if best and best["local_saving"] >= min_saving:
            out.append(best)
    out.sort(key=lambda c: -c["local_saving"])
    return out


def minimal(graph: Graph, mods) -> list[str]:
    """The modules of `mods` no other of them imports, directly or not."""
    mods = sorted(set(mods))
    return [m for m in mods if not any(o != m and graph.closure[o] >> graph.index[m] & 1 for o in mods)]


def rebuild_work(imps, vis, modes, time: dict[str, float]) -> float:
    """The work rebuilt after an edit of each module, summed over modules:
    each module's time, for each module of the project whose outputs its
    build reads (`lean_shards.reads`), as Lake rebuilds it when one of those
    changes."""
    read = shards.reads(imps, shards.closures(imps), vis, modes)
    return sum(time.get(m, 0.0) * len(r) for m, r in read.items())


def critical_path(imps, time: dict[str, float]) -> float:
    """The longest chain of imports of a full build, by time."""
    return max(shards.paths(imps, {m: time.get(m, 0.0) for m in imps}).values())


class Baseline:
    """What `evaluate` compares a split with: every module's closure work,
    the rebuild work of an edit (`rebuild_work`), the critical path and CI's
    plan of a full rebuild (`lean_closure.full_plan`)."""

    def __init__(self, graph: Graph, weights: Weights, time: dict[str, float]):
        self.work = {m: weights(graph.closure[m]) for m in graph.order}
        self.modes: dict[str, dict] = {}
        imps, self.vis, _ = shards.source_info(shards.modules(), import_modes=self.modes)
        self.everything = {m: list(dict.fromkeys(v)) for m, v in imps.items()}
        self.time = time
        self.plan = lean_closure.full_plan(self.everything, time)
        self.rebuild = rebuild_work(self.everything, self.vis, self.modes, time)
        self.path = critical_path(self.everything, time)


def evaluate(graph: Graph, base: Baseline, cand: dict, info: dict) -> dict:
    """What the split saves: the new module X' imports the owners of what
    moves and X's tactics, X imports X', and the switched importers import
    X' instead of X. The closure work of the modules there were (X' adds
    one module to its importers' closures, which builds once), and the full
    rebuild's plan: the work CI's shards build more than once, and the
    slowest shard's estimate with as many shards as before, each compared
    with the plan with X' added but no importer switched."""
    x = cand["module"]
    new = x + "Light"
    imports = minimal(graph, list(cand["owners"]) + list(cand["tactics"]))
    share = len(cand["moved"]) / max(info["size"], 1)
    time = dict(base.time)
    time[new] = base.time.get(x, 0.0) * share + IMPORT_TIME
    time[x] = base.time.get(x, 0.0) * (1 - share)

    def split(imps, switch=cand["switch"]):
        imps = {m: list(v) for m, v in imps.items()}
        imps[new] = list(imports)
        imps[x] = imps[x] + [new]
        for m in switch:
            imps[m] = [new if i == x else i for i in imps[m]]
        return imps

    def visible(vis, modes):
        """X' passes on everything it imports, X passes X' on, and the
        switched importers import X' as they imported X."""
        vis, modes = dict(vis), {m: {k: list(v) for k, v in d.items()} for m, d in modes.items()}
        vis[new] = (list(imports), [])
        if vis.get(x) is not None:
            vis[x] = (vis[x][0] + [new], vis[x][1])
        for m in cand["switch"]:
            if vis.get(m) is not None:
                vis[m] = tuple([new if i == x else i for i in part] for part in vis[m])
            for k in modes.get(m, {}):
                modes[m][k] = [new if i == x else i for i in modes[m][k]]
        return vis, modes

    after = Graph(split(graph.imps))
    weights = Weights(after, time)
    saved = 0.0
    shrunk = 0
    for m in graph.order:
        if after.closure[m].bit_count() < graph.closure[m].bit_count() + (after.closure[m] >> after.index[new] & 1):
            shrunk += 1
            saved += base.work[m] - weights(after.closure[m])
    # The greedy plan moves by minutes with any new module: compare with the
    # same new module that no importer uses yet.
    plan = lean_closure.full_plan(split(base.everything), time, base.plan["shards"])
    null = lean_closure.full_plan(split(base.everything, []), time, base.plan["shards"])
    everything = split(base.everything)
    project = sum(1 for m in base.everything if m.split(".")[0] == LIBRARY)
    return {"closure_work_saved": saved, "modules_shrunk": shrunk, "new_imports": imports,
            "rebuild_saved_per_edit": (base.rebuild - rebuild_work(everything, *visible(base.vis, base.modes), time))
            / project,
            "critical_path_saved": base.path - critical_path(everything, time),
            "twice_saved": null["twice"] - plan["twice"],
            "slowest_saved": null["slowest_at"] - plan["slowest_at"]}


def library_imports() -> tuple[dict[str, list[str]], dict[str, str]]:
    mods = {m: p for m, p in shards.modules().items() if m.split(".")[0] == LIBRARY}
    texts = {m: p.read_text() for m, p in mods.items()}
    return {m: list(dict.fromkeys(shards.imported_by(t, texts))) for m, t in texts.items()}, texts


def scoped(mods, prefixes: list[str] | None) -> list[str]:
    return sorted(m for m in mods if not prefixes or any(m == p or m.startswith(p + ".") for p in prefixes))


def show(cands: list[dict], evaluated: dict[str, dict], top: int) -> None:
    for c in cands[:top]:
        e = evaluated.get(c["module"], {})
        if e:
            print(f"{c['module']}: closure work saved {e['closure_work_saved']:.0f} s in {e['modules_shrunk']} "
                  f"modules; rebuild per edit {e['rebuild_saved_per_edit']:.2f} s less; critical path "
                  f"{e['critical_path_saved']:.0f} s shorter; full rebuild: {e['twice_saved']:.0f} s less built "
                  f"twice, slowest shard {e['slowest_saved']:.0f} s faster")
        else:
            print(f"{c['module']}: closure work saved {c['local_saving']:.0f} s in the switched importers")
        print(f"  move {len(c['moved'])} of its {c['decls']} declarations into a new module, "
              f"whose closure takes {c['new_closure_work']:.0f} s of its {c['closure_work']:.0f} s:")
        for d in c["moved"][:12]:
            print(f"    {d}")
        if len(c["moved"]) > 12:
            print(f"    … {len(c['moved']) - 12} more")
        print(f"  the new module imports: {', '.join(e.get('new_imports', c['owners'] + c['tactics']))}")
        print(f"  switch {len(c['switch'])} of its {c['importers']} importers: {', '.join(c['switch'][:8])}"
              f"{' …' if len(c['switch']) > 8 else ''}")


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="cmd", required=True)
    for name in ("read", "advise"):
        p = sub.add_parser(name)
        p.add_argument("--prefix", nargs="+", help="modules under these names (default: all)")
        p.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) - 1))
        p.add_argument("--batch", type=int, default=100)
    sub.choices["read"].add_argument("-m", "--modules", nargs="+")
    adv = sub.choices["advise"]
    adv.add_argument("--top", type=int, default=20)
    adv.add_argument("--evaluate", type=int, default=20, help="evaluate the top N exactly (default 20)")
    adv.add_argument("--min-saving", type=float, default=10.0)
    adv.add_argument("--json", type=pathlib.Path)
    args = parser.parse_args(argv)
    os.environ["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + os.environ.get("PATH", "")
    imps, texts = library_imports()
    cache = Cache()
    if args.cmd == "read":
        mods = args.modules or scoped(imps, args.prefix)
        missing = read(cache, mods, args.jobs, args.batch)
        print(f"{len(cache.modules)} modules in the cache; {len(missing)} not read")
        return 0
    graph = Graph(imps)
    scope = scoped(imps, args.prefix)
    # A candidate needs its own declarations and its importers' uses.
    needed = set(scope) | {u for x in scope for u in graph.users.get(x, [])}
    read(cache, sorted(needed), args.jobs, args.batch)
    time_of = {}
    for m in shards.modules():
        t = cache.modules[m]["time"] if m in cache.modules else profile_time(m)
        time_of[m] = (t or 0.0) + IMPORT_TIME
    weights = Weights(graph, time_of)
    cands = candidates(graph, weights, cache, texts, set(scope), args.min_saving)
    evaluated = {}
    if cands[:args.evaluate]:
        progress(f"evaluating {len(cands[:args.evaluate])} of {len(cands)} candidates")
        base = Baseline(graph, weights, time_of)
        for c in cands[:args.evaluate]:
            evaluated[c["module"]] = evaluate(graph, base, c, cache.modules[c["module"]])
    cands[:args.evaluate] = sorted(cands[:args.evaluate],
                                   key=lambda c: -evaluated[c["module"]]["closure_work_saved"])
    show(cands, evaluated, args.top)
    if args.json:
        args.json.write_text(json.dumps([{**c, **evaluated.get(c["module"], {})} for c in cands], indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
