#!/usr/bin/env python3
"""Packs Lean builds into Lake's per-module archives, and restores them.

  python3 ci/lean_cache.py pack lean .lake/build .lake/packages | zstd -T0 -5 -o cache.tar.zst
  zstd -dc cache.tar.zst | python3 ci/lean_cache.py unpack lean

  python3 ci/lean_cache.py store lean .lake/build    # then cache lean/.lake/ltar
  python3 ci/lean_cache.py restore lean              # after restoring it

`pack` updates `.lake/ltar/`, which holds an `.ltar` archive of each built
module's outputs (its `.olean`, `.olean.server`, `.olean.private`, `.ilean`,
`.ir.sig`, `.ir`, `.c` and `.trace`) in the given directories (relative to
the Lean project, `lean/`): the format of Lake's `ltar` facet and Mathlib's
cache, a fifth of the size `zstd` makes of the same files, since `leantar`
encodes an `.olean`'s objects compactly before compressing them. A module's
archive is `.lake/ltar/<build>/<Module>.ltar`, where `<build>` is its build
directory relative to `.lake/` (`build`, or `packages/mathlib/.lake/build`).
Of a module's `.c`, which only building native code reads, an archive keeps
only that of a module the build compiled (an object, `ir/<Module>.c.o.*`,
next to it: the precompiled libraries' modules, and the few of the
packages' executables): the others' are nine tenths of the C (1.2 GB),
written and never read. `unpack` and `restore` write an empty file in its
place, which is all Lake looks for (the `.c.hash` in `files.tar` gives its
hash), and `lakefile.toml` makes compiling an empty file an error.
`.lake/ltar/index.json` records the dependency hash and output hashes of
each archive's module, and whether it holds the `.c`: `pack` packs only the
modules that changed since,
and removes the archives of modules that no longer exist. Before packing a
module, it moves the messages of its `.trace` (the build's profile, nine
tenths of the traces' bytes) to `.lake/ltar/logs.json.gz`, so that the archive
keeps the trace as just its hashes, and unpacking writes a few bytes for it
(archives packed before `logs.json.gz` are packed again). It writes every
other file in the directories (the outputs' `.hash` files, native
libraries, Lake's checkouts of the dependencies, but not the dependencies'
executables) to `.lake/ltar/files.tar.gz`, then, as `bundle` does, a tar
of the archives with `files.tar` (decompressed) first, to stdout.

It packs with `leantar-batch` (`--leantar`), the release of reaperhulk/leangz
that `ci/leantar_release.py` downloads (`.github/actions/leantar`), which
packs every module in one process at zstd level `--level` (default 5); the
toolchain's own `leantar` takes half a CPU-second for each module. `restore`
unpacks with it too, in a third of the toolchain's CPU time.

`store` does the same but for the tar to stdout, so that `.lake/ltar`
alone holds the build: CI's Actions cache keeps it, and each job that
restores it runs `restore`, which extracts `files.tar.gz` and unpacks every
archive, keeping them, so that the build's next `store` packs only what
changed. A shard needs only the modules its targets import: `restore
--modules` unpacks only theirs, and `--except` the others, before the
shard assembles the build.

`store` and `restore` accept `--archive-dir` to keep Mathlib's Actions cache
in `.lake/mathlib-ltar`, independently of the project's `.lake/ltar` (each
has its own index and `files.tar.gz`). `pack --reuse .lake/mathlib-ltar` copies
matching module archives into the published cache, repacking missing or
changed modules. The published format stays `.lake/ltar`.

`bundle lean .lake/ltar .lake/mathlib-ltar` publishes those existing caches
without installing Lean or expanding module outputs: it combines their
indexes, `logs.json.gz` and `files.tar.gz` (decompressed: `files.tar` of an
archive directory from before it also works), and streams the indexed
`.ltar` files in one tar, with `files.tar` first. Inputs must have disjoint, nonempty indexes
and all indexed archives. It leaves both source caches unchanged.

`unpack` extracts such a tar from stdin into the Lean project. `tar`
extracts `files.tar` in the background, as `restore` does: its files are
most of the files, each small, and `tarfile` would create them one at a
time, as long as `leantar` takes for all the archives. The archives go to
the toolchain's `leantar` in batches of `--batch` bytes, each unpacked while
the next arrives. The outputs come out byte for byte as they were packed;
the `.trace` keeps what Lake needs (the dependency hash and the outputs'
hashes), without the build's messages or the record of its inputs that
Lake writes only for people to read. The messages, with the profile
`ci/lean_profile.py` reads, are written only with `--logs`: one file,
`.lake/ltar/logs.json.gz`.

`restore --empty-private` and `unpack --empty-private` write each module's
`.olean.private` (but the trusted base's) as an empty file, half of what
unpacking writes: nothing that imports a module as a module reads it. It
needs the release's leantar (`ci/leantar_release.py`), which `unpack` then
downloads (once) unless given `--leantar`. `unpack` keeps the archives of the
project's modules (`KEPT`), from which `fill-private` writes the private parts
a tool reads (`lake shake`, a file that is not a module, an `import all`) when
it needs them: `check_lean_public_imports.py` and `lit_imports.py` run it
themselves (`lean/README.md`, "Without the private parts").

It stages `files.tar` and each batch in `--tmp` (default: `/dev/shm`, a
tmpfs, when there is one), so they never reach the disk, and removes them.
"""

import argparse
import gzip
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

import leantar_release

# A module's outputs in its build directory's `lib/lean` (base 0) and `ir`
# (base 1), in the order `leantar` wants them: the `.olean`'s parts first.
OUTPUTS = [(0, ".olean"), (0, ".olean.server"), (0, ".olean.private"), (0, ".ilean"),
           (0, ".ir.sig"), (0, ".ir"), (1, ".c")]
LTAR = Path(".lake/ltar")
# `store`'s tar of the files not in an archive.
FILES = "files.tar"
# `FILES` as `store` keeps it, compressed: `.hash` files are most of its
# entries, each 16 bytes in 1 KiB of tar, and every CI job that restores an
# archive directory writes it to disk before extracting it. The published
# cache holds `FILES` itself, which `unpack` stages in memory.
STORED = "files.tar.gz"
# The key of each archive's module (`key`), by archive, so `pack` repacks only what changed.
INDEX = "index.json"
# The build's messages (the `log` of each module's `.trace`, with the profile
# `lean_profile.py` reads), by archive, with the dependency hash of the build
# that wrote them: `pack` moves them out of the traces before packing them, so
# that each archive keeps its trace as just its hashes, and `unpack` writes
# them, one file, only if asked. Its presence says that every archive of its
# index was packed so.
LOGS = "logs.json.gz"


def leantar(lean):
    """The `leantar` of the project's toolchain, next to its `lean`."""
    prefix = subprocess.run(["lean", "--print-prefix"], cwd=lean, check=True,
                            capture_output=True, text=True).stdout.strip()
    return Path(prefix) / "bin" / "leantar"


def build_dirs(lean, roots):
    """Every Lake build directory under the roots (relative to `lean`)."""
    for root in roots:
        for lib in sorted((lean / root).glob("**/lib/lean")):
            build = lib.parent.parent
            if build.name == "build" and build.parent.name == ".lake":
                yield build.relative_to(lean)


def modules(lean, build):
    """The built modules of `build`: their names, traces, the outputs their
    archives hold, and the `.c` they leave out, if any (paths relative to
    `lean`)."""
    lib = lean / build / "lib" / "lean"
    for trace in sorted(lib.glob("**/*.trace")):
        name = str(trace.relative_to(lib))[:-len(".trace")]
        if not (lib / (name + ".olean")).is_file():
            continue  # not a module (a native library's trace)
        outputs = [(base, ext, build / ("lib/lean", "ir")[base] / (name + ext)) for base, ext in OUTPUTS]
        outputs = [o for o in outputs if (lean / o[2]).is_file()]
        c = build / "ir" / (name + ".c")
        if compiled(lean, c):
            yield name, trace, outputs, None
        else:
            yield name, trace, [o for o in outputs if o[2] != c], c


def compiled(lean, c):
    """Whether the build compiled the C file `c` (relative to `lean`): Lake
    writes its object next to it, `<Module>.c.o.export` or
    `<Module>.c.o.noexport`."""
    return any((lean / c.parent / (c.name + o)).is_file() for o in (".o.export", ".o.noexport"))


def key(trace, c):
    """What a module's archive holds: its dependency hash, its outputs'
    hashes, and whether its `.c` (`c`, a bool)."""
    t = json.loads(trace.read_text())
    return json.dumps([t["depHash"], t["outputs"], c], sort_keys=True)


def placeholder(lean, rel):
    """Writes an empty file in place of the `.c` of the module whose archive
    is at `.lake/ltar/<rel>`, before `leantar` unpacks the archive, which
    replaces it if the archive holds the `.c`; it replaces whatever `.c` was
    there (of another build of the module). Lake only checks that the file
    exists, and reads its hash from its `.c.hash`; compiling it fails
    (`lakefile.toml`'s `moreLeancArgs`)."""
    build = build_of(rel)
    end = len(Path(build).parts) - 1
    name = Path(*Path(rel).parts[end:]).with_suffix(".c")
    c = lean / build / "ir" / name
    c.parent.mkdir(parents=True, exist_ok=True)
    c.open("w").close()


def read_logs(path):
    return json.loads(gzip.decompress(path.read_bytes()))


def logs_bytes(logs):
    """`LOGS`'s contents: gzip, a tenth of the JSON's size, since every job
    that restores CI's Actions cache writes it (`mtime=0`: the same logs, the
    same bytes)."""
    return gzip.compress(json.dumps(logs, sort_keys=True, separators=(",", ":")).encode(), mtime=0)


def take_log(trace, rel, logs, old_logs):
    """Moves the messages of the module's `.trace` to `logs[rel]`, with the
    trace's dependency hash, and rewrites the trace without them. A trace
    without messages (the module unpacked from an archive, not built) keeps
    the entry of `old_logs` for the same dependency hash."""
    t = json.loads(trace.read_text())
    if t.get("log"):
        logs[rel] = {"depHash": t["depHash"], "log": t.pop("log")}
        trace.write_text(json.dumps(t))
    elif rel in old_logs and old_logs[rel]["depHash"] == t["depHash"]:
        logs[rel] = old_logs[rel]
    else:
        logs.pop(rel, None)


def update(lean, roots, jobs, level, tool, archive_dir=LTAR, reuse=None):
    """Brings the archives of `archive_dir` up to date with the builds under
    `roots`, and returns the files they hold."""
    ltars = lean / archive_dir
    old = json.loads((ltars / INDEX).read_text()) if (ltars / INDEX).is_file() else {}
    # Archives packed with their messages in them (before `LOGS`) are packed again.
    old_logs = read_logs(ltars / LOGS) if (ltars / LOGS).is_file() else None
    if old_logs is None:
        old = {}
    reused, reused_logs = {}, {}
    if reuse is not None and (lean / reuse / INDEX).is_file() and (lean / reuse / LOGS).is_file():
        reused = json.loads((lean / reuse / INDEX).read_text())
        reused_logs = read_logs(lean / reuse / LOGS)
    builds = list(build_dirs(lean, roots))
    # Entries of builds not packed now stay.
    index = {rel: k for rel, k in old.items()
             if not any(build_of(rel) == build for build in builds)}
    logs = {rel: entry for rel, entry in (old_logs or {}).items() if rel in index}
    packed = set()
    tasks = []
    kept = 0
    for build in builds:
        for name, trace, outputs, c in modules(lean, build):
            rel = str(build.relative_to(".lake") / name)
            ltar = archive_dir / (rel + ".ltar")
            index[rel] = key(trace, c is None)
            take_log(trace, rel, logs, old_logs or {})
            # The outputs' `.hash` files stay: without them Lake would read
            # every output again to hash it. A `.c` left out of the archive
            # goes nowhere: unpacking writes an empty file in its place.
            packed.add(trace.relative_to(lean))
            packed.update(path for _, _, path in outputs)
            if c is not None:
                packed.add(c)
            if old.get(rel) == index[rel] and (lean / ltar).is_file():
                kept += 1
                continue
            (lean / ltar).parent.mkdir(parents=True, exist_ok=True)
            # The publisher can reuse the independently cached Mathlib
            # archives. Missing or changed entries are packed normally.
            if reused.get(rel) == index[rel] and (lean / reuse / (rel + ".ltar")).is_file():
                shutil.copyfile(lean / reuse / (rel + ".ltar"), lean / ltar)
                if rel not in logs and rel in reused_logs:
                    logs[rel] = reused_logs[rel]
                kept += 1
                continue
            # A placeholder (`restore --empty-private`) of a module this build did not
            # build: never pack it, as the archive would then lose its private data.
            for _, ext, path in outputs:
                if ext == ".olean.private" and (lean / path).stat().st_size == 0:
                    raise SystemExit(f"{path} is a placeholder (`restore --empty-private`), "
                                     f"but its module's archive is out of date")
            # Without `-s`, the archive keeps the trace's dependency hash, so
            # unpacking needs nothing but the archive.
            files = []
            for base, ext, _ in outputs:
                files += ["-i", str(base), name + ext]
            tasks.append({"out": str(ltar), "trace": name + ".trace", "files": files,
                          "base": [str(build / "lib/lean"), str(build / "ir")]})
    # Until the archives are packed, the index must not vouch for them.
    (ltars / INDEX).unlink(missing_ok=True)
    (ltars / LOGS).unlink(missing_ok=True)
    if tasks:
        subprocess.run([tool, "--jobs", str(jobs), "--level", str(level), "-p", "-"], cwd=lean,
                       input=json.dumps(tasks).encode(), check=True)
    # The archives of modules that no longer exist.
    removed = 0
    for ltar in sorted(ltars.rglob("*.ltar")):
        if str(ltar.relative_to(ltars))[:-len(".ltar")] not in index:
            ltar.unlink()
            removed += 1
    ltars.mkdir(parents=True, exist_ok=True)
    (ltars / LOGS).write_bytes(logs_bytes(logs))
    (ltars / INDEX).write_text(json.dumps(index, sort_keys=True))
    print(f"Packed {len(tasks)} modules, kept {kept}, removed {removed}", file=sys.stderr)
    return packed


def other_files(lean, roots, packed):
    """The entries under `roots` that are not in a module's archive, but for
    the dependencies' executables (`.lake/packages/<name>/.lake/build/bin`,
    Mathlib's `cache`, 114 MiB): only CI's setup runs one, on a miss of
    Mathlib's Actions cache, where Lake builds it anyway."""
    paths = []
    for root in roots:
        for dirpath, dirnames, filenames in os.walk(lean / root):
            dirnames.sort()
            rel = Path(dirpath).relative_to(lean)
            if rel.parts[:2] == (".lake", "packages") and rel.parts[3:6] == (".lake", "build", "bin"):
                dirnames.clear()
                continue
            paths.append(str(rel))
            paths += [str(rel / f) for f in sorted(filenames) if rel / f not in packed]
            # Symbolic links to directories are entries, not walked.
            paths += [str(rel / d) for d in dirnames if (lean / rel / d).is_symlink()]
    return paths


def pack(lean, roots, jobs, level, tool, out, reuse=None):
    store(lean, roots, jobs, level, tool, reuse=reuse)
    bundle(lean, [LTAR], out)


def stored_files(source):
    """The `files.tar` of an archive directory: `STORED`, or `FILES` from
    before it."""
    return source / STORED if (source / STORED).is_file() else source / FILES


def bundle(lean, archive_dirs, out):
    """Publish existing caches without unpacking or repacking any module.

    The caches must cover disjoint modules. GNU tar concatenates their
    files.tar archives, decompressed, without extracting the small files.
    Only indexed modules are included; leftover archives are ignored.
    """
    index, logs, archives = {}, {}, []
    for directory in archive_dirs:
        source = lean / directory
        entries = json.loads((source / INDEX).read_text())
        if (source / LOGS).is_file():
            logs.update((rel, entry) for rel, entry in read_logs(source / LOGS).items()
                        if rel in entries)
        if not entries:
            raise ValueError(f"Empty module cache: {directory}")
        if not stored_files(source).is_file():
            raise FileNotFoundError(source / STORED)
        for rel, key in entries.items():
            if Path(rel).is_absolute() or ".." in Path(rel).parts:
                raise ValueError(f"Invalid module archive path: {rel}")
            if rel in index:
                raise ValueError(f"Overlapping module caches: {rel}")
            archive = source / (rel + ".ltar")
            if not archive.is_file():
                raise FileNotFoundError(archive)
            index[rel] = key
            archives.append((rel, archive))
    # Validate all inputs before writing anything to stdout. The temporary
    # file holds only miscellaneous files, never expanded module outputs.
    with tempfile.TemporaryDirectory(prefix="lean-cache-bundle-") as tmp:
        files = Path(tmp) / FILES
        for i, directory in enumerate(archive_dirs):
            part = files if i == 0 else Path(tmp) / f"{i}.tar"
            source = stored_files(lean / directory)
            if source.name == STORED:
                with gzip.open(source) as f, open(part, "wb") as g:
                    shutil.copyfileobj(f, g)
            else:
                shutil.copyfile(source, part)
            if i:
                subprocess.run(["tar", "--concatenate", "--file", str(files), str(part)], check=True)
        with tarfile.open(fileobj=out, mode="w|", dereference=True) as tar:
            tar.add(files, arcname=str(LTAR / FILES))
            for name, data in ((INDEX, json.dumps(index, sort_keys=True).encode()), (LOGS, logs_bytes(logs))):
                member = tarfile.TarInfo(str(LTAR / name))
                member.size = len(data)
                tar.addfile(member, io.BytesIO(data))
            for rel, archive in sorted(archives):
                tar.add(archive, arcname=str(LTAR / (rel + ".ltar")))
    print(f"Bundled {len(archives)} modules", file=sys.stderr)


def store(lean, roots, jobs, level, tool, archive_dir=LTAR, reuse=None):
    paths = other_files(lean, roots, update(lean, roots, jobs, level, tool, archive_dir, reuse))
    (lean / archive_dir / FILES).unlink(missing_ok=True)
    subprocess.run(["tar", "-C", str(lean), "-czf", str(lean / archive_dir / STORED), "--no-recursion",
                    "--null", "-T", "-"], input="\0".join(paths).encode(), check=True)


# The modules of this project whose private data (`.olean.private`)
# `--empty-private` unpacks all the same: the trusted base, which `Emit.lean`
# and `EmitOne.lean` load as files that are not modules. The packages' (Mathlib's)
# are unpacked too: `VerifiedGarbageAuditBase.lean` reads them.
KEEP_PRIVATE = ("VerifiedGarbage.TCB.",)

# Where `unpack --empty-private` keeps the archives of the project's modules,
# from which `fill_private` writes their private parts when a tool needs them
# (`.lake/ltar`, where CI keeps them, is read too). Laid out as `.lake/ltar`.
KEPT = Path(".lake/ltar-private")

IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)")


def imports_of(lean, module):
    """The modules the source of `module` (of the project, or a path ending in
    `.lean`) imports, from its header; [] if there is no such source (a module
    of a package)."""
    src = (Path(module) if module.endswith(".lean")
           else lean.joinpath(*module.split(".")).with_suffix(".lean"))
    if not src.is_file():
        return []
    out, comment = [], False
    with src.open(encoding="utf-8") as f:
        for line in f:
            t = line.strip()
            if comment:
                comment = "-/" not in t
                continue
            if t.startswith("/-!"):
                break  # the module's docstring, after the header
            if t.startswith("/-"):
                comment = "-/" not in t
                continue
            if not t or t.startswith("--") or t in ("module", "prelude"):
                continue
            m = IMPORT.match(t)
            if not m:
                break
            out.append(m.group(1))
    return out


def closure(lean, modules):
    """`modules` and every module of the project they import, transitively."""
    seen, stack = set(), list(modules)
    while stack:
        m = stack.pop()
        if m not in seen:
            seen.add(m)
            stack += imports_of(lean, m)
    return seen


def fill_private(lean, modules, tool=None, jobs=None):
    """Writes the private part (`.olean.private`) of each module of `modules`
    and of everything they import that `--empty-private` left empty, from its
    archive (`KEPT`, or CI's `.lake/ltar`), before a tool that reads them runs:
    `lake shake` reads the private part of each module it checks and of all
    they import. Only `.olean.private` is written: the module's other outputs,
    and its trace, are what they were. Run it after building `modules`: an
    empty part is then one of the restored build, whose archive is current
    (Lake rebuilds a module whose sources changed, private part and all), and
    the sources' imports are the build's. Returns how many it wrote."""
    lib = lean / ".lake/build/lib/lean"
    found, missing = [], []
    for m in sorted(closure(lean, modules)):
        if m.endswith(".lean"):
            continue
        rel = Path(*m.split("."))
        private = lib / (str(rel) + ".olean.private")
        if not private.is_file() or private.stat().st_size:
            continue
        for d in (KEPT, LTAR):
            archive = lean / d / "build" / (str(rel) + ".ltar")
            if archive.is_file():
                found.append((rel, archive, private))
                break
        else:
            missing.append(m)
    if missing:
        raise SystemExit(f"{len(missing)} modules have an empty .olean.private and no archive "
                         f"(e.g. {missing[0]}): restore the build again without --empty-private "
                         "(lean/README.md, \"Without the private parts\")")
    if not found:
        return 0
    with tempfile.TemporaryDirectory(dir=lean / ".lake") as tmp:
        out = Path(tmp)
        records = [{"file": str(archive), "base": [str(out / "lib/lean"), str(out / "ir")]}
                   for _, archive, _ in found]
        subprocess.run([tool or str(leantar(lean)), "-f", "--jobs", str(jobs or os.cpu_count()),
                        "-x", "-j", "-"], cwd=lean, input=json.dumps(records).encode(), check=True)
        for rel, _, private in found:
            os.replace(out / "lib/lean" / (str(rel) + ".olean.private"), private)
    print(f"Wrote the private parts of {len(found)} modules", file=sys.stderr)
    return len(found)


def restore(lean, jobs, tool, archive_dir=LTAR, modules=None, others=None, empty_private=False):
    """Extracts `files.tar` and unpacks the archives; with `modules` (a
    file of module names, one per line), only the archives of those of the
    project's build, and with `others` (such a file), only the archives
    `modules` left out, and not `files.tar` again: a build in between may
    have changed its `.hash` files.

    With `empty_private`, each module's `.olean.private` but `KEEP_PRIVATE`'s is
    an empty file (`leantar --empty-private`), half of the data, which nothing
    that imports a module as a module reads: Lake only checks that it is there,
    and the emitter's audits read the audit records (`TCB/AuditRecords.lean`)."""
    ltars = lean / archive_dir
    chosen = set((modules or others).read_text().split()) if modules or others else set()
    stored = stored_files(ltars)
    files = extract(lean, stored) if stored.is_file() and not others else None
    try:
        records = []
        for ltar in sorted(ltars.rglob("*.ltar")):
            rel = ltar.relative_to(ltars)
            m = module_of(rel)
            # A package's archive goes with `modules`, as `files.tar` does.
            if modules and m is not None and m not in chosen:
                continue
            if others and (m is None or m in chosen):
                continue
            build = build_of(rel)
            placeholder(lean, rel)
            records.append(({"file": str(ltar.relative_to(lean)),
                             "base": [str(build / "lib/lean"), str(build / "ir")]},
                            empty_private and m is not None and not m.startswith(KEEP_PRIVATE)))
        for empty in (False, True):
            batch = [r for r, e in records if e == empty]
            if batch:
                # `-f`: a trace already there (from a build of other sources) would
                # otherwise keep that build's outputs.
                subprocess.run([tool or str(leantar(lean)), "-f", "--jobs", str(jobs), "-x"] +
                               (["--empty-private"] if empty else []) + ["-j", "-"],
                               cwd=lean, input=json.dumps(batch).encode(), check=True)
    finally:
        finish(files)
    print(f"Unpacked {len(records)} modules", file=sys.stderr)


def extract(lean, files):
    """Starts `tar` extracting a `files.tar` into the Lean project. It runs
    while the archives unpack: its files are most of the files, each small.
    `--no-same-owner`: CI's runner user owns the archive's files, and
    extracting them as root (as in a container) would keep that owner. Git
    would then refuse the dependencies' checkouts, so Lake would clone them
    again and build Mathlib from source.

    `files.tar` lists each root (`.lake/build`, `.lake/packages`) before what
    it holds, but not `.lake`. Without `.lake`, `tar` makes it for the first
    root, retries the root, and fails ("Unexpected inconsistency when making
    directory") if the archives' unpacking made the root in between."""
    (lean / ".lake").mkdir(parents=True, exist_ok=True)
    return subprocess.Popen(["tar", "--no-same-owner", "-xf", str(files), "-C", str(lean)]
                            + (["-z"] if files.name == STORED else []))


def finish(files):
    """Waits for `extract`'s `tar`, if there is one, and fails if it did."""
    if files is not None and files.wait():
        raise SystemExit(f"tar failed ({files.returncode})")


def module_of(rel):
    """The module of the project's build whose archive is at
    `.lake/ltar/<rel>`, or None for a package's."""
    parts = Path(rel).with_suffix("").parts
    return ".".join(parts[1:]) if parts[0] == "build" else None


def build_of(rel):
    """The build directory (relative to the Lean project) of an archive at
    `.lake/ltar/<rel>`: `<rel>` starts with `build`, or with a package's
    `packages/<name>/.lake/build`."""
    parts = Path(rel).parts
    end = 1 if parts[0] == "build" else parts.index("build") + 1
    return Path(".lake", *parts[:end])


def unpack(lean, jobs, tmp, batch, tool, stream, logs=False, empty_private=False):
    """With `empty_private`, as `restore`'s: it needs a leantar with
    `--empty-private` (`ci/leantar_release.py`, its default then)."""
    if tool is None:
        tool = str(leantar_release.fetch()) if empty_private else str(leantar(lean))
    stage = Path(tempfile.mkdtemp(prefix="lean-cache-", dir=tmp))
    # Another restore's archives would not be this build's.
    shutil.rmtree(lean / KEPT, ignore_errors=True)
    running = []
    count = 0

    def wait():
        for proc in running:
            if proc.wait():
                raise SystemExit(f"leantar failed ({proc.returncode})")

    def start(records):
        procs = []
        for empty in (False, True):
            part = [r for r, e in records if e == empty]
            if not part:
                continue
            # `-f`: a trace already there (from a build of other sources) would
            # otherwise keep that build's outputs.
            proc = subprocess.Popen([tool, "-f", "--jobs", str(jobs), "-x"] +
                                    (["--empty-private"] if empty else []) + ["-j", "-"],
                                    cwd=lean, stdin=subprocess.PIPE)
            proc.stdin.write(json.dumps(part).encode())
            proc.stdin.close()
            procs.append(proc)
        return procs

    files = None
    try:
        # The archives go to the staging directory, a batch at a time, and
        # `leantar` unpacks each batch while the next arrives; `files.tar`
        # goes there too, for `tar`.
        records, size, n = [], 0, 0
        with tarfile.open(fileobj=stream, mode="r|") as tar:
            for member in tar:
                rel = Path(member.name)
                if rel.parts[:2] != LTAR.parts:
                    raise ValueError(f"Unexpected cache entry: {member.name}")
                if rel == LTAR / FILES and member.isfile() and files is None:
                    with open(stage / FILES, "wb") as f:
                        shutil.copyfileobj(tar.extractfile(member), f)
                    files = extract(lean, stage / FILES)
                    continue
                if rel == LTAR / LOGS and member.isfile():
                    if logs:
                        (lean / LTAR).mkdir(parents=True, exist_ok=True)
                        with open(lean / LTAR / LOGS, "wb") as f:
                            shutil.copyfileobj(tar.extractfile(member), f)
                    continue
                if not member.isfile() or rel.suffix != ".ltar":
                    continue  # the index, and directories
                n += 1
                m = module_of(rel.relative_to(LTAR))
                file = stage / str(n)
                if empty_private and m is not None:
                    # Kept, for `fill_private`.
                    file = lean / KEPT / rel.relative_to(LTAR)
                    file.parent.mkdir(parents=True, exist_ok=True)
                with open(file, "wb") as f:
                    shutil.copyfileobj(tar.extractfile(member), f)
                build = build_of(rel.relative_to(LTAR))
                placeholder(lean, rel.relative_to(LTAR))
                records.append(({"file": str(file), "base": [str(build / "lib/lean"), str(build / "ir")]},
                                empty_private and m is not None and not m.startswith(KEEP_PRIVATE)))
                size += member.size
                if size >= batch:
                    wait()
                    running = start(records)
                    count += len(records)
                    records, size = [], 0
        wait()
        running = []
        if records:
            running = start(records)
            count += len(records)
            wait()
    finally:
        for proc in running:
            proc.wait()
        try:
            finish(files)
        finally:
            shutil.rmtree(stage)
    print(f"Unpacked {count} modules", file=sys.stderr)


def tmp_dir():
    """Memory, when there is a tmpfs, rather than the disk."""
    return "/dev/shm" if os.path.isdir("/dev/shm") else None


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("pack", help="write a tar of the directories to stdout")
    p.add_argument("lean", type=Path, help="the Lean project (lean/)")
    p.add_argument("roots", nargs="+", type=Path, help="directories to pack, relative to it")
    p.add_argument("--reuse", type=Path,
                   help="reuse matching module archives from this directory, relative to lean")
    b = sub.add_parser("bundle", help="combine existing module caches into a tar on stdout")
    b.add_argument("lean", type=Path, help="the Lean project (lean/)")
    b.add_argument("archive_dirs", nargs="+", type=Path, help="cache directories relative to it")
    st = sub.add_parser("store", help="update `.lake/ltar`, with a tar of the other files in it")
    st.add_argument("lean", type=Path, help="the Lean project (lean/)")
    st.add_argument("roots", nargs="+", type=Path, help="directories to store, relative to it")
    r = sub.add_parser("restore", help="restore what `store` stored, keeping `.lake/ltar`")
    r.add_argument("lean", type=Path, help="the Lean project (lean/)")
    r.add_argument("--leantar", default="leantar-batch",
                   help="the leantar to unpack with (default: leantar-batch)")
    only = r.add_mutually_exclusive_group()
    only.add_argument("--modules", type=Path,
                      help="a file of modules: unpack only their archives (and every package's)")
    only.add_argument("--except", dest="others", type=Path,
                      help="a file of modules: unpack only the other archives, without files.tar")
    r.add_argument("--empty-private", action="store_true",
                   help="write the modules' .olean.private as empty files, the trusted base's aside")
    fp = sub.add_parser("fill-private", help="write the private parts --empty-private left empty, "
                        "of modules and all they import")
    fp.add_argument("lean", type=Path, help="the Lean project (lean/)")
    fp.add_argument("modules", nargs="+",
                    help="module names, or files (`.lean`, e.g. a script `lake env lean` runs) whose imports")
    fp.add_argument("--leantar", help="the leantar to unpack with (default: the toolchain's)")
    u = sub.add_parser("unpack", help="extract a tar of `pack` from stdin")
    u.add_argument("lean", type=Path, help="the Lean project (lean/)")
    u.add_argument("--batch", type=int, default=256 << 20,
                   help="bytes of archives to stage before unpacking them (default: 256 MiB)")
    u.add_argument("--leantar", help="the leantar to unpack with (default: the toolchain's, or with "
                   "--empty-private the release ci/leantar_release.py downloads)")
    u.add_argument("--empty-private", action="store_true",
                   help="as restore's, keeping the project's archives for fill-private")
    u.add_argument("--logs", action="store_true",
                   help=f"also write the build's messages, with its profile, to {LTAR / LOGS} (`lean_profile.py`)")
    u.add_argument("--tmp", default=tmp_dir(),
                   help="where to stage the archives (default: /dev/shm, if there is one)")
    for q in (st, r):
        q.add_argument("--archive-dir", type=Path, default=LTAR,
                       help="archive directory relative to lean (default: .lake/ltar)")
    for q in (p, st):
        q.add_argument("--level", type=int, default=5, help="zstd level (default: 5)")
        q.add_argument("--leantar", default="leantar-batch",
                       help="a leantar with `-p` (default: leantar-batch)")
    for q in (p, st, r, u):
        q.add_argument("--jobs", type=int, default=os.cpu_count())
    args = parser.parse_args(argv)
    if args.command == "pack":
        pack(args.lean.resolve(), args.roots, args.jobs, args.level, args.leantar, sys.stdout.buffer, args.reuse)
    elif args.command == "bundle":
        bundle(args.lean.resolve(), args.archive_dirs, sys.stdout.buffer)
    elif args.command == "store":
        store(args.lean.resolve(), args.roots, args.jobs, args.level, args.leantar, args.archive_dir)
    elif args.command == "fill-private":
        fill_private(args.lean.resolve(), args.modules, args.leantar)
    elif args.command == "restore":
        restore(args.lean.resolve(), args.jobs, args.leantar, args.archive_dir, args.modules, args.others,
                args.empty_private)
    else:
        unpack(args.lean.resolve(), args.jobs, args.tmp, args.batch, args.leantar, sys.stdin.buffer,
               args.logs, args.empty_private)


if __name__ == "__main__":
    main()
