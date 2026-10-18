#!/usr/bin/env python3
"""Packs Lean builds into Lake's per-module archives, and restores them.

  python3 ci/lean_cache.py pack lean .lake/build .lake/packages | zstd -T0 -5 -o cache.tar.zst
  zstd -dc cache.tar.zst | python3 ci/lean_cache.py unpack lean

`pack` updates `.lake/ltar/`, which holds an `.ltar` archive of each built
module's outputs (its `.olean`, `.olean.server`, `.olean.private`, `.ilean`,
`.ir.sig`, `.ir`, `.c` and `.trace`) in the given directories (relative to
the Lean project, `lean/`): the format of Lake's `ltar` facet and Mathlib's
cache, a fifth of the size `zstd` makes of the same files, since `leantar`
encodes an `.olean`'s objects compactly before compressing them. A module's
archive is `.lake/ltar/<build>/<Module>.ltar`, where `<build>` is its build
directory relative to `.lake/` (`build`, or `packages/mathlib/.lake/build`).
`.lake/ltar/index.json` records the dependency hash and output hashes of
each archive's module: `pack` packs only the modules that changed since,
and removes the archives of modules that no longer exist. It then writes a
tar of `.lake/ltar` and of every other file in the directories (the
outputs' `.hash` files, native libraries, Lake's checkouts of the
dependencies) to stdout.

It packs with `leantar-batch` (`--leantar`), leantar with digama0/leangz#13
(`.github/actions/leantar`), which packs every module in one process at zstd
level `--level` (default 5); the toolchain's own `leantar` takes half a
CPU-second for each module.

`unpack` extracts such a tar from stdin into the Lean project. It writes
each file that is not an archive in its place, and passes the archives to
the toolchain's `leantar` in batches of `--batch` bytes, each unpacked while
the next arrives. The outputs come out byte for byte as they were packed;
the `.trace` keeps everything Lake reads (the dependency hash, the outputs'
hashes and the build's messages, with the profile `ci/lean_profile.py`
reads), without the record of the build's inputs that Lake writes only for
people to read.

It stages each batch in `--tmp` (default: `/dev/shm`, a tmpfs, when there
is one), so the archives never reach the disk, and removes them.
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

# A module's outputs in its build directory's `lib/lean` (base 0) and `ir`
# (base 1), in the order `leantar` wants them: the `.olean`'s parts first.
OUTPUTS = [(0, ".olean"), (0, ".olean.server"), (0, ".olean.private"), (0, ".ilean"),
           (0, ".ir.sig"), (0, ".ir"), (1, ".c")]
LTAR = Path(".lake/ltar")
# The key of each archive's module (`key`), by archive, so `pack` repacks only what changed.
INDEX = "index.json"


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
    """The built modules of `build`: their names, traces and outputs (paths relative to `lean`)."""
    lib = lean / build / "lib" / "lean"
    for trace in sorted(lib.glob("**/*.trace")):
        name = str(trace.relative_to(lib))[:-len(".trace")]
        if not (lib / (name + ".olean")).is_file():
            continue  # not a module (a native library's trace)
        outputs = [(base, ext, build / ("lib/lean", "ir")[base] / (name + ext)) for base, ext in OUTPUTS]
        yield name, trace, [o for o in outputs if (lean / o[2]).is_file()]


def key(trace):
    """What a module's archive holds: its dependency hash and its outputs' hashes."""
    t = json.loads(trace.read_text())
    return json.dumps([t["depHash"], t["outputs"]], sort_keys=True)


def pack(lean, roots, jobs, level, tool, out):
    ltars = lean / LTAR
    old = json.loads((ltars / INDEX).read_text()) if (ltars / INDEX).is_file() else {}
    builds = list(build_dirs(lean, roots))
    # Entries of builds not packed now stay.
    index = {rel: k for rel, k in old.items()
             if not any(build_of(rel) == build for build in builds)}
    packed = set()
    tasks = []
    kept = 0
    for build in builds:
        for name, trace, outputs in modules(lean, build):
            rel = str(build.relative_to(".lake") / name)
            ltar = LTAR / (rel + ".ltar")
            index[rel] = key(trace)
            # The outputs' `.hash` files stay: without them Lake would read
            # every output again to hash it.
            packed.add(trace.relative_to(lean))
            packed.update(path for _, _, path in outputs)
            if old.get(rel) == index[rel] and (lean / ltar).is_file():
                kept += 1
                continue
            (lean / ltar).parent.mkdir(parents=True, exist_ok=True)
            # Without `-s`, the archive keeps the trace's dependency hash, so
            # unpacking needs nothing but the archive.
            files = []
            for base, ext, _ in outputs:
                files += ["-i", str(base), name + ext]
            tasks.append({"out": str(ltar), "trace": name + ".trace", "files": files,
                          "base": [str(build / "lib/lean"), str(build / "ir")]})
    # Until the archives are packed, the index must not vouch for them.
    (ltars / INDEX).unlink(missing_ok=True)
    if tasks:
        subprocess.run([tool, "--jobs", str(jobs), "--level", str(level), "-p", "-"], cwd=lean,
                       input=json.dumps(tasks).encode(), check=True)
    # The archives of modules that no longer exist.
    removed = 0
    for ltar in sorted(ltars.rglob("*.ltar")):
        if str(ltar.relative_to(ltars))[:-len(".ltar")] not in index:
            ltar.unlink()
            removed += 1
    (ltars / INDEX).write_text(json.dumps(index, sort_keys=True))
    print(f"Packed {len(tasks)} modules, kept {kept}, removed {removed}", file=sys.stderr)
    paths = []
    for root in roots:
        for dirpath, dirnames, filenames in os.walk(lean / root):
            dirnames.sort()
            rel = Path(dirpath).relative_to(lean)
            paths.append(str(rel))
            paths += [str(rel / f) for f in sorted(filenames) if rel / f not in packed]
            # Symbolic links to directories are entries, not walked.
            paths += [str(rel / d) for d in dirnames if (lean / rel / d).is_symlink()]
    out.flush()
    # The archives (all of `.lake/ltar`) first, then everything else.
    subprocess.run(["tar", "-C", str(lean), "-cf", "-", str(LTAR), "--no-recursion", "--null", "-T", "-"],
                   input="\0".join(paths).encode(), stdout=out, check=True)


def build_of(rel):
    """The build directory (relative to the Lean project) of an archive at
    `.lake/ltar/<rel>`: `<rel>` starts with `build`, or with a package's
    `packages/<name>/.lake/build`."""
    parts = Path(rel).parts
    end = 1 if parts[0] == "build" else parts.index("build") + 1
    return Path(".lake", *parts[:end])


def unpack(lean, jobs, tmp, batch, tool, stream):
    tool = tool or str(leantar(lean))
    stage = Path(tempfile.mkdtemp(prefix="lean-cache-", dir=tmp))
    running = None
    count = 0

    def wait():
        if running is not None and running.wait():
            raise SystemExit(f"leantar failed ({running.returncode})")

    def start(records):
        # `-f`: a trace already there (from a build of other sources) would
        # otherwise keep that build's outputs.
        proc = subprocess.Popen([tool, "-f", "--jobs", str(jobs), "-x", "-j", "-"], cwd=lean,
                                stdin=subprocess.PIPE)
        proc.stdin.write(json.dumps(records).encode())
        proc.stdin.close()
        return proc

    try:
        # The archives go to the staging directory, a batch at a time, and
        # `leantar` unpacks each batch while the next arrives; every other
        # file goes where it belongs.
        records, size, n = [], 0, 0
        with tarfile.open(fileobj=stream, mode="r|") as tar:
            for member in tar:
                rel = Path(member.name)
                if rel.parts[:2] != LTAR.parts:
                    tar.extract(member, lean, set_attrs=True, filter=without_owner)
                    continue
                if not member.isfile() or rel.suffix != ".ltar":
                    continue  # the index, and directories
                n += 1
                file = stage / str(n)
                with open(file, "wb") as f:
                    shutil.copyfileobj(tar.extractfile(member), f)
                build = build_of(rel.relative_to(LTAR))
                records.append({"file": str(file), "base": [str(build / "lib/lean"), str(build / "ir")]})
                size += member.size
                if size >= batch:
                    wait()
                    running = start(records)
                    count += len(records)
                    records, size = [], 0
        wait()
        running = None
        if records:
            running = start(records)
            count += len(records)
            wait()
    finally:
        if running is not None:
            running.wait()
        shutil.rmtree(stage)
    print(f"Unpacked {count} modules", file=sys.stderr)


def without_owner(member, path):
    """`tar --no-same-owner`: CI's runner user owns the archive's files, and
    extracting them as root (as in a container) would keep that owner. Git
    would then refuse the dependencies' checkouts, so Lake would clone them
    again and build Mathlib from source."""
    return tarfile.tar_filter(member, path).replace(uid=None, gid=None, uname=None, gname=None)


def tmp_dir():
    """Memory, when there is a tmpfs, rather than the disk."""
    return "/dev/shm" if os.path.isdir("/dev/shm") else None


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("pack", help="write a tar of the directories to stdout")
    p.add_argument("lean", type=Path, help="the Lean project (lean/)")
    p.add_argument("roots", nargs="+", type=Path, help="directories to pack, relative to it")
    p.add_argument("--level", type=int, default=5, help="zstd level (default: 5)")
    p.add_argument("--leantar", default="leantar-batch", help="a leantar with `-p` (default: leantar-batch)")
    u = sub.add_parser("unpack", help="extract a tar of `pack` from stdin")
    u.add_argument("lean", type=Path, help="the Lean project (lean/)")
    u.add_argument("--batch", type=int, default=256 << 20,
                   help="bytes of archives to stage before unpacking them (default: 256 MiB)")
    u.add_argument("--leantar", help="the leantar to unpack with (default: the toolchain's)")
    u.add_argument("--tmp", default=tmp_dir(),
                   help="where to stage the archives (default: /dev/shm, if there is one)")
    for q in (p, u):
        q.add_argument("--jobs", type=int, default=os.cpu_count())
    args = parser.parse_args(argv)
    if args.command == "pack":
        pack(args.lean.resolve(), args.roots, args.jobs, args.level, args.leantar, sys.stdout.buffer)
    else:
        unpack(args.lean.resolve(), args.jobs, args.tmp, args.batch, args.leantar, sys.stdin.buffer)


if __name__ == "__main__":
    main()
