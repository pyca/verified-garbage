"""Pack a fake Lean build into module archives and restore it, with a stub leantar."""

import gzip
import io
import json
import os
import shutil
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest import mock

import lean_cache

# A stand-in for leantar: `-p -` writes each job's files, by base, into its
# `out` as JSON (and logs the job); `-x -j -` writes them back under each
# record's bases, with `--empty-private` each `.olean.private` empty.
STUB = r'''#!/usr/bin/env python3
import json, os, sys
args = sys.argv[1:]
records = json.load(sys.stdin)
if "-p" in args:
    with open(os.environ["STUB_LOG"], "a") as log:
        for job in records:
            log.write(job["out"] + "\n")
            names, it = [(0, job["trace"])], iter(job["files"])
            for arg in it:
                if arg == "-i":
                    names.append((int(next(it)), next(it)))
            out = {}
            for base, name in names:
                with open(os.path.join(job["base"][base], name)) as f:
                    out[f"{base}/{name}"] = f.read()
            with open(job["out"], "w") as f:
                json.dump(out, f)
else:
    for record in records:
        with open(record["file"]) as f:
            files = json.load(f)
        for key, text in files.items():
            base, name = key.split("/", 1)
            if "--empty-private" in args and name.endswith(".olean.private"):
                text = ""
            path = os.path.join(record["base"][int(base)], name)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w") as f:
                f.write(text)
'''


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def module(build, name, dep="1", body="x", log=None):
    """A built module of `build`: its outputs, their `.hash` files and its
    trace, with the messages `log` if given."""
    lib = build / "lib/lean"
    for ext in (".olean", ".olean.server", ".olean.private", ".ilean", ".ir.sig", ".ir"):
        write(lib / (name + ext), f"{name}{ext} {body}")
        write(lib / (name + ext + ".hash"), "0")
    write(build / "ir" / (name + ".c"), f"{name}.c {body}")
    write(build / "ir" / (name + ".c.hash"), "0")
    trace = {"depHash": dep, "outputs": {"o": body}}
    if log is not None:
        trace["log"] = log
    write(lib / (name + ".trace"), json.dumps(trace))


def compile_c(build, name):
    """Marks `name`'s C as compiled, as Lake leaves its object."""
    write(build / "ir" / (name + ".c.o.export"), "object")
    write(build / "ir" / (name + ".c.o.export.hash"), "0")


def as_restored(files):
    """A tree of files (path to bytes) as unpacking it gives it: the `.c` of
    a module the build did not compile is empty."""
    return {path: b"" if path.suffix == ".c" and path.with_name(path.name + ".o.export") not in files
            else data for path, data in files.items()}


class LeanArchiveTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.lean = self.root / "lean"
        self.stub = self.root / "leantar"
        self.stub.write_text(STUB)
        self.stub.chmod(0o755)
        self.log = self.root / "log"
        os.environ["STUB_LOG"] = str(self.log)
        build = self.lean / ".lake/build"
        module(build, "A/B")
        module(build, "C")
        compile_c(build, "C")
        write(build / "lib/libNative.so", "native")
        write(build / "lib/lean/libNative.so.trace", "{}")  # not a module
        mathlib = self.lean / ".lake/packages/mathlib"
        write(mathlib / "Mathlib.lean", "source")
        write(mathlib / "scripts/run.sh", "#!/bin/sh\n")
        (mathlib / "scripts/run.sh").chmod(0o755)
        module(mathlib / ".lake/build", "Mathlib/Order")

    def pack(self):
        self.log.write_text("")
        with tempfile.TemporaryFile() as f:  # tar writes to a real file
            lean_cache.pack(self.lean, [Path(".lake/build"), Path(".lake/packages")], 2, 5,
                            str(self.stub), f)
            f.seek(0)
            data = f.read()
        return data, self.log.read_text().split()

    def test_pack_and_unpack(self):
        data, packed = self.pack()
        self.assertEqual(len(packed), 3)
        ltar = self.lean / ".lake/ltar"
        self.assertEqual(sorted(str(p.relative_to(ltar)) for p in ltar.rglob("*.ltar")),
                         ["build/A/B.ltar", "build/C.ltar",
                          "packages/mathlib/.lake/build/Mathlib/Order.ltar"])
        self.check_unpack(data)

    def test_unpack_rejects_entries_outside_archive_directory(self):
        data = io.BytesIO()
        with tarfile.open(fileobj=data, mode="w") as tar:
            tar.addfile(tarfile.TarInfo(".lake/build"))
        data.seek(0)
        target = self.root / "restored"
        target.mkdir()
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaisesRegex(ValueError, "Unexpected cache entry: .lake/build"):
                lean_cache.unpack(target, 2, tmp, 1, str(self.stub), data)
            self.assertEqual(os.listdir(tmp), [])
        self.assertEqual(os.listdir(target), [])

    def check_unpack(self, data):
        target = self.root / "restored"
        target.mkdir()
        with tempfile.TemporaryDirectory() as tmp:
            # A tiny batch: one leantar run per archive.
            lean_cache.unpack(target, 2, tmp, 1, str(self.stub), io.BytesIO(data))
            self.assertEqual(os.listdir(tmp), [])
        original = {p.relative_to(self.lean): p.read_bytes()
                    for p in (self.lean / ".lake").rglob("*") if p.is_file()
                    and ".lake/ltar" not in str(p)}
        restored = {p.relative_to(target): p.read_bytes()
                    for p in (target / ".lake").rglob("*") if p.is_file()}
        self.assertEqual(restored, as_restored(original))
        self.assertTrue(os.access(target / ".lake/packages/mathlib/scripts/run.sh", os.X_OK))

    def test_the_build_messages_leave_the_traces(self):
        build = self.lean / ".lake/build"
        log = [{"level": "info", "message": "A/B.lean:1:0: simp took 2ms"}]
        module(build, "A/B", log=log)
        data, packed = self.pack()
        self.assertEqual(len(packed), 3)
        # The archive's trace is just its hashes; the messages are in `logs.json.gz`.
        trace = build / "lib/lean/A/B.trace"
        self.assertEqual(json.loads(trace.read_text()), {"depHash": "1", "outputs": {"o": "x"}})
        logs = {"build/A/B": {"depHash": "1", "log": log}}
        self.assertEqual(lean_cache.read_logs(self.lean / ".lake/ltar/logs.json.gz"), logs)
        for keep in (False, True):
            target = self.root / f"restored-{keep}"
            target.mkdir()
            with tempfile.TemporaryDirectory() as tmp:
                lean_cache.unpack(target, 2, tmp, 1, str(self.stub), io.BytesIO(data), keep)
            self.assertEqual((target / ".lake/build/lib/lean/A/B.trace").read_bytes(), trace.read_bytes())
            written = target / ".lake/ltar/logs.json.gz"
            self.assertEqual(lean_cache.read_logs(written) if keep else None,
                             logs if keep else None)
            self.assertEqual(written.exists(), keep)
        # Unchanged, a module keeps its messages, from `logs.json.gz`.
        _, packed = self.pack()
        self.assertEqual(packed, [])
        self.assertEqual(lean_cache.read_logs(self.lean / ".lake/ltar/logs.json.gz"), logs)
        # Rebuilt (here without messages), it drops the old build's.
        module(build, "A/B", dep="2")
        _, packed = self.pack()
        self.assertEqual(packed, [".lake/ltar/build/A/B.ltar"])
        self.assertEqual(lean_cache.read_logs(self.lean / ".lake/ltar/logs.json.gz"), {})

    def test_archives_from_before_logs_are_packed_again(self):
        self.pack()
        (self.lean / ".lake/ltar/logs.json.gz").unlink()
        _, packed = self.pack()
        self.assertEqual(len(packed), 3)

    def test_bundle_merges_the_logs(self):
        log = [{"level": "info", "message": "x took 1ms"}]
        module(self.lean / ".lake/build", "A/B", log=log)
        module(self.lean / ".lake/packages/mathlib/.lake/build", "Mathlib/Order", log=log)
        directories = self.independent_caches()
        out = io.BytesIO()
        lean_cache.bundle(self.lean, directories, out)
        with tarfile.open(fileobj=io.BytesIO(out.getvalue())) as tar:
            self.assertEqual(json.loads(gzip.decompress(tar.extractfile(".lake/ltar/logs.json.gz").read())),
                             {"build/A/B": {"depHash": "1", "log": log},
                              "packages/mathlib/.lake/build/Mathlib/Order": {"depHash": "1", "log": log}})

    def test_unpack_fails_when_tar_does(self):
        data, _ = self.pack()
        target = self.root / "restored"
        # `tar` cannot write a file where a directory (not empty) is.
        write(target / ".lake/packages/mathlib/Mathlib.lean/file", "")
        with tempfile.TemporaryDirectory() as tmp, self.assertRaisesRegex(SystemExit, "tar failed"):
            lean_cache.unpack(target, 2, tmp, 1, str(self.stub), io.BytesIO(data))

    def test_pack_repacks_only_what_changed(self):
        self.pack()
        build = self.lean / ".lake/build"
        module(build, "C", dep="2", body="y")
        for ext in (".olean", ".olean.server", ".olean.private", ".ilean", ".ir.sig", ".ir", ".trace"):
            (build / "lib/lean" / ("A/B" + ext)).unlink()
        _, packed = self.pack()
        self.assertEqual([Path(p).name for p in packed], ["C.ltar"])
        ltar = self.lean / ".lake/ltar"
        self.assertFalse((ltar / "build/A/B.ltar").exists())
        index = json.loads((ltar / "index.json").read_text())
        self.assertEqual(sorted(index), ["build/C", "packages/mathlib/.lake/build/Mathlib/Order"])

    def test_pack_of_one_build_keeps_the_others(self):
        self.pack()
        self.log.write_text("")
        with tempfile.TemporaryFile() as f:
            lean_cache.pack(self.lean, [Path(".lake/build")], 2, 5, str(self.stub), f)
        index = json.loads((self.lean / ".lake/ltar/index.json").read_text())
        self.assertIn("packages/mathlib/.lake/build/Mathlib/Order", index)
        self.assertTrue((self.lean / ".lake/ltar/packages/mathlib/.lake/build/Mathlib/Order.ltar").exists())
        self.assertEqual(self.log.read_text(), "")

    def test_store_and_restore(self):
        lean_cache.store(self.lean, [Path(".lake/build")], 2, 5, str(self.stub))
        ltar = self.lean / ".lake/ltar"
        self.assertTrue((ltar / "files.tar.gz").is_file())
        with gzip.open(ltar / "files.tar.gz") as f:
            self.assertIn(".lake/build/lib/libNative.so", tarfile.open(fileobj=f).getnames())
        original = {p.relative_to(self.lean): p.read_bytes()
                    for p in (self.lean / ".lake/build").rglob("*") if p.is_file()}
        # Restored where only `.lake/ltar` was kept, as from the Actions cache.
        target = self.root / "restored"
        (target / ".lake").mkdir(parents=True)
        ltar.rename(target / ".lake/ltar")
        lean_cache.restore(target, 2, str(self.stub))
        restored = {p.relative_to(target): p.read_bytes()
                    for p in (target / ".lake/build").rglob("*") if p.is_file()}
        self.assertEqual(restored, as_restored(original))
        # The archives stay, so the next store packs nothing.
        self.log.write_text("")
        lean_cache.store(target, [Path(".lake/build")], 2, 5, str(self.stub))
        self.assertEqual(self.log.read_text(), "")

    def test_restore_empty_private(self):
        build = self.lean / ".lake/build"
        module(build, "VerifiedGarbage/TCB/Mem")
        lean_cache.store(self.lean, [Path(".lake/build")], 2, 5, str(self.stub))
        original = {p.relative_to(self.lean): p.read_bytes()
                    for p in (self.lean / ".lake/build").rglob("*") if p.is_file()}
        target = self.root / "restored"
        (target / ".lake").mkdir(parents=True)
        (self.lean / ".lake/ltar").rename(target / ".lake/ltar")
        lean_cache.restore(target, 2, str(self.stub), empty_private=True)
        restored = {p.relative_to(target): p.read_bytes()
                    for p in (target / ".lake/build").rglob("*") if p.is_file()}
        expected = as_restored(original)
        for path in expected:
            if path.name.endswith(".olean.private") and "TCB" not in path.parts:
                expected[path] = b""
        self.assertEqual(restored, expected)
        # The trusted base's private data is real; the others' are placeholders.
        lib = Path(".lake/build/lib/lean")
        self.assertNotEqual(restored[lib / "VerifiedGarbage/TCB/Mem.olean.private"], b"")
        self.assertEqual(restored[lib / "A/B.olean.private"], b"")
        # Nothing changed: the next store packs nothing.
        self.log.write_text("")
        lean_cache.store(target, [Path(".lake/build")], 2, 5, str(self.stub))
        self.assertEqual(self.log.read_text(), "")
        # A module rebuilt but for its placeholder: never packed.
        trace = target / lib / "A/B.trace"
        trace.write_text(trace.read_text().replace('"1"', '"2"'))
        with self.assertRaisesRegex(SystemExit, "placeholder"):
            lean_cache.store(target, [Path(".lake/build")], 2, 5, str(self.stub))

    def test_restore_some_modules_then_the_others(self):
        lean_cache.store(self.lean, [Path(".lake/build")], 2, 5, str(self.stub))
        original = {p.relative_to(self.lean): p.read_bytes()
                    for p in (self.lean / ".lake/build").rglob("*") if p.is_file()}
        target = self.root / "restored"
        (target / ".lake").mkdir(parents=True)
        (self.lean / ".lake/ltar").rename(target / ".lake/ltar")
        chosen = self.root / "modules"
        chosen.write_text("A.B\n")
        lean_cache.restore(target, 2, str(self.stub), modules=chosen)
        lib = target / ".lake/build/lib/lean"
        self.assertTrue((lib / "A/B.olean").is_file())
        self.assertFalse((lib / "C.olean").exists())
        # `files.tar`: every `.hash` file, and the files of no module.
        self.assertTrue((lib / "C.olean.hash").is_file())
        self.assertTrue((target / ".lake/build/lib/libNative.so").is_file())
        # A build in between rewrites A/B's outputs; the others leave them.
        (lib / "A/B.olean").write_text("rebuilt")
        (lib / "A/B.olean.hash").write_text("1")
        lean_cache.restore(target, 2, str(self.stub), others=chosen)
        restored = {p.relative_to(target): p.read_bytes()
                    for p in (target / ".lake/build").rglob("*") if p.is_file()}
        expected = as_restored(original)
        expected[Path(".lake/build/lib/lean/A/B.olean")] = b"rebuilt"
        expected[Path(".lake/build/lib/lean/A/B.olean.hash")] = b"1"
        self.assertEqual(restored, expected)

    def test_module_of(self):
        self.assertEqual(lean_cache.module_of(Path("build/A/B.ltar")), "A.B")
        self.assertIsNone(lean_cache.module_of(Path("packages/mathlib/.lake/build/Mathlib/Order.ltar")))

    def test_independent_package_cache_and_publication(self):
        packages = Path(".lake/mathlib-ltar")
        lean_cache.store(self.lean, [Path(".lake/build")], 2, 5, str(self.stub))
        project = self.lean / lean_cache.LTAR
        before = {p.relative_to(project): p.read_bytes() for p in project.rglob("*") if p.is_file()}
        lean_cache.main(["store", str(self.lean), ".lake/packages", "--archive-dir", str(packages),
                         "--leantar", str(self.stub), "--jobs", "2"])
        self.assertEqual(before, {p.relative_to(project): p.read_bytes()
                                  for p in project.rglob("*") if p.is_file()})
        # Restore the independent caches into an otherwise empty project.
        target = self.root / "restored-caches"
        shutil.copytree(self.lean / ".lake/ltar", target / ".lake/ltar")
        shutil.copytree(self.lean / packages, target / packages)
        lean_cache.restore(target, 2, str(self.stub))
        lean_cache.main(["restore", str(target), "--archive-dir", str(packages),
                         "--leantar", str(self.stub), "--jobs", "2"])
        self.assertEqual((target / ".lake/build/lib/lean/C.olean").read_bytes(),
                         (self.lean / ".lake/build/lib/lean/C.olean").read_bytes())
        self.assertEqual((target / ".lake/packages/mathlib/Mathlib.lean").read_text(), "source")
        self.assertTrue(os.access(target / ".lake/packages/mathlib/scripts/run.sh", os.X_OK))
        # The publisher reuses both caches, regenerates files.tar for both
        # roots, and leaves the independently saved Mathlib cache untouched.
        package_before = {p.relative_to(self.lean / packages): p.read_bytes()
                          for p in (self.lean / packages).rglob("*") if p.is_file()}
        self.log.write_text("")
        with tempfile.TemporaryFile() as f:
            lean_cache.pack(self.lean, [Path(".lake/build"), Path(".lake/packages")],
                            2, 5, str(self.stub), f, reuse=packages)
            f.seek(0)
            data = f.read()
        self.assertEqual(self.log.read_text(), "")
        self.assertEqual(package_before, {p.relative_to(self.lean / packages): p.read_bytes()
                                         for p in (self.lean / packages).rglob("*") if p.is_file()})
        # Exclude the independent cache from check_unpack's original tree.
        shutil.rmtree(self.lean / packages)
        self.check_unpack(data)

    def independent_caches(self):
        directories = [lean_cache.LTAR, Path(".lake/mathlib-ltar")]
        for root, directory in zip((".lake/build", ".lake/packages"), directories):
            lean_cache.store(self.lean, [Path(root)], 2, 5, str(self.stub), directory)
        return directories

    def test_bundle_without_expanded_build_or_toolchain(self):
        directories = self.independent_caches()
        # Record the expected expanded build, then keep only the two caches.
        expected = {p.relative_to(self.lean): p.read_bytes()
                    for root in (".lake/build", ".lake/packages")
                    for p in (self.lean / root).rglob("*") if p.is_file()}
        shutil.rmtree(self.lean / ".lake/build")
        shutil.rmtree(self.lean / ".lake/packages")
        # Unindexed stale archives and private metadata must not be published.
        write(self.lean / directories[0] / "build/Stale.ltar", "stale")
        write(self.lean / directories[0] / "mathlib-cache-key", "dependency-key")
        before = {p.relative_to(self.lean): p.read_bytes()
                  for p in self.lean.rglob("*") if p.is_file()}
        self.log.write_text("")
        result = subprocess.run([sys.executable, lean_cache.__file__, "bundle", str(self.lean),
                                 *map(str, directories)], capture_output=True, check=True)
        data = io.BytesIO(result.stdout)
        self.assertIn(b"Bundled 3 modules", result.stderr)
        self.assertEqual(self.log.read_text(), "")
        self.assertEqual(before, {p.relative_to(self.lean): p.read_bytes()
                                  for p in self.lean.rglob("*") if p.is_file()})
        with tarfile.open(fileobj=io.BytesIO(data.getvalue())) as tar:
            self.assertEqual(tar.getnames()[0], ".lake/ltar/files.tar")
            self.assertEqual(len(tar.getnames()), 6)  # files, index, logs, three modules
            index = json.load(tar.extractfile(".lake/ltar/index.json"))
            self.assertEqual(len(index), 3)
            for rel in index:
                original = next(self.lean / d / (rel + ".ltar") for d in directories
                                if (self.lean / d / (rel + ".ltar")).is_file())
                self.assertEqual(tar.extractfile(f".lake/ltar/{rel}.ltar").read(), original.read_bytes())
        target = self.root / "bundled-restore"
        target.mkdir()
        lean_cache.unpack(target, 2, str(self.root), 1, str(self.stub), io.BytesIO(data.getvalue()))
        self.assertEqual(as_restored(expected), {p.relative_to(target): p.read_bytes()
                                                 for p in target.rglob("*") if p.is_file()})
        self.assertTrue(os.access(target / ".lake/packages/mathlib/scripts/run.sh", os.X_OK))
        # The merged index also supports keeping and restoring the caches.
        cached = self.root / "bundled-cache"
        cached.mkdir()
        subprocess.run(["tar", "-xf", "-", "-C", str(cached)], input=data.getvalue(), check=True)
        lean_cache.restore(cached, 2, str(self.stub))
        self.log.write_text("")
        lean_cache.store(cached, [Path(".lake/build"), Path(".lake/packages")], 2, 5, str(self.stub))
        self.assertEqual(self.log.read_text(), "")

    def test_bundle_rejects_incomplete_or_overlapping_caches_before_output(self):
        directories = self.independent_caches()
        for missing in ("index.json", "files.tar.gz", "build/C.ltar"):
            path = self.lean / directories[0] / missing
            saved = path.read_bytes()
            path.unlink()
            data = io.BytesIO()
            with self.subTest(missing=missing), self.assertRaises(FileNotFoundError):
                lean_cache.bundle(self.lean, directories, data)
            self.assertEqual(data.getvalue(), b"")
            path.write_bytes(saved)
        data = io.BytesIO()
        with self.assertRaisesRegex(ValueError, "Overlapping"):
            lean_cache.bundle(self.lean, [directories[0], directories[0]], data)
        self.assertEqual(data.getvalue(), b"")
        (self.lean / directories[0] / "index.json").write_text("{}")
        with self.assertRaisesRegex(ValueError, "Empty"):
            lean_cache.bundle(self.lean, directories, data)

    def test_bundle_copies_compressed_and_plain_tar_members_without_external_tar(self):
        directories = self.independent_caches()
        first, second = self.lean / directories[0], self.lean / directories[1]
        # Include metadata, links, empty files and a PAX long name. Keep
        # duplicate names in source order, as tar concatenation does.
        members = []
        for name, kind, body in [('directory', tarfile.DIRTYPE, b''),
                                 ('directory/script', tarfile.REGTYPE, b'#!/bin/sh\n'),
                                 ('symlink', tarfile.SYMTYPE, b''),
                                 ('hardlink', tarfile.LNKTYPE, b''),
                                 ('empty', tarfile.REGTYPE, b''),
                                 ('long/' + 'x' * 150, tarfile.REGTYPE, b'long'),
                                 ('directory/script', tarfile.REGTYPE, b'last')]:
            member = tarfile.TarInfo(name)
            member.type, member.size = kind, len(body)
            member.mode, member.uid, member.gid, member.mtime = 0o755, 123, 456, 123456
            member.uname, member.gname = 'owner', 'group'
            if kind in (tarfile.SYMTYPE, tarfile.LNKTYPE):
                member.linkname = 'directory/script'
            members.append((member, body))
        with tarfile.open(first / lean_cache.STORED, 'w:gz') as tar:
            for member, body in members[:-1]:
                tar.addfile(member, io.BytesIO(body))
        (second / lean_cache.STORED).unlink()
        with tarfile.open(second / lean_cache.FILES, 'w') as tar:
            member, body = members[-1]
            tar.addfile(member, io.BytesIO(body))
        data = io.BytesIO()
        with mock.patch.object(lean_cache.subprocess, 'run', side_effect=AssertionError('external tool')):
            lean_cache.bundle(self.lean, directories, data)
        with tarfile.open(fileobj=io.BytesIO(data.getvalue())) as outer:
            with tarfile.open(fileobj=outer.extractfile('.lake/ltar/files.tar')) as combined:
                actual = combined.getmembers()
                self.assertEqual(len(actual), len(members))
                for got, (want, body) in zip(actual, members):
                    for field in ('name', 'type', 'size', 'mode', 'uid', 'gid', 'mtime',
                                  'uname', 'gname', 'linkname'):
                        self.assertEqual(getattr(got, field), getattr(want, field))
                    if got.isfile():
                        self.assertEqual(combined.extractfile(got).read(), body)

    def test_reuse_repacks_missing_or_changed_archives(self):
        packages = Path(".lake/mathlib-ltar")
        lean_cache.store(self.lean, [Path(".lake/packages")], 2, 5, str(self.stub), packages)
        archive = self.lean / packages / "packages/mathlib/.lake/build/Mathlib/Order.ltar"
        archive.unlink()
        self.log.write_text("")
        lean_cache.update(self.lean, [Path(".lake/packages")], 2, 5, str(self.stub), reuse=packages)
        self.assertEqual(len(self.log.read_text().splitlines()), 1)
        shutil.rmtree(self.lean / lean_cache.LTAR)
        lean_cache.store(self.lean, [Path(".lake/packages")], 2, 5, str(self.stub), packages)
        module(self.lean / ".lake/packages/mathlib/.lake/build", "Mathlib/Order", dep="2", body="new")
        self.log.write_text("")
        lean_cache.update(self.lean, [Path(".lake/packages")], 2, 5, str(self.stub), reuse=packages)
        self.assertEqual(len(self.log.read_text().splitlines()), 1)
        # No Mathlib cache at all also packs normally.
        shutil.rmtree(self.lean / lean_cache.LTAR)
        shutil.rmtree(self.lean / packages)
        self.log.write_text("")
        lean_cache.update(self.lean, [Path(".lake/packages")], 2, 5, str(self.stub), reuse=packages)
        self.assertEqual(len(self.log.read_text().splitlines()), 1)

    def test_restore_fails_when_tar_does(self):
        lean_cache.store(self.lean, [Path(".lake/build")], 2, 5, str(self.stub))
        target = self.root / "restored"
        (target / ".lake").mkdir(parents=True)
        (self.lean / ".lake/ltar").rename(target / ".lake/ltar")
        # `tar` cannot write a file where a directory (not empty) is.
        write(target / ".lake/build/lib/libNative.so/file", "")
        with self.assertRaisesRegex(SystemExit, "tar failed"):
            lean_cache.restore(target, 2, str(self.stub))

    def test_restore_reads_an_uncompressed_files_tar_from_before(self):
        lean_cache.store(self.lean, [Path(".lake/build")], 2, 5, str(self.stub))
        ltar = self.lean / ".lake/ltar"
        with gzip.open(ltar / "files.tar.gz") as f, open(ltar / "files.tar", "wb") as g:
            shutil.copyfileobj(f, g)
        (ltar / "files.tar.gz").unlink()
        target = self.root / "restored"
        (target / ".lake").mkdir(parents=True)
        ltar.rename(target / ".lake/ltar")
        lean_cache.restore(target, 2, str(self.stub))
        self.assertTrue((target / ".lake/build/lib/libNative.so").is_file())
        # The next store replaces it with the compressed one.
        lean_cache.store(target, [Path(".lake/build")], 2, 5, str(self.stub))
        self.assertEqual(sorted(p.name for p in (target / ".lake/ltar").glob("files.*")), ["files.tar.gz"])

    def test_dependencies_executables_are_left_out(self):
        bin_dir = self.lean / ".lake/packages/mathlib/.lake/build/bin"
        write(bin_dir / "cache", "executable")
        write(bin_dir / "cache.trace", "{}")
        data, _ = self.pack()
        with tarfile.open(fileobj=io.BytesIO(data)) as tar:
            inner = tarfile.open(fileobj=tar.extractfile(".lake/ltar/files.tar")).getnames()
        self.assertFalse([name for name in inner if "/bin" in name])
        self.assertIn(".lake/packages/mathlib/Mathlib.lean", inner)

    def test_pack_writes_files_tar_first(self):
        lean_cache.store(self.lean, [Path(".lake/build")], 2, 5, str(self.stub))
        data, _ = self.pack()
        with tarfile.open(fileobj=io.BytesIO(data)) as tar:
            names = tar.getnames()
            inner = tarfile.open(fileobj=tar.extractfile(".lake/ltar/files.tar")).getnames()
        self.assertEqual(names[0], ".lake/ltar/files.tar")
        self.assertEqual(names.count(".lake/ltar/files.tar"), 1)
        self.assertIn(".lake/ltar/build/C.ltar", names)
        # Of both directories, replacing `store`'s, of the build alone.
        self.assertIn(".lake/packages/mathlib/Mathlib.lean", inner)
        self.assertIn(".lake/build/lib/libNative.so", inner)
        # Nothing but `.lake/ltar`.
        self.assertTrue(all(name.startswith(".lake/ltar") for name in names))

    def test_archives_hold_only_the_compiled_c(self):
        self.pack()
        ltar = self.lean / ".lake/ltar"
        for rel, has_c in (("build/A/B", False), ("build/C", True),
                           ("packages/mathlib/.lake/build/Mathlib/Order", False)):
            names = json.loads((ltar / (rel + ".ltar")).read_text())
            self.assertEqual(any(n.endswith(".c") for n in names), has_c, rel)
        with tarfile.open(ltar / "files.tar.gz") as tar:
            names = tar.getnames()
        # Nor in `files.tar.gz`, which keeps every `.c.hash` and the objects.
        self.assertNotIn(".lake/build/ir/A/B.c", names)
        self.assertIn(".lake/build/ir/A/B.c.hash", names)
        self.assertIn(".lake/build/ir/C.c.o.export", names)

    def test_compiling_a_module_packs_its_c_again(self):
        self.pack()
        compile_c(self.lean / ".lake/build", "A/B")
        _, packed = self.pack()
        self.assertEqual(packed, [".lake/ltar/build/A/B.ltar"])
        names = json.loads((self.lean / ".lake/ltar/build/A/B.ltar").read_text())
        self.assertIn("1/A/B.c", names)

    def test_unpacking_replaces_a_stale_c(self):
        data, _ = self.pack()
        target = self.root / "restored"
        write(target / ".lake/build/ir/A/B.c", "another build's C")
        write(target / ".lake/build/ir/C.c", "another build's C")
        with tempfile.TemporaryDirectory() as tmp:
            lean_cache.unpack(target, 2, tmp, 1, str(self.stub), io.BytesIO(data))
        self.assertEqual((target / ".lake/build/ir/A/B.c").read_bytes(), b"")
        self.assertEqual((target / ".lake/build/ir/C.c").read_text(), "C.c x")
        self.assertEqual((target / ".lake/packages/mathlib/.lake/build/ir/Mathlib/Order.c").read_bytes(), b"")

    def test_build_of(self):
        self.assertEqual(lean_cache.build_of("build/A/B"), Path(".lake/build"))
        self.assertEqual(lean_cache.build_of("packages/mathlib/.lake/build/Mathlib/Order"),
                         Path(".lake/packages/mathlib/.lake/build"))


if __name__ == "__main__":
    unittest.main()
