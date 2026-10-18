"""Pack a fake Lean build into module archives and restore it, with a stub leantar."""

import io
import json
import os
from pathlib import Path
import subprocess
import tarfile
import tempfile
import unittest

import lean_cache

# A stand-in for leantar: `-p -` writes each job's files, by base, into its
# `out` as JSON (and logs the job); `-x -j -` writes them back under each
# record's bases.
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
            path = os.path.join(record["base"][int(base)], name)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w") as f:
                f.write(text)
'''


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def module(build, name, dep="1", body="x"):
    """A built module of `build`: its outputs, their `.hash` files and its trace."""
    lib = build / "lib/lean"
    for ext in (".olean", ".olean.server", ".olean.private", ".ilean", ".ir.sig", ".ir"):
        write(lib / (name + ext), f"{name}{ext} {body}")
        write(lib / (name + ext + ".hash"), "0")
    write(build / "ir" / (name + ".c"), f"{name}.c {body}")
    write(build / "ir" / (name + ".c.hash"), "0")
    write(lib / (name + ".trace"), json.dumps({"depHash": dep, "outputs": {"o": body}}))


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

    def test_unpack_reads_the_tar_before_files_tar(self):
        # `pack`'s tar before `files.tar` (`latest` in the registry): the
        # archives, then every other file as a member of its own.
        roots = [Path(".lake/build"), Path(".lake/packages")]
        packed = lean_cache.update(self.lean, roots, 2, 5, str(self.stub))
        paths = lean_cache.other_files(self.lean, roots, packed)
        data = subprocess.run(["tar", "-C", str(self.lean), "-cf", "-", ".lake/ltar",
                               "--no-recursion", "--null", "-T", "-"],
                              input="\0".join(paths).encode(), capture_output=True, check=True).stdout
        self.check_unpack(data)

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
        self.assertEqual(restored, original)
        self.assertTrue(os.access(target / ".lake/packages/mathlib/scripts/run.sh", os.X_OK))

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
        self.assertTrue((ltar / "files.tar").is_file())
        original = {p.relative_to(self.lean): p.read_bytes()
                    for p in (self.lean / ".lake/build").rglob("*") if p.is_file()}
        # Restored where only `.lake/ltar` was kept, as from the Actions cache.
        target = self.root / "restored"
        (target / ".lake").mkdir(parents=True)
        ltar.rename(target / ".lake/ltar")
        lean_cache.restore(target, 2, str(self.stub))
        restored = {p.relative_to(target): p.read_bytes()
                    for p in (target / ".lake/build").rglob("*") if p.is_file()}
        self.assertEqual(restored, original)
        # The archives stay, so the next store packs nothing.
        self.log.write_text("")
        lean_cache.store(target, [Path(".lake/build")], 2, 5, str(self.stub))
        self.assertEqual(self.log.read_text(), "")

    def test_restore_fails_when_tar_does(self):
        lean_cache.store(self.lean, [Path(".lake/build")], 2, 5, str(self.stub))
        target = self.root / "restored"
        (target / ".lake").mkdir(parents=True)
        (self.lean / ".lake/ltar").rename(target / ".lake/ltar")
        # `tar` cannot write a file where a directory (not empty) is.
        write(target / ".lake/build/lib/libNative.so/file", "")
        with self.assertRaisesRegex(SystemExit, "tar failed"):
            lean_cache.restore(target, 2, str(self.stub))

    def test_pack_writes_its_own_files_tar_first(self):
        lean_cache.store(self.lean, [Path(".lake/build")], 2, 5, str(self.stub))
        data, _ = self.pack()
        with tarfile.open(fileobj=io.BytesIO(data)) as tar:
            names = tar.getnames()
            inner = tarfile.open(fileobj=tar.extractfile(".lake/ltar/files.tar")).getnames()
        self.assertEqual(names[0], ".lake/ltar/files.tar")
        self.assertEqual(names.count(".lake/ltar/files.tar"), 1)
        self.assertIn(".lake/ltar/build/C.ltar", names)
        # `pack`'s, of both directories, not `store`'s, of the build alone.
        self.assertIn(".lake/packages/mathlib/Mathlib.lean", inner)
        self.assertIn(".lake/build/lib/libNative.so", inner)
        # Its files again after the archives, for an `unpack` from before it.
        ltars = [i for i, name in enumerate(names) if name.startswith(".lake/ltar/")]
        self.assertEqual(names[ltars[-1] + 1:], inner)

    def test_build_of(self):
        self.assertEqual(lean_cache.build_of("build/A/B"), Path(".lake/build"))
        self.assertEqual(lean_cache.build_of("packages/mathlib/.lake/build/Mathlib/Order"),
                         Path(".lake/packages/mathlib/.lake/build"))


if __name__ == "__main__":
    unittest.main()
