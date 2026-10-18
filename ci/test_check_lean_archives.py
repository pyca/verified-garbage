"""Pack a fake Lean build into module archives and restore it, with a stub leantar."""

import io
import json
import os
from pathlib import Path
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

    def test_build_of(self):
        self.assertEqual(lean_cache.build_of("build/A/B"), Path(".lake/build"))
        self.assertEqual(lean_cache.build_of("packages/mathlib/.lake/build/Mathlib/Order"),
                         Path(".lake/packages/mathlib/.lake/build"))


if __name__ == "__main__":
    unittest.main()
