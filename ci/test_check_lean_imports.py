"""What `check_lean_imports.py` rejects in TCB/; no builds."""

import pathlib
import tempfile
import unittest

import check_lean_imports


def tree(files: dict) -> tempfile.TemporaryDirectory:
    d = tempfile.TemporaryDirectory()
    for rel, text in files.items():
        p = pathlib.Path(d.name) / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    return d


class TcbLemmas(unittest.TestCase):
    def test_definitions_only(self):
        # The words in comments and strings, and in other directories, are not lemmas.
        with tree({"lean/VerifiedGarbage/TCB/A.lean":
                   "module\n/-- Not a theorem. -/\ndef a : Nat := 1\n-- lemma\ndef s := \"theorem \"\n",
                   "lean/VerifiedGarbage/Proof/A.lean": "module\ntheorem t : True := trivial\n"}) as d:
            lean = pathlib.Path(d) / "lean" / "VerifiedGarbage"
            self.assertEqual(check_lean_imports.tcb_lemmas(lean), [])

    def test_a_lemma(self):
        with tree({"lean/VerifiedGarbage/TCB/X/Isa.lean":
                   "module\ndef a : Nat := 1\n\n@[simp] theorem a_eq : a = 1 := rfl\nprivate lemma b : True := trivial\n"}) as d:
            lean = pathlib.Path(d) / "lean" / "VerifiedGarbage"
            self.assertEqual(check_lean_imports.tcb_lemmas(lean), [
                "lean/VerifiedGarbage/TCB/X/Isa.lean:4: a theorem in TCB/, which holds definitions only; "
                "prove it under Proof/",
                "lean/VerifiedGarbage/TCB/X/Isa.lean:5: a lemma in TCB/, which holds definitions only; "
                "prove it under Proof/"])


class OtherLibraries(unittest.TestCase):
    def check(self, files):
        with tree(files) as d:
            lean = pathlib.Path(d) / "lean" / "VerifiedGarbage"
            texts = {f: f.read_text() for f in lean.rglob("*.lean")}
            return check_lean_imports.other_library_imports(lean, texts)

    def test_mentions_and_own_imports(self):
        # A name in a comment, and an import of the library's own modules, are fine.
        self.assertEqual(self.check({
            "lean/VerifiedGarbage/Proof/A.lean":
                "module\npublic import VerifiedGarbage.Spec.A\n"
                "import VerifiedGarbageTestHelpers.X\n/-! `VerifiedGarbageTest/A.lean` checks it. -/\n",
            "lean/VerifiedGarbageTest/A.lean": "module\nimport VerifiedGarbage.Proof.A\n"}), [])

    def test_imports_of_other_libraries(self):
        # From any directory, in any kind of import, and the library's root too.
        self.assertEqual(self.check({
            "lean/VerifiedGarbage/Proof/A.lean":
                "module\npublic import VerifiedGarbage.Spec.A\nimport VerifiedGarbageTest.Helper\n",
            "lean/VerifiedGarbage/Artifacts/A/X.lean": "module\npublic meta import all VerifiedGarbageTest\n",
            "lean/VerifiedGarbage/TCB/A.lean": "module\nimport VerifiedGarbageAuditBase\n"}), [
            "lean/VerifiedGarbage/Artifacts/A/X.lean:2: may not import VerifiedGarbageTest, a module of "
            "VerifiedGarbageTest: the emitter's audits do not read its records",
            "lean/VerifiedGarbage/Proof/A.lean:3: may not import VerifiedGarbageTest.Helper, a module of "
            "VerifiedGarbageTest: the emitter's audits do not read its records",
            "lean/VerifiedGarbage/TCB/A.lean:2: may not import VerifiedGarbageAuditBase, a module of "
            "VerifiedGarbageAuditBase: the emitter's audits do not read its records"])


class Plugins(unittest.TestCase):
    def test_every_library_but_the_exempt(self):
        plugin = {"plugins": [check_lean_imports.AUDIT_PLUGIN]}
        config = {"lean_lib": [{"name": "VerifiedGarbage", **plugin}, {"name": "NativeAuditRecords"},
                               {"name": "AuditBase"}, {"name": "NewTests"},
                               {"name": "Other", "plugins": ["Something:shared"]}]}
        self.assertEqual(check_lean_imports.plugin_problems(config), [
            f"lean/lakefile.toml: library {n} does not load the audit records' plugin: "
            f"give it `plugins = [\"{check_lean_imports.AUDIT_PLUGIN}\"]`, as every other library has "
            "(TCB/AuditRecords.lean would trust its modules unread)" for n in ("NewTests", "Other")])


class Imports(unittest.TestCase):
    def test_lines_and_kinds(self):
        text = ("module\n\npublic import A.B\n  meta import all C\npublic meta import D\n"
                "-- a comment: import E\ndef x := 1 -- import F\nimport\nG\n\timport H")
        self.assertEqual(list(check_lean_imports.imports(text)),
                         [(3, "A.B"), (4, "C"), (5, "D"), (10, "H")])


class NativeTcb(unittest.TestCase):
    # TCB.Mem (no target's), TCB.A.Isa and TCB.B.Isa (targets A and B), a
    # native spec importing TCB.Mem, and a proof of A.
    TCB = {"VG.TCB.Mem": None, "VG.TCB.A.Isa": "A", "VG.TCB.B.Isa": "B"}
    SPLIT = {"NativeTCB": frozenset({"VG.TCB.Mem"}), "NativeTCBA": frozenset({"VG.TCB.A.Isa"}),
             "NativeTCBB": frozenset({"VG.TCB.B.Isa"}), "NativeSpec": frozenset({"VG.Spec.X"})}
    NAMES = {"NativeTCBA": "VerifiedGarbage_NativeTCBA", "NativeTCBB": "VerifiedGarbage_NativeTCBB"}

    def check(self, libraries, traces, names=NAMES):
        return check_lean_imports.native_tcb(self.TCB, libraries, names, traces, {"A", "B"})

    def test_a_library_per_target(self):
        traces = {"VG.TCB.Mem": frozenset(), "VG.TCB.A.Isa": frozenset({"VG.TCB.Mem"}),
                  "VG.TCB.B.Isa": frozenset({"VG.TCB.Mem"}), "VG.Spec.X": frozenset({"VG.TCB.Mem"}),
                  "VG.Proof.A.P": frozenset({"VG.TCB.A.Isa", "VG.TCB.Mem"})}
        self.assertEqual(self.check(self.SPLIT, traces), [])

    def test_one_library(self):
        # The spec's native trace has the whole library: every target's ISA.
        libraries = {"NativeTCB": frozenset(self.TCB), "NativeSpec": frozenset({"VG.Spec.X"})}
        traces = {"VG.TCB.Mem": frozenset(), "VG.TCB.A.Isa": frozenset({"VG.TCB.Mem"}),
                  "VG.TCB.B.Isa": frozenset({"VG.TCB.Mem"}), "VG.Spec.X": frozenset(self.TCB),
                  "VG.Proof.B.P": frozenset(self.TCB)}
        self.assertEqual(self.check(libraries, traces), [
            "VG.TCB.A.Isa: in NativeTCB; it belongs in NativeTCBA (lean/lakefile.toml)",
            "VG.TCB.B.Isa: in NativeTCB; it belongs in NativeTCBB (lean/lakefile.toml)",
            "VG.Proof.B.P: of B, rebuilt by a change to A's TCB/",
            "VG.Spec.X: a module of NativeSpec, rebuilt by a change to A's TCB/ "
            "(imports from TCB/ only what no target owns)",
            "VG.Spec.X: a module of NativeSpec, rebuilt by a change to B's TCB/ "
            "(imports from TCB/ only what no target owns)"])

    def test_the_audit_records(self):
        # Their own library, not NativeTCB.
        tcb = dict(self.TCB, **{"VerifiedGarbage.TCB.AuditRecords": None})
        traces = {m: frozenset() for m in tcb}
        for lib, problem in (("NativeAuditRecords", []), ("NativeTCB", [
                "VerifiedGarbage.TCB.AuditRecords: in NativeTCB; it belongs in NativeAuditRecords "
                "(lean/lakefile.toml)"])):
            libraries = {k: set(v) for k, v in self.SPLIT.items()}
            libraries.setdefault(lib, set()).add("VerifiedGarbage.TCB.AuditRecords")
            libraries = {k: frozenset(v) for k, v in libraries.items()}
            self.assertEqual(check_lean_imports.native_tcb(tcb, libraries, self.NAMES, traces, {"A", "B"}),
                             problem)

    def test_unlisted_and_unnamed(self):
        libraries = dict(self.SPLIT, NativeTCB=frozenset())
        traces = dict.fromkeys([*self.TCB, "VG.Spec.X"], frozenset())
        self.assertEqual(self.check(libraries, traces, {"NativeTCBA": "VerifiedGarbage_NativeTCBA"}), [
            "VG.TCB.Mem: in 0 precompiled libraries (none); list it in exactly one, NativeTCB, "
            "in lean/lakefile.toml",
            'NativeTCBB: give it `libName = "VerifiedGarbage_NativeTCBB"` (lean/lakefile.toml), '
            "the shared library the emitter loads"])


if __name__ == "__main__":
    unittest.main()
