"""Regression tests for instruction locations in the MCDT checker."""

import contextlib
import io
import pathlib
import tempfile
import unittest
from unittest.mock import patch

import check_mcdt


class Assembly(unittest.TestCase):
    def test_functions(self):
        # Each function's instructions, the line of each, and its labels; the
        # header's comments and blank lines are skipped.
        text = "\n".join([
            "// The functions of `src/m.rs`",
            "",
            "vg_f:",
            "\t.p2align 6",
            "20:",
            "\tmov eax, 8127",
            "21:",
            "21:",
            "\tpmuludq xmm0, xmm1",
            "\tjne 20b",
            "",
            "// vg_g: the function `vg_f`",
            "",
            "vg_h:",
            "\tcall {vg_f}",
            "\tret",
        ])
        self.assertEqual(check_mcdt.functions(text), ([
            ("vg_f", [".p2align 6", "mov eax, 8127", "pmuludq xmm0, xmm1", "jne 20b"],
             [4, 6, 9, 10], {"20": [1], "21": [2, 2]}),
            ("vg_h", ["call {vg_f}", "ret"], [15, 16], {}),
        ], []))

    def test_unread_lines(self):
        self.assertEqual(check_mcdt.functions("mov eax, 1\nvg_f:\n\tret\n  ret\n")[1], [1, 4])

    def run_main(self, src, assembly):
        """`main`'s status and errors, with the module `m` of each target
        `src` and its assembly file `assembly` (`None`: none)."""
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            for arch in check_mcdt.TARGETS:
                crate = root / "crates" / f"verified-garbage-asm-{arch}"
                (crate / "src").mkdir(parents=True)
                (crate / "src" / "lib.rs").write_text("")
                (crate / "src" / "m.rs").write_text(src)
                if assembly is not None:
                    (crate / "assembly").mkdir()
                    (crate / "assembly" / "m.s").write_text(assembly)
            stderr = io.StringIO()
            with patch.object(check_mcdt, "ROOT", root), contextlib.redirect_stderr(stderr), \
                    contextlib.redirect_stdout(io.StringIO()):
                status = check_mcdt.main()
        return status, stderr.getvalue().splitlines()

    NAKED = "#[unsafe(naked)]\npub unsafe extern \"sysv64\" fn vg_f() {}\n"

    def test_diagnostics(self):
        status, errors = self.run_main(self.NAKED * 2, "// header\n\nvg_f:\n\tpmuludq xmm0, xmm1\n"
                                       "\nvg_g:\n\tpmullw xmm0, xmm1\n")
        self.assertEqual(status, 1)
        self.assertEqual(errors, [
            line for arch in check_mcdt.TARGETS for line in [
                f"crates/verified-garbage-asm-{arch}/assembly/m.s (vg_f):4: `pmuludq xmm0, xmm1` "
                "is outside Intel's MXCSR prologue and epilogue "
                "(MCDT, see lean/VerifiedGarbage/TCB/X86_64/Isa.lean)",
                f"crates/verified-garbage-asm-{arch}/assembly/m.s (vg_g):7: `pmullw xmm0, xmm1` "
                "is outside Intel's MXCSR prologue and epilogue "
                "(MCDT, see lean/VerifiedGarbage/TCB/X86_64/Isa.lean)"]])

    def test_unlisted_functions_fail(self):
        # Every naked function of the module is in its assembly file, read in full.
        status, errors = self.run_main(self.NAKED * 2, "vg_f:\n\tret\n")
        self.assertEqual(status, 1)
        self.assertEqual(errors, [f"crates/verified-garbage-asm-{arch}/assembly/m.s: lists 1 of the "
                                  f"2 naked functions of crates/verified-garbage-asm-{arch}/src/m.rs"
                                  for arch in check_mcdt.TARGETS])
        status, errors = self.run_main(self.NAKED, None)
        self.assertEqual(errors, [f"crates/verified-garbage-asm-{arch}/src/m.rs: has no assembly file "
                                  f"crates/verified-garbage-asm-{arch}/assembly/m.s"
                                  for arch in check_mcdt.TARGETS])
        status, errors = self.run_main(self.NAKED, "vg_f:\n\tret\nret\n")
        self.assertEqual(errors, [f"crates/verified-garbage-asm-{arch}/assembly/m.s:3: neither a "
                                  "function, an instruction nor a label" for arch in check_mcdt.TARGETS])

    def test_passes(self):
        status, errors = self.run_main(self.NAKED, "vg_f:\n\tret\n")
        self.assertEqual((status, errors), (0, []))


class ColdBranch(unittest.TestCase):
    PROLOGUE = [
        "stmxcsr DWORD PTR [rsp]",
        "mov eax, 8127",
        "mov DWORD PTR [rsp+4], eax",
        "ldmxcsr DWORD PTR [rsp+4]",
        "lfence",
    ]
    EPILOGUE = ["lfence", "ldmxcsr DWORD PTR [rsp]", "ret"]

    def test_cold_branch_inside_a_region(self):
        # `je 20f` to cold code after the `ret`, whose `jmp 21b` returns into
        # the region.
        instrs = self.PROLOGUE + ["je 20f", "pmuludq xmm0, xmm1"] + self.EPILOGUE + [
            "pmuludq xmm0, xmm2", "jmp 21b"]
        labels = {"21": [6], "20": [len(instrs) - 2]}
        errors, _ = check_mcdt.check_function("f", instrs, list(range(len(instrs))), labels)
        self.assertIn("f:11: `jmp 21b` jumps into the MCDT region at line 5 from outside it", errors)


class StatusClear(unittest.TestCase):
    CLEAR = [
        "stmxcsr DWORD PTR [rsp]",
        "mov r11d, DWORD PTR [rsp]",
        "and r11d, 65472",
        "mov DWORD PTR [rsp], r11d",
        "ldmxcsr DWORD PTR [rsp]",
    ]

    def check(self, instrs, labels=None):
        return check_mcdt.check_function("f", instrs, list(range(len(instrs))), labels or {})

    def test_after_a_region(self):
        # The scrub's clearing of MXCSR's status flags, after the code's
        # last region: it is no prologue, and starts no region.
        instrs = ColdBranch.PROLOGUE + ["pmuludq xmm0, xmm1"] + ColdBranch.EPILOGUE[:2] + self.CLEAR + ["ret"]
        self.assertEqual(self.check(instrs), ([], 1))
        self.assertEqual(self.check(self.CLEAR + ["ret"]), ([], 0))

    def test_protects_nothing(self):
        errors, _ = self.check(self.CLEAR + ["pmuludq xmm0, xmm1", "ret"])
        self.assertEqual(errors, ["f:5: `pmuludq xmm0, xmm1` is outside Intel's MXCSR prologue and "
                                  "epilogue (MCDT, see lean/VerifiedGarbage/TCB/X86_64/Isa.lean)"])

    def test_not_inside_a_region(self):
        instrs = ColdBranch.PROLOGUE + self.CLEAR + ColdBranch.EPILOGUE
        errors, _ = self.check(instrs)
        self.assertIn("f:4: the MCDT region after this prologue has no epilogue", errors)

    def test_only_the_exact_sequence(self):
        other = "`ldmxcsr DWORD PTR [rsp]` is not Intel's MCDT prologue"
        for k, line in [(0, "stmxcsr DWORD PTR [rsp+4]"), (1, "mov r11d, DWORD PTR [rsp+4]"),
                        (1, "mov r11, DWORD PTR [rsp]"), (2, "and r11d, 65535"), (2, "or r11d, 65472"),
                        (2, "and r10d, 65472"), (3, "mov DWORD PTR [rsp], r10d"),
                        (3, "mov DWORD PTR [rsp+4], r11d")]:
            instrs = self.CLEAR[:k] + [line] + self.CLEAR[k + 1:] + ["ret"]
            errors, _ = self.check(instrs)
            self.assertTrue(any(other in e for e in errors), line)
        # A label inside it: a jump could skip the masking.
        errors, _ = self.check(self.CLEAR + ["ret"], {"20": [3]})
        self.assertTrue(any(other in e for e in errors))
        # Too close to the function's start to be the sequence.
        errors, _ = self.check(self.CLEAR[2:] + ["ret"])
        self.assertTrue(any(other in e for e in errors))


if __name__ == "__main__":
    unittest.main()
