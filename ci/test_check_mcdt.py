"""Regression tests for instruction locations in the MCDT checker."""

import contextlib
import io
import pathlib
import tempfile
import unittest
from unittest.mock import patch

import check_mcdt


class Listings(unittest.TestCase):
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

    def run_main(self, src, listing):
        """`main`'s status and errors, with the module `m` of each target
        `src` and its listing `listing` (`None`: none)."""
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            for arch in check_mcdt.TARGETS:
                crate = root / "crates" / f"verified-garbage-asm-{arch}"
                (crate / "src").mkdir(parents=True)
                (crate / "src" / "lib.rs").write_text("")
                (crate / "src" / "m.rs").write_text(src)
                if listing is not None:
                    (crate / "listing").mkdir()
                    (crate / "listing" / "m.s").write_text(listing)
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
                f"crates/verified-garbage-asm-{arch}/listing/m.s (vg_f):4: `pmuludq xmm0, xmm1` "
                "is outside Intel's MXCSR prologue and epilogue "
                "(MCDT, see lean/VerifiedGarbage/TCB/X86_64/Isa.lean)",
                f"crates/verified-garbage-asm-{arch}/listing/m.s (vg_g):7: `pmullw xmm0, xmm1` "
                "is outside Intel's MXCSR prologue and epilogue "
                "(MCDT, see lean/VerifiedGarbage/TCB/X86_64/Isa.lean)"]])

    def test_unlisted_functions_fail(self):
        # Every naked function of the module is in its listing, read in full.
        status, errors = self.run_main(self.NAKED * 2, "vg_f:\n\tret\n")
        self.assertEqual(status, 1)
        self.assertEqual(errors, [f"crates/verified-garbage-asm-{arch}/listing/m.s: lists 1 of the "
                                  f"2 naked functions of crates/verified-garbage-asm-{arch}/src/m.rs"
                                  for arch in check_mcdt.TARGETS])
        status, errors = self.run_main(self.NAKED, None)
        self.assertEqual(errors, [f"crates/verified-garbage-asm-{arch}/src/m.rs: has no listing "
                                  f"crates/verified-garbage-asm-{arch}/listing/m.s"
                                  for arch in check_mcdt.TARGETS])
        status, errors = self.run_main(self.NAKED, "vg_f:\n\tret\nret\n")
        self.assertEqual(errors, [f"crates/verified-garbage-asm-{arch}/listing/m.s:3: neither a "
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


if __name__ == "__main__":
    unittest.main()
