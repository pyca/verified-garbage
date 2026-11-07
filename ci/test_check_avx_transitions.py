"""Tests of the SSE/AVX transition checker."""

import contextlib
import io
import pathlib
import tempfile
import unittest
from unittest.mock import patch

import check_avx_transitions as cat
from check_mcdt import functions


def check(*fns):
    """The errors of the functions whose code is `fns`, each a list of lines
    (`name:` then its instructions and labels), all in the file `m.s`."""
    text = "\n".join("\n".join(lines) for lines in fns) + "\n"
    found, unread = functions(text)
    assert not unread, unread
    program = cat.Program({name: ("m.s", i, l, lb) for name, i, l, lb in found})
    errors = []
    for name, *_ in found:
        errors += program.summary(name, False)[0]
    return errors


class Classify(unittest.TestCase):
    def test_writes_xmm_legacy(self):
        for instr in ("movdqa xmm14, xmm15", "movdqu xmm15, XMMWORD PTR [rdx+48]",
                      "pxor xmm0, xmm1", "aesdec xmm0, xmm8", "ptest xmm0, xmm0",
                      "pcmpistrm xmm1, xmm2, 0"):
            self.assertTrue(cat.writes_xmm_legacy(instr), instr)
        for instr in ("movdqu XMMWORD PTR [rdx], xmm0", "movq rax, xmm0",
                      "pextrq rax, xmm1, 1", "vmovdqu xmm15, XMMWORD PTR [rdx]",
                      "vpxord xmm0, xmm0, xmm1", "ldmxcsr DWORD PTR [rsp]", "mov rax, rbx",
                      ".p2align 6", "kmovq k1, rax"):
            self.assertFalse(cat.writes_xmm_legacy(instr), instr)

    def test_writes_wide(self):
        for instr in ("vmovdqu32 zmm14, ZMMWORD PTR [rdx]", "vpxor ymm0, ymm0, ymm1",
                      "vshufi32x4 zmm15, zmm15, zmm14, 0"):
            self.assertTrue(cat.writes_wide(instr), instr)
        # A store, a 128-bit VEX write, and `zmm16`–`zmm31`, which
        # `vzeroupper` does not track.
        for instr in ("vmovdqu32 ZMMWORD PTR [rdx], zmm0", "vmovdqu xmm15, XMMWORD PTR [rdx]",
                      "vpxord zmm16, zmm16, zmm17", "vextracti128 xmm14, ymm0, 1"):
            self.assertFalse(cat.writes_wide(instr), instr)


class Flow(unittest.TestCase):
    def test_legacy_after_wide(self):
        errors = check(["vg_f:", "\tvpxor ymm0, ymm0, ymm1", "\tmovdqa xmm1, xmm2",
                        "\tvzeroupper", "\tret"])
        self.assertEqual(len(errors), 1)
        self.assertIn("m.s:3 (vg_f): `movdqa xmm1, xmm2` writes an xmm register with legacy SSE", errors[0])

    def test_clean(self):
        # Legacy SSE before the wide write, VEX and reads of `xmm` after it,
        # and `vzeroupper` before the legacy code and the `ret`.
        self.assertEqual(check(["vg_f:", "\tpxor xmm0, xmm0", "\tvpxor ymm0, ymm0, ymm1",
                                "\tvmovdqu xmm15, XMMWORD PTR [rdx]", "\tmovq rax, xmm0",
                                "\tmovdqu XMMWORD PTR [rdx], xmm0", "\tvzeroupper",
                                "\tpxor xmm1, xmm1", "\tret"]), [])

    def test_dirty_ret(self):
        errors = check(["vg_f:", "\tvpxord zmm0, zmm0, zmm1", "\tret"])
        self.assertEqual(len(errors), 1)
        self.assertIn("`ret` returns with dirty upper state", errors[0])

    def test_high_registers_are_clean(self):
        self.assertEqual(check(["vg_f:", "\tvpxord zmm16, zmm16, zmm17", "\tpxor xmm0, xmm1",
                                "\tret"]), [])

    def test_branches(self):
        # The wide write is on one path only, and the jump back to the loop
        # (`20b`) carries the dirty state round to its start, before the
        # `vzeroupper` the forward jump (`21f`) skips to.
        errors = check(["vg_f:", "20:", "\tpxor xmm0, xmm1", "\tcmp rcx, 1", "\tje 21f",
                        "\tvpxor ymm0, ymm0, ymm1", "\tjmp 20b", "21:", "\tvzeroupper", "\tret"])
        self.assertEqual(len(errors), 1)
        self.assertIn("m.s:3 (vg_f): `pxor xmm0, xmm1`", errors[0])
        # Without the jump back, only straight-line legacy code: clean.
        self.assertEqual(check(["vg_f:", "\tcmp rcx, 1", "\tje 20f", "\tvpxor ymm0, ymm0, ymm1",
                                "\tvzeroupper", "20:", "\tpxor xmm0, xmm1", "\tret"]), [])

    def test_cold_code_after_ret(self):
        errors = check(["vg_f:", "\tje 20f", "21:", "\tvzeroupper", "\tret",
                        "20:", "\tvpxor ymm0, ymm0, ymm1", "\tpxor xmm2, xmm2", "\tjmp 21b"])
        self.assertEqual(len(errors), 1)
        self.assertIn("`pxor xmm2, xmm2`", errors[0])

    def test_unresolved_and_fallthrough(self):
        errors = check(["vg_f:", "\tje 29f", "\tmov rax, rbx"])
        self.assertEqual(len(errors), 2)
        self.assertIn("jumps to a target this check cannot resolve", errors[0])
        self.assertIn("falls through past the end of its function", errors[1])

    def test_calls(self):
        # A callee that writes `ymm` and returns dirty makes its caller's
        # legacy code after the call an error; one that runs legacy SSE is
        # an error only when called dirty.
        dirty = ["vg_dirty:", "\tvpxor ymm0, ymm0, ymm1", "\tret"]
        legacy = ["vg_legacy:", "\tpxor xmm0, xmm1", "\tret"]
        errors = check(dirty, legacy, ["vg_f:", "\tcall {vg_dirty}", "\tpxor xmm3, xmm3",
                                       "\tcall {vg_legacy}", "\tvzeroupper", "\tret"])
        self.assertEqual(len(errors), 3)
        self.assertIn("m.s:3 (vg_dirty): `ret` returns with dirty upper state", errors[0])
        self.assertIn("(vg_f): `pxor xmm3, xmm3` writes an xmm register", errors[1])
        self.assertIn("(vg_f): `call {vg_legacy}` calls vg_legacy with dirty upper state, which then: "
                      "m.s:5 (vg_legacy): `pxor xmm0, xmm1`", errors[2])
        # A callee returning clean leaves its caller clean.
        self.assertEqual(check(["vg_g:", "\tvpxor ymm0, ymm0, ymm1", "\tvzeroupper", "\tret"],
                               ["vg_f:", "\tcall {vg_g}", "\tpxor xmm3, xmm3", "\tret"]), [])

    def test_indirect_calls(self):
        errors = check(["vg_f:", "\tvpxor ymm0, ymm0, ymm1", "\tcall r11", "\tpxor xmm0, xmm0", "\tret"])
        self.assertEqual(len(errors), 1)
        self.assertIn("`call r11` calls code this check cannot see with dirty upper state", errors[0])

    def test_recursion(self):
        errors = check(["vg_f:", "\tcall {vg_f}", "\tret"])
        self.assertIn("m.s:2 (vg_f): `call {vg_f}` is a recursive call", errors[0])


class Main(unittest.TestCase):
    def run_main(self, assembly):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            for arch in cat.TARGETS:
                crate = root / "crates" / f"verified-garbage-asm-{arch}"
                (crate / "assembly" / "internal").mkdir(parents=True)
                (crate / "assembly" / "m.s").write_text(assembly)
                (crate / "assembly" / "internal" / "vg_h.s").write_text("vg_h:\n\tret\n")
            stderr = io.StringIO()
            with patch.object(cat, "ROOT", root), contextlib.redirect_stderr(stderr), \
                    contextlib.redirect_stdout(io.StringIO()):
                status = cat.main()
        return status, stderr.getvalue().splitlines()

    def test_main(self):
        self.assertEqual(self.run_main("// header\n\nvg_f:\n\tcall {vg_h}\n\tret\n"), (0, []))
        status, errors = self.run_main("vg_f:\n\tvpxor ymm0, ymm0, ymm1\n\tret\nret\n")
        self.assertEqual(status, 1)
        self.assertEqual(errors, [
            line for arch in cat.TARGETS for line in [
                f"crates/verified-garbage-asm-{arch}/assembly/m.s:4: neither a function, an instruction nor a label",
                f"crates/verified-garbage-asm-{arch}/assembly/m.s:3 (vg_f): `ret` returns with dirty upper "
                "state (no vzeroupper since a ymm/zmm write)"]])

    def test_duplicate_function(self):
        status, errors = self.run_main("vg_h:\n\tret\n")
        self.assertEqual(status, 1)
        self.assertIn("vg_h is also in", errors[0])


if __name__ == "__main__":
    unittest.main()
