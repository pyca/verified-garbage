"""Regression tests for instruction locations in the MCDT checker."""

import contextlib
import io
import pathlib
import tempfile
import unittest
from unittest.mock import patch

import check_mcdt


class InstructionLocations(unittest.TestCase):
    def test_labels_and_ignored_lines(self):
        body = '\n'.join([
            '    naked_asm!(',
            '        "2:",',
            '',
            '        "mov eax, 8127",',
            '        "3:",',
            '        "3:",',
            '',
            '        "pmuludq xmm0, xmm1",',
            '        "2:",',
            '        "ret",',
            '    );',
        ])
        self.assertEqual(
            check_mcdt.code(body, 10),
            (["mov eax, 8127", "pmuludq xmm0, xmm1", "ret"],
             [13, 17, 19], {"2": [0, 2], "3": [1, 1]}),
        )

    def test_multiline_literals(self):
        # The emitter writes each run of lines as one literal.
        body = '\n'.join([
            '    naked_asm!(',
            '        "2:',
            'mov eax, 8127',
            '3:",',
            '        "pmuludq xmm0, xmm1",',
            '        "call {vg_f}',
            'ret",',
            '        vg_f = sym super::f::vg_f,',
            '    );',
        ])
        self.assertEqual(
            check_mcdt.code(body, 10),
            (["mov eax, 8127", "pmuludq xmm0, xmm1", "call {vg_f}", "ret"],
             [12, 14, 15, 16], {"2": [0], "3": [1]}),
        )

    def test_encoded_instructions(self):
        # An encoded instruction is a comment of its text above the literal
        # holding its bytes; the literal's other lines come after them.
        body = '\n'.join([
            '    naked_asm!(',
            '        ".p2align 6",',
            '        // mov eax, 8127',
            '        // pmuludq xmm0, xmm1',
            '        r".byte 0xb8,0xbf,0x1f,0x00,0x00,0x66,0x0f,0xf4,0xc1',
            '2:',
            'jne 2b",',
            '        // ret',
            '        r".octa 0xc3",',
            '    );',
        ])
        self.assertEqual(
            check_mcdt.code(body, 10),
            ([".p2align 6", "mov eax, 8127", "pmuludq xmm0, xmm1", "jne 2b", "ret"],
             [11, 12, 13, 16, 17], {"2": [3]}),
        )

    def test_diagnostics_across_functions_and_files(self):
        # Include documentation, blank lines, and labels before instructions;
        # main() must reset its file offset and code() must include labels.
        text = '\n'.join([
            '// generated code',
            '',
            'pub(crate) unsafe extern "sysv64" fn vg_first() {',
            '    naked_asm!(',
            '        "2:',
            'pmuludq xmm0, xmm1",',
            '    );',
            '}',
            '',
            '/// second function',
            'pub(crate) unsafe extern "sysv64" fn vg_second() {',
            '',
            '    naked_asm!(',
            '        "pmullw xmm0, xmm1",',
            '    );',
            '}',
        ])
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            for arch in check_mcdt.TARGETS:
                path = root / "src" / "asm" / arch / "test.rs"
                path.parent.mkdir(parents=True)
                path.write_text(text)
            stderr = io.StringIO()
            with patch.object(check_mcdt, "ROOT", root), patch.object(
                check_mcdt, "ASM", root / "src" / "asm"
            ), contextlib.redirect_stderr(stderr):
                self.assertEqual(check_mcdt.main(), 1)
        expected = []
        for arch in check_mcdt.TARGETS:
            for name, line, instr in [
                ("vg_first", 6, "pmuludq xmm0, xmm1"),
                ("vg_second", 14, "pmullw xmm0, xmm1"),
            ]:
                expected.append(
                    f"src/asm/{arch}/test.rs ({name}):{line}: `{instr}` is outside "
                    "Intel's MXCSR prologue and epilogue "
                    "(MCDT, see lean/VerifiedGarbage/TCB/X86_64/Isa.lean)"
                )
        self.assertEqual(stderr.getvalue().splitlines(), expected)


    def run_main(self, text):
        """`main`'s status and errors, with `text` the only file of each target."""
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            for arch in check_mcdt.TARGETS:
                path = root / "src" / "asm" / arch / "test.rs"
                path.parent.mkdir(parents=True)
                path.write_text(text)
            stderr = io.StringIO()
            with patch.object(check_mcdt, "ROOT", root), patch.object(
                check_mcdt, "ASM", root / "src" / "asm"
            ), contextlib.redirect_stderr(stderr), contextlib.redirect_stdout(io.StringIO()):
                status = check_mcdt.main()
        return status, stderr.getvalue().splitlines()

    def test_public_functions_are_read(self):
        # A target's crate's functions are `pub`.
        status, errors = self.run_main('#[unsafe(naked)]\n'
                                       'pub unsafe extern "sysv64" fn vg_f() {\n'
                                       '    naked_asm!(\n        "pmullw xmm0, xmm1",\n    );\n}\n')
        self.assertEqual(status, 1)
        self.assertEqual(len(errors), len(check_mcdt.TARGETS))
        self.assertTrue(all("(vg_f):4: `pmullw xmm0, xmm1` is outside" in e for e in errors))

    def test_unread_functions_fail(self):
        # A naked function written in a form `FN` does not read is an error,
        # not a function quietly left unchecked.
        status, errors = self.run_main('#[unsafe(naked)]\n'
                                       'pub(in crate) unsafe extern "sysv64" fn vg_f() {\n'
                                       '    naked_asm!(\n        "pmullw xmm0, xmm1",\n    );\n}\n')
        self.assertEqual(status, 1)
        self.assertEqual(errors, [f"src/asm/{arch}/test.rs: read 0 of its 1 naked functions"
                                  for arch in check_mcdt.TARGETS])


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
