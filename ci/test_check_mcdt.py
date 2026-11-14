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


class RegionCalls(unittest.TestCase):
    """A region's `call`s of internal functions that run only inside regions."""

    PROLOGUE = ["stmxcsr DWORD PTR [rsp]", "mov eax, 8127", "mov DWORD PTR [rsp+4], eax",
                "ldmxcsr DWORD PTR [rsp+4]", "lfence"]
    EPILOGUE = ["lfence", "ldmxcsr DWORD PTR [rsp]"]

    def fn(self, name, body):
        return f"{name}:\n" + "".join(f"\t{x}\n" for x in body)

    def region(self, body):
        return self.PROLOGUE + body + self.EPILOGUE + ["ret"]

    def run_files(self, module, internal):
        """`main`'s status and errors (those of x86_64), with the module `m`'s
        functions `module` and the internal functions `internal`, each
        `{name: body}`, in each target."""
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            for arch in check_mcdt.TARGETS:
                crate = root / "crates" / f"verified-garbage-asm-{arch}"
                (crate / "src" / "internal").mkdir(parents=True)
                (crate / "assembly" / "internal").mkdir(parents=True)
                (crate / "src" / "lib.rs").write_text("")
                (crate / "src" / "m.rs").write_text(Assembly.NAKED * len(module))
                (crate / "assembly" / "m.s").write_text("\n".join(self.fn(n, b) for n, b in module.items()))
                for n, b in internal.items():
                    (crate / "src" / "internal" / f"{n}.rs").write_text(Assembly.NAKED)
                    (crate / "assembly" / "internal" / f"{n}.s").write_text(self.fn(n, b))
            stderr = io.StringIO()
            with patch.object(check_mcdt, "ROOT", root), contextlib.redirect_stderr(stderr), \
                    contextlib.redirect_stdout(io.StringIO()):
                status = check_mcdt.main()
        errors = stderr.getvalue().splitlines()
        return status, [e.removeprefix("crates/verified-garbage-asm-x86_64/") for e in errors
                        if "asm-x86_64/" in e]

    MUL = ["pmuludq xmm0, xmm1", "ret"]

    def test_call_inside_a_region(self):
        # `vg_f`'s multiplication runs inside `vg_g`'s region, as does
        # `vg_h`'s, which only `vg_f` calls.
        self.assertEqual(self.run_files(
            {"vg_g": self.region(["call {vg_f}", "pmuludq xmm0, xmm1", "call {vg_f}"])},
            {"vg_f": ["call {vg_h}", "pmuludq xmm0, xmm1", "ret"], "vg_h": self.MUL}), (0, []))

    def test_called_outside_a_region(self):
        status, errors = self.run_files(
            {"vg_g": self.region(["call {vg_f}"]), "vg_k": ["call {vg_f}", "ret"]},
            {"vg_f": self.MUL})
        self.assertEqual(status, 1)
        self.assertEqual(errors, [
            "assembly/m.s (vg_g):7: `call {vg_f}` is inside an MCDT region, and calls no internal "
            "function that runs only inside MCDT regions",
            "assembly/internal/vg_f.s (vg_f):2: `pmuludq xmm0, xmm1` is outside Intel's MXCSR "
            "prologue and epilogue (MCDT, see lean/VerifiedGarbage/TCB/X86_64/Isa.lean): its function "
            "is not called only inside MCDT regions (vg_k calls it outside an MCDT region, at "
            "crates/verified-garbage-asm-x86_64/assembly/m.s:13)"])

    def test_called_through_one_called_outside(self):
        # `vg_h` is called only by `vg_f`, which `vg_k` calls outside a region.
        status, errors = self.run_files(
            {"vg_g": self.region(["call {vg_f}"]), "vg_k": ["call {vg_f}", "ret"]},
            {"vg_f": ["call {vg_h}", "ret"], "vg_h": self.MUL})
        self.assertEqual(status, 1)
        self.assertIn("assembly/internal/vg_h.s (vg_h):2: `pmuludq xmm0, xmm1` is outside Intel's "
                      "MXCSR prologue and epilogue (MCDT, see lean/VerifiedGarbage/TCB/X86_64/Isa.lean): "
                      "its function is not called only inside MCDT regions (vg_f calls it outside an "
                      "MCDT region, at crates/verified-garbage-asm-x86_64/assembly/internal/vg_f.s:2)", errors)

    def test_never_called(self):
        status, errors = self.run_files({}, {"vg_f": self.MUL})
        self.assertEqual(errors, [
            "assembly/internal/vg_f.s (vg_f):2: `pmuludq xmm0, xmm1` is outside Intel's MXCSR "
            "prologue and epilogue (MCDT, see lean/VerifiedGarbage/TCB/X86_64/Isa.lean): its function "
            "is not called only inside MCDT regions (it is never called)"])

    def test_calls_rejected_inside_a_region(self):
        # An artifact (Rust calls it), an internal function with its own
        # region (it writes MXCSR), a function of no name, and recursion.
        status, errors = self.run_files(
            {"vg_g": self.region(["call {vg_a}", "call {vg_r}", "call rax", "call {vg_p}"]),
             "vg_a": self.MUL[1:]},
            {"vg_r": self.region(["pmuludq xmm0, xmm1"]),
             "vg_p": ["call {vg_q}", "ret"], "vg_q": ["call {vg_p}", "ret"]})
        self.assertEqual(status, 1)
        self.assertEqual([e for e in errors if "m.s (vg_g)" in e], [
            f"assembly/m.s (vg_g):{n}: `{c}` is inside an MCDT region, and calls no internal "
            "function that runs only inside MCDT regions"
            for n, c in [(7, "call {vg_a}"), (8, "call {vg_r}"), (9, "call rax"), (10, "call {vg_p}")]])
        self.assertEqual([e for e in errors if "m.s (vg_g)" not in e], [])

    def test_names_are_unique(self):
        # An artifact of the same name as an internal function would make
        # the internal one's calls ambiguous.
        status, errors = self.run_files({"vg_g": self.region(["call {vg_f}"]), "vg_f": ["ret"]},
                                        {"vg_f": self.MUL})
        self.assertEqual(status, 1)
        self.assertEqual(errors[0], "assembly/internal/vg_f.s: defines vg_f, as "
                         "crates/verified-garbage-asm-x86_64/assembly/m.s does")

    def test_ret_inside_a_region(self):
        status, errors = self.run_files({"vg_g": self.PROLOGUE + ["ret"] + self.EPILOGUE + ["ret"]}, {})
        self.assertEqual(errors, ["assembly/m.s (vg_g):7: `ret` is inside an MCDT region"])


if __name__ == "__main__":
    unittest.main()
