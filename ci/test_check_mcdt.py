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


class Flags(unittest.TestCase):
    """An epilogue may not restore MXCSR with its status flags cleared."""

    def regions(self, save):
        instrs = (["stmxcsr DWORD PTR [rsp]", "mov r11d, DWORD PTR [rsp]"] + save +
                  ["mov r11d, 8127", "mov DWORD PTR [rsp+4], r11d", "ldmxcsr DWORD PTR [rsp+4]",
                   "lfence", "lfence", "ldmxcsr DWORD PTR [rsp]", "ret"])
        return check_mcdt.check_function("f", instrs, list(range(len(instrs))), {})[0]

    def test_scrub_tail(self):
        # `mxFix`: the saved value masked (reserved bits and flags cleared), then the flags set.
        self.assertEqual(self.regions(["and r11d, 65472", "or r11d, 63", "mov DWORD PTR [rsp], r11d"]), [])
        self.assertEqual(self.regions(["and r11d, 65472", "mov DWORD PTR [rsp], r11d"]), [
            "f:9: `ldmxcsr DWORD PTR [rsp]` may restore MXCSR with its status flags cleared, which "
            "code after it may rely on"])

    def test_saved_value_kept(self):
        # The reserved bits cleared, the flags kept; or the slot as `stmxcsr` left it.
        self.assertEqual(self.regions(["and r11d, 65535", "mov DWORD PTR [rsp], r11d"]), [])
        self.assertEqual(self.regions([]), [])

    def test_restored_from_a_register(self):
        # ML-KEM's `withMxcsr`: the masked value kept in `r11`, stored back in the epilogue.
        instrs = ["stmxcsr DWORD PTR [rdi+768]", "mov r11d, DWORD PTR [rdi+768]", "and r11d, {}",
                  "mov eax, 8127", "mov DWORD PTR [rdi+772], eax", "ldmxcsr DWORD PTR [rdi+772]",
                  "lfence", "pmuludq xmm0, xmm1", "lfence", "mov DWORD PTR [rdi+768], r11d",
                  "ldmxcsr DWORD PTR [rdi+768]", "ret"]
        for mask, ok in ((65535, True), (65472, False)):
            code = [x.format(mask) for x in instrs]
            errors = check_mcdt.check_function("f", code, list(range(len(code))), {})[0]
            self.assertEqual(errors == [], ok)


class Enter(unittest.TestCase):
    CODE = ["push rax", "stmxcsr DWORD PTR [rsp]", "mov eax, DWORD PTR [rsp]", "or eax, 63",
            "mov DWORD PTR [rsp], eax", "ldmxcsr DWORD PTR [rsp]", "lfence", "pop rcx", "ret"]

    def test_accepted(self):
        self.assertEqual(check_mcdt.check_enter("e", self.CODE, list(range(len(self.CODE)))), [])

    def test_affected_or_call_rejected(self):
        for bad in ("pmuludq xmm0, xmm1", "call {vg_f}"):
            code = self.CODE[:-1] + [bad, "ret"]
            self.assertEqual(check_mcdt.check_enter("e", code, list(range(len(code)))), [
                f"e:{len(code) - 2}: `{bad}` is in vg_mcdt_enter, which may neither run an "
                "instruction MCDT affects nor call"])

    def test_only_vg_mcdt_enter(self):
        # The same code under another name is not Intel's prologue.
        code = self.CODE
        errors, _ = check_mcdt.check_function("f", code, list(range(len(code))), {})
        self.assertEqual(errors, ["f:5: `ldmxcsr DWORD PTR [rsp]` is not Intel's MCDT prologue: "
                                  "not preceded by `mov r32, 8127` and a store of it to its operand"])


class Entered(unittest.TestCase):
    """Affected instructions outside regions, in functions every run of which is
    under `vg_mcdt_enter`, which their dispatchers run first (x86-64 only)."""

    def fn(self, name, vis="pub(crate) "):
        return f"#[unsafe(naked)]\n{vis}unsafe extern \"sysv64\" fn {name}() {{}}\n"

    def dispatcher(self, name, enter=True):
        first = check_mcdt.ENTER_LINE + "\n" if enter else ""
        return (f"pub unsafe fn {name}_auto(_dit: verified_garbage_cpu::Dit<'_>) {{\n{first}"
                f"    unsafe {{ crate::m::{name}() }}\n}}\n")

    def check(self, src, assembly, dispatch="", tables=""):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            crate = root / "crates" / "verified-garbage-asm-x86_64"
            for d in ("src/dispatch", "src/fn_tables", "assembly"):
                (crate / d).mkdir(parents=True)
            (crate / "src" / "m.rs").write_text(src)
            (crate / "assembly" / "m.s").write_text(assembly)
            (crate / "src" / "dispatch" / "m.rs").write_text(dispatch)
            (crate / "src" / "fn_tables" / "t.rs").write_text(tables)
            stderr = io.StringIO()
            with patch.object(check_mcdt, "ROOT", root), contextlib.redirect_stderr(stderr), \
                    contextlib.redirect_stdout(io.StringIO()):
                status = check_mcdt.main()
        return status, stderr.getvalue().splitlines()

    ERROR = ("crates/verified-garbage-asm-x86_64/assembly/m.s (vg_f):2: `pmuludq xmm0, xmm1` is "
             "outside Intel's MXCSR prologue and epilogue (MCDT, see "
             "lean/VerifiedGarbage/TCB/X86_64/Isa.lean)")
    F = "vg_f:\n\tpmuludq xmm0, xmm1\n\tret\n"

    def test_dispatched(self):
        self.assertEqual(self.check(self.fn("vg_f"), self.F, self.dispatcher("vg_f")), (0, []))

    def test_dispatcher_without_enter(self):
        self.assertEqual(self.check(self.fn("vg_f"), self.F, self.dispatcher("vg_f", enter=False)),
                         (1, [self.ERROR]))

    def test_never_named(self):
        self.assertEqual(self.check(self.fn("vg_f"), self.F), (1, [self.ERROR]))

    def test_called_from_entered(self):
        asm = self.F + "\nvg_h:\n\tcall {vg_f}\n\tret\n"
        src = self.fn("vg_f") + self.fn("vg_h")
        self.assertEqual(self.check(src, asm, self.dispatcher("vg_h")), (0, []))
        # A caller that is not.
        self.assertEqual(self.check(src, asm, self.dispatcher("vg_h", enter=False)), (1, [self.ERROR]))

    def test_table_or_public(self):
        self.assertEqual(self.check(self.fn("vg_f"), self.F, self.dispatcher("vg_f"),
                                  tables="static T: [*const (); 1] = [crate::m::vg_f as *const ()];\n"),
                         (1, [self.ERROR]))
        self.assertEqual(self.check(self.fn("vg_f", vis="pub "), self.F, self.dispatcher("vg_f")),
                         (1, [self.ERROR]))


class Guarded(unittest.TestCase):
    """Affected instructions after the function's own successful call of
    `vg_mcdt_enter` (`Rust.mcdtOpen`), on x86-64."""

    ERROR = ("f:{}: `pmuludq xmm0, xmm1` is outside Intel's MXCSR prologue and epilogue "
             "(MCDT, see lean/VerifiedGarbage/TCB/X86_64/Isa.lean)")
    GUARD = ["call {vg_mcdt_enter}", "test eax, eax", "je 20f"]

    def errors(self, instrs, labels):
        guard = check_mcdt.guarded(instrs, labels)
        return check_mcdt.check_function("f", instrs, list(range(len(instrs))), labels, guard=guard)[0]

    def code(self, fallback, rest, after=()):
        """The guard, `rest` when it returned 1, `fallback` when it returned 0,
        then `after`: `Code.ite .e fallback rest` as the printer lays it out."""
        instrs = self.GUARD + rest + ["jmp 21f"] + fallback + list(after) + ["ret"]
        return instrs, {"20": [len(self.GUARD) + len(rest) + 1],
                        "21": [len(self.GUARD) + len(rest) + 1 + len(fallback)]}

    MUL = ["pmuludq xmm0, xmm1"]

    def test_after_the_guard(self):
        self.assertEqual(self.errors(*self.code(["mov eax, 1"], self.MUL)), [])
        # A loop, and a cold branch out of the code and back into it.
        rest = ["mov ecx, 4", "pmuludq xmm0, xmm1", "sub ecx, 1", "jne 22b", "jb 23f", "pmuludq xmm0, xmm2"]
        instrs, labels = self.code(["mov eax, 1"], rest)
        instrs += ["pmuludq xmm0, xmm3", "jmp 24b"]
        labels.update({"22": [4], "23": [len(instrs) - 2], "24": [8]})
        self.assertEqual(self.errors(instrs, labels), [])

    def test_fallback_or_after(self):
        instrs, labels = self.code(self.MUL, [])
        self.assertEqual(self.errors(instrs, labels), [self.ERROR.format(4)])
        instrs, labels = self.code(["mov eax, 1"], self.MUL, self.MUL)
        self.assertEqual(self.errors(instrs, labels), [self.ERROR.format(6)])

    def test_not_the_guard(self):
        for k, bad in ((0, "call {vg_f}"), (1, "test rax, rax"), (1, "test edx, edx"), (2, "jne 20f")):
            instrs, labels = self.code(["mov eax, 1"], self.MUL)
            instrs[k] = bad
            self.assertEqual(self.errors(instrs, labels), [self.ERROR.format(3)], bad)

    def test_entered_otherwise(self):
        # A jump to the test or the `je`, past the call, or past the guard.
        for k in (1, 2, 3):
            instrs, labels = self.code(["mov eax, 1"], self.MUL)
            instrs, labels = ["jb 25f"] + instrs, {l: [d + 1 for d in ds] for l, ds in labels.items()}
            labels["25"] = [k + 1]
            self.assertEqual(self.errors(instrs, labels), [self.ERROR.format(4)], k)
        # A loop back to before the guard runs it again.
        instrs, labels = self.code(["mov eax, 1"], self.MUL, ["jne 25b"])
        labels["25"] = [0]
        self.assertEqual(self.errors(instrs, labels), [])

    def test_unknown_target(self):
        instrs, labels = self.code(["mov eax, 1"], self.MUL + ["jmp rax"])
        self.assertEqual(check_mcdt.guarded(instrs, labels), [False] * len(instrs))

    def test_callee(self):
        # A function called only after a guard needs no dispatcher's `vg_mcdt_enter`.
        e = Entered()
        src = e.fn("vg_f") + e.fn("vg_h")
        h = "\nvg_h:\n\tcall {vg_mcdt_enter}\n\ttest eax, eax\n\tje 20f\n\tcall {vg_f}\n20:\n\tret\n"
        self.assertEqual(e.check(src, e.F + h, e.dispatcher("vg_h", enter=False)), (0, []))
        # Called otherwise too.
        self.assertEqual(e.check(src, e.F + h.replace("\tret\n", "\tcall {vg_f}\n\tret\n"),
                                 e.dispatcher("vg_h", enter=False)), (1, [e.ERROR]))
        # In the function itself, through `main`.
        f = "vg_f:\n\tcall {vg_mcdt_enter}\n\ttest eax, eax\n\tje 20f\n\tpmuludq xmm0, xmm1\n20:\n\tret\n"
        self.assertEqual(e.check(e.fn("vg_f"), f, e.dispatcher("vg_f", enter=False)), (0, []))


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
