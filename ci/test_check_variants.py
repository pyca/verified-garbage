"""Tests for the variant checker: the composition of suffixes, the flow of
variants to callers, and the Rust code it counts as using them."""

import pathlib
import tempfile
import unittest

import check_variants

SIG = ("out: *mut u8", "")


def fns(calls):
    """A target's functions, all with one signature, from their callees."""
    return {"x": {name: (SIG, set(callees)) for name, callees in calls.items()}}


class Composition(unittest.TestCase):
    # Two independent dimensions: `h` (with `h_a`) and `f` (with `f_b`),
    # both called by `g`.
    BASE = {
        "vg_h": [], "vg_h_a": [], "vg_f": [], "vg_f_b": [],
        "vg_g": ["vg_h", "vg_f"], "vg_g_a": ["vg_h_a", "vg_f"], "vg_g_b": ["vg_h", "vg_f_b"],
    }
    RUST = "vg_g vg_g_a vg_g_b"

    def test_either_order(self):
        for name in ("vg_g_a_b", "vg_g_b_a"):
            with self.subTest(name=name):
                calls = dict(self.BASE, **{name: ["vg_h_a", "vg_f_b"]})
                self.assertEqual(check_variants.check(fns(calls), self.RUST + " " + name), [])

    def test_missing_composition(self):
        errors = check_variants.check(fns(self.BASE), self.RUST)
        self.assertEqual(len(errors), 2)
        self.assertIn("vg_g_a calls vg_f, which has the variant vg_f_b, but there is no vg_g_a_b",
                      errors[0])
        self.assertIn("vg_g_b calls vg_h, which has the variant vg_h_a, but there is no vg_g_b_a",
                      errors[1])

    def test_composition_must_not_call_baseline(self):
        calls = dict(self.BASE, vg_g_a_b=["vg_h_a", "vg_f"])
        errors = check_variants.check(fns(calls), self.RUST + " vg_g_a_b")
        self.assertEqual(len(errors), 1)
        self.assertIn("x: vg_g_a_b, the variant of vg_g_a for vg_f_b, calls the baseline vg_f",
                      errors[0])


class Dispatchers(unittest.TestCase):
    # `f` has the variant `f_s`, which only its dispatcher `f_auto` calls.
    CALLS = {"vg_f": [], "vg_f_s": []}
    DISP = {"x": {"vg_f_auto": {"vg_f_s", "vg_f"}}}

    def test_used_dispatcher_uses_its_variants(self):
        self.assertEqual(check_variants.check(fns(self.CALLS), "vg_f_auto", disp=self.DISP), [])

    def test_unused_dispatcher_uses_none(self):
        errors = check_variants.check(fns(self.CALLS), "vg_f", disp=self.DISP)
        self.assertEqual(len(errors), 1)
        self.assertIn("the variant vg_f_s is neither called", errors[0])

    def test_read_from_generated_code(self):
        text = (
            "pub unsafe fn vg_f_auto(out: *mut u8) {\n"
            "    if cpu.contains(crate::f::VG_F_S_FEATURES) {\n"
            "        return unsafe { crate::f::vg_f_s(out) };\n"
            "    }\n"
            "    unsafe { crate::f::vg_f(out) }\n"
            "}\n"
            "pub use crate::g::vg_g as vg_g_auto;\n"
            "pub use self::vg_h as vg_h_s;\n"
        )
        self.assertEqual(check_variants.file_dispatchers(text),
                         {"vg_f_auto": {"vg_f_s", "vg_f"}, "vg_g_auto": {"vg_g"}})
        self.assertEqual(check_variants.aliases(text), {"vg_h_s": "vg_h"})
        self.assertEqual(check_variants.unread([("x", text)]), [])


class Flow(unittest.TestCase):
    # `g` calls `f`, which has the variant `f_s`.
    BASE = {"vg_f": [], "vg_f_s": [], "vg_g": ["vg_f"]}
    RUST = "vg_g vg_g_s"

    def test_variant_calls_variant(self):
        calls = dict(self.BASE, vg_g_s=["vg_f_s"])
        self.assertEqual(check_variants.check(fns(calls), self.RUST), [])

    def test_variant_does_the_work_itself(self):
        # An optimized `g_s` that calls none of `f`'s implementations.
        calls = dict(self.BASE, vg_g_s=["vg_k"], vg_k=[])
        self.assertEqual(check_variants.check(fns(calls), self.RUST + " vg_f_s"), [])

    def test_variant_missing(self):
        errors = check_variants.check(fns(self.BASE), "vg_g vg_f_s")
        self.assertEqual(len(errors), 1)
        self.assertIn("vg_g calls vg_f, which has the variant vg_f_s, but there is no vg_g_s",
                      errors[0])

    def test_variant_calls_baseline(self):
        for callees in (["vg_f"], ["vg_f", "vg_f_s"]):
            with self.subTest(callees=callees):
                calls = dict(self.BASE, vg_g_s=callees)
                errors = check_variants.check(fns(calls), self.RUST + " vg_f_s")
                self.assertEqual(len(errors), 1)
                self.assertIn("vg_g_s, the variant of vg_g for vg_f_s, calls the baseline vg_f",
                              errors[0])

    def test_variant_calls_its_baseline(self):
        # A variant may call the function it is a variant of.
        calls = dict(self.BASE, vg_g_s=["vg_f_s", "vg_g"])
        self.assertEqual(check_variants.check(fns(calls), self.RUST), [])

    def test_helper_of_rewritten_callers(self):
        # `k` calls `g`, a helper the Rust code does not use; `k_s` does the
        # work of `g` itself, so nothing would call a `g_s`.
        calls = dict(self.BASE, vg_k=["vg_g"], vg_k_s=["vg_f_s"])
        self.assertEqual(check_variants.check(fns(calls), "vg_k vg_k_s"), [])
        # Through a helper of the helper.
        calls = dict(self.BASE, vg_h=["vg_g"], vg_k=["vg_h"], vg_k_s=["vg_f_s"])
        self.assertEqual(check_variants.check(fns(calls), "vg_k vg_k_s"), [])

    def test_helper_still_needed(self):
        for name, calls, rust in [
            # The Rust code uses `g`.
            ("used", dict(self.BASE, vg_k=["vg_g"], vg_k_s=["vg_f_s"]), "vg_g vg_k vg_k_s"),
            # `k_s` calls `g`, and so the baseline `f`.
            ("called", dict(self.BASE, vg_k=["vg_g"], vg_k_s=["vg_g", "vg_f_s"]), "vg_k vg_k_s"),
            # `k` has no variant for `f_s`.
            ("no variant", dict(self.BASE, vg_k=["vg_g"]), "vg_k vg_f_s"),
        ]:
            with self.subTest(name):
                errors = check_variants.check(fns(calls), rust)
                self.assertEqual(len(errors), 1)
                self.assertIn("vg_g calls vg_f, which has the variant vg_f_s, but there is no",
                              errors[0])

    def test_variant_unused(self):
        calls = dict(self.BASE, vg_g_s=["vg_f_s"])
        errors = check_variants.check(fns(calls), "vg_g")
        self.assertEqual(len(errors), 1)
        self.assertIn("the variant vg_g_s is neither called", errors[0])

    def test_variant_used_through_another_name(self):
        # `g_s` is the code of `g_t`, which the Rust code uses only by the
        # name `g_s`.
        calls = dict(self.BASE, vg_g_s=["vg_f_s"], vg_g_t=["vg_f_s"])
        names = {"x": {"vg_g_s": "vg_g_t"}}
        self.assertEqual(check_variants.check(fns(calls), "vg_g vg_g_s", names=names), [])
        self.assertEqual(len(check_variants.check(fns(calls), "vg_g vg_g_s")), 1)


class Internal(unittest.TestCase):
    # Internal functions (`fn <name>()`, no signature): `vg_f` with the variant
    # `vg_f_s`, whose suffix a function with a signature has (`vg_g_s`), and
    # `vg_f_mod`, whose suffix none has, nor `vg_f_x`, whose suffix is only a
    # word of one (`vg_g_x_s`).
    def targets(self, calls):
        out = {}
        for name, callees in calls.items():
            sig = check_variants.INTERNAL if name.startswith("vg_f") else SIG
            out[name] = (sig, set(callees))
        return {"x": out}

    def test_variants(self):
        t = self.targets({"vg_f": [], "vg_f_s": [], "vg_f_mod": [], "vg_f_x": [],
                          "vg_g": ["vg_f", "vg_f_mod", "vg_f_x"],
                          "vg_g_s": ["vg_f_s", "vg_f_mod", "vg_f_x"], "vg_g_x_s": ["vg_f", "vg_f_mod", "vg_f_x"]})["x"]
        self.assertEqual(check_variants.variants(t), {"vg_g_s": ("vg_g", "s"), "vg_g_x_s": ("vg_g", "x_s"),
                                                      "vg_f_s": ("vg_f", "s")})

    def test_qualified_part(self):
        # `vg_f_t_s`'s suffix is a qualified part of `vg_g_t_s_u_s`'s whose
        # `s` is a suffix (`vg_k_s`'s); `vg_f_u` has no such `<suffix>`.
        t = self.targets({"vg_f": [], "vg_f_t_s": [], "vg_f_u": [], "vg_k": [], "vg_k_s": [],
                          "vg_g": ["vg_f"], "vg_g_t_s_u_s": ["vg_f_t_s"]})["x"]
        self.assertEqual(check_variants.variants(t), {"vg_k_s": ("vg_k", "s"),
                                                      "vg_g_t_s_u_s": ("vg_g", "t_s_u_s"),
                                                      "vg_f_t_s": ("vg_f", "t_s")})

    def test_flow(self):
        calls = {"vg_f": [], "vg_f_s": [], "vg_g": ["vg_f"], "vg_g_s": ["vg_f"], "vg_h": [],
                 "vg_h_s": []}
        errors = check_variants.check(self.targets(calls), "vg_g vg_g_s vg_h vg_h_s")
        self.assertEqual(len(errors), 2)
        self.assertIn("vg_g_s, the variant of vg_g for vg_f_s, calls the baseline vg_f", errors[0])
        self.assertIn("the variant vg_f_s is neither called", errors[1])
        calls["vg_g_s"] = ["vg_f_s"]
        self.assertEqual(check_variants.check(self.targets(calls), "vg_g vg_g_s vg_h vg_h_s"), [])

    def test_read(self):
        text = """// @generated
pub(crate) const VG_F_S_FEATURES: verified_garbage_cpu::Features = verified_garbage_cpu::Features(verified_garbage_cpu::feature::SHA);

/// An internal function.
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_f_s() {
    core::arch::naked_asm!(
        r"ret",
        vg_k = sym crate::internal::vg_k::vg_k,
    )
}
"""
        fs = check_variants.functions([("x", text)])["x"]
        self.assertEqual(fs, {"vg_f_s": (check_variants.INTERNAL, {"vg_k"})})
        self.assertEqual(check_variants.features([("x", text)]), {"x": {"vg_f_s": frozenset({"sha"})}})
        self.assertEqual(check_variants.unread([("x", text)]), [])


class Aliases(unittest.TestCase):
    TEXT = (
        'pub(crate) unsafe extern "C" fn vg_g(out: *mut u8) {\n'
        "    core::arch::naked_asm!(\n"
        '        "call {vg_f}",\n'
        "        vg_f = sym super::f::vg_f,\n"
        "    )\n"
        "}\n"
        "#[allow(unused_imports)]\n"
        "pub(crate) use self::vg_g as vg_g_s;\n"
    )

    def test_public_items(self):
        # A target's crate's items are `pub`.
        text = self.TEXT.replace("pub(crate) ", "pub ")
        targets = check_variants.functions([("x", text)])
        self.assertEqual(targets["x"]["vg_g_s"], targets["x"]["vg_g"])
        self.assertEqual(targets["x"]["vg_g"][1], {"vg_f"})

    def test_unread_items_fail(self):
        # Items written in a form the script does not read are errors, not
        # items quietly left unchecked.
        read = "#[unsafe(naked)]\n" + self.TEXT + (
            "pub const VG_G_FEATURES: crate::cpu::Features = "
            "crate::cpu::Features(crate::cpu::feature::AVX);\n")
        self.assertEqual(check_variants.unread([("x", read)]), [])
        # Named by its crate rather than its alias, `crate::cpu`.
        named = read.replace("crate::cpu::", "verified_garbage_cpu::")
        self.assertEqual(check_variants.unread([("x", named)]), [])
        self.assertEqual(check_variants.features([("x", named)]), {"x": {"vg_g": frozenset({"avx"})}})
        unread = read.replace("pub(crate) ", "pub(in crate) ").replace("pub const", "pub(in crate) const")
        self.assertEqual(check_variants.unread([("x", unread)]), [
            "x: read 0 of the 1 naked functions of a generated file",
            "x: read 0 of the 1 other names of a generated file",
            "x: read 0 of the 1 _FEATURES constants of a generated file",
        ])

    def test_another_name_is_the_function(self):
        targets = check_variants.functions([("x", self.TEXT)])
        self.assertEqual(targets["x"]["vg_g_s"], targets["x"]["vg_g"])
        self.assertEqual(targets["x"]["vg_g"][1], {"vg_f"})
        self.assertEqual(check_variants.all_aliases([("x", self.TEXT)]),
                         {"x": {"vg_g_s": "vg_g"}})



class BestCallee(unittest.TestCase):
    # `f` has `f_a` (feature a) and `f_ab` (a and b); `g` has `g_ab`, which
    # needs a and b.
    BASE = {"vg_f": [], "vg_f_a": [], "vg_f_ab": [], "vg_g": ["vg_f"]}
    FEATS = {"x": {"vg_f_a": frozenset("a"), "vg_f_ab": frozenset("ab"), "vg_g_ab": frozenset("ab")}}
    RUST = "vg_g vg_g_ab vg_f_a"

    def check(self, **calls):
        return check_variants.best_callees("x", fns(dict(self.BASE, **calls))["x"],
                                           check_variants.variants(fns(dict(self.BASE, **calls))["x"]),
                                           self.FEATS["x"])

    def test_calls_the_best(self):
        self.assertEqual(self.check(vg_g_ab=["vg_f_ab"]), [])

    def test_calls_a_lesser_variant(self):
        errors = self.check(vg_g_ab=["vg_f_a"])
        self.assertEqual(len(errors), 1)
        self.assertIn("x: vg_g_ab (features a, b) calls vg_f_a, but no implementation of vg_g "
                      "calls vg_f_ab", errors[0])

    def test_another_combination_calls_it(self):
        # `g_ab` calls `f_a`, but `g_ab_x`, which needs no more, calls `f_ab`.
        self.assertEqual(self.check(vg_g_ab=["vg_f_a"], vg_g_ab_x=["vg_f_ab"]), [])

    def test_needs_more_than_the_caller(self):
        # `f_ab` needs b, which `g_a` does not have.
        feats = dict(self.FEATS["x"], vg_g_a=frozenset("a"))
        calls = dict(self.BASE, vg_g_a=["vg_f_a"])
        self.assertEqual(check_variants.best_callees("x", fns(calls)["x"],
                                                     check_variants.variants(fns(calls)["x"]), feats), [])

    def test_variant_calling_its_baseline(self):
        # `f_ab` calls the baseline `f` for a tail: exempt.
        self.assertEqual(self.check(vg_f_ab=["vg_f"], vg_g_ab=["vg_f_ab"]), [])

    def test_through_check(self):
        calls = dict(self.BASE, vg_g_ab=["vg_f_a"])
        errors = check_variants.check(fns(calls), self.RUST, self.FEATS)
        self.assertTrue(any("no implementation of vg_g calls vg_f_ab" in e for e in errors))


class NeverWith(unittest.TestCase):
    # ChaCha20-Poly1305's shape: `g` calls `h` (a cipher, with `h_ssse3`
    # and `h_avx2`) and `f` (a MAC, with `f_avx2`); the Rust code never
    # chooses `h_ssse3` with avx and avx2, so no CPU chooses `g_ssse3_avx2`.
    CALLS = {
        "vg_h": [], "vg_h_ssse3": [], "vg_h_avx2": [], "vg_f": [], "vg_f_avx2": [],
        "vg_g": ["vg_h", "vg_f"], "vg_g_ssse3": ["vg_h_ssse3", "vg_f"],
        "vg_g_avx2": ["vg_h_avx2", "vg_f_avx2"],
    }
    FEATS = {"x": {"vg_h_ssse3": frozenset({"ssse3"}), "vg_h_avx2": frozenset({"avx", "avx2"}),
                   "vg_f_avx2": frozenset({"avx", "avx2"}), "vg_g_ssse3": frozenset({"ssse3"}),
                   "vg_g_avx2": frozenset({"avx", "avx2"})}}
    RUST = "vg_g vg_g_ssse3 vg_g_avx2"

    def check(self, never_with, calls=None):
        return check_variants.check(fns(calls or self.CALLS), self.RUST, self.FEATS, never_with=never_with)

    def test_combination_required_without_an_entry(self):
        errors = self.check({})
        self.assertEqual(len(errors), 1)
        self.assertIn("vg_g_ssse3 calls vg_f, which has the variant vg_f_avx2, but there is no "
                      "vg_g_ssse3_avx2", errors[0])

    def test_combination_no_cpu_chooses(self):
        self.assertEqual(self.check({"x": {"vg_h_ssse3": [{"avx", "avx2"}]}}), [])

    def test_entry_must_cover_the_combination(self):
        # Never chosen with avx512f, or with avx2 and sha, says nothing
        # about CPUs with avx and avx2.
        errors = self.check({"x": {"vg_h_ssse3": [{"avx512f"}, {"avx2", "sha"}]}})
        self.assertEqual(len(errors), 1)
        self.assertIn("there is no vg_g_ssse3_avx2", errors[0])

    def test_entry_must_name_an_implementation_the_caller_runs(self):
        # An entry for a function `g_ssse3` neither is nor calls excuses nothing.
        calls = dict(self.CALLS, vg_m=[], vg_m_ssse3=[])
        feats = {"x": dict(self.FEATS["x"], vg_m_ssse3=frozenset({"ssse3"}))}
        errors = check_variants.check(fns(calls), self.RUST + " vg_m vg_m_ssse3", feats,
                                      never_with={"x": {"vg_m_ssse3": [{"avx", "avx2"}]}})
        self.assertEqual(len(errors), 1)
        self.assertIn("there is no vg_g_ssse3_avx2", errors[0])

    def test_entry_must_not_exclude_its_own_features(self):
        errors = self.check({"x": {"vg_h_ssse3": [{"avx", "avx2"}], "vg_h_avx2": [{"avx2"}]}})
        self.assertEqual(errors, ["x: NEVER_WITH says vg_h_avx2 is never chosen with avx2, which it "
                                  "needs itself: it could never be chosen"])

    def test_entry_must_name_a_generated_function(self):
        errors = self.check({"x": {"vg_h_sse9": [{"avx2"}]}})
        self.assertIn("x: NEVER_WITH names vg_h_sse9, which is not a generated function", errors[0])


class Qualified(unittest.TestCase):
    # A caller of two interfaces whose variants share the suffix `a`: `h`
    # (with `h_a`) and `f` (with `f_a`), its instances qualified by the tags
    # `p` and `q`.
    CALLS = {
        "vg_h": [], "vg_h_a": [], "vg_f": [], "vg_f_a": [],
        "vg_g": ["vg_h", "vg_f"], "vg_g_p_a": ["vg_h_a", "vg_f"], "vg_g_q_a": ["vg_h", "vg_f_a"],
        "vg_g_p_a_q_a": ["vg_h_a", "vg_f_a"],
    }
    RUST = "vg_g vg_g_p_a vg_g_q_a vg_g_p_a_q_a"

    def test_qualified(self):
        self.assertEqual(check_variants.check(fns(self.CALLS), self.RUST), [])

    def test_qualified_part_in_any_position(self):
        # Only the combination: its first part is the variant for `h_a`, its
        # second the one for `f_b` (as DSA's `_sha1_avx_bmi_sha256_avx2`).
        calls = {"vg_h": [], "vg_h_a": [], "vg_f": [], "vg_f_b": [],
                 "vg_g": ["vg_h", "vg_f"], "vg_g_p_a_q_b": ["vg_h_a", "vg_f_b"]}
        self.assertEqual(check_variants.check(fns(calls), "vg_g vg_g_p_a_q_b"), [])

    def test_qualified_missing(self):
        calls = {k: v for k, v in self.CALLS.items() if k != "vg_g_p_a_q_a"}
        errors = check_variants.check(fns(calls), "vg_g vg_g_p_a vg_g_q_a")
        self.assertEqual(len(errors), 2)
        self.assertIn("vg_g_p_a calls vg_f, which has the variant vg_f_a, but there is no", errors[0])

    def test_qualified_must_not_call_baseline(self):
        calls = dict(self.CALLS, vg_g_q_a=["vg_h", "vg_f"])
        errors = check_variants.check(fns(calls), self.RUST)
        self.assertEqual(len(errors), 1)
        self.assertIn("x: vg_g_p_a, vg_g_q_a all call the baseline vg_f", errors[0])

    def test_qualified_does_the_work_itself(self):
        calls = dict(self.CALLS, vg_g_q_a=["vg_h"], vg_g_p_a_q_a=["vg_h_a"])
        self.assertEqual(check_variants.check(fns(calls), self.RUST + " vg_f_a"), [])


def production(files):
    """The production Rust code of a crate whose `src/` has `files`."""
    with tempfile.TemporaryDirectory() as d:
        src = pathlib.Path(d).resolve() / "src"
        for name, text in files.items():
            (src / name).parent.mkdir(parents=True, exist_ok=True)
            (src / name).write_text(text)
        return check_variants.production_rust(src)


def used(rust):
    return {t for t in rust.split() if t.startswith("vg_")}


class TestCode(unittest.TestCase):
    def test_items(self):
        rust = production({"lib.rs": """
            fn a() { vg_a(); }
            #[cfg(test)]
            mod tests {
                fn t() { vg_t1(); let s = "}"; let c = '}'; let l: &'static str = r#"{"#; }
                /* } */ // }
                fn u() { vg_t2(); }
            }
            #[cfg(all(test, target_arch = "aarch64"))]
            #[allow(unused)]
            fn t3() -> [u8; 2] { vg_t3(); [0; 2] }
            #[cfg(any(test, feature = "x"))]
            fn b() { vg_b(); }
            #[cfg(not(test))]
            fn c() { vg_c(); }
            #[test]
            fn t4() { vg_t4(); }
            #[cfg(test)]
            use crate::arch::vg_t5;
            #[cfg(test)]
            const T6: [u8; 1] = { vg_t6(); [0] };
            fn d() {
                #[cfg(test)]
                vg_t7();
                vg_d();
                let s = Struct {
                    #[cfg(test)]
                    t: vg_t8(),
                    e: vg_e(),
                };
            }
            macro_rules! m {
                () => {
                    #[cfg(all(test, target_arch = "aarch64"))]
                    mod tests { fn t() { $crate::vg_t9(); } }
                    fn f() { vg_f(); }
                };
            }
        """})
        self.assertEqual(used(rust), {"vg_a", "vg_b", "vg_c", "vg_d", "vg_e", "vg_f"})

    def test_comments_and_strings(self):
        # A comment or string does not end a test item early.
        rust = production({"lib.rs": r"""
            #[cfg(test)]
            mod tests {
                /* nested /* } */ } */
                const S: &str = "\"}";
                const B: &[u8] = br"}";
                const C: char = '\'';
                fn t() { vg_t(); }
            }
            fn a() { vg_a(); }
        """})
        self.assertEqual(used(rust), {"vg_a"})

    def test_files(self):
        rust = production({
            "lib.rs": """
                mod a;
                #[cfg(test)]
                mod tests;
                #[cfg(all(test, target_arch = "aarch64"))]
                #[path = "other_tests.rs"]
                mod other;
                #[cfg(test)]
                mod inline { mod nested; }
                mod inner;
            """,
            "a.rs": "fn a() { vg_a(); }",
            "tests.rs": "mod helpers; fn t() { vg_t1(); }",
            "tests/helpers.rs": "fn t() { vg_t2(); }",
            "other_tests.rs": "fn t() { vg_t3(); }",
            "inline/nested.rs": "fn t() { vg_t4(); }",
            "inner.rs": "#![cfg(test)]\nfn t() { vg_t5(); }",
        })
        self.assertEqual(used(rust), {"vg_a"})


class Avoided(unittest.TestCase):
    # `g` calls `f`, which has `f_vaes`; `g_aesni` needs only `aes` and
    # calls none of `f`'s implementations.
    CALLS = {"vg_f": [], "vg_f_vaes": [], "vg_k": [], "vg_g": ["vg_f"], "vg_g_aesni": ["vg_k"]}
    FEATS = {"x": {"vg_f_vaes": frozenset({"aes", "vaes"}), "vg_g_aesni": frozenset({"aes"})}}
    RUST = "vg_g vg_g_aesni vg_f_vaes"

    def check(self, calls, feats=None):
        return check_variants.check(fns(calls), self.RUST, feats or self.FEATS)

    def test_no_variant_needed(self):
        self.assertEqual(self.check(self.CALLS), [])

    def test_needs_more_features(self):
        feats = {"x": dict(self.FEATS["x"], vg_g_aesni=frozenset({"aes", "avx512f"}))}
        errors = self.check(self.CALLS, feats)
        self.assertEqual(len(errors), 1)
        self.assertIn("there is no vg_g_vaes", errors[0])

    def test_another_implementation_calls_the_baseline(self):
        calls = dict(self.CALLS, vg_g_avx=["vg_f"])
        feats = {"x": dict(self.FEATS["x"], vg_g_avx=frozenset({"aes"}))}
        errors = check_variants.check(fns(calls), self.RUST + " vg_g_avx", feats)
        self.assertTrue(any("vg_g calls vg_f, which has the variant vg_f_vaes, but there is "
                            "no vg_g_vaes" in e for e in errors), errors)


if __name__ == "__main__":
    unittest.main()
