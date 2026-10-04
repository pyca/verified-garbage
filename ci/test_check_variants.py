"""Tests for the variant checker's composition of suffixes."""

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

    def test_composition_must_call_both(self):
        calls = dict(self.BASE, vg_g_a_b=["vg_h_a", "vg_f"])
        errors = check_variants.check(fns(calls), self.RUST + " vg_g_a_b")
        self.assertEqual(errors, ["x: vg_g_a_b does not call vg_f_b"])



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

    def test_qualified_missing(self):
        calls = {k: v for k, v in self.CALLS.items() if k != "vg_g_p_a_q_a"}
        errors = check_variants.check(fns(calls), "vg_g vg_g_p_a vg_g_q_a")
        self.assertEqual(len(errors), 2)
        self.assertIn("vg_g_p_a calls vg_f, which has the variant vg_f_a, but there is no", errors[0])

    def test_qualified_must_call(self):
        calls = dict(self.CALLS, vg_g_q_a=["vg_h", "vg_f"])
        errors = check_variants.check(fns(calls), self.RUST)
        self.assertEqual(errors, ["x: none of vg_g_p_a, vg_g_q_a calls vg_f_a"])


if __name__ == "__main__":
    unittest.main()
