import unittest

import check_residue_allowlist as c


class Test(unittest.TestCase):
    def test_entries_skip_comments_and_blanks(self):
        self.assertEqual(c.entries("# c\n\nx86_64  vg_a\n  x86_64 vg_b  \n"), {"x86_64 vg_a", "x86_64 vg_b"})

    def test_removal_is_fine(self):
        self.assertEqual(c.added("x86_64 vg_a\nx86_64 vg_b\n", "x86_64 vg_a\n"), [])

    def test_addition_is_reported(self):
        self.assertEqual(c.added("x86_64 vg_a\n", "x86_64 vg_a\nx86_64 vg_c\n# x86_64 vg_d\n"), ["x86_64 vg_c"])

    def test_reordering_and_spacing_are_not_additions(self):
        self.assertEqual(c.added("x86_64 vg_a\nx86_64 vg_b\n", "x86_64   vg_b\nx86_64 vg_a\n"), [])

    def test_a_target_not_yet_required_may_list_its_functions(self):
        self.assertEqual(c.added("x86_64 vg_a\n", "x86_64 vg_a\narm vg_b\nx86_64 vg_c\n", frozenset({"arm"})),
                         ["x86_64 vg_c"])

    def test_target_requires(self):
        t = ('@[reducible] def target : Target where\n  name := "arm"\n  isa := isa\n'
             '  noResidue := some NoResidue\n\nend VG.Arm\n')
        self.assertEqual(c.target_requires(t), ("arm", True))
        self.assertEqual(c.target_requires(t.replace("  noResidue := some NoResidue\n", "")), ("arm", False))
        self.assertIsNone(c.target_requires("def abi : Abi isa where\n"))


if __name__ == "__main__":
    unittest.main()
