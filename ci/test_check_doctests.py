import unittest

import check_doctests as c


class CodeBlocks(unittest.TestCase):
    def test_prose_is_not_code(self):
        self.assertEqual(c.code_blocks("/// A key.\n///\n/// * an item\n///   wrapped\nfn f() {}\n"), [])

    def test_fences(self):
        self.assertEqual(c.code_blocks("/// x\n/// ```\n/// f();\n/// ```\n"), [2, 4])
        self.assertEqual(c.code_blocks("//! ~~~\n"), [1])
        self.assertEqual(c.code_blocks('#[doc = concat!("```", "")]\n'), [1])

    def test_indented(self):
        self.assertEqual(c.code_blocks("    ///\n    ///     f();\n"), [2])
        self.assertEqual(c.code_blocks("///\tf();\n"), [1])
        self.assertEqual(c.code_blocks("//// not a doc comment\n////     f();\n"), [])

    def test_manifest(self):
        self.assertTrue(c.doctests_off("[lib]\ndoctest = false\n"))
        self.assertFalse(c.doctests_off("[package]\nname = 'x'\n"))
        self.assertFalse(c.doctests_off("[lib]\ndoctest = true\n"))


if __name__ == "__main__":
    unittest.main()
