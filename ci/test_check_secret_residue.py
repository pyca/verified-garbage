"""Tests of ci/check_secret_residue.py: which buffer moves need a reason."""

import pathlib
import tempfile
import unittest

import check_secret_residue as c


class Calls(unittest.TestCase):
    def test_unjustified_calls(self):
        text = (
            "fn f(out: &mut Vec<u8>, l: usize) {\n"
            "    out.drain(..l);\n"
            "    out.truncate(l);\n"
            "    out.extend_from_slice(&[1]);\n"
            "    out.copy_within(1.., 0);\n"
            "    out.resize :: <> (3, 0);\n"
            "}\n"
        )
        self.assertEqual(
            c.violations_in(text),
            [(2, "drain"), (3, "truncate"), (4, "extend_from_slice"), (5, "copy_within"), (6, "resize")],
        )

    def test_marker_on_the_line_or_in_the_comments_above(self):
        text = (
            "fn f(out: &mut Vec<u8>) {\n"
            "    out.truncate(1); // NO-SECRET-RESIDUE: zeros after it\n"
            "    // The message.\n"
            "    // NO-SECRET-RESIDUE: zeros after it,\n"
            "    // by the contract.\n"
            "    out.truncate(1);\n"
            "    // NO-SECRET-RESIDUE: only covers the comment block it ends.\n"
            "    let x = 1;\n"
            "    out.truncate(x);\n"
            "}\n"
        )
        self.assertEqual(c.violations_in(text), [(9, "truncate")])

    def test_marker_needs_a_reason(self):
        text = "fn f(o: &mut Vec<u8>) {\n    o.truncate(1); // NO-SECRET-RESIDUE:\n}\n"
        self.assertEqual(c.violations_in(text), [(2, "truncate")])

    def test_not_calls(self):
        # Comments, strings, other methods and names that only start alike.
        text = (
            "// out.drain(..)\n"
            "/* out.truncate(1) /* nested */ out.push(1) */\n"
            'const S: &str = "out.push(1)";\n'
            'const R: &str = r#"out.push(1) " still"#;\n'
            "const C: char = '.';\n"
            "fn f<'a>(o: &'a mut Vec<u8>) { o.pushes(); o.len(); o.truncated(); }\n"
        )
        self.assertEqual(c.violations_in(text), [])

    def test_code_only_keeps_offsets(self):
        text = 'a // b\n"x\\"y" /* c\nd */ e'
        code = c.code_only(text)
        self.assertEqual(len(code), len(text))
        self.assertEqual(code.count("\n"), text.count("\n"))
        self.assertNotIn("b", code)
        self.assertNotIn("x", code)
        self.assertIn("e", code)


class TestCode(unittest.TestCase):
    def test_cfg_test_items_are_skipped(self):
        text = (
            "fn f(o: &mut Vec<u8>) { o.push(1); }\n"
            "#[cfg(test)]\n"
            "fn helper(o: &mut Vec<u8>) { if true { o.push(1); } }\n"
            "#[cfg(test)]\n"
            "mod tests {\n"
            "    #[test]\n"
            "    fn t() { let mut v = vec![]; v.push(1); }\n"
            "}\n"
            "fn g(o: &mut Vec<u8>) { o.push(2); }\n"
        )
        self.assertEqual(c.violations_in(text), [(1, "push"), (9, "push")])

    def test_test_files_are_skipped(self):
        root = pathlib.Path(tempfile.mkdtemp())
        body = "fn f(o: &mut Vec<u8>) { o.push(1); }\n"
        for name in ["src/a.rs", "src/a/tests.rs", "src/b/vetted_tests.rs"]:
            (root / name).parent.mkdir(parents=True, exist_ok=True)
            (root / name).write_text(body)
        self.assertEqual(len(c.violations(root)), 1)
        self.assertTrue(c.violations(root)[0].startswith("src/a.rs:1:"))


if __name__ == "__main__":
    unittest.main()
