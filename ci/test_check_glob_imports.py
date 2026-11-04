import unittest

from check_glob_imports import globs


class Globs(unittest.TestCase):
    def test_globs(self):
        self.assertEqual(globs("use super::*;\n"), [1])
        self.assertEqual(globs("fn f() {}\n    pub use a::b::*;\n"), [2])
        self.assertEqual(globs("use a::{self, *};\n"), [1])
        self.assertEqual(globs("use a::{\n    b,\n    *,\n};\n"), [1])
        self.assertEqual(globs("use a::{b::{c, *}, d};\n"), [1])
        self.assertEqual(globs("macro_rules! m { () => { use super::*; } }\n"), [1])

    def test_named(self):
        self.assertEqual(globs("use super::{a, b};\nuse c::d as e;\n"), [])
        self.assertEqual(globs("use a::{self, b};\nlet x = *y;\n"), [])
        self.assertEqual(globs("use super::{$($req),*};\n"), [])

    def test_comments_and_strings(self):
        self.assertEqual(globs("// use super::*;\n/* use a::*; */\n"), [])
        self.assertEqual(globs('let s = "use a::*;";\nlet c = \'*\';\n'), [])
        self.assertEqual(globs('let s = r#"use a::*;"#;\n'), [])
        self.assertEqual(globs("/* /* nested */ use a::*; */\nuse b::*;\n"), [2])


if __name__ == "__main__":
    unittest.main()
