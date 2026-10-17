"""The check of each architecture's coverage alone (ci/merge_rust_coverage.py)."""

import contextlib
import io
from pathlib import Path
import tempfile
import unittest

import merge_rust_coverage


def lcov(source, counts):
    """An lcov record of `source`'s lines, with their counts."""
    lines = "".join(f"DA:{line},{count}\n" for line, count in counts.items())
    return f"SF:{source}\n{lines}end_of_record\n"


class Arches(unittest.TestCase):
    def check(self, files):
        with tempfile.TemporaryDirectory() as d:
            d = Path(d)
            source = d / "a.rs"
            source.write_text("fn a() {}\n// NO-COVERAGE-START\nfn b() {}\n// NO-COVERAGE-END\n")
            for name, counts in files.items():
                (d / name).write_text(lcov(source, counts))
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                ok = merge_rust_coverage.check_arches(d)
            return ok, out.getvalue()

    def test_each_architecture_covers_its_lines(self):
        ok, out = self.check({
            "x86_64-1.lcov": {1: 0, 3: 0},
            "x86_64-2.lcov": {1: 2},
            "arm-1.lcov": {1: 1},
        })
        self.assertTrue(ok)
        self.assertIn("arm: 1 of 1 lines covered", out)
        self.assertIn("x86_64: 1 of 1 lines covered", out)

    def test_a_line_only_another_architecture_covers(self):
        ok, out = self.check({
            "x86_64-1.lcov": {1: 1},
            "x86-1.lcov": {1: 0},
        })
        self.assertFalse(ok)
        self.assertIn("x86: 0 of 1 lines covered", out)
        self.assertIn("a.rs:1", out)


if __name__ == "__main__":
    unittest.main()
