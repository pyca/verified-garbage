"""Regression tests for the AES round-pair checker."""

import contextlib
import io
import pathlib
import tempfile
import unittest
from unittest.mock import patch

import check_aes_pairs


def check(instrs, labels=None):
    return check_aes_pairs.check_function("f", instrs, list(range(len(instrs))), labels or {})


class Pairs(unittest.TestCase):
    def test_adjacent(self):
        self.assertEqual(
            check(["aese v0.16b, v1.16b", "aesmc v0.16b, v0.16b",
                   "aesd v2.16b, v1.16b", "aesimc v2.16b, v2.16b"]),
            ([], 2),
        )

    def test_split(self):
        errors, pairs = check(["aese v0.16b, v30.16b", "pmull v28.1q, v21.1d, v23.1d",
                               "aesmc v0.16b, v0.16b"])
        self.assertEqual(pairs, 1)
        self.assertEqual(errors, [
            "f:0: `aese v0.16b, v30.16b` and its `aesmc v0.16b, v0.16b` (line 2) "
            "are not adjacent, so they do not fuse: "
            "`pmull v28.1q, v21.1d, v23.1d` is between them"])

    def test_not_a_pair(self):
        # A final round, a key schedule's SubWord read through another form
        # of the register, and an `aesmc` of another register.
        self.assertEqual(
            check(["aese v0.16b, v1.16b", "eor v0.16b, v0.16b, v2.16b",
                   "aese v3.16b, v4.16b", "nop", "umov w5, v3.s[0]", "aesmc v3.16b, v3.16b",
                   "aese v6.16b, v1.16b", "aesmc v7.16b, v7.16b", "str q6, [x0]"]),
            ([], 0),
        )

    def test_other_forms_of_the_register(self):
        # `ldr q0` writes v0 between the two.
        self.assertEqual(
            check(["aese v0.16b, v1.16b", "ldr q0, [x1]", "aesmc v0.16b, v0.16b"]), ([], 0))

    def test_straight_line_code_only(self):
        # A label or a branch between them ends the search.
        self.assertEqual(
            check(["aese v0.16b, v1.16b", "nop", "aesmc v0.16b, v0.16b"], {"2": [1]}), ([], 0))
        self.assertEqual(
            check(["aese v0.16b, v1.16b", "b.ne 2f", "aesmc v0.16b, v0.16b"]), ([], 0))

    def test_main(self):
        text = '\n'.join([
            '// generated code',
            'pub(crate) unsafe extern "C" fn vg_first() {',
            '    naked_asm!(',
            '        "aese v0.16b, v1.16b',
            'aesmc v0.16b, v0.16b",',
            '    );',
            '}',
            '',
            'pub(crate) unsafe extern "C" fn vg_second() {',
            '    naked_asm!(',
            '        "aese v0.16b, v1.16b",',
            '        "eor v2.16b, v2.16b, v3.16b",',
            '        "aesmc v0.16b, v0.16b",',
            '    );',
            '}',
        ])
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            path = root / "src" / "asm" / check_aes_pairs.TARGET / "test.rs"
            path.parent.mkdir(parents=True)
            path.write_text(text)
            stderr = io.StringIO()
            with patch.object(check_aes_pairs, "ROOT", root), patch.object(
                check_aes_pairs, "ASM", root / "src" / "asm"
            ), contextlib.redirect_stderr(stderr):
                self.assertEqual(check_aes_pairs.main(), 1)
        self.assertEqual(stderr.getvalue().splitlines(), [
            "src/asm/aarch64/test.rs (vg_second):11: `aese v0.16b, v1.16b` and its "
            "`aesmc v0.16b, v0.16b` (line 13) are not adjacent, so they do not fuse: "
            "`eor v2.16b, v2.16b, v3.16b` is between them"])


if __name__ == "__main__":
    unittest.main()
