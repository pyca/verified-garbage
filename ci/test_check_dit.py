"""Tests of ci/check_dit.py: which files may give which reasons for public work."""

import pathlib
import tempfile
import unittest

import check_dit


def tree(files: dict[str, str]) -> pathlib.Path:
    root = pathlib.Path(tempfile.mkdtemp())
    for path, text in files.items():
        (root / path).parent.mkdir(parents=True, exist_ok=True)
        (root / path).write_text(text)
    return root


TOMLS = {
    "docs/algorithms/sha256.toml": 'family = "Hashes"\nmodules = ["src/hashes/sha256.rs"]\n',
    "docs/algorithms/hmac-sha256.toml": 'family = "MACs"\nmodules = ["src/hmac/sha256.rs"]\n',
    "docs/algorithms/ml-dsa-44.toml": 'family = "Signatures"\nmodules = ["src/mldsa44.rs"]\n',
    "docs/algorithms/x25519.toml": 'family = "Key agreement"\nmodules = ["src/x25519.rs"]\n',
}


class Families(unittest.TestCase):
    def test_listed_directory_and_common(self):
        listed = check_dit.families(tree(TOMLS))
        self.assertEqual(check_dit.file_families("src/hashes/sha256.rs", listed), {"Hashes"})
        # Unlisted: its directory's, or `<name>*.rs`'s for `<name>_common.rs`.
        self.assertEqual(check_dit.file_families("src/hashes/mod.rs", listed), {"Hashes"})
        self.assertEqual(check_dit.file_families("src/mldsa_common.rs", listed), {"Signatures"})
        self.assertEqual(check_dit.file_families("src/zeroize.rs", listed), set())


class Violations(unittest.TestCase):
    def check(self, files: dict[str, str]) -> list[str]:
        return check_dit.violations(tree({**TOMLS, **files}))

    def test_allowed(self):
        self.assertEqual(self.check({
            "src/hashes/mod.rs": "dit::public(dit::Why::UnkeyedHash)",
            "src/mldsa_common.rs": "public(Why::Verify); public(Why::PublicKey)",
            "src/x25519.rs": "public(Why::PublicKey)",
            "src/zeroize.rs": "public(Why::Wipe)",
            "src/hmac/sha256.rs": "enter!(dit); public(Why::Wipe); public(Why::Test)",
            "src/dit.rs": "Dit::assume() Why::Anything",
        }), [])

    def test_keyed_family_as_public_work(self):
        errors = self.check({"src/hmac/sha256.rs": "\nenter_if!(dit, k, Why::UnkeyedHash)"})
        self.assertEqual(len(errors), 1)
        self.assertIn("src/hmac/sha256.rs:2: `Why::UnkeyedHash` in a file of MACs", errors[0])

    def test_reason_of_another_family(self):
        errors = self.check({"src/x25519.rs": "public(Why::Verify)"})
        self.assertEqual(len(errors), 1)
        self.assertIn("`Why::Verify` in a file of Key agreement", errors[0])

    def test_no_family(self):
        errors = self.check({"src/zeroize.rs": "public(Why::Verify)"})
        self.assertEqual(len(errors), 1)
        self.assertIn("of no algorithm's family", errors[0])

    def test_unknown_reason_and_assume(self):
        errors = self.check({"src/hashes/sha256.rs": "Why::Because\nDit::assume()"})
        self.assertEqual(errors, [
            "src/hashes/sha256.rs:2: only src/dit.rs makes tokens (`Dit::assume`)",
            "src/hashes/sha256.rs:1: unknown reason `Why::Because`",
        ])

    def test_comments_are_skipped(self):
        self.assertEqual(self.check({"src/x25519.rs": "// not `Why::Verify`"}), [])


if __name__ == "__main__":
    unittest.main()
