"""The groups of tests that `rust-cpu-features`' lines run (cpu_tests.py)."""

from pathlib import Path
import unittest
from unittest import mock

import cpu_tests

CI = Path(__file__).resolve().parent
WORKFLOW = CI.parent / ".github/workflows/ci.yml"

GROUPS = {
    "aes_gcm": {"lib": ["aes_gcm"], "tests": ["wycheproof::aes_gcm"]},
    "sha256": {"lib": ["hashes::sha256"], "tests": ["wycheproof::ecdsa_p256::sha256_test"]},
}

LISTED = {
    "lib": ["aes_gcm::tests::round_trip", "aes_gcm_siv::tests::errors", "hashes::sha256::tests::select"],
    "tests": ["wycheproof::aes_gcm::aes_gcm", "wycheproof::aes_gcm_siv::aes_gcm_siv",
              "wycheproof::ecdsa_p256::sha256_test", "wycheproof::ecdsa_p256::sha256_test_more"],
}


@mock.patch.dict(cpu_tests.GROUPS, GROUPS, clear=True)
class SelectTests(unittest.TestCase):
    def test_a_path_selects_its_test_and_its_module(self):
        self.assertTrue(cpu_tests.selects("aes_gcm", "aes_gcm::tests::round_trip"))
        self.assertTrue(cpu_tests.selects("rfc7748::x448", "rfc7748::x448"))
        # Not a name it is only the start of.
        self.assertFalse(cpu_tests.selects("aes_gcm", "aes_gcm_siv::tests::errors"))
        self.assertFalse(cpu_tests.selects("rfc7748::x448", "rfc7748::x448_vectors"))

    def test_each_binary_gets_its_own_tests(self):
        self.assertEqual(cpu_tests.select("lib", LISTED, ["aes_gcm"]), ["aes_gcm::tests::round_trip"])
        self.assertEqual(cpu_tests.select("tests", LISTED, ["aes_gcm", "sha256"]),
                         ["wycheproof::aes_gcm::aes_gcm", "wycheproof::ecdsa_p256::sha256_test"])

    def test_a_group_selecting_nothing_on_this_cpu_is_an_error(self):
        listed = {"lib": ["aes_gcm::tests::round_trip"], "tests": []}
        self.assertEqual(cpu_tests.select("tests", listed, ["aes_gcm"]), [])
        with self.assertRaises(SystemExit) as e:
            cpu_tests.select("lib", listed, ["sha256"])
        self.assertIn("group sha256 selects no test", str(e.exception))

    def test_an_unknown_group_is_an_error(self):
        with self.assertRaises(SystemExit) as e:
            cpu_tests.groups_of("aes_gcm sha3")
        self.assertIn("sha3", str(e.exception))

    def test_parse_list(self):
        text = "aes_gcm::tests::round_trip: test\nfoo: benchmark\n\n2 tests, 0 benchmarks\n"
        self.assertEqual(cpu_tests.parse_list(text), ["aes_gcm::tests::round_trip"])

    def test_runs_groups(self):
        self.assertEqual(cpu_tests.runs_groups("- | sha256 aes_gcm\nnone | all\n\naes | aes_gcm\n"),
                         ["aes_gcm", "sha256"])


@mock.patch.dict(cpu_tests.GROUPS, GROUPS, clear=True)
class CheckTests(unittest.TestCase):
    def record(self, cpu, groups, lib=(), tests=()):
        return {"cpu": cpu, "groups": groups, "tests": {"lib": list(lib), "tests": list(tests)}}

    def test_every_path_selects_a_test_on_some_cpu(self):
        records = [
            # sha256's unit tests only on x86-64, its line only on aarch64.
            self.record("native x86_64", ["aes_gcm"], LISTED["lib"], LISTED["tests"]),
            self.record("native aarch64", ["sha256"], ["aes_gcm::tests::round_trip"],
                        ["wycheproof::ecdsa_p256::sha256_test"]),
        ]
        self.assertEqual(cpu_tests.check(records), [])

    def test_a_path_selecting_nothing_anywhere_is_an_error(self):
        records = [self.record("native x86_64", ["aes_gcm", "sha256"], ["aes_gcm::tests::round_trip"],
                               ["wycheproof::aes_gcm::aes_gcm"])]
        self.assertEqual(cpu_tests.check(records), [
            "group sha256: lib path hashes::sha256 selects no test on any CPU",
            "group sha256: tests path wycheproof::ecdsa_p256::sha256_test selects no test on any CPU",
        ])

    def test_an_unused_group_is_an_error(self):
        records = [self.record("native x86_64", ["aes_gcm"], LISTED["lib"], LISTED["tests"])]
        self.assertEqual(cpu_tests.check(records), ["group sha256 is used by no CPU's runs"])


class LintTests(unittest.TestCase):
    def test_the_workflow_names_only_groups(self):
        self.assertEqual(cpu_tests.lint(WORKFLOW.read_text()), [])

    def test_an_unknown_group_or_a_bad_path_is_an_error(self):
        text = WORKFLOW.read_text().replace(" | aes_gcm cpu\n", " | aes_gcm cpu aes_gcmm\n", 1)
        self.assertEqual(cpu_tests.lint(text), ["aes_gcmm: not a group of ci/cpu_tests.py"])
        with mock.patch.dict(cpu_tests.GROUPS, {"x": {"lib": ["a::"], "tests": []}}):
            self.assertIn("group x: lib path 'a::' is not a path", cpu_tests.lint(WORKFLOW.read_text()))


if __name__ == "__main__":
    unittest.main()
