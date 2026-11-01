"""The groups of tests that `rust-cpu-features`' lines run (cpu_tests.py)."""

from pathlib import Path
import tomllib
import unittest
from unittest import mock

import cpu_tests
from cpu_shards import parse_runs

CI = Path(__file__).resolve().parent
MATRIX = CI / "rust_matrix.toml"

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

    def test_cavp_tests_run_in_their_own_binary(self):
        self.assertTrue(cpu_tests.runs_in("cavp", "cavp::aes_gcm::aes_gcm"))
        self.assertFalse(cpu_tests.runs_in("cavp", "wycheproof::aes_gcm::aes_gcm"))
        self.assertTrue(cpu_tests.runs_in("tests", "wycheproof::aes_gcm::aes_gcm"))
        self.assertFalse(cpu_tests.runs_in("tests", "cavp::aes_gcm::aes_gcm"))
        self.assertTrue(cpu_tests.runs_in("lib", "aes_gcm::tests::round_trip"))

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
    def test_the_matrix_names_only_groups(self):
        self.assertEqual(cpu_tests.lint(MATRIX.read_text()), [])

    def test_an_unknown_group_or_a_bad_path_is_an_error(self):
        text = MATRIX.read_text().replace(" | aes_gcm cpu\n", " | aes_gcm cpu aes_gcmm\n", 1)
        self.assertEqual(cpu_tests.lint(text), ["aes_gcmm: not a group of ci/cpu_tests.py"])
        with mock.patch.dict(cpu_tests.GROUPS, {"x": {"lib": ["a::"], "tests": []}}):
            self.assertIn("group x: lib path 'a::' is not a path", cpu_tests.lint(MATRIX.read_text()))

    def test_a_repeated_value_of_vg_cpu_features_is_an_error(self):
        text = MATRIX.read_text().replace("\nneon | chacha20\n", "\nneon | chacha20\nneon | cpu\n", 1)
        self.assertEqual(cpu_tests.lint(text), ["native: VG_CPU_FEATURES=neon twice"])


class RsaEmulationTests(unittest.TestCase):
    def selected(self, chip, binary, listed, emulated=False):
        cpu = next(c for c in tomllib.loads(MATRIX.read_text())["cpu"] if c["chip"] == chip)
        runs = cpu_tests.emulated_rsa_runs(chip, cpu["runs"]) if emulated else cpu["runs"]
        return [set(cpu_tests.select(binary, listed, groups.split()))
                for _, groups in parse_runs(runs)]

    def test_icx_keeps_ifma_vectors_without_repeating_prime_generation_or_stress(self):
        # Include a test for every path, so select also checks that no group
        # silently selects nothing. Add expensive native checks to ensure
        # broad module paths do not bring them back into the emulated run.
        listed = {b: sorted({p + "::test" for g in cpu_tests.GROUPS.values() for p in g[b]})
                  for b in cpu_tests.BINARIES}
        # Exact test paths must be represented by themselves, too.
        for b in cpu_tests.BINARIES:
            listed[b] += [p for g in cpu_tests.GROUPS.values() for p in g[b]]
        expensive = {"wycheproof::rsa_keygen::rsa_keygen_primes",
                     "wycheproof::rsa_keygen::rsa_keygen_composites",
                     "wycheproof::rsa_pss::rsa_pss_sign_test",
                     "wycheproof::rsa_oaep::rsa_shared_key_leases"}
        listed["tests"] += list(expensive)
        selectors = {"rsa_pss::sha256::tests::backend_features",
                     "rsa_oaep::sha256::tests::backend_features"}
        listed["lib"] += list(selectors)
        runs = self.selected("icx", "tests", listed, emulated=True)
        self.assertFalse(set.union(*runs) & expensive)
        for path in ["wycheproof::rsa::rsa_oaep_test", "wycheproof::rsa_pkcs1_enc::rsa_pkcs1_test",
                     "wycheproof::rsa_pss::rsa_pss_large_keys",
                     "wycheproof::rsa_oaep::rsa_shared_key_leases_smoke"]:
            listed["tests"].append(path)
            self.assertEqual(sum(path in r for r in self.selected("icx", "tests", listed, emulated=True)), 1, path)
        lib = set.union(*self.selected("icx", "lib", listed, emulated=True))
        self.assertIn("rsa_keygen::tests::generate_small_d", lib)
        self.assertNotIn("rsa_keygen::test", lib)
        self.assertFalse(lib & selectors)
        # The full suites still belong to native and SKX runs.
        for chip in ("native", "skx", "icx"):
            self.assertTrue(expensive <= set.union(*self.selected(chip, "tests", listed)))
            self.assertTrue(selectors <= set.union(*self.selected(chip, "lib", listed)))

    def test_full_hosts_may_leave_optional_emulation_groups_unused(self):
        listed = {b: [p for g in cpu_tests.GROUPS.values() for p in g[b]]
                  for b in cpu_tests.BINARIES}
        records = [{"cpu": c["chip"], "groups": cpu_tests.runs_groups(c["runs"]), "tests": listed}
                   for c in tomllib.loads(MATRIX.read_text())["cpu"]]
        self.assertEqual(cpu_tests.check(records), [])

    def test_reduction_preserves_feature_lines_and_other_cpus(self):
        for cpu in tomllib.loads(MATRIX.read_text())["cpu"]:
            runs = cpu["runs"]
            reduced = cpu_tests.emulated_rsa_runs(cpu["chip"], runs)
            self.assertEqual([f for f, _ in parse_runs(runs)],
                             [f for f, _ in parse_runs(reduced)])
            if cpu["chip"] not in ("icx", "dmr"):
                self.assertEqual(reduced, runs)

    def test_hash_only_runs_keep_pss_and_oaep_combinations(self):
        for group, paths in {
            "rsa_pkcs1_hashes": ["rsa_guidance::rsa_pkcs1_appendix_b_small"],
            "rsa_oaep_pairs": ["wycheproof::rsa_oaep::rsa_oaep_every_pair"],
            "rsa_pss_hashes": ["wycheproof::rsa_pss::rsa_pss_every_hash"],
        }.items():
            listed = {"lib": [], "tests": paths + ["wycheproof::rsa_pss::rsa_pss_sign_test"]}
            self.assertEqual(cpu_tests.select("tests", listed, [group]), paths)


if __name__ == "__main__":
    unittest.main()
