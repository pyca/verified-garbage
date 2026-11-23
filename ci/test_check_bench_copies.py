"""ci/bench_copies.py's selection, versions and aggregation; no builds."""

import csv
import pathlib
import tempfile
import unittest

import bench_copies


class Listing(unittest.TestCase):
    def test_bench_names_are_those_with_benchmarks(self):
        listing = "\n".join([
            "sha256: bench",
            "sha256/verified-garbage/64: benchmark",
            "sha256/openssl/64: benchmark",
            "ffdh: bench",  # Nothing on this architecture.
            "x25519: bench",
            "x25519/verified-garbage/32: benchmark",
            "",
        ])
        self.assertEqual(bench_copies.bench_names(listing), ["sha256", "x25519"])
        # A binary that does not name its benchmarks.
        self.assertEqual(bench_copies.bench_names("sha256/openssl/64: benchmark\n"), [])

    def test_openssl_version(self):
        self.assertEqual(bench_copies.openssl_version("openssl: OpenSSL 4.1.0 23 Oct 2026\n"),
                         "OpenSSL 4.1.0 23 Oct 2026")
        self.assertIsNone(bench_copies.openssl_version("sha256/openssl/64: benchmark\n"))


class Versions(unittest.TestCase):
    def test_aws_lc(self):
        lock = {"package": [{"name": "aws-lc-rs", "version": "1.19.0"}, {"name": "aws-lc-sys", "version": "0.47.0"},
                            {"name": "openssl", "version": "0.10.82"}]}
        self.assertEqual(bench_copies.aws_lc_version(lock), "aws-lc-rs 1.19.0 (aws-lc-sys 0.47.0)")
        self.assertIsNone(bench_copies.aws_lc_version({"package": [{"name": "aws-lc-rs", "version": "1.19.0"}]}))
        self.assertIsNone(bench_copies.aws_lc_version({}))

    def test_two_versions_are_both_named(self):
        lock = {"package": [{"name": "aws-lc-sys", "version": "0.47.0"}, {"name": "aws-lc-sys", "version": "0.46.0"}]}
        self.assertEqual(bench_copies.locked(lock, "aws-lc-sys"), "0.46.0, 0.47.0")


class Aggregate(unittest.TestCase):
    def test_times_by_copy_in_natural_order(self):
        copies = [
            [("sha256", "openssl", 1024, 30.0), ("sha256", "openssl", 64, 3.0), ("ecdh_p256", "openssl", 32, 9.0)],
            [("sha256", "openssl", 64, 5.0), ("sha256", "openssl", 1024, 31.0), ("ecdh_p256", "openssl", 32, 8.0)],
            [("sha256", "openssl", 64, 4.0), ("sha256", "openssl", 1024, 29.0), ("ecdh_p256", "openssl", 32, 7.0)],
        ]
        times = bench_copies.aggregate(copies)
        self.assertEqual(list(times), [("ecdh_p256", "openssl", 32), ("sha256", "openssl", 64),
                                       ("sha256", "openssl", 1024)])
        self.assertEqual(times["sha256", "openssl", 64], [3.0, 5.0, 4.0])
        self.assertEqual(bench_copies.spread([3.0, 5.0, 4.0]), 0.5)

    def test_a_benchmark_missing_from_a_copy_is_an_error(self):
        with self.assertRaises(SystemExit) as e:
            bench_copies.aggregate([[("sha256", "openssl", 64, 3.0)], []])
        self.assertIn("sha256/openssl/64", str(e.exception))

    def test_csv(self):
        with tempfile.TemporaryDirectory() as d:
            path = pathlib.Path(d) / "r.csv"
            bench_copies.write_csv(path, {("sha256", "openssl", 64): [3.0, 5.0, 4.0]}, 3)
            with open(path, newline="") as f:
                rows = list(csv.reader(f))
        self.assertEqual(rows, [
            ["group", "library", "size", "copy1_ns", "copy2_ns", "copy3_ns", "median_ns", "spread"],
            ["sha256", "openssl", "64", "3.000", "5.000", "4.000", "4.000", "0.5000"],
        ])


class Arguments(unittest.TestCase):
    def test_refuses_a_directory_with_results(self):
        with tempfile.TemporaryDirectory() as d:
            (pathlib.Path(d) / "copy-1").mkdir()
            with self.assertRaises(SystemExit):
                bench_copies.main(["--json", "r.json", "--out", d])


if __name__ == "__main__":
    unittest.main()
