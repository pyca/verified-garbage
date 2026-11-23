import unittest

from check_bench_lock import duplicates


def lock(*packages):
    return {"package": [{"name": n, "version": v} for n, v in packages]}


class Duplicates(unittest.TestCase):
    def test_one_of_each(self):
        self.assertEqual(
            duplicates(lock(("aws-lc-rs", "1.19.0"), ("aws-lc-sys", "0.47.0"), ("openssl", "0.10.82"))),
            {},
        )

    def test_two_aws_lc_sys(self):
        self.assertEqual(
            duplicates(lock(("aws-lc-rs", "1.19.0"), ("aws-lc-sys", "0.47.0"), ("aws-lc-sys", "0.46.0"))),
            {"aws-lc-sys": ["0.46.0", "0.47.0"]},
        )

    def test_other_crates_may_repeat(self):
        self.assertEqual(duplicates(lock(("syn", "1.0.0"), ("syn", "2.0.0"))), {})

    def test_no_packages(self):
        self.assertEqual(duplicates({}), {})


if __name__ == "__main__":
    unittest.main()
