import unittest

from check_case_collisions import collisions


class Collisions(unittest.TestCase):
    def test_files(self):
        self.assertEqual(
            collisions(["a/VCheckS.lean", "a/VChecks.lean", "a/VMain.lean"]),
            [["a/VCheckS.lean", "a/VChecks.lean"]],
        )

    def test_directories(self):
        self.assertEqual(
            collisions(["Proof/X/a.lean", "proof/X/b.lean"]),
            [["Proof", "proof"]],
        )

    def test_none(self):
        self.assertEqual(collisions(["a/VCheckScalar.lean", "a/VChecks.lean"]), [])


if __name__ == "__main__":
    unittest.main()
