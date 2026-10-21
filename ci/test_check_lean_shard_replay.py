"""Historical replay uses observed rebuilds and checks proposed coverage."""

import unittest

import lean_shard_replay as replay
import lean_shards as shards


class Observations(unittest.TestCase):
    def test_duplicate_modules_use_the_median_and_cache_steps_do_not_count(self):
        metrics = {"lean": {"jobs": [
            {"built": {"Check the shard's proofs": {"A": 10.0, "B": 20.0}}},
            {"built": {"Check the shard's proofs": {"A": 14.0}, "Restore cache": {"B": 500.0}}},
            {"built": {"Run ./.github/actions/lean-assemble": {"C": 1.0}}},
        ]}}
        self.assertEqual(replay.observations(metrics), {"A": 12.0, "B": 20.0, "C": 1.0})

    def test_a_solo_plan_retains_cached_dependency_costs(self):
        imps = {"A": [], "B": ["A"], "unrelated": []}
        result = replay.evaluate(shards, imps, shards.closures(imps), {"B"}, {"B": 20.0}, {"B": 20.0})
        self.assertEqual(result["shards"], 0)
        self.assertEqual(result["finish_s"], 20.0 + shards.UP_TO_DATE)
        self.assertEqual(result["module_work_s"], 20.0 + shards.UP_TO_DATE)
        self.assertEqual(result["duplicate_work_s"], 0.0)

    def test_an_incomplete_plan_is_rejected(self):
        class Broken:
            @staticmethod
            def schedule(*args):
                return 0, {}, ([1.0, 1.0], [["A"], ["B"]], [{"A"}, {"B"}])

        imps = {"A": [], "B": [], "C": []}
        with self.assertRaisesRegex(AssertionError, "cover every"):
            replay.evaluate(Broken, imps, shards.closures(imps), set(imps), {}, dict.fromkeys(imps, 1.0))
