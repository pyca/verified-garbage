"""Focused regressions for benchmark selection; no builds or measurements."""

import json
import unittest
from unittest import mock

import bench_arches as planner
import bench_compare


# A `src/cpu.rs` detecting features as the real one does.
CPU = """
const NAMES: [&str; 6] = ["ssse3", "aes", "bmi2", "adx", "sha3", "neon"];

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn runtime() -> u32 {
    let ssse3 = 1;
    let aes = 1;
    let bmi2 = 1;
    let adx = 1;
    ssse3 | (aes << 1) | (bmi2 << 2) | (adx << 3)
}

#[cfg(target_arch = "aarch64")]
fn runtime() -> u32 {
    Features::of(&["sha3"]).0
        | Features::of(&["neon"]).0
}

impl Features {
    pub(crate) fn of(names: &[&str]) -> Features {
        Features(names.len() as u32)
    }
}

#[cfg(test)]
mod tests {
    fn of_names() {}
}
"""


def asm(*features, old=False):
    """A generated module with a variant needing each of `features`: as a
    `Features` constant, or with `old` as the list of names generated before."""
    if old:
        return "".join(f"pub(crate) const VG_F{i}_FEATURES: &[&str] = &{json.dumps(f)};\n"
                       for i, f in enumerate(features))
    return "".join(f"pub(crate) const VG_F{i}_FEATURES: crate::cpu::Features = "
                   f"crate::cpu::Features::of(&{json.dumps(f)});\n"
                   for i, f in enumerate(features))


class Selection(unittest.TestCase):
    def setUp(self):
        planner.read.cache_clear()
        self.catalog = {'old': {'old'}, 'triple_des_ecb': {'triple_des_ecb', 'triple_des'},
                        'x448': {'x448'}, 'keccak': {'keccak'}, 'chacha': {'chacha'},
                        'hmac_sha256': {'hmac_sha256', 'sha256'}, 'argon2': {'argon2'},
                        'poly': {'poly'}}
        self.base_files = {}
        self.files = {
            'src/cpu.rs': CPU,
            'src/asm/x86_64/x448.rs': asm(['bmi2'], ['bmi2', 'adx'], ['aes', 'ssse3', 'sha3']),
            'src/asm/aarch64/keccak.rs': asm(['sha3']),
            # Reads the names itself: FEAT_SHA3 only when `sha3` is named.
            'src/hashes/keccak.rs': 'std::env::var("VG_CPU_FEATURES"); Features::of(&["sha3"])',
            # A literal in Rust code, on the one architecture detecting it.
            'src/chacha.rs': 'if f.contains(Features::of(&["neon"])) {}',
            'bench/benches/primitives/argon2.rs': 'pub const USES: &[&str] = &["argon2"];',
            'src/hmac/mod.rs': 'pub struct InvalidMac;',
            'src/poly.rs': 'pub use crate::hmac::InvalidMac;',
        }

    def read(self, path, revision=None, root='.'):
        if revision and path in self.base_files:
            return self.base_files[path]
        return self.files.get(path)

    def cpu(self, old, new, base=None):
        """`src/cpu.rs` changed from `CPU` (or `base`) by replacing `old`."""
        self.base_files['src/cpu.rs'] = base or CPU
        self.files['src/cpu.rs'] = (base or CPU).replace(old, new)
        assert self.files['src/cpu.rs'] != self.base_files['src/cpu.rs']
        return self.rows(['src/cpu.rs'])

    def modules(self, rows):
        return {r['arch']: r['modules'] for r in rows}

    def rows(self, paths, registered=('triple_des_ecb',)):
        with mock.patch.object(planner, 'bench_catalog', return_value=self.catalog), \
                mock.patch.object(planner, 'read', self.read), \
                mock.patch.object(planner, 'rust_files', lambda root='.': sorted(
                    p for p in self.files if p.startswith('src/'))), \
                mock.patch.object(planner, 'registrations', return_value=set(registered)):
            return planner.arches(paths, base='base')

    def configurations(self, rows, arch):
        return [r['cpu-features'] for r in rows if r['arch'] == arch]

    def full_matrix(self):
        """The number of rows of the full matrix: every platform, without and
        with each of its CPU-feature configurations."""
        return sum(1 + len(planner.CPU_FEATURES.get(a, [])) for a in planner.PLATFORMS)

    def test_registration_addition_selects_modules_and_their_configurations(self):
        rows = self.rows(['src/lib.rs', 'src/triple_des_ecb.rs', 'bench/benches/primitives/main.rs'])
        self.assertEqual({r['modules'] for r in rows}, {'triple_des triple_des_ecb'})
        # Neither module has a variant for a CPU feature: one configuration each.
        self.assertEqual([(r['arch'], r['cpu-features']) for r in rows],
                         [(a, '') for a in planner.PLATFORMS])

    def test_shared_and_unknown_dependencies_preserve_full_suite(self):
        for path in ['Cargo.lock', 'ci/bench_compare.py', 'src/unknown.rs']:
            with self.subTest(path=path):
                rows = self.rows([path])
                self.assertEqual(len(rows), self.full_matrix())
                self.assertTrue(all(r['modules'] == '' for r in rows))

    def test_planner_changes_need_no_benchmarks(self):
        self.assertEqual(self.rows(['ci/bench_arches.py']), [])

    def test_cpu_detection_selects_modules_choosing_by_the_features_it_names(self):
        # The feature a line detects is the first it names, not `bmi2`.
        rows = self.cpu('let adx = 1;', 'let adx = (ebx >> 19) & bmi2;')
        self.assertEqual(self.modules(rows), {'x86_64': 'x448'})
        self.assertEqual(self.configurations(rows, 'x86_64'), ['', 'avx,avx2,bmi1,bmi2', 'none'])
        rows = self.cpu('Features::of(&["sha3"]).0\n', '(Features::of(&["sha3"]).0 & 1)\n')
        self.assertEqual(self.modules(rows), {'aarch64': 'keccak'})
        # A feature no module chooses by needs nothing.
        self.assertEqual(self.cpu('let aes = 1;', 'let aes = 2;'), [])

    def test_cpu_detection_naming_no_feature_selects_all_of_its_architectures(self):
        rows = self.cpu('    let ssse3 = 1;', '    let leaf = 7;\n    let ssse3 = 1;')
        self.assertEqual(self.modules(rows), {'x86_64': 'x448'})

    def test_shared_cpu_code_selects_every_module_choosing_by_features(self):
        rows = self.cpu('Features(names.len() as u32)', 'Features(names.len() as u32 + 0)')
        # Not ARMv7 or x86, where nothing chooses.
        self.assertEqual(self.modules(rows), {'x86_64': 'x448', 'aarch64': 'chacha keccak'})
        names = '["ssse3", "aes", "bmi2", "adx", "sha3", "neon"]'
        rows = self.cpu(names, '["aes", "ssse3", "bmi2", "adx", "sha3", "neon"]')
        self.assertEqual(self.modules(rows), {'x86_64': 'x448', 'aarch64': 'chacha keccak'})

    def test_cpu_tests_comments_and_appended_names_need_nothing(self):
        self.assertEqual(self.cpu('fn of_names() {}', 'fn of_names() { assert!(true); }'), [])
        self.assertEqual(self.cpu('impl Features {', '// Sets.\nimpl Features {'), [])
        self.assertEqual(self.cpu('"sha3", "neon"]', '"sha3", "neon", "vaes"]'), [])
        self.assertEqual(self.cpu('const NAMES: [&str; 6]', 'const NAMES: [&str; 7]'), [])

    def test_unreadable_cpu_change_runs_every_benchmark(self):
        self.base_files['src/cpu.rs'] = None
        rows = self.rows(['src/cpu.rs'])
        self.assertEqual(len(rows), self.full_matrix())
        self.assertTrue(all(r['modules'] == '' for r in rows))

    def test_configurations_choosing_the_same_implementations_run_once(self):
        rows = self.rows(['src/asm/x86_64/x448.rs'])
        # Both variants, the BMI2 one alone, and neither (as `none`): a
        # variant runs only with all of its features, never with only some
        # (`aes,ssse3`), or with one the architecture never detects (`sha3`).
        self.assertEqual(self.configurations(rows, 'x86_64'), ['', 'avx,avx2,bmi1,bmi2', 'none'])
        self.assertEqual({r['modules'] for r in rows}, {'x448'})

    def test_features_listed_by_names_at_base_count(self):
        # Only the base has the variant needing ADX, as a list of names.
        self.files['src/asm/x86_64/x448.rs'] = asm(['bmi2'])
        self.base_files['src/asm/x86_64/x448.rs'] = asm(['bmi2'], ['bmi2', 'adx'], old=True)
        rows = self.rows(['src/asm/x86_64/x448.rs'])
        self.assertEqual(self.configurations(rows, 'x86_64'), ['', 'avx,avx2,bmi1,bmi2', 'none'])

    def test_features_named_in_rust_count_where_detected(self):
        rows = self.rows(['src/chacha.rs'])
        self.assertEqual(self.configurations(rows, 'aarch64'), ['', 'none'])
        self.assertEqual(self.configurations(rows, 'x86_64'), [''])

    def test_features_chosen_only_when_named_keep_their_configurations(self):
        rows = self.rows(['src/asm/aarch64/keccak.rs'])
        # Without naming `sha3`, every configuration chooses the same.
        self.assertEqual(self.configurations(rows, 'aarch64'), ['', 'sha3'])

    def test_unreadable_detection_runs_every_configuration(self):
        del self.files['src/cpu.rs']
        rows = self.rows(['src/asm/x86_64/x448.rs'])
        self.assertEqual(self.configurations(rows, 'x86_64'), ['', *planner.CPU_FEATURES['x86_64']])

    def test_family_code_and_benchmark_tests_select_their_modules(self):
        # Its members, and the modules using it.
        self.assertEqual({r['modules'] for r in self.rows(['src/hmac/mod.rs'])}, {'hmac_sha256 poly'})
        self.assertEqual({r['modules'] for r in self.rows(['bench/tests/argon2.rs'])}, {'argon2'})
        self.assertEqual({r['modules'] for r in self.rows(['src/nofamily/mod.rs'])}, {''})

    def test_shared_hash_code_selects_every_hash(self):
        # `hmac_sha256`'s benchmark follows through its `USES` of `sha256`.
        self.files['src/hashes/sha256.rs'] = ''
        self.files['src/hashes/mod.rs'] = ''
        self.catalog['sha256'] = {'sha256'}
        rows = self.rows(['src/hashes/mod.rs'])
        self.assertEqual({r['modules'] for r in rows}, {'keccak sha256'})
        self.assertEqual(self.configurations(rows, 'aarch64'), ['', 'sha3'])
        self.assertEqual(self.configurations(rows, 'x86_64'), [''])

    def test_test_only_modules_need_nothing(self):
        self.files['src/lib.rs'] = '#[cfg(test)]\nmod argon2_tests;\npub mod argon2;\n'
        self.assertEqual(self.rows(['src/argon2_tests.rs']), [])
        # Unless the base compiled it outside tests too.
        self.base_files['src/lib.rs'] = 'mod argon2_tests;\n'
        self.assertEqual(len(self.rows(['src/argon2_tests.rs'])), self.full_matrix())

    def test_private_helpers_select_the_modules_using_them(self):
        self.files.update({
            'src/lib.rs': 'mod ct;\npub mod argon2;\n#[cfg(test)]\nmod argon2_tests;\nmod unused;\n',
            'src/ct.rs': 'pub(crate) fn eq() { crate::ct::eq() }',
            'src/argon2.rs': 'use crate::ct::eq;',
            # Every hash module, through the shared hash code; not a test.
            'src/hashes/mod.rs': 'crate::ct::eq()',
            'src/hashes/sha256.rs': '',
            'src/argon2_tests.rs': 'crate::ct::eq()',
            'src/unused.rs': '',
        })
        self.catalog['sha256'] = {'sha256'}
        self.assertEqual({r['modules'] for r in self.rows(['src/ct.rs'])},
                         {'argon2 keccak sha256'})
        # One nothing uses runs every benchmark.
        self.assertEqual(len(self.rows(['src/unused.rs'])), self.full_matrix())

    def test_benchmark_helpers_select_their_callers_uses(self):
        self.files['bench/benches/primitives/kem.rs'] = 'macro_rules! kem_bench { () => {} }'
        # Called through a `use`, by the macro's name alone.
        self.files['bench/benches/primitives/x448.rs'] = 'use super::*;\nkem_bench!();'
        self.assertEqual({r['modules'] for r in self.rows(['bench/benches/primitives/kem.rs'])},
                         {'x448'})
        # One no benchmark calls runs every benchmark.
        self.files['bench/benches/primitives/x448.rs'] = ''
        self.assertEqual(len(self.rows(['bench/benches/primitives/kem.rs'])), self.full_matrix())

    def test_shards_follow_the_number_of_benchmarks(self):
        shards = lambda n: [r['shard'] for r in planner.platforms('arm', benchmarks=n)]
        with mock.patch.object(planner, 'BENCHMARKS_PER_JOB', None):
            self.assertEqual(shards(1000), [''])
        per_job = 30
        patch = mock.patch.object(planner, 'BENCHMARKS_PER_JOB', per_job)
        patch.start()
        self.addCleanup(patch.stop)
        self.assertEqual(shards(0), [''])
        self.assertEqual(shards(per_job), [''])
        self.assertEqual(shards(per_job + 1), ['1/2', '2/2'])
        self.assertEqual(shards(2 * per_job + 1), ['1/3', '2/3', '3/3'])
        # Each configuration is sharded; the benchmarks counted are those
        # the selected modules run (`hmac_sha256`'s and `poly`'s).
        with mock.patch.object(planner, 'BENCHMARKS_PER_JOB', 1):
            rows = self.rows(['src/hmac/mod.rs'])
        self.assertEqual([(r['cpu-features'], r['shard']) for r in rows if r['arch'] == 'aarch64'],
                         [('', '1/2'), ('', '2/2')])

    def test_shards_deal_out_groups_by_size(self):
        groups = {'a': 3, 'b': 3, 'c': 2, 'd': 1, 'e': 1}
        parts = [bench_compare.shard_groups(groups, i, 2) for i in (1, 2)]
        self.assertEqual(parts, [['a', 'c'], ['b', 'd', 'e']])
        self.assertEqual(bench_compare.shard_groups(groups, 1, 1), sorted(groups))
        # More shards than groups leaves some empty.
        self.assertEqual(bench_compare.shard_groups({'a': 1}, 2, 2), [])

    def test_registration_edits_only(self):
        def names(lines):
            with mock.patch.object(planner.subprocess, 'check_output', return_value=lines):
                return planner.registrations('src/lib.rs', 'base')
        self.assertEqual(names('+++ b/src/lib.rs\n+pub mod triple_des_ecb;'), {'triple_des_ecb'})
        self.assertEqual(names('+#[rustfmt::skip]\n+pub(crate) mod triple_des;'), {'triple_des'})
        self.assertEqual(names('+(triple_des_ecb::USES, triple_des_ecb::bench),'), {'triple_des_ecb'})
        self.assertIsNone(planner.registrations('src/lib.rs', None))
        self.assertIsNone(names('+fn helper() {}'))
        self.assertIsNone(names('+#[cfg(feature = "alloc")]\n+pub mod old;'))

    def test_comparison_filters_each_binary_without_full_suite_fallback(self):
        with mock.patch.object(bench_compare, 'bench_catalog', return_value={'old': {'old'}}):
            self.assertEqual(bench_compare.selected_modules('base', 'old new'), 'old')
            self.assertIsNone(bench_compare.selected_modules('base', 'new'))
            self.assertEqual(bench_compare.selected_modules('base', ''), '')


if __name__ == '__main__':
    unittest.main()
