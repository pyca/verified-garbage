"""Focused regressions for benchmark selection; no builds or measurements."""

import contextlib
import io
import json
import os
import pathlib
import re
import subprocess
import tempfile
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
        """The matrix for `paths`, with `registered` as what registrations
        add (None: read them from the files)."""
        with contextlib.ExitStack() as stack:
            stack.enter_context(mock.patch.object(planner, 'bench_catalog', return_value=self.catalog))
            stack.enter_context(mock.patch.object(planner, 'read', self.read))
            stack.enter_context(mock.patch.object(planner, 'rust_files', lambda root='.': sorted(
                p for p in self.files if p.startswith('src/'))))
            if registered is not None:
                stack.enter_context(mock.patch.object(planner, 'registrations',
                                                      return_value=set(registered)))
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

    def test_unbenchmarked_asm_module_selects_its_users(self):
        # The generated tables of constants, which no benchmark lists, and
        # its declaration: the modules of that architecture using them.
        self.files['src/asm/x86_64/consts.rs'] = 'pub(crate) static VG_T: [u64; 1] = [1];\n'
        self.files['src/asm/x86_64/x448.rs'] += 'T = sym super::consts::VG_T,\n'
        self.files['src/asm/x86_64/mod.rs'] = 'pub(crate) mod consts;\npub(crate) mod x448;\n'
        for paths, registered in [(['src/asm/x86_64/consts.rs'], ()),
                                  (['src/asm/x86_64/mod.rs'], ('consts',))]:
            with self.subTest(paths=paths):
                self.assertEqual(self.modules(self.rows(paths, registered)), {'x86_64': 'x448'})
        # Used by Rust code outside the generated modules, or by none: every
        # benchmark of that architecture.
        for user in ['src/ct.rs', None]:
            with self.subTest(user=user):
                if user:
                    self.files[user] = 'use crate::arch::consts::VG_T;\n'
                else:
                    del self.files['src/ct.rs']
                    self.files['src/asm/x86_64/x448.rs'] = asm(['bmi2'])
                rows = self.rows(['src/asm/x86_64/consts.rs'])
                self.assertEqual({r['arch'] for r in rows}, {'x86_64'})
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

    def test_a_module_directory_selects_the_module_and_its_private_submodules_follow_it(self):
        # `src/rsa/mod.rs` is the module `rsa`'s code as well as the shared
        # code of `rsa_pss`; `scratch` is a private submodule, x86-64's alone.
        self.catalog.update({'rsa': {'rsa'}, 'rsa_pss': {'rsa_pss', 'rsa'}})
        self.files.update({
            'src/rsa/mod.rs': '#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]\n'
                              '#[cfg(target_arch = "x86_64")]\nmod scratch;\nfn f() {}\n',
            'src/rsa/scratch.rs': 'pub(crate) struct Scratch;\n',
        })
        self.base_files['src/rsa/mod.rs'] = self.files['src/rsa/mod.rs'].replace('f()', 'f(x: u8)')
        self.assertEqual(self.modules(self.rows(['src/rsa/mod.rs'])),
                         {'x86_64': 'rsa rsa_pss', 'aarch64': 'rsa rsa_pss'})
        # New: on the architectures compiling its declaration, as its parent.
        self.assertEqual(self.modules(self.rows(['src/rsa/scratch.rs'])), {'x86_64': 'rsa rsa_pss'})
        # A private helper it uses selects its parent's modules, and a
        # feature it names chooses among its parent's implementations.
        self.files.update({'src/lib.rs': 'mod ct;\npub mod rsa;\n', 'src/ct.rs': 'pub(crate) fn eq() {}',
                           'src/rsa/scratch.rs': 'crate::ct::eq(); Features::of(&["adx"])'})
        self.assertEqual({r['modules'] for r in self.rows(['src/ct.rs'])}, {'rsa rsa_pss'})
        with mock.patch.object(planner, 'read', self.read), mock.patch.object(
                planner, 'rust_files', lambda root='.': sorted(p for p in self.files if p.startswith('src/'))):
            self.assertIn('src/rsa/scratch.rs', planner.sources('rsa'))
            self.assertEqual(planner.requirements('x86_64', {'rsa'}, [None]), {frozenset({'adx'})})
        # Declared nowhere, it is no module's: every benchmark runs.
        self.files['src/rsa/mod.rs'] = self.files['src/rsa/mod.rs'].replace('mod scratch;', '')
        self.base_files.pop('src/rsa/mod.rs')
        self.assertEqual(len(self.rows(['src/rsa/scratch.rs'])), self.full_matrix())

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

    def test_new_and_removed_test_only_modules_need_nothing(self):
        # Declared, with its file, only at head; or only at base.
        tests = '#[cfg(test)]\nmod argon2_tests;\n'
        for base, head in [('pub mod argon2;\n', tests + 'pub mod argon2;\n'),
                           (tests + 'pub mod argon2;\n', 'pub mod argon2;\n')]:
            with self.subTest(base=base):
                self.base_files['src/lib.rs'], self.files['src/lib.rs'] = base, head
                self.assertEqual(self.rows(['src/lib.rs', 'src/argon2_tests.rs'], registered=None), [])
        # A new module compiled outside tests still counts.
        self.files['src/lib.rs'] = 'mod argon2_tests;\npub mod argon2;\n'
        self.assertEqual(len(self.rows(['src/argon2_tests.rs'])), self.full_matrix())
        # One declared at neither is no module of the crate.
        with mock.patch.object(planner, 'read', self.read):
            self.assertFalse(planner.test_only('unknown', 'base'))

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

    def test_manual_runs_select_architectures_and_configurations(self):
        rows = planner.manual()
        self.assertEqual(len(rows), self.full_matrix())
        self.assertTrue(all(r['modules'] == '' for r in rows))
        self.assertEqual(self.configurations(planner.manual('aarch64'), 'aarch64'),
                         ['', *planner.CPU_FEATURES['aarch64']])
        # `-` is the configuration without a restriction, and others need
        # not be in `CPU_FEATURES`; the platforms keep their order.
        rows = planner.manual('arm x86_64', '- avx2,avx')
        self.assertEqual([(r['arch'], r['cpu-features']) for r in rows],
                         [('x86_64', ''), ('x86_64', 'avx2,avx'), ('arm', ''), ('arm', 'avx2,avx')])
        with self.assertRaisesRegex(ValueError, 'unknown architecture'):
            planner.manual('riscv64')

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

    def test_changes_to_tests_alone_need_nothing(self):
        code = 'fn f() {}\n'
        tests = '#[cfg(test)]\nmod tests {\n    #[test]\n    fn a() {}\n}\n'
        self.base_files['src/chacha.rs'] = code + tests
        # A test added, or a test module where there was none.
        self.files['src/chacha.rs'] = code + tests.replace('fn a() {}', 'fn a() {}\n    fn b() {}')
        self.assertEqual(self.rows(['src/chacha.rs']), [])
        self.base_files['src/chacha.rs'] = code
        self.files['src/chacha.rs'] = code + tests
        self.assertEqual(self.rows(['src/chacha.rs']), [])
        # Any change outside the tests counts.
        self.files['src/chacha.rs'] = 'fn f() { g() }\n' + tests
        self.assertEqual({r['modules'] for r in self.rows(['src/chacha.rs'])}, {'chacha'})

    def test_features_named_in_tests_alone_choose_nothing(self):
        self.files['src/chacha.rs'] = ('fn f() {}\n#[cfg(test)]\nmod tests {\n'
                                       '    const F: Features = Features::of(&["neon"]);\n}\n')
        self.assertEqual(self.configurations(self.rows(['src/chacha.rs']), 'aarch64'), [''])

    def test_registration_edits_only(self):
        def names(old, new, arch='x86_64'):
            self.base_files['src/lib.rs'] = old
            self.files['src/lib.rs'] = new
            with mock.patch.object(planner, 'read', self.read):
                return planner.registrations('src/lib.rs', 'base', arch)
        lib = 'mod ct;\n'
        self.assertEqual(names(lib, lib + 'pub mod triple_des_ecb;\n'), {'triple_des_ecb'})
        self.assertEqual(names(lib, lib + '#[rustfmt::skip]\npub(crate) mod triple_des;\n'),
                         {'triple_des'})
        self.assertEqual(names(lib, lib + '// Its benchmark.\n(triple_des_ecb::USES, triple_des_ecb::bench),\n'),
                         {'triple_des_ecb'})
        self.assertIsNone(planner.registrations('src/lib.rs', None, 'x86_64'))
        self.assertIsNone(names(lib, lib + 'fn helper() {}\n'))
        self.assertIsNone(names(lib, lib + '#[cfg(feature = "alloc")]\npub mod old;\n'))
        # Lines another architecture alone compiles are not there.
        ppc = '#[cfg(target_arch = "powerpc64")]\nuse asm::powerpc64le as arch;\n'
        self.assertEqual(names(lib, lib + ppc + 'pub mod x448;\n'), {'x448'})
        x86 = '#[cfg(target_arch = "x86")]\nfn helper() {}\n'
        self.assertEqual(names(lib, lib + x86), set())
        self.assertIsNone(names(lib, lib + x86, 'x86'))
        # A test module's declaration, added or removed with its attribute.
        tests = '#[cfg(test)]\nmod aes_tests;\n'
        self.assertEqual(names(lib, lib + tests), set())
        self.assertEqual(names(lib + tests, lib), set())
        self.assertEqual(names(lib + 'pub mod aes;\n', lib + '#[cfg(test)]\nmod aes;\n'), {'aes'})
        # Before another test module, whose attribute a diff could pair with it.
        other = '#[cfg(test)]\nmod argon2_tests;\n'
        self.assertEqual(names(lib + other, lib + tests + other), set())
        # The attribute alone, or on anything else, may change what compiles.
        self.assertEqual(names(lib + tests, lib + 'mod aes_tests;\n'), {'aes_tests'})
        self.assertIsNone(names(lib + tests, lib + 'mod aes_tests;\n#[cfg(test)]\n'))
        self.assertIsNone(names(lib, lib + '#[cfg(test)]\n(aes::USES, aes::bench),\n'))
        self.assertIsNone(names(lib, lib + '#[cfg(test)]\n#[cfg(test)]\nmod aes_tests;\n'))

    def test_code_other_architectures_compile_needs_nothing_here(self):
        # As in bringing up PPC64LE: its module, its `arch`, a `cfg_attr`
        # only it applies, and its entry in a module's list of architectures.
        self.base_files.update({
            'src/lib.rs': 'mod ct;\npub mod chacha;\n#[cfg(target_arch = "x86_64")]\nuse asm::x86_64 as arch;\n',
            'src/asm/mod.rs': '#[cfg(target_arch = "x86_64")]\n#[rustfmt::skip]\npub(crate) mod x86_64;\n',
            'src/ct.rs': '//! Helpers.\n#![cfg_attr(target_arch = "powerpc64", allow(dead_code))]\n'
                         'pub(crate) fn eq() {}\n',
            'src/chacha.rs': '#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]\nfn f() {}\n',
        })
        self.files.update({
            'src/lib.rs': self.base_files['src/lib.rs']
            + '#[cfg(all(target_arch = "powerpc64", target_endian = "little"))]\n'
              'use asm::powerpc64le as arch;\n',
            'src/asm/mod.rs': self.base_files['src/asm/mod.rs']
            + '\n#[cfg(all(target_arch = "powerpc64", target_endian = "little"))]\n'
              '#[rustfmt::skip]\npub(crate) mod powerpc64le {\n    fn f() -> [u8; 2] { [b\'}\', 0] }\n}\n',
            'src/ct.rs': 'pub(crate) fn eq() {}\n',
            'src/chacha.rs': '#![cfg(any(\n    target_arch = "x86_64",\n    target_arch = "aarch64",\n'
                             '    target_arch = "powerpc64"\n))]\nfn f() {}\n',
        })
        paths = ['src/lib.rs', 'src/asm/mod.rs', 'src/ct.rs', 'src/chacha.rs']
        self.assertEqual(self.rows(paths, registered=None), [])
        # One architecture's code needs that architecture's benchmarks alone.
        self.files['src/chacha.rs'] += '#[cfg(target_arch = "aarch64")]\nfn g() {}\n'
        self.assertEqual(self.modules(self.rows(['src/chacha.rs'])), {'aarch64': 'chacha'})
        # A module only some architectures compile, on those.
        self.base_files['src/chacha.rs'] = self.files['src/chacha.rs'].replace('f()', 'f(x: u8)')
        self.assertEqual(self.modules(self.rows(['src/chacha.rs'])),
                         {'x86_64': 'chacha', 'aarch64': 'chacha'})

    def test_cfg_evaluation(self):
        value = planner.cfg_value
        self.assertIs(value('target_arch = "x86"', 'x86'), True)
        self.assertIs(value('not(target_arch = "x86")', 'x86'), False)
        self.assertIs(value('all(target_arch = "powerpc64", target_endian = "little")', 'arm'), False)
        self.assertIs(value('all(target_arch = "x86_64", target_endian = "little")', 'x86_64'), True)
        # What depends on more than the architecture is unknown.
        self.assertIsNone(value('all(target_arch = "x86_64", target_feature = "sse2")', 'x86_64'))
        self.assertIs(value('all(target_arch = "x86", target_feature = "sse2")', 'arm'), False)
        self.assertIsNone(value('any(test, target_arch = "x86")', 'arm'))
        self.assertIs(value('any(test, target_arch = "x86")', 'x86'), True)
        self.assertIsNone(value('not(test)', 'x86'))
        for bad in ['not(a, b)', 'target_arch == "x86"']:
            with self.assertRaises(planner.Unreadable):
                value(bad, 'x86')

    def test_compiled_lines(self):
        lines = lambda text, arch='x86_64': planner.for_arch(text, arch)
        # Comments go, and `cfg`s that hold; items whose `cfg` does not,
        # whatever brackets their literals hold.
        text = ('// A "{" comment.\n#[cfg(target_arch = "x86_64")]\nfn a() {}\n'
                '#[cfg(target_arch = "arm")]\nfn b() -> char { let s = "}"; let r = r#"}"#; \'}\' }\n'
                'match x {\n    #[cfg(target_arch = "arm")]\n    A => f(),\n'
                '    #[cfg(target_arch = "arm")]\n    B => {}\n    C => g(\'a\'),\n}\n'
                '/* gone */ fn c<\'a>() {}\n')
        self.assertEqual(lines(text), ['fn a() {}', 'match x {', 'C => g(\'a\'),', '}', 'fn c<\'a>() {}'])
        # A file whose inner `cfg` does not hold is empty, after inner attributes.
        self.assertEqual(lines('#![allow(x)]\n#![cfg(target_arch = "arm")]\nfn a() {}\n'), [])
        self.assertEqual(lines(None), [])
        # A `cfg_attr` that holds or may stays.
        self.assertEqual(lines('#[cfg_attr(test, allow(x))]\nfn a() {}\n'),
                         ['#[cfg_attr(test, allow(x))]', 'fn a() {}'])
        for bad in ['fn a() { "', '/* a', '#[cfg(a, b)]\nfn a() {}', 'fn a() {}\n#![cfg(target_arch = "arm")]',
                    '#[cfg(target_arch = "arm")', '#[cfg(target_arch = "arm") x']:
            with self.subTest(text=bad), self.assertRaises(planner.Unreadable):
                lines(bad)

    def test_unreadable_or_unchanged_rust_counts_everywhere(self):
        self.base_files['src/chacha.rs'] = 'fn a() { "'
        with mock.patch.object(planner, 'read', self.read):
            self.assertEqual(planner.affected('src/chacha.rs', 'base'), list(planner.PLATFORMS))
            # A file the same at both revisions (as here, without a base).
            self.assertEqual(planner.affected('src/argon2.rs', 'base'), list(planner.PLATFORMS))
            self.assertEqual(planner.affected('Cargo.lock', 'base'), list(planner.PLATFORMS))

    def test_comparison_filters_each_binary_without_full_suite_fallback(self):
        with mock.patch.object(bench_compare, 'bench_catalog', return_value={'old': {'old'}}):
            self.assertEqual(bench_compare.selected_modules('base', 'old new'), 'old')
            self.assertIsNone(bench_compare.selected_modules('base', 'new'))
            self.assertEqual(bench_compare.selected_modules('base', ''), '')


class Lacking(unittest.TestCase):
    """A benchmark run that src/cpu.rs stops for naming features the CPU
    does not have."""

    def test_matches_the_library_panic(self):
        # The message src/cpu.rs's own test expects.
        panic = re.search(r'should_panic\(expected = "(VG_CPU_FEATURES names [^"]*)"\)',
                          pathlib.Path('src/cpu.rs').read_text())[1]
        self.assertEqual(bench_compare.LACKING.search(panic)[1], 'sha,avx')

    def test_run_raises_it_and_other_failures_stay_failures(self):
        args = mock.Mock(warm_up_time=0.1, measurement_time=0.3)
        with tempfile.TemporaryDirectory() as tmp:
            for stderr, error in [("VG_CPU_FEATURES names avx512f, which this CPU does not have", bench_compare.Lacking),
                                  ("some other panic", subprocess.CalledProcessError)]:
                binary = pathlib.Path(tmp, 'bench')
                binary.write_text(f'#!/bin/sh\necho "{stderr}" >&2\nexit 101\n')
                os.chmod(binary, 0o755)
                with self.subTest(stderr=stderr), contextlib.redirect_stderr(io.StringIO()), \
                        mock.patch.object(bench_compare, 'cpu_features', return_value='avx512f'), \
                        self.assertRaises(error) as raised:
                    bench_compare.run(str(binary), pathlib.Path(tmp), bench_compare.VG, args, None, '')
                if error is bench_compare.Lacking:
                    self.assertEqual(raised.exception.args, ('avx512f',))

    def test_report_names_what_was_not_measured(self):
        report = bench_compare.not_measured('avx,avx512f', 'avx512f', 'AMD EPYC 7763')
        self.assertIn('VG_CPU_FEATURES=avx,avx512f', report)
        self.assertIn('(AMD EPYC 7763) does not have avx512f', report)
        self.assertNotIn('()', bench_compare.not_measured('avx', 'avx', None))


if __name__ == '__main__':
    unittest.main()
