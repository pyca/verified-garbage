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
import rust_arches


# A `src/cpu.rs` detecting features as the real one does.
CPU = """
const NAMES: [&str; 6] = ["ssse3", "aes", "bmi2", "adx", "sha3", "neon"];

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn runtime() -> u32 {
    decode(|leaf, sub| cpuid(leaf, sub), || xgetbv(0))
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn decode(cpuid: impl Fn(u32, u32) -> [u32; 4], xgetbv: impl Fn() -> u64) -> u32 {
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


def asm(*features, old=None):
    """A generated module with a variant needing each of `features`: as a
    `Features` constant of their bits, or as generated before, with `old`
    `"of"` as one of their names (`Features::of`) and `"names"` as the list
    of their names."""
    if old == "names":
        return "".join(f"pub(crate) const VG_F{i}_FEATURES: &[&str] = &{json.dumps(f)};\n"
                       for i, f in enumerate(features))
    if old == "of":
        return "".join(f"pub(crate) const VG_F{i}_FEATURES: crate::cpu::Features = "
                       f"crate::cpu::Features::of(&{json.dumps(f)});\n"
                       for i, f in enumerate(features))
    return "".join(f"pub(crate) const VG_F{i}_FEATURES: crate::cpu::Features = "
                   f"crate::cpu::Features({' | '.join(f'crate::cpu::feature::{n.upper()}' for n in f)});\n"
                   for i, f in enumerate(features))


# `CPU` as it is written since its features are bits: a table of the names
# and bits, and detection naming the bits.
CPU_BITS = (CPU
            .replace('const NAMES: [&str; 6] = ["ssse3", "aes", "bmi2", "adx", "sha3", "neon"];',
                     'const NAMES: [(&str, u32); 6] = [("ssse3", feature::SSSE3), ("aes", feature::AES), '
                     '("bmi2", feature::BMI2), ("adx", feature::ADX), ("sha3", feature::SHA3), '
                     '("neon", feature::NEON)];')
            .replace('Features::of(&["sha3"]).0', 'feature::SHA3')
            .replace('Features::of(&["neon"]).0', 'feature::NEON'))


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
            # As `read`: a file not changed at the base is there too.
            stack.enter_context(mock.patch.object(planner, 'bench_rust_files', lambda revision=None, root='.': sorted(
                p for p in {*self.files, *(self.base_files if revision else ())}
                if p.startswith('bench/') and p.endswith('.rs'))))
            planner.includes.cache_clear()
            if registered is not None:
                stack.enter_context(mock.patch.object(planner, 'registrations',
                                                      return_value=set(registered)))
            return planner.arches(paths, base='base')

    def configurations(self, rows, arch):
        # Each configuration once, from its first shard.
        return [r['cpu-features'] for r in rows
                if r['arch'] == arch and r.get('shard', '') in ('', f"1/{r['shard'].split('/')[-1]}")]

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
        for path in ['bench/Cargo.lock', 'ci/bench_compare.py', 'src/unknown.rs']:
            with self.subTest(path=path):
                rows = self.rows([path])
                self.assertEqual(len(rows), self.full_matrix())
                self.assertTrue(all(r['modules'] == '' for r in rows))

    def test_unbenchmarked_asm_module_selects_its_users(self):
        # The generated tables of constants, which no benchmark lists, and
        # its declaration: the modules of that architecture using them.
        self.files['src/asm/x86_64/consts/mod.rs'] = 'mod vg_t;\npub(crate) use vg_t::VG_T;\n'
        self.files['src/asm/x86_64/consts/vg_t.rs'] = 'pub(crate) static VG_T: [u64; 1] = [1];\n'
        self.files['src/asm/x86_64/x448.rs'] += 'T = sym super::consts::VG_T,\n'
        self.files['src/asm/x86_64/mod.rs'] = 'pub(crate) mod consts;\npub(crate) mod x448;\n'
        for paths, registered in [(['src/asm/x86_64/consts/vg_t.rs'], ()),
                                  (['src/asm/x86_64/consts/mod.rs'], ()),
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
                rows = self.rows(['src/asm/x86_64/consts/vg_t.rs'])
                self.assertEqual({r['arch'] for r in rows}, {'x86_64'})
                self.assertTrue(all(r['modules'] == '' for r in rows))

    def test_asm_directories_select_their_architectures(self):
        # PPC64LE's verified functions are in `src/asm/powerpc64le/`, its
        # `target_arch` is `powerpc64`; each entry names both.
        self.assertEqual({a: planner.asm_dir(a) for a in planner.PLATFORMS if planner.asm_dir(a) != a},
                         {'powerpc64': 'powerpc64le'})
        for a in planner.PLATFORMS:
            self.assertEqual(rust_arches.ARCHES[planner.asm_dir(a)], a)
        self.files['src/asm/powerpc64le/x448.rs'] = ''
        rows = self.rows(['src/asm/powerpc64le/x448.rs'])
        self.assertEqual([(r['arch'], r['asm'], r['cpu-features'], r['modules']) for r in rows],
                         [('powerpc64', 'powerpc64le', '', 'x448')])
        # Its tables of constants select the modules of its directory using them.
        self.files['src/asm/powerpc64le/consts/vg_t.rs'] = 'pub(crate) static VG_T: [u64; 1] = [1];\n'
        self.files['src/asm/powerpc64le/x448.rs'] = 'T = sym super::consts::VG_T,\n'
        self.assertEqual(self.modules(self.rows(['src/asm/powerpc64le/consts/vg_t.rs'], ())),
                         {'powerpc64': 'x448'})
        # The directory of an architecture that is not benchmarked needs nothing.
        self.assertEqual(self.rows(['src/asm/s390x/x448.rs']), [])
        self.files['src/asm/riscv64/x448.rs'] = ''
        self.assertEqual(self.modules(self.rows(['src/asm/riscv64/x448.rs'])), {'riscv64': 'x448'})
        # Manual runs check out the directory of the architecture they run.
        self.assertEqual({(r['arch'], r['asm']) for r in planner.manual('powerpc64 thumb aarch64-apple')},
                         {('powerpc64', 'powerpc64le'), ('thumb', 'arm'), ('aarch64-apple', 'aarch64')})

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

    def test_generated_crates(self):
        # A file of a target's crate is the same module as in `src/asm/`.
        old = self.rows(['src/asm/x86_64/x448.rs'])
        self.assertEqual(self.rows(['crates/verified-garbage-asm-x86_64/src/x448.rs']), old)
        # The crate of `Features`: every module choosing by a feature, where
        # a feature is detected, as `Features` in `src/cpu.rs`.
        rows = self.rows(['crates/verified-garbage-cpu/src/lib.rs'])
        self.assertEqual(self.modules(rows), {'x86_64': 'x448', 'aarch64': 'chacha keccak'})

    def test_cpu_detection_by_bits(self):
        # Detection naming a feature's bit, `feature::SHA3`, as by its name.
        rows = self.cpu('feature::SHA3\n', '(feature::SHA3 & 1)\n', base=CPU_BITS)
        self.assertEqual(self.modules(rows), {'aarch64': 'keccak'})
        # The table of names and bits names what detection can find.
        self.assertEqual(planner.detectable('aarch64', CPU_BITS), {'sha3', 'neon'})
        self.assertEqual(planner.detectable('x86_64', CPU_BITS), planner.detectable('x86_64', CPU))
        # A name appended to the table needs nothing.
        self.assertEqual(self.cpu('("neon", feature::NEON)];', '("neon", feature::NEON), ("vaes", feature::VAES)];',
                                  base=CPU_BITS), [])

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
        self.base_files['src/asm/x86_64/x448.rs'] = asm(['bmi2'], ['bmi2', 'adx'], old="names")
        rows = self.rows(['src/asm/x86_64/x448.rs'])
        self.assertEqual(self.configurations(rows, 'x86_64'), ['', 'avx,avx2,bmi1,bmi2', 'none'])

    def test_features_named_by_their_crate_count(self):
        # Only the base has the variant needing ADX, its constant naming
        # `verified_garbage_cpu` rather than its alias.
        self.files['src/asm/x86_64/x448.rs'] = asm(['bmi2'])
        self.base_files['src/asm/x86_64/x448.rs'] = asm(['bmi2'], ['bmi2', 'adx']).replace(
            'crate::cpu::', 'verified_garbage_cpu::')
        rows = self.rows(['src/asm/x86_64/x448.rs'])
        self.assertEqual(self.configurations(rows, 'x86_64'), ['', 'avx,avx2,bmi1,bmi2', 'none'])

    def test_features_of_names_at_base_count(self):
        # Only the base has the variant needing ADX, made by `Features::of`.
        self.files['src/asm/x86_64/x448.rs'] = asm(['bmi2'])
        self.base_files['src/asm/x86_64/x448.rs'] = asm(['bmi2'], ['bmi2', 'adx'], old="of")
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

    def test_a_benchmark_selects_only_the_modules_no_other_benchmark_uses(self):
        # Its shared `sha256` would run `sha256`'s benchmark too; its
        # configurations still follow every module it uses.
        self.catalog.update({'sha256': {'sha256'}, 'rsa_pss': {'rsa_pss', 'sha256', 'keccak'}})
        self.files['bench/benches/primitives/rsa_pss.rs'] = (
            'pub const USES: &[&str] = &["rsa_pss", "sha256", "keccak"];')
        rows = self.rows(['bench/benches/primitives/rsa_pss.rs'])
        self.assertEqual({r['modules'] for r in rows}, {'rsa_pss'})
        self.assertEqual(self.configurations(rows, 'aarch64'), ['', 'sha3'])
        # One whose modules are all shared selects them all.
        self.files['bench/benches/primitives/hmac_sha256.rs'] = (
            'pub const USES: &[&str] = &["hmac_sha256", "sha256"];')
        self.catalog['other'] = {'hmac_sha256'}
        self.assertEqual({r['modules'] for r in self.rows(['bench/benches/primitives/hmac_sha256.rs'])},
                         {'hmac_sha256 sha256'})

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

    def test_external_test_file_uses_its_parent_gate_and_path(self):
        # #1417: the file's name differs from its module, and its test gate
        # also restricts the architecture. Its own items have no cfg(test).
        self.files.update({
            'src/mldsa_common.rs': '#[cfg(all(test, target_arch = "aarch64"))]\n'
                                   '#[path = "mldsa_fused_tests.rs"]\nmod fused_tests;\n',
            'src/mldsa_fused_tests.rs': '#[test]\nfn fused() {}\n',
        })
        self.assertEqual(self.rows(['src/mldsa_fused_tests.rs']), [])
        self.base_files.update(self.files)
        self.files['src/mldsa_fused_tests.rs'] += '#[test]\nfn another() {}\n'
        self.assertEqual(self.rows(['src/mldsa_fused_tests.rs']), [])
        # Removing the file and declaration also needs no benchmark.
        del self.files['src/mldsa_fused_tests.rs']
        self.files['src/mldsa_common.rs'] = ''
        self.assertEqual(self.rows(['src/mldsa_fused_tests.rs']), [])

    def test_external_test_gate_must_exclude_production_at_both_revisions(self):
        path = '#[path = "separate_tests.rs"]\nmod tests;\n'
        self.files.update({'src/old.rs': '#[cfg(test)]\n' + path,
                           'src/separate_tests.rs': '#[test]\nfn a() {}\n'})
        self.base_files.update(self.files)
        for gate in ['', '#[cfg(any(test, feature = "extra"))]\n',
                     '#[cfg(not(test))]\n', '#[cfg(target_arch = "aarch64")]\n']:
            for revision in [self.files, self.base_files]:
                with self.subTest(gate=gate, base=revision is self.base_files):
                    revision['src/old.rs'] = gate + path
                    self.assertEqual(len(self.rows(['src/separate_tests.rs'])), self.full_matrix())
                    revision['src/old.rs'] = '#[cfg(test)]\n' + path

    def test_external_file_with_production_alias_keeps_benchmarks(self):
        self.files.update({
            'src/old.rs': '#[cfg(test)]\n#[path = "shared.rs"]\nmod tests;\n',
            'src/other.rs': '#[path = "shared.rs"]\nmod helper;\n',
            'src/shared.rs': 'fn helper() {}\n',
        })
        self.assertEqual(len(self.rows(['src/shared.rs'])), self.full_matrix())

    def test_deleted_production_alias_keeps_base_benchmarks(self):
        self.files.update({'src/old.rs': '#[cfg(test)]\n#[path = "shared.rs"]\nmod tests;\n',
                           'src/shared.rs': 'fn helper() {}\n'})
        self.base_files.update(self.files)
        self.base_files['src/removed.rs'] = '#[path = "shared.rs"]\nmod helper;\n'
        self.assertEqual(len(self.rows(['src/shared.rs', 'src/removed.rs'])), self.full_matrix())

    def test_unresolved_path_alias_keeps_benchmarks(self):
        self.files.update({
            'src/old.rs': '#[cfg(test)]\n#[path = "shared.rs"]\nmod tests;\n',
            'src/shared.rs': 'fn helper() {}\n',
        })
        for alias in ['mod inline {\n#[path = "../shared.rs"]\nmod helper;\n}\n',
                      'mod inline {\nmod helper;\n}\n',
                      '#[cfg_attr(feature = "extra", path = "shared.rs")]\nmod helper;\n']:
            with self.subTest(alias=alias):
                self.files['src/other.rs'] = alias
                self.assertEqual(len(self.rows(['src/shared.rs'])), self.full_matrix())

    def test_external_test_paths_are_relative_and_support_default_modules(self):
        self.files.update({
            'src/old.rs': '#[cfg(all(\n    test,\n    feature = "extra",\n))]\nmod tests;\n',
            'src/old/tests.rs': '#[test]\nfn a() {}\n',
            'src/other/mod.rs': '#[cfg(test)]\n#[path = "../renamed.rs"]\nmod tests;\n',
            'src/renamed.rs': '#[test]\nfn b() {}\n',
        })
        self.assertEqual(self.rows(['src/old/tests.rs', 'src/renamed.rs']), [])

    def test_module_like_literals_and_inline_modules_do_not_exclude_files(self):
        fake = '#[cfg(test)]\n#[path = "shared.rs"]\nmod tests;\n'
        self.files['src/shared.rs'] = 'fn helper() {}\n'
        for parent in ['const S: &str = r#"\n' + fake + '"#;\n',
                       'mod inline {\n' + fake + '}\n']:
            with self.subTest(parent=parent):
                self.files['src/old.rs'] = parent
                self.assertEqual(len(self.rows(['src/shared.rs'])), self.full_matrix())

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

    def test_included_files_select_their_includers_uses(self):
        self.files.update({
            # On x86-64 alone, through a `#[path]` module.
            'bench/benches/primitives/x448.rs': 'pub const USES: &[&str] = &["x448"];\n'
                                                '#[cfg(target_arch = "x86_64")]\n'
                                                '#[path = "../../support/shared.rs"]\nmod shared;\n',
            # Everywhere, through an `include!` in a differential test.
            'bench/tests/argon2.rs': 'include!("../support/shared.rs");\n',
            'bench/support/shared.rs': 'pub fn helper() {}\n',
        })
        rows = self.rows(['bench/support/shared.rs'])
        self.assertEqual(self.modules(rows), {'x86_64': 'argon2 x448', 'aarch64': 'argon2',
                                              'x86': 'argon2', 'arm': 'argon2', 'powerpc64': 'argon2',
                                              'riscv64': 'argon2'})
        # A file outside `bench/` (e.g. test vectors), and one a helper
        # includes, follow the benchmarks including them in turn.
        self.files['bench/tests/argon2.rs'] = ''
        self.files['bench/support/shared.rs'] = '#[path = "../../tests/cavp/v.rs"]\nmod v;\n'
        self.files['tests/cavp/v.rs'] = ''
        self.assertEqual(self.modules(self.rows(['tests/cavp/v.rs'])), {'x86_64': 'x448'})
        # Included by a benchmark at the base alone, it was measured there.
        self.base_files['bench/benches/primitives/x448.rs'] = self.files.pop('bench/benches/primitives/x448.rs')
        self.files['bench/benches/primitives/argon2.rs'] += '\n#[path = "../../support/shared.rs"]\nmod s;\n'
        self.assertEqual(self.modules(self.rows(['bench/support/shared.rs'])),
                         {'x86_64': 'argon2 x448', 'aarch64': 'argon2', 'x86': 'argon2', 'arm': 'argon2',
                          'powerpc64': 'argon2', 'riscv64': 'argon2'})
        # A file nothing includes needs nothing outside `bench/`, and every
        # benchmark inside it.
        self.assertEqual(self.rows(['tests/cavp/other.rs']), [])
        self.assertEqual(len(self.rows(['bench/support/other.rs'])), self.full_matrix())

    def test_files_included_by_no_benchmark_or_unresolved_run_every_benchmark(self):
        self.files['bench/support/shared.rs'] = ''
        for includer, text in [
                ('bench/benches/primitives/main.rs', '#[path = "../../support/shared.rs"]\nmod shared;\n'),
                # In an inline module, whose path this does not follow.
                ('bench/benches/primitives/argon2.rs',
                 'pub const USES: &[&str] = &["argon2"];\nmod m {\n    #[path = "x/shared.rs"]\n    mod s;\n}\n'),
                # Two files including each other, which no benchmark includes.
                ('bench/support/other.rs', '#[path = "shared.rs"]\nmod s;\n')]:
            with self.subTest(includer=includer):
                self.files[includer] = text
                if includer == 'bench/support/other.rs':
                    self.files['bench/support/shared.rs'] = '#[path = "other.rs"]\nmod o;\n'
                self.assertEqual(len(self.rows(['bench/support/shared.rs'])), self.full_matrix())
                del self.files[includer]

    def test_manifest_target_tables_select_their_architectures(self):
        manifest = '[package]\nname = "b"\n\n[dependencies]\nx = "1"\n'
        target = ('\n[target.\'cfg(any(target_arch = "x86_64", target_arch = "aarch64"))\'.dependencies]\n'
                  'x = { version = "1", features = ["all"] }\n')
        for path in planner.MANIFESTS:
            with self.subTest(path=path):
                self.base_files[path] = manifest
                self.files[path] = manifest + target
                rows = self.rows([path])
                self.assertEqual({r['arch'] for r in rows}, {'x86_64', 'aarch64'})
                self.assertTrue(all(r['modules'] == '' for r in rows))
                # A `cfg` this cannot decide, a target triple, a change
                # outside the target tables, and unparsable TOML: everywhere.
                for new in [manifest + target.replace('target_arch = "aarch64"', 'unix'),
                            manifest + '\n[target.x86_64-unknown-linux-gnu.dependencies]\ny = "1"\n',
                            manifest.replace('"1"', '"2"') + target, manifest + '[']:
                    self.files[path] = new
                    self.assertEqual(len(self.rows([path])), self.full_matrix())

    def test_library_lockfile_alone_plans_nothing(self):
        # The benchmarks build from their own workspace's `bench/Cargo.lock`.
        self.assertEqual(self.rows(['Cargo.lock']), [])
        self.assertEqual(len(self.rows(['bench/Cargo.lock'])), self.full_matrix())

    def test_library_dev_dependencies_alone_plan_nothing(self):
        manifest = ('[package]\nname = "verified-garbage"\n\n[dependencies]\ngetrandom = "0.4"\n\n'
                    '[dev-dependencies]\nserde = "1"\n')
        self.base_files['Cargo.toml'] = manifest
        # Only the library's tests build with its dev-dependencies, plain or
        # in a target table (a new one, or one that also has others).
        for new in [manifest + 'libc = "0.2"\n',
                    manifest + '\n[target.\'cfg(unix)\'.dev-dependencies]\nlibc = "0.2"\n',
                    manifest.replace('serde = "1"', 'serde = "2"')]:
            with self.subTest(new=new):
                self.files['Cargo.toml'] = new
                self.assertEqual(self.rows(['Cargo.toml', 'Cargo.lock']), [])
        # Its dependencies are the benchmarks' too: everywhere.
        for new in [manifest.replace('"0.4"', '"0.5"'),
                    manifest + '\n[target.\'cfg(unix)\'.dependencies]\nlibc = "0.2"\n']:
            with self.subTest(new=new):
                self.files['Cargo.toml'] = new
                self.assertEqual(len(self.rows(['Cargo.toml', 'Cargo.lock'])), self.full_matrix())
        # The benchmarks' own dev-dependencies are compiled into them.
        self.base_files['bench/Cargo.toml'] = manifest
        self.files['bench/Cargo.toml'] = manifest + 'libc = "0.2"\n'
        self.assertEqual(len(self.rows(['bench/Cargo.toml'])), self.full_matrix())

    def test_manual_runs_select_architectures_and_configurations(self):
        rows = planner.manual()
        # Every configuration, split into shards of BENCHMARKS_PER_JOB.
        self.assertEqual(len({(r['arch'], r['cpu-features']) for r in rows}), self.full_matrix())
        shards = -(-planner.bench_count(planner.ALL) // planner.BENCHMARKS_PER_JOB)
        self.assertEqual(len(rows), self.full_matrix() * shards)
        self.assertTrue(all(r['modules'] == '' for r in rows))
        self.assertEqual(self.configurations(planner.manual('aarch64'), 'aarch64'),
                         ['', *planner.CPU_FEATURES['aarch64']])
        # `-` is the configuration without a restriction, and others need
        # not be in `CPU_FEATURES`; the platforms keep their order.
        rows = [r for r in planner.manual('arm x86_64', '- avx2,avx') if r['shard'] in ('', f'1/{shards}')]
        self.assertEqual([(r['arch'], r['cpu-features']) for r in rows],
                         [('x86_64', ''), ('x86_64', 'avx2,avx'), ('arm', ''), ('arm', 'avx2,avx')])
        with self.assertRaisesRegex(ValueError, 'unknown architecture'):
            planner.manual('s390x')

    def test_thumb_is_explicit_and_uses_arm_benchmarks(self):
        self.assertNotIn('thumb', {r['arch'] for r in planner.manual()})
        arm = planner.manual('arm', modules='chacha20')
        thumb = planner.manual('thumb', modules='chacha20')
        self.assertTrue(thumb)
        self.assertEqual(thumb, [{**r, 'arch': 'thumb',
                                 'target': 'thumbv7neon-unknown-linux-gnueabihf'} for r in arm])
        self.assertIn('thumb (runner:', planner.choices())

    def test_manual_runs_select_modules_and_their_configurations(self):
        with mock.patch.object(planner, 'bench_catalog', return_value=self.catalog), \
                mock.patch.object(planner, 'read', self.read), \
                mock.patch.object(planner, 'rust_files', lambda root='.': sorted(
                    p for p in self.files if p.startswith('src/'))):
            # Neither module has a variant: one configuration each.
            rows = planner.manual(modules='triple_des_ecb')
            self.assertEqual([(r['arch'], r['cpu-features'], r['modules']) for r in rows],
                             [(a, '', 'triple_des_ecb') for a in planner.PLATFORMS])
            # Configurations named run as named.
            rows = planner.manual('x86_64', 'none', 'triple_des_ecb')
            self.assertEqual([(r['arch'], r['cpu-features']) for r in rows], [('x86_64', 'none')])
            with self.assertRaisesRegex(ValueError, 'no benchmark uses module'):
                planner.manual(modules='nonexistent')
            choices = planner.choices()
        for arch in planner.PLATFORMS:
            self.assertIn(f'  {arch} (runner: ', choices)
        self.assertIn('  triple_des_ecb: ', choices)

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

    def test_pull_requests_never_run_every_benchmark(self):
        for path in ['bench/Cargo.lock', 'ci/bench_compare.py', 'src/unknown.rs']:
            with self.subTest(path=path):
                rows, skipped = planner.without_full_runs(self.rows([path]))
                self.assertEqual(rows, [])
                self.assertIn(', '.join(planner.PLATFORMS), skipped)
        # Targeted entries stay, those of an architecture needing every
        # benchmark go, in all of its configurations.
        matrix = (planner.platforms('x86_64', {'sha256'}, benchmarks=1)
                  + planner.platforms('aarch64', benchmarks=200))
        rows, skipped = planner.without_full_runs(matrix)
        self.assertEqual(rows, planner.platforms('x86_64', {'sha256'}, benchmarks=1))
        self.assertIn('every benchmark on aarch64,', skipped)
        self.assertEqual(planner.without_full_runs(rows), (rows, None))

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
        # As in bringing up an architecture that is not benchmarked (as
        # PPC64LE was): its module, its `arch`, a `cfg_attr` only it applies,
        # and its entry in a module's list of architectures.
        self.base_files.update({
            'src/lib.rs': 'mod ct;\npub mod chacha;\n#[cfg(target_arch = "x86_64")]\nuse asm::x86_64 as arch;\n',
            'src/asm/mod.rs': '#[cfg(target_arch = "x86_64")]\n#[rustfmt::skip]\npub(crate) mod x86_64;\n',
            'src/ct.rs': '//! Helpers.\n#![cfg_attr(target_arch = "s390x", allow(dead_code))]\n'
                         'pub(crate) fn eq() {}\n',
            'src/chacha.rs': '#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]\nfn f() {}\n',
        })
        self.files.update({
            'src/lib.rs': self.base_files['src/lib.rs']
            + '#[cfg(target_arch = "s390x")]\nuse asm::s390x as arch;\n',
            'src/asm/mod.rs': self.base_files['src/asm/mod.rs']
            + '\n#[cfg(target_arch = "s390x")]\n'
              '#[rustfmt::skip]\npub(crate) mod s390x {\n    fn f() -> [u8; 2] { [b\'}\', 0] }\n}\n',
            'src/ct.rs': 'pub(crate) fn eq() {}\n',
            'src/chacha.rs': '#![cfg(any(\n    target_arch = "x86_64",\n    target_arch = "aarch64",\n'
                             '    target_arch = "s390x"\n))]\nfn f() {}\n',
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


class Interleaving(unittest.TestCase):
    """The order the two sides' benchmarks run in."""

    LIST = ("sha256: bench\nsha256/verified-garbage/64: benchmark\nsha256/verified-garbage/1024: benchmark\n\n"
            "hmac_sha256: bench\nhmac-sha256/verified-garbage/64: benchmark\n\n"
            "hmac-sha256-verify/verified-garbage/64: benchmark\n")

    def test_the_list_names_each_groups_benchmark(self):
        groups, owner = bench_compare.parse_list(self.LIST)
        self.assertEqual(groups, {'sha256': 2, 'hmac-sha256': 1, 'hmac-sha256-verify': 1})
        self.assertEqual(owner, {'sha256': 'sha256', 'hmac-sha256': 'hmac_sha256',
                                 'hmac-sha256-verify': 'hmac_sha256'})
        # A binary that does not name them (base's own benchmarks), or a group
        # in two benchmarks, leaves the sides whole.
        unnamed = re.sub(r'^\w+: bench\n', '', self.LIST, flags=re.M)
        self.assertEqual(bench_compare.parse_list(unnamed), (groups, None))
        self.assertIsNone(bench_compare.parse_list(self.LIST + 'x: bench\nsha256/verified-garbage/9: benchmark\n')[1])

    def test_each_benchmark_runs_on_both_sides_alternately(self):
        _, owner = bench_compare.parse_list(self.LIST)
        runs = bench_compare.units(['hmac-sha256-verify', 'sha256', 'hmac-sha256'], owner)
        self.assertEqual(runs, [('sha256', ['sha256']), ('hmac_sha256', ['hmac-sha256', 'hmac-sha256-verify'])])
        both = {'base': 'b', 'head': 'h'}
        self.assertEqual([(s, b) for s, b, _ in bench_compare.interleaved(runs, both)],
                         [('base', 'sha256'), ('head', 'sha256'), ('head', 'hmac_sha256'), ('base', 'hmac_sha256')])
        self.assertEqual([s for s, _, _ in bench_compare.interleaved(runs, both, 1)],
                         ['head', 'base', 'base', 'head'])
        self.assertEqual([s for s, _, _ in bench_compare.interleaved(runs, {'base': None, 'head': 'h'})],
                         ['head', 'head'])
        # Without the benchmarks' names, each side runs at once.
        self.assertEqual(bench_compare.units(None, None), [(None, None)])
        self.assertEqual(list(bench_compare.interleaved([(None, None)], both, 1)),
                         [('head', None, None), ('base', None, None)])


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


class Executables(unittest.TestCase):
    def test_every_platform_has_an_executable_format(self):
        self.assertEqual(set(bench_compare.EXECUTABLES), set(planner.PLATFORMS) | set(planner.MANUAL_PLATFORMS))

    def test_check_arch_reads_the_header(self):
        # The first 20 bytes of an ELF (class, then e_machine at 18) or a
        # 64-bit Mach-O (cputype at 4) of each architecture.
        elf = lambda bits, machine: (b'\x7fELF' + bytes([bits // 32]) + bytes(13)
                                     + machine.to_bytes(2, 'little'))
        headers = {
            'x86_64': elf(64, 62), 'aarch64': elf(64, 183), 'x86': elf(32, 3), 'arm': elf(32, 40),
            'thumb': elf(32, 40), 'powerpc64': elf(64, 21), 'riscv64': elf(64, 243),
            'aarch64-apple': b'\xcf\xfa\xed\xfe' + (0x0100000C).to_bytes(4, 'little') + bytes(12),
        }
        with tempfile.TemporaryDirectory() as tmp:
            binary = pathlib.Path(tmp, 'bench')
            for built, header in headers.items():
                binary.write_bytes(header)
                for arch in headers:
                    with self.subTest(built=built, arch=arch):
                        if bench_compare.EXECUTABLES[arch] == bench_compare.EXECUTABLES[built]:
                            bench_compare.check_arch(binary, arch)
                        else:
                            with self.assertRaisesRegex(SystemExit, f"not {arch}'s"):
                                bench_compare.check_arch(binary, arch)
            binary.write_bytes(b'#!/bin/sh\n')
            with self.assertRaises(SystemExit):
                bench_compare.check_arch(binary, 'arm')



if __name__ == '__main__':
    unittest.main()


class FreshCopies(unittest.TestCase):
    def test_only_the_p521_comb_chacha20poly1305_aes_gcm_sha512_family_mlkem_and_sha256_groups_run_from_copies(self):
        # P-521's comb table (747 KB) moved its times by up to 7% between
        # identical copies of one binary; P-384's and P-256's did not move.
        # ChaCha20-Poly1305's moved by up to 29% on AMD's Zen 3, and
        # AES-GCM's by up to 35%; ChaCha20's, Poly1305's and AES-GCM-SIV's
        # own groups are not known to. The SHA-512 family's digests and
        # PBKDF2's moved by up to 11% and 9% on AMD's Zen 4, and their
        # HMAC's by 3–4% on Zen 5. ML-KEM's moved by up to 14%. SHA-256's and
        # SHA-224's digests, HMACs and PBKDF2's moved by up to 3.5%, 1.6% and
        # 8.6% on an Arm Neoverse N2; SHA-1's and MD5's are not known to.
        for group in ['mlkem768_keygen', 'mlkem768_encaps', 'mlkem768_encaps_from_bytes', 'mlkem768_decaps',
                      'mlkem1024_keygen', 'mlkem1024_encaps', 'mlkem1024_encaps_from_bytes', 'mlkem1024_decaps',
                      'sha384', 'sha512', 'sha512-224', 'sha512-256', 'pbkdf2-hmac-sha384',
                      'pbkdf2-hmac-sha512', 'pbkdf2-hmac-sha512-224', 'pbkdf2-hmac-sha512-256',
                      'hmac-sha384', 'hmac-sha384-verify', 'hmac-sha512', 'hmac-sha512-verify',
                      'hmac-sha512-224', 'hmac-sha512-224-verify', 'hmac-sha512-256', 'hmac-sha512-256-verify',
                      'ecdsa_p521_sha512_sign', 'ecdsa_p521_sha512_verify', 'ec_p521_public_key',
                      'chacha20poly1305', 'chacha20poly1305-decrypt',
                      'chacha20poly1305-encrypt-out-of-place', 'chacha20poly1305-copy-encrypt-in-place',
                      'aes-128-gcm-encrypt', 'aes-128-gcm-decrypt', 'aes-128-gcm-stream',
                      'aes-128-gcm-tls-seal', 'aes-256-gcm-tls-open',
                      'sha224', 'sha256', 'hmac-sha224', 'hmac-sha224-verify', 'hmac-sha256',
                      'hmac-sha256-verify', 'pbkdf2-hmac-sha224', 'pbkdf2-hmac-sha256',
                      'pbkdf2-hmac-sha256-verify']:
            self.assertTrue(bench_compare.FRESH_COPIES.match(group), group)
        for group in ['ecdh_p521', 'ecdsa_p384_sha384_sign', 'ec_p384_public_key', 'ec_p256_public_key',
                      'chacha20', 'poly1305', 'xchacha20poly1305',
                      'aes-128-gcm-siv-encrypt', 'aes-128-gcm-siv-decrypt', 'aes-128-ctr', 'gcm-ghash',
                      'sha512-256-hash', 'sha512-verify', 'mldsa65_sign', 'sha1', 'hmac-sha1',
                      'pbkdf2-hmac-sha1', 'hmac-md5', 'sha256-hash', 'sha3-256']:
            self.assertFalse(bench_compare.FRESH_COPIES.match(group), group)

    def test_the_copies_select_only_the_modules_with_those_groups(self):
        # Every group of FRESH_COPIES is in the benchmarks that
        # FRESH_COPIES_MODULES selects, and those alone run from the copies.
        root = pathlib.Path(__file__).resolve().parent.parent
        catalog = planner.bench_catalog(root=str(root))
        modules = bench_compare.FRESH_COPIES_MODULES.split()
        selected = [name for name, uses in catalog.items()
                    if any(m in uses for m in modules)]
        # The copies' runs set up the benchmarks holding those groups, and
        # beyond the four that used to run from copies, only benchmarks of
        # code built on SHA-512 or SHA-256 (which the `sha512` and `sha256`
        # modules select).
        held = ['aes_gcm', 'aes_gcm_siv', 'chacha20poly1305', 'ecdsa_p521', 'mlkem1024', 'mlkem768',
                'hmac_sha384', 'hmac_sha512', 'hmac_sha512_224', 'hmac_sha512_256',
                'pbkdf2_sha384', 'pbkdf2_sha512', 'pbkdf2_sha512_224', 'pbkdf2_sha512_256', 'sha384', 'sha512',
                'sha512_224', 'sha512_256', 'sha224', 'sha256', 'hmac_sha224', 'hmac_sha256',
                'pbkdf2_sha224', 'pbkdf2_sha256']
        self.assertLessEqual(set(held), set(selected))
        for name in set(selected) - set(held):
            self.assertTrue('sha512' in catalog[name] or 'sha256' in catalog[name], name)
        source = (root / 'bench/benches/primitives/ecdsa_p521.rs').read_text()
        for group in ['ec_p521_public_key', 'ecdsa_p521_{name}_sign', 'ecdsa_p521_{name}_verify']:
            self.assertIn(f'"{group}"', source)
        source = (root / 'bench/benches/primitives/chacha20poly1305.rs').read_text()
        for group in ['chacha20poly1305', 'chacha20poly1305-decrypt', 'chacha20poly1305-encrypt-out-of-place',
                      'chacha20poly1305-copy-encrypt-in-place']:
            self.assertIn(f'"{group}"', source)
        for bench, group in [('sha384', 'sha384'), ('sha512', 'sha512'), ('sha512_224', 'sha512-224'),
                             ('sha512_256', 'sha512-256'), ('pbkdf2_sha384', 'pbkdf2-hmac-sha384'),
                             ('pbkdf2_sha512', 'pbkdf2-hmac-sha512'),
                             ('pbkdf2_sha512_224', 'pbkdf2-hmac-sha512-224'),
                             ('pbkdf2_sha512_256', 'pbkdf2-hmac-sha512-256'),
                             ('hmac_sha384', 'hmac-sha384'), ('hmac_sha384', 'hmac-sha384-verify'),
                             ('hmac_sha512', 'hmac-sha512'), ('hmac_sha512', 'hmac-sha512-verify'),
                             ('hmac_sha512_224', 'hmac-sha512-224'),
                             ('hmac_sha512_224', 'hmac-sha512-224-verify'),
                             ('hmac_sha512_256', 'hmac-sha512-256'),
                             ('hmac_sha512_256', 'hmac-sha512-256-verify')]:
            source = (root / f'bench/benches/primitives/{bench}.rs').read_text()
            self.assertIn(f'"{group}"', source)
        for bench, group in [('sha224', 'sha224'), ('sha256', 'sha256'), ('hmac_sha224', 'hmac-sha224'),
                             ('hmac_sha224', 'hmac-sha224-verify'), ('hmac_sha256', 'hmac-sha256'),
                             ('hmac_sha256', 'hmac-sha256-verify'), ('pbkdf2_sha224', 'pbkdf2-hmac-sha224'),
                             ('pbkdf2_sha256', 'pbkdf2-hmac-sha256'),
                             ('pbkdf2_sha256', 'pbkdf2-hmac-sha256-verify')]:
            source = (root / f'bench/benches/primitives/{bench}.rs').read_text()
            self.assertIn(f'"{group}"', source)
        source = (root / 'bench/benches/primitives/mlkem.rs').read_text()
        for suffix in ['_keygen', '_encaps', '_encaps_from_bytes', '_decaps']:
            self.assertIn(f'concat!(stringify!($module), "{suffix}")', source)
        source = (root / 'bench/benches/primitives/aes_gcm.rs').read_text()
        for group in ['aes-128-gcm-encrypt', 'aes-128-gcm-decrypt', 'aes-{bits}-gcm-tls-seal',
                      'aes-{bits}-gcm-tls-open']:
            self.assertIn(f'"{group}"', source)

    def test_both_sides_are_built_at_one_path(self):
        # The library's symbol hashes, and with them its layout, depend on
        # its path: each side is staged at STAGE, with the benchmark crate
        # asked for and without what the build does not read.
        with tempfile.TemporaryDirectory() as tmp:
            tmp = pathlib.Path(tmp)
            for side in ['base', 'head']:
                for f in ['Cargo.toml', 'src/lib.rs', 'bench/Cargo.toml', 'lean/big.olean',
                          '.git/HEAD', 'bench-head/Cargo.toml', 'src/lean/x.rs']:
                    (tmp / side / f).parent.mkdir(parents=True, exist_ok=True)
                    (tmp / side / f).write_text(f'{side} {f}')
            with mock.patch.object(bench_compare, 'STAGE', tmp / 'stage'):
                crate = bench_compare.stage(tmp / 'base', tmp / 'head' / 'bench')
                self.assertEqual(crate, tmp / 'stage' / 'bench')
                files = sorted(str(p.relative_to(tmp / 'stage')) for p in (tmp / 'stage').rglob('*') if p.is_file())
                self.assertEqual(files, ['Cargo.toml', 'bench/Cargo.toml', 'src/lean/x.rs', 'src/lib.rs'])
                self.assertEqual((crate / 'Cargo.toml').read_text(), 'head bench/Cargo.toml')
                bench_compare.stage(tmp / 'head')
                self.assertEqual((tmp / 'stage' / 'src/lib.rs').read_text(), 'head src/lib.rs')
                self.assertEqual((crate / 'Cargo.toml').read_text(), 'head bench/Cargo.toml')

    def test_listing_ignores_the_cpu_feature_restriction(self):
        # A shard lists the groups before any run; a CPU lacking a feature
        # VG_CPU_FEATURES names would stop the library there instead.
        seen = {}

        def fake_run(cmd, env, **kwargs):
            seen.update(env)
            return subprocess.CompletedProcess(cmd, 0, stdout='a/verified-garbage/1: benchmark\n')
        with mock.patch.dict(os.environ, {'VG_CPU_FEATURES': 'avx512f'}), \
                mock.patch.object(bench_compare.subprocess, 'run', fake_run):
            self.assertEqual(bench_compare.list_groups('bin', 'ec_p521'), ({'a': 1}, None))
        self.assertNotIn('VG_CPU_FEATURES', seen)
        self.assertEqual(seen['VG_BENCH_MODULES'], 'ec_p521')
        self.assertEqual(seen['VG_BENCH_NAMES'], '1')

    def test_a_copy_is_a_new_executable_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = pathlib.Path(tmp)
            binary = target / 'primitives-0'
            binary.write_bytes(b'\x7fELF')
            with mock.patch.object(bench_compare, 'TARGET', target):
                copy = bench_compare.fresh_copy(str(binary), 1)
            self.assertEqual(copy.read_bytes(), b'\x7fELF')
            self.assertNotEqual(os.stat(copy).st_ino, os.stat(binary).st_ino)
            self.assertTrue(os.access(copy, os.X_OK))
