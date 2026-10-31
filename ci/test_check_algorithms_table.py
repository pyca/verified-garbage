"""What `algorithms_table.py` puts in a cell; no builds."""

import pathlib
import tempfile
import unittest
from unittest import mock

import algorithms_table


def tree(files: dict) -> tempfile.TemporaryDirectory:
    d = tempfile.TemporaryDirectory()
    for rel, text in files.items():
        p = pathlib.Path(d.name) / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    return d


def features(name, fs):
    return (f"pub(crate) const {name}_FEATURES: crate::cpu::Features = "
            f"crate::cpu::Features({' | '.join(f'crate::cpu::feature::{f.upper()}' for f in fs)});\n")


class Cells(unittest.TestCase):
    def variants(self, files, arch):
        with tree(files) as d, mock.patch.object(algorithms_table, "ROOT", pathlib.Path(d)):
            return algorithms_table.variants({"asm": ["m"]}, arch)

    def test_features_that_others_bring(self):
        # AVX2 brings AVX, and AVX SSSE3: only AVX2 is named.
        asm = features("VG_F_AVX2", ["avx", "avx2", "ssse3"])
        self.assertEqual(self.variants({"src/asm/x86_64/m.rs": asm}, "x86_64"), "AVX2")
        # Alone, each is named.
        asm = features("VG_F_AVX", ["avx"]) + features("VG_G_SSSE3", ["ssse3"])
        self.assertEqual(self.variants({"src/asm/x86_64/m.rs": asm}, "x86_64"), "AVX")
        asm = features("VG_F_SSSE3", ["ssse3"])
        self.assertEqual(self.variants({"src/asm/x86/m.rs": asm}, "x86"), "SSSE3")
        asm = features("VG_F_SHANI", ["sha", "ssse3"])
        self.assertEqual(self.variants({"src/asm/x86_64/m.rs": asm}, "x86_64"), "SHA extensions")

    def test_a_variant_without_features(self):
        # A `_neon` function on AArch64 is named after the features.
        asm = (features("VG_F_SVE2", ["sve2"]) + "fn vg_f(x: u64) {}\nfn vg_f_neon(x: u64) {}\n"
               "fn vg_f_sve2(x: u64) {}\n")
        self.assertEqual(self.variants({"src/asm/aarch64/m.rs": asm}, "aarch64"), "SVE2, NEON")
        # Elsewhere the suffix means nothing.
        self.assertEqual(self.variants({"src/asm/x86_64/m.rs": "fn vg_f_neon(x: u64) {}\n"}, "x86_64"), "")

    def test_a_row_describes_no_optimizations(self):
        row = ('name = "A"\nfamily = "Hashes"\nspecs = []\nmodules = []\nasm = []\n'
               'optimized = { x86_64 = "unrolled" }\n')
        with tree({"docs/algorithms/a.toml": row}) as d, \
                mock.patch.object(algorithms_table, "ROWS", pathlib.Path(d) / "docs/algorithms"), \
                mock.patch.object(algorithms_table, "ROOT", pathlib.Path(d)):
            errors = []
            algorithms_table.table(errors)
        [e] = errors
        self.assertIn("a.toml: unknown keys optimized", e)


if __name__ == "__main__":
    unittest.main()
