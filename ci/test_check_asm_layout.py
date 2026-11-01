"""Where the generated code of each target is (ci/asm_layout.py), in either
layout."""

import pathlib
import tempfile
import unittest

import asm_layout


class Paths(unittest.TestCase):
    def test_logical(self):
        self.assertEqual(asm_layout.logical("crates/verified-garbage-asm-x86_64/asm/md5.rs"),
                         "src/asm/x86_64/md5.rs")
        self.assertEqual(asm_layout.logical("crates/verified-garbage-asm-x86_64/src/md5.rs"),
                         "src/asm/x86_64/md5.rs")
        self.assertEqual(asm_layout.logical("crates/verified-garbage-asm-x86_64/src/lib.rs"),
                         "src/asm/x86_64/mod.rs")
        self.assertEqual(asm_layout.logical("crates/verified-garbage-asm-x86/src/consts/vg_t.rs"),
                         "src/asm/x86/consts/vg_t.rs")
        # Anything else, the manifests and the other crates too, as it is.
        for path in ["src/asm/x86_64/md5.rs", "crates/verified-garbage-asm-x86_64/Cargo.toml",
                     "crates/verified-garbage-cpu/src/lib.rs", "src/lib.rs"]:
            self.assertEqual(asm_layout.logical(path), path)

    def test_physical(self):
        self.assertEqual(asm_layout.physical("src/asm/x86_64/mod.rs"),
                         ["crates/verified-garbage-asm-x86_64/asm/lib.rs",
                          "crates/verified-garbage-asm-x86_64/src/lib.rs", "src/asm/x86_64/mod.rs"])
        self.assertEqual(asm_layout.physical("src/lib.rs"), ["src/lib.rs"])
        for path in ["src/asm/aarch64/sha256.rs", "src/asm/x86/consts/mod.rs"]:
            self.assertEqual(asm_layout.logical(asm_layout.physical(path)[0]), path)


class Trees(unittest.TestCase):
    def tree(self, files):
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        root = pathlib.Path(d.name)
        for f in files:
            (root / f).parent.mkdir(parents=True, exist_ok=True)
            (root / f).write_text("")
        return root

    def test_old_layout(self):
        root = self.tree(["src/asm/mod.rs", "src/asm/x86_64/mod.rs", "src/asm/x86_64/md5.rs"])
        self.assertEqual(asm_layout.target_dir(root, "x86_64"), root / "src/asm/x86_64")
        self.assertEqual(asm_layout.target_dirs(root), {"x86_64": root / "src/asm/x86_64"})
        self.assertEqual(list(asm_layout.generated_files(root)),
                         ["src/asm/mod.rs", "src/asm/x86_64/md5.rs", "src/asm/x86_64/mod.rs"])

    def test_crates_src(self):
        root = self.tree(["crates/verified-garbage-asm-x86_64/Cargo.toml",
                          "crates/verified-garbage-asm-x86_64/src/lib.rs",
                          "crates/verified-garbage-asm-x86_64/src/md5.rs",
                          "crates/verified-garbage-cpu/src/lib.rs"])
        crate = root / "crates/verified-garbage-asm-x86_64/src"
        self.assertEqual(asm_layout.target_dir(root, "x86_64"), crate)
        self.assertEqual(asm_layout.target_dirs(root), {"x86_64": crate})
        self.assertEqual(asm_layout.generated_files(root), {
            "src/asm/x86_64/md5.rs": crate / "md5.rs", "src/asm/x86_64/mod.rs": crate / "lib.rs"})

    def test_empty_asm(self):
        # An `asm/` without a `lib.rs` (left by a checkout) is not the code.
        root = self.tree(["crates/verified-garbage-asm-x86_64/src/lib.rs",
                          "crates/verified-garbage-asm-x86_64/asm/consts/.keep"])
        self.assertEqual(asm_layout.target_dir(root, "x86_64"),
                         root / "crates/verified-garbage-asm-x86_64/src")

    def test_crates(self):
        # At a revision whose crates had both: a crate's `asm/`, and not its
        # `src/` beside it.
        root = self.tree(["crates/verified-garbage-asm-x86_64/Cargo.toml",
                          "crates/verified-garbage-asm-x86_64/asm/lib.rs",
                          "crates/verified-garbage-asm-x86_64/asm/md5.rs",
                          "crates/verified-garbage-asm-x86_64/src/lib.rs",
                          "crates/verified-garbage-asm-x86_64/src/md5.rs",
                          "crates/verified-garbage-asm-arm/asm/lib.rs",
                          "crates/verified-garbage-asm-mips/Cargo.toml",
                          "crates/verified-garbage-cpu/src/lib.rs"])
        crate = root / "crates/verified-garbage-asm-x86_64/asm"
        arm = root / "crates/verified-garbage-asm-arm/asm"
        self.assertEqual(asm_layout.target_dir(root, "x86_64"), crate)
        self.assertEqual(asm_layout.target_dirs(root), {"arm": arm, "x86_64": crate})
        self.assertEqual(asm_layout.generated_files(root), {
            "src/asm/arm/mod.rs": arm / "lib.rs",
            "src/asm/x86_64/md5.rs": crate / "md5.rs", "src/asm/x86_64/mod.rs": crate / "lib.rs"})


if __name__ == "__main__":
    unittest.main()
