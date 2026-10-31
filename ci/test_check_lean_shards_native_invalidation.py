"""Live Lake regression: native sibling changes cross private import boundaries."""

import pathlib
import shutil
import subprocess
import tempfile
import unittest
from unittest import mock

import lean_shards as shards


@unittest.skipUnless(shutil.which("lake"), "Lean toolchain is not installed")
class NativeInvalidation(unittest.TestCase):
    def check_native_sibling_change(self, independent):
        toolchain = (shards.LEAN / "lean-toolchain").read_text()
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / "lean-toolchain").write_text(toolchain)
            (root / "lakefile.toml").write_text('''name = "nativeInvalidation"
defaultTargets = ["Base", "Native", "Broad"]

[[lean_lib]]
name = "Broad"
roots = []
globs = ["Demo.+"]
PLATFORM_FLAG

[[lean_lib]]
name = "Native"
roots = []
globs = ["Demo.Native.+"]
precompileModules = true

[[lean_lib]]
name = "Base"
roots = []
globs = ["Demo.Base.+"]
precompileModules = true
'''.replace("PLATFORM_FLAG", f"platformIndependent = {str(independent).lower()}"))
            sources = {
                "Demo.Base.Helper": "module\n@[expose] public def helper : Nat := 42\n",
                "Demo.Native.Main": "module\npublic import Demo.Base.Helper\n"
                                    "@[expose] public def answer : Nat := helper\n",
                "Demo.Base.Unrelated": "module\n@[expose] public def unrelated : Nat := 7\n",
                "Demo.Consumer": "module\nimport Demo.Native.Main\nexample : answer = 42 := rfl\n",
            }
            for module, text in sources.items():
                path = root.joinpath(*module.split(".")).with_suffix(".lean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)

            def build(*targets):
                result = subprocess.run(
                    ["lake", "build", "--log-level=warning", *targets], cwd=root,
                    capture_output=True, text=True, timeout=60)
                log = result.stdout + result.stderr
                self.assertEqual(result.returncode, 0, log)
                return log

            build()
            # A scoped target already resolves correctly; no library-first fix
            # is needed. Both commands must reuse the same canonical cache.
            self.assertEqual(shards.BUILT.findall(build("+Demo.Consumer")), [])
            self.assertEqual(shards.BUILT.findall(build("Native", "+Demo.Consumer")), [])

            imps = {"Demo.Base.Helper": [], "Demo.Native.Main": ["Demo.Base.Helper"],
                    "Demo.Base.Unrelated": [], "Demo.Consumer": ["Demo.Native.Main"]}
            closure = shards.closures(imps)
            visibility = dict.fromkeys(imps, ([], []))
            visibility["Demo.Native.Main"] = (["Demo.Base.Helper"], [])
            ordinary = shards.reads(imps, closure, visibility)
            with mock.patch.object(shards, "LEAN", root):
                libraries = shards.precompiled_libraries(closure)
                trace_modules = shards.native_trace_modules(closure)
            native = shards.native_reads(imps, closure, libraries, trace_modules)
            changed = {"Demo.Base.Unrelated"}
            self.assertEqual(shards.stale_of(changed, ordinary), changed)
            expected = shards.stale_of(changed, {m: ordinary[m] | native[m] for m in imps})
            self.assertEqual(expected, changed | {"Demo.Native.Main"} |
                             (set() if independent else {"Demo.Consumer"}))

            (root / "Demo/Base/Unrelated.lean").write_text(
                "module\n@[expose] public def unrelated : Nat := 8\n")
            log = build("+Demo.Consumer")
            observed = {m for m, components in shards.log_timings(log)["components"].items()
                        if "lean" in components}
            self.assertEqual(observed, expected, log)
            self.assertEqual(shards.BUILT.findall(build("+Demo.Consumer")), [])

    def test_shared_library_hashes_invalidate_native_and_ordinary_consumers(self):
        self.check_native_sibling_change(False)

    def test_platform_independent_proofs_stay_cached_but_native_consumers_rebuild(self):
        self.check_native_sibling_change(True)


if __name__ == "__main__":
    unittest.main()
