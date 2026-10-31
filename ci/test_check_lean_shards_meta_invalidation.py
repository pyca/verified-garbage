"""Live regression for meta-import IR dependencies behind private imports."""

import hashlib
import pathlib
import shutil
import subprocess
import tempfile
import unittest

import lean_shards as shards


@unittest.skipUnless(shutil.which("lake"), "Lean toolchain is not installed")
class MetaInvalidation(unittest.TestCase):
    def test_private_ir_change_rebuilds_meta_consumers_and_preserves_ordinary_cache(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / "lean-toolchain").write_text((shards.LEAN / "lean-toolchain").read_text())
            (root / "lakefile.toml").write_text('''name = "metaInvalidation"
defaultTargets = ["Demo"]
[[lean_lib]]
name = "Demo"
roots = []
globs = ["Demo.+"]
platformIndependent = true
''')
            sources = {
                "Demo.C": "module\n@[expose] public def hidden : Nat := 1\n",
                "Demo.B": "module\nimport Demo.C\npublic def answer : Nat := hidden\n",
                "Demo.Ordinary": "module\nimport Demo.B\nexample : True := trivial\n",
                "Demo.Meta": "module\nmeta import Demo.B\nexample : True := trivial\n",
                "Demo.PublicMeta": "module\npublic meta import Demo.B\n",
                "Demo.Downstream": "module\nimport Demo.PublicMeta\n",
                "Demo.PrivateMeta": "module\nmeta import Demo.B\n",
                "Demo.PrivateDownstream": "module\nimport Demo.PrivateMeta\n",
                "Demo.Mixed": "module\npublic import Demo.B\nmeta import Demo.B\n",
                "Demo.MixedDownstream": "module\nimport Demo.Mixed\n",
            }
            paths = {}
            for module, text in sources.items():
                path = root.joinpath(*module.split(".")).with_suffix(".lean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
                paths[module] = path

            def build():
                r = subprocess.run(["lake", "build", "--log-level=warning"], cwd=root,
                                   capture_output=True, text=True, timeout=60)
                log = r.stdout + r.stderr
                self.assertEqual(r.returncode, 0, log)
                return log

            build()
            self.assertEqual(shards.BUILT.findall(build()), [])
            modes = {}
            imps, vis, _ = shards.source_info(paths, import_modes=modes)
            closure = shards.closures(imps)
            changed = {"Demo.C"}
            self.assertEqual(shards.stale_of(changed, shards.reads(imps, closure, vis)),
                             {"Demo.C", "Demo.B"})
            predicted = shards.stale_of(changed, shards.reads(imps, closure, vis, modes))
            self.assertEqual(predicted, {"Demo.C", "Demo.B", "Demo.Meta", "Demo.PublicMeta",
                                         "Demo.Downstream", "Demo.PrivateMeta", "Demo.Mixed"})
            lib = root / ".lake/build/lib/lean/Demo"
            before = {ext: hashlib.sha256((lib / ("B" + ext)).read_bytes()).digest()
                      for ext in (".olean", ".ir")}
            paths["Demo.C"].write_text("module\n@[expose] public def hidden : Nat := 2\n")
            log = build()
            actual = {m for m, components in shards.log_timings(log)["components"].items()
                      if "lean" in components}
            self.assertEqual(actual, predicted, log)
            self.assertEqual(before[".olean"], hashlib.sha256((lib / "B.olean").read_bytes()).digest())
            self.assertNotEqual(before[".ir"], hashlib.sha256((lib / "B.ir").read_bytes()).digest())
            self.assertEqual(shards.BUILT.findall(build()), [])


if __name__ == "__main__":
    unittest.main()
