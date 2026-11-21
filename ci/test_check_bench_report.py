"""ci/bench_report.py's results files and the page it fills; no builds."""

import json
import pathlib
import re
import tempfile
import unittest

import bench_report


def criterion(root, group, library, size, median):
    """A Criterion result, as `cargo bench` leaves it under `root`."""
    d = root / group / library / str(size) / "new"
    d.mkdir(parents=True)
    (d / "estimates.json").write_text(json.dumps({"median": {"point_estimate": median}}))


class Records(unittest.TestCase):
    def test_record_keeps_only_what_it_has(self):
        self.assertEqual(bench_report.record("sha256", "openssl", 64, 10.0),
                         {"group": "sha256", "library": "openssl", "size": 64, "time_ns": 10.0})
        r = bench_report.record("sha256", "verified-garbage", 64, 9.0, [9.0, 9.5], "head", "abc")
        self.assertEqual((r["samples"], r["side"], r["commit"]), ([9.0, 9.5], "head", "abc"))
        # One run is its own time: no samples.
        self.assertNotIn("samples", bench_report.record("sha256", "openssl", 64, 9.0, [9.0]))

    def test_document_ids_follow_contents(self):
        a = bench_report.document({"arch": "x86_64", "shard": None}, [])
        self.assertEqual(a["format"], bench_report.FORMAT)
        self.assertEqual(a["context"], {"arch": "x86_64"})
        self.assertEqual(a["id"], bench_report.document({"arch": "x86_64"}, [])["id"])
        self.assertNotEqual(a["id"], bench_report.document({"arch": "aarch64"}, [])["id"])

    def test_meta(self):
        self.assertEqual(bench_report.parse_meta(["a=1", "url=x=y"]), {"a": "1", "url": "x=y"})
        self.assertEqual(bench_report.parse_meta(None), {})
        for bad in ("a", "=1"):
            with self.assertRaises(SystemExit):
                bench_report.parse_meta([bad])

    def test_collect_reads_criterion(self):
        with tempfile.TemporaryDirectory() as tmp:
            home = pathlib.Path(tmp)
            criterion(home, "ecdh_p256", "verified-garbage", 32, 1000.5)
            criterion(home, "ecdh_p256", "openssl", 32, 3000.0)
            criterion(home, "mul", "verified-garbage", "mul_acc4", 5.0)
            (home / "ecdh_p256" / "report").mkdir()
            doc = bench_report.collect(home, {"label": "laptop"}, "Some CPU")
        self.assertEqual(sorted((r["group"], r["library"], r["size"], r["time_ns"]) for r in doc["results"]), [
            ("ecdh_p256", "openssl", 32, 3000.0),
            ("ecdh_p256", "verified-garbage", 32, 1000.5),
            ("mul", "verified-garbage", "mul_acc4", 5.0),
        ])
        self.assertEqual((doc["context"]["label"], doc["context"]["cpu"], doc["context"]["source"]),
                         ("laptop", "Some CPU", "local"))


class Page(unittest.TestCase):
    def files(self, root):
        one = bench_report.document({"arch": "x86_64"}, [bench_report.record("sha256", "openssl", 64, 1.0)])
        two = bench_report.document({"arch": "aarch64"}, [bench_report.record("sha256", "openssl", 64, 2.0)])
        (root / "a").mkdir()
        (root / "a" / "bench-results.json").write_text(json.dumps(one))
        (root / "b").mkdir()
        (root / "b" / "bench-results.json").write_text(json.dumps(two))
        # A merged file holding one of the same again.
        (root / "merged.json").write_text(json.dumps({"files": [one]}))
        return one, two

    def test_load_merges_and_skips_repeats(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            one, two = self.files(root)
            files = bench_report.load([root])
        self.assertEqual([f["id"] for f in files], [one["id"], two["id"]])
        self.assertEqual(files[0]["name"], "bench-results.json")

    def test_load_rejects_other_json(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "x.json"
            path.write_text("{}")
            with self.assertRaises(SystemExit):
                bench_report.load([path])

    def test_template_has_one_data_element(self):
        template = bench_report.TEMPLATE.read_text()
        self.assertEqual(len(bench_report.DATA.findall(template)), 1)
        self.assertEqual(bench_report.DATA.search(template)[2], "null")
        # The page loads nothing from the network.
        self.assertIsNone(re.search(r'<(?:script|link)[^>]+(?:src|href)=', template))

    def test_embed_escapes_and_round_trips(self):
        doc = bench_report.document({"label": "</script><b>"}, [bench_report.record("x</script>", "openssl", 1, 1.0)])
        page = bench_report.embed(bench_report.TEMPLATE.read_text(), [doc], "Run <1> & co")
        self.assertIn("<title>Run &lt;1&gt; &amp; co</title>", page)
        # What the page reads back (its `extractEmbedded` matches the same way).
        data = re.search(r'<script type="application/json" id="bench-data">([\s\S]*?)</script>', page)[1]
        self.assertEqual(json.loads(data), {"files": [doc]})

    def test_html_command(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            self.files(root)
            out = root / "out.html"
            self.assertEqual(bench_report.main(["html", str(root / "a"), str(root / "b"), "-o", str(out)]), 0)
            data = json.loads(bench_report.DATA.search(out.read_text())[2])
        self.assertEqual(len(data["files"]), 2)


if __name__ == "__main__":
    unittest.main()
