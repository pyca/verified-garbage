"""Fetch the Lean cache from a fake registry whose connections drop."""

import hashlib
import http.server
import io
import json
import os
import threading
import unittest
from contextlib import redirect_stderr, redirect_stdout
from unittest import mock

import fetch_lean_cache

BLOB = os.urandom(3 * fetch_lean_cache.CHUNK + 1234)
DIGEST = "sha256:" + hashlib.sha256(BLOB).hexdigest()


class FakeRegistry(http.server.BaseHTTPRequestHandler):
    """Serves one manifest and its layer, dropping each blob response at
    the next offset in `drops` (after sending that many bytes in all)."""

    protocol_version = "HTTP/1.1"
    drops = []
    ignore_range = False
    digest = DIGEST
    ranges = []

    def log_message(self, *args):
        pass

    def send(self, status, body, headers=()):
        self.send_response(status)
        for k, v in headers:
            self.send_header(k, v)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        if self.path.startswith("/token?"):
            return self.send(200, json.dumps({"token": "t"}).encode())
        if self.headers.get("Authorization") != "Bearer t":
            return self.send(401, b"")
        if self.path == "/v2/pyca/vg-lean-cache/manifests/latest":
            manifest = {"layers": [{"digest": self.digest, "size": len(BLOB)}],
                        "annotations": {"org.opencontainers.image.revision": "abc"}}
            return self.send(200, json.dumps(manifest).encode())
        if self.path != f"/v2/pyca/vg-lean-cache/blobs/{self.digest}":
            return self.send(404, b"")
        rng = self.headers.get("Range")
        self.ranges.append(rng)
        start = int(rng[len("bytes="):-1]) if rng and not self.ignore_range else 0
        status, headers = 200, []
        if start:
            status = 206
            headers = [("Content-Range", f"bytes {start}-{len(BLOB) - 1}/{len(BLOB)}")]
        end = self.drops.pop(0) if self.drops else len(BLOB)
        self.send_response(status)
        for k, v in headers:
            self.send_header(k, v)
        # Announce the whole rest, then send only up to the drop.
        self.send_header("Content-Length", str(len(BLOB) - start))
        self.end_headers()
        try:
            self.wfile.write(BLOB[start:max(start, end)])
        except ConnectionError:
            pass  # The client refused a response that does not resume.
        self.close_connection = True


class FetchLeanCacheTests(unittest.TestCase):
    def setUp(self):
        FakeRegistry.drops = []
        FakeRegistry.ignore_range = False
        FakeRegistry.digest = DIGEST
        FakeRegistry.ranges = []
        self.server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), FakeRegistry)
        # A short poll, so that `shutdown` in tearDown does not wait out the default
        # half second.
        threading.Thread(target=self.server.serve_forever, args=(0.01,), daemon=True).start()
        self.sleeps = []

    def tearDown(self):
        self.server.shutdown()
        self.server.server_close()

    def fetch(self):
        out, log = io.BytesIO(), io.StringIO()
        fetch_lean_cache.fetch(out, registry=f"http://127.0.0.1:{self.server.server_port}",
                               sleep=self.sleeps.append, log=log)
        return out.getvalue(), log.getvalue()

    def test_uninterrupted_download(self):
        data, log = self.fetch()
        self.assertEqual(data, BLOB)
        self.assertEqual(FakeRegistry.ranges, [None])
        self.assertIn("Lean cache of abc", log)
        self.assertEqual(self.sleeps, [])

    def test_resumes_where_each_connection_dropped(self):
        FakeRegistry.drops = [1000, 2 * fetch_lean_cache.CHUNK + 5]
        data, log = self.fetch()
        self.assertEqual(data, BLOB)
        self.assertEqual(FakeRegistry.ranges,
                         [None, "bytes=1000-", f"bytes={2 * fetch_lean_cache.CHUNK + 5}-"])
        self.assertIn("Connection failed after 1000 of", log)
        # Each drop came after progress: no backoff builds up.
        self.assertEqual(self.sleeps, [2, 2])

    def test_gives_up_without_progress(self):
        FakeRegistry.drops = [1000] + [1000] * fetch_lean_cache.RETRIES
        with self.assertRaises(SystemExit) as raised:
            self.fetch()
        self.assertIn("Giving up after 1000 of", str(raised.exception))
        self.assertEqual(self.sleeps, [2, 4, 8, 16])

    def test_refuses_a_response_that_does_not_resume(self):
        FakeRegistry.drops = [1000]
        FakeRegistry.ignore_range = True
        with self.assertRaises(SystemExit) as raised:
            self.fetch()
        self.assertIn("did not resume at byte 1000", str(raised.exception))

    def test_digest_mismatch_fails(self):
        FakeRegistry.digest = "sha256:" + "0" * 64
        with self.assertRaises(SystemExit) as raised:
            self.fetch()
        self.assertIn("does not match", str(raised.exception))


class Arguments(unittest.TestCase):
    """--help answers without downloading anything; other arguments are refused."""

    def run_main(self, argv):
        stdout, stderr = io.StringIO(), io.StringIO()
        with mock.patch.object(fetch_lean_cache, "fetch") as fetch, \
                redirect_stdout(stdout), redirect_stderr(stderr), \
                self.assertRaises(SystemExit) as raised:
            fetch_lean_cache.main(argv)
        fetch.assert_not_called()
        return raised.exception.code, stdout.getvalue(), stderr.getvalue()

    def test_help(self):
        code, stdout, _ = self.run_main(["--help"])
        self.assertEqual(code, 0)
        self.assertIn("usage:", stdout)
        self.assertIn("zstd -dc | python3 ci/lean_cache.py unpack", stdout)

    def test_refuses_arguments(self):
        code, _, stderr = self.run_main(["lean"])
        self.assertEqual(code, 2)
        self.assertIn("unrecognized arguments", stderr)

    def test_no_arguments_fetches_to_stdout(self):
        with mock.patch.object(fetch_lean_cache, "fetch") as fetch:
            fetch_lean_cache.main([])
        fetch.assert_called_once_with(fetch_lean_cache.sys.stdout.buffer)


if __name__ == "__main__":
    unittest.main()
