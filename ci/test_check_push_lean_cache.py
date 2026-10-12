"""Push the Lean cache image to a fake registry that asks for a token, as GHCR does."""

import base64
import hashlib
import http.server
import io
import json
import os
from pathlib import Path
import tarfile
import tempfile
import threading
import unittest
import urllib.parse

import push_lean_cache


class FakeRegistry(http.server.BaseHTTPRequestHandler):
    """A registry with token authentication and relative upload locations."""

    blobs = {}
    manifests = {}
    uploads = []
    puts = []

    def log_message(self, *args):
        pass

    def reply(self, status, body=b"", headers=()):
        self.send_response(status)
        for k, v in headers:
            self.send_header(k, v)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(body)

    def authorized(self):
        if self.headers.get("Authorization") == "Bearer the-token":
            return True
        realm = f"http://{self.headers['Host']}/token"
        self.reply(401, headers=[("WWW-Authenticate",
                                  f'Bearer realm="{realm}",service="fake",'
                                  f'scope="repository:pyca/vg-lean-cache:pull"')])
        return False

    def do_GET(self):
        url = urllib.parse.urlsplit(self.path)
        query = urllib.parse.parse_qs(url.query)
        basic = base64.b64encode(b"actor:secret").decode()
        if (url.path == "/token" and self.headers.get("Authorization") == f"Basic {basic}"
                and query == {"service": ["fake"],
                              "scope": ["repository:pyca/vg-lean-cache:pull,push"]}):
            self.reply(200, json.dumps({"token": "the-token"}).encode())
        else:
            self.reply(403)

    def do_HEAD(self):
        if self.authorized():
            digest = self.path.rsplit("/", 1)[1]
            self.reply(200 if digest in self.blobs else 404)

    def do_POST(self):
        if self.authorized():
            self.uploads.append(self.path)
            self.reply(202, headers=[("Location", "/v2/pyca/vg-lean-cache/blobs/uploads/u1?state=x")])

    def do_PUT(self):
        if not self.authorized():
            return
        body = self.rfile.read(int(self.headers["Content-Length"]))
        url = urllib.parse.urlsplit(self.path)
        self.puts.append(self.path)
        if url.path.startswith("/v2/pyca/vg-lean-cache/blobs/uploads/u1"):
            digest = urllib.parse.parse_qs(url.query)["digest"][0]
            if digest != "sha256:" + hashlib.sha256(body).hexdigest():
                return self.reply(400)
            self.blobs[digest] = body
            self.reply(201)
        elif url.path == "/v2/pyca/vg-lean-cache/manifests/latest":
            self.manifests["latest"] = (self.headers["Content-Type"], body)
            self.reply(201)
        else:
            self.reply(404)


class PushLeanCacheTests(unittest.TestCase):
    def setUp(self):
        FakeRegistry.blobs = {}
        FakeRegistry.manifests = {}
        FakeRegistry.uploads = []
        FakeRegistry.puts = []
        self.server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), FakeRegistry)
        threading.Thread(target=self.server.serve_forever, daemon=True).start()
        self.host = f"127.0.0.1:{self.server.server_port}"
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.archive = Path(tmp.name) / "lean-cache.tar.zst"
        # Not a multiple of the tar block, and over one read chunk.
        self.archive.write_bytes(os.urandom(push_lean_cache.CHUNK + 1000))

    def tearDown(self):
        self.server.shutdown()
        self.server.server_close()

    def push(self, password="secret"):
        push_lean_cache.push(str(self.archive), f"{self.host}/pyca/vg-lean-cache:latest",
                             {"io.pyca.lean.cache-key": "key"}, "actor", password, "http")

    def test_image_holds_the_archive_and_labels(self):
        self.push()
        media_type, body = FakeRegistry.manifests["latest"]
        manifest = json.loads(body)
        self.assertEqual(media_type, push_lean_cache.OCI_MANIFEST)
        [layer] = manifest["layers"]
        self.assertEqual(layer["mediaType"], push_lean_cache.OCI_LAYER)
        data = FakeRegistry.blobs[layer["digest"]]
        self.assertEqual(layer["size"], len(data))
        with tarfile.open(fileobj=io.BytesIO(data)) as tar:
            self.assertEqual(tar.getnames(), ["lean-cache.tar.zst"])
            self.assertEqual(tar.extractfile("lean-cache.tar.zst").read(),
                             self.archive.read_bytes())
        config = json.loads(FakeRegistry.blobs[manifest["config"]["digest"]])
        self.assertEqual(config["config"]["Labels"], {"io.pyca.lean.cache-key": "key"})
        self.assertEqual(config["rootfs"]["diff_ids"], [layer["digest"]])

    def test_existing_blobs_are_not_uploaded_again(self):
        self.push()
        uploads = len(FakeRegistry.uploads)
        self.push()
        self.assertEqual(len(FakeRegistry.uploads), uploads)

    def test_rejected_credentials_fail(self):
        with self.assertRaises(SystemExit):
            self.push(password="wrong")
        self.assertEqual(FakeRegistry.manifests, {})


if __name__ == "__main__":
    unittest.main()
