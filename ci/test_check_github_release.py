"""`github_release.py`: public and authenticated downloads, and retries; no network."""

import io
import json
import os
import tempfile
import unittest
import urllib.error
import urllib.request
from pathlib import Path
from unittest import mock

import github_release

API = "https://api.github.com"
ASSET = f"{API}/repos/owner/repo/releases/assets/7"


class Server:
    """Serves the API's release and asset, and public URLs, recording each request."""

    def __init__(self, errors=()):
        self.errors, self.requests = list(errors), []

    def __call__(self, req):
        self.requests.append(req)
        if self.errors:
            raise self.errors.pop(0)
        url = req.full_url
        if url == ASSET or url.startswith("https://github.com/"):
            return io.BytesIO(b"data")
        if url.startswith(f"{API}/repos/owner/repo/releases/"):
            return io.BytesIO(json.dumps({"tag_name": "v1", "assets": [
                {"name": "other.tar.gz", "url": f"{API}/repos/owner/repo/releases/assets/6"},
                {"name": "tool.tar.gz", "url": ASSET}]}).encode())
        raise AssertionError(url)


def http_error(code):
    return urllib.error.HTTPError("https://example.com", code, "error", {}, None)


class Download(unittest.TestCase):
    def setUp(self):
        self.slept = []

    def download(self, server, tag="v1", name="tool.tar.gz", token=None):
        return github_release.download("owner/repo", tag, name, token, server, self.slept.append)

    def test_public(self):
        server = Server()
        self.assertEqual(self.download(server), b"data")
        self.assertEqual(self.download(server, tag="latest"), b"data")
        self.assertEqual([r.full_url for r in server.requests], [
            "https://github.com/owner/repo/releases/download/v1/tool.tar.gz",
            "https://github.com/owner/repo/releases/latest/download/tool.tar.gz"])
        for req in server.requests:
            self.assertFalse(req.has_header("Authorization"))
            self.assertIsNone(req.get_header("Authorization"))

    def test_authenticated(self):
        server = Server()
        self.assertEqual(self.download(server, token="secret"), b"data")
        self.assertEqual(self.download(server, tag="latest", token="secret"), b"data")
        self.assertEqual([r.full_url for r in server.requests], [
            f"{API}/repos/owner/repo/releases/tags/v1", ASSET,
            f"{API}/repos/owner/repo/releases/latest", ASSET])
        for req in server.requests:
            # Sent to the API alone: not copied onto a redirect.
            self.assertEqual(req.unredirected_hdrs["Authorization"], "Bearer secret")
            self.assertNotIn("Authorization", req.headers)
        self.assertEqual(server.requests[1].get_header("Accept"), "application/octet-stream")

    def test_token_not_redirected(self):
        # What urllib sends to the host an asset redirects to.
        req = github_release.api_request(ASSET, "secret", "application/octet-stream")
        handler = urllib.request.HTTPRedirectHandler()
        new = handler.redirect_request(req, None, 302, "Found", {},
                                       "https://release-assets.example.com/x")
        self.assertIsNone(new.get_header("Authorization"))

    def test_only_api_urls(self):
        with self.assertRaisesRegex(SystemExit, "not a URL of https://api.github.com"):
            github_release.api_request("https://example.com/x", "secret", "*/*")

    def test_no_such_file(self):
        with self.assertRaisesRegex(SystemExit, "owner/repo v1: no file missing.tar.gz"):
            self.download(Server(), name="missing.tar.gz", token="secret")

    def test_retries_transient_failures(self):
        server = Server([http_error(503), http_error(429), urllib.error.URLError("reset"),
                         ConnectionResetError()])
        self.assertEqual(self.download(server), b"data")
        self.assertEqual(len(server.requests), 5)
        self.assertEqual(self.slept, [2, 4, 8, 16])

    def test_gives_up(self):
        server = Server([http_error(504)] * 5)
        with self.assertRaises(urllib.error.HTTPError):
            self.download(server, token="secret")
        self.assertEqual(len(server.requests), 5)
        self.assertEqual(self.slept, [2, 4, 8, 16])

    def test_client_error_not_retried(self):
        server = Server([http_error(404)])
        with self.assertRaises(urllib.error.HTTPError):
            self.download(server)
        self.assertEqual(len(server.requests), 1)
        self.assertEqual(self.slept, [])

    def test_other_error_not_retried(self):
        with self.assertRaises(ValueError):
            self.download(Server([ValueError("bad")]))
        self.assertEqual(self.slept, [])


class Main(unittest.TestCase):
    def test_writes_the_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "tool.tar.gz"
            with mock.patch.dict(os.environ, {"GH_TOKEN": "secret"}), \
                 mock.patch.object(github_release, "urlopen", Server()) as server:
                github_release.main(["owner/repo", "latest", "tool.tar.gz", str(out)])
            self.assertEqual(out.read_bytes(), b"data")
            self.assertEqual(server.requests[0].full_url, f"{API}/repos/owner/repo/releases/latest")
            self.assertEqual(os.listdir(tmp), ["tool.tar.gz"])


if __name__ == "__main__":
    unittest.main()
