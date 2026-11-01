"""`leantar_release.py`: the platform's archive, checked and kept; no network."""

import hashlib
import io
import os
import tarfile
import tempfile
import unittest
from pathlib import Path

import leantar_release

TAG = "v1.2.3-vg.1"
PLAT = "x86_64-unknown-linux-musl"


def archive(name, binary=b"\x7fELF leantar"):
    data = io.BytesIO()
    with tarfile.open(fileobj=data, mode="w:gz") as tar:
        info = tarfile.TarInfo(f"{name}/leantar")
        info.size = len(binary)
        tar.addfile(info, io.BytesIO(binary))
    return data.getvalue()


class Opener:
    """Serves `data` for any URL, recording each."""

    def __init__(self, data):
        self.data, self.urls = data, []

    def __call__(self, url):
        self.urls.append(url)
        return io.BytesIO(self.data)


class Target(unittest.TestCase):
    def test_platforms(self):
        self.assertEqual(leantar_release.target("Linux", "x86_64"), "x86_64-unknown-linux-musl")
        self.assertEqual(leantar_release.target("Linux", "aarch64"), "aarch64-unknown-linux-musl")
        self.assertEqual(leantar_release.target("Darwin", "arm64"), "aarch64-apple-darwin")
        self.assertEqual(leantar_release.target("Darwin", "x86_64"), "x86_64-apple-darwin")
        self.assertIsInstance(leantar_release.target(), str)

    def test_no_release(self):
        with self.assertRaisesRegex(SystemExit, "no leantar release for Windows"):
            leantar_release.target("Windows", "AMD64")
        with self.assertRaisesRegex(SystemExit, "no leantar release for Linux riscv64"):
            leantar_release.target("Linux", "riscv64")


class Fetch(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.cache = Path(self.tmp.name)
        self.data = archive(f"leantar-{TAG}-{PLAT}")
        self.rel = {"tag": TAG, "url": "https://example.com/{tag}/{name}.tar.gz",
                    "sha256": {PLAT: hashlib.sha256(self.data).hexdigest()}}

    def tearDown(self):
        self.tmp.cleanup()

    def test_downloads_once(self):
        opener = Opener(self.data)
        path = leantar_release.fetch(self.rel, PLAT, self.cache, opener)
        self.assertEqual(path, self.cache / TAG / PLAT / "leantar")
        self.assertEqual(path.read_bytes(), b"\x7fELF leantar")
        self.assertTrue(os.access(path, os.X_OK))
        self.assertEqual(opener.urls, [f"https://example.com/{TAG}/leantar-{TAG}-{PLAT}.tar.gz"])
        # Kept: the next use downloads nothing.
        self.assertEqual(leantar_release.fetch(self.rel, PLAT, self.cache, opener), path)
        self.assertEqual(len(opener.urls), 1)

    def test_rejects_another_archive(self):
        opener = Opener(archive(f"leantar-{TAG}-{PLAT}", b"something else"))
        with self.assertRaisesRegex(SystemExit, "SHA-256 .* but release.toml pins"):
            leantar_release.fetch(self.rel, PLAT, self.cache, opener)
        self.assertFalse((self.cache / TAG).exists())

    def test_platform_not_pinned(self):
        with self.assertRaisesRegex(SystemExit, "pins no archive for aarch64-apple-darwin"):
            leantar_release.fetch(self.rel, "aarch64-apple-darwin", self.cache, Opener(self.data))

    def test_archive_without_the_binary(self):
        data = archive("another-name")
        self.rel["sha256"][PLAT] = hashlib.sha256(data).hexdigest()
        with self.assertRaises(KeyError):
            leantar_release.fetch(self.rel, PLAT, self.cache, Opener(data))

    def test_pinned_release(self):
        # Every platform `target` names has a hash, and the URL names the archive.
        rel = leantar_release.release()
        for system, machine in (("Linux", "x86_64"), ("Linux", "aarch64"),
                                ("Darwin", "arm64"), ("Darwin", "x86_64")):
            self.assertRegex(rel["sha256"][leantar_release.target(system, machine)], "^[0-9a-f]{64}$")
        self.assertIn("{tag}", rel["url"])
        self.assertIn("{name}", rel["url"])


if __name__ == "__main__":
    unittest.main()
