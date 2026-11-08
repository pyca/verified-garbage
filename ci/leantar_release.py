#!/usr/bin/env python3
"""The project's `leantar`, from a release of reaperhulk/leangz.

  python3 ci/leantar_release.py   # prints its path, downloading it once

leangz, the toolchain's compressor for Lake's per-module `.ltar` archives, with
what this project needs and digama0/leangz does not have yet: a faster unpack
(each payload decompressed in one call into zstd), batch packing (`-p -`, a
build's 16,000 modules in one process, and `--level`, digama0/leangz#13), and
`-x --empty-private` (each module's `.olean.private` written as an empty file;
`ci/lean_cache.py restore --empty-private` and `unpack --empty-private`).
`ci/lean_cache.py` packs and unpacks with it.

The fork's release workflow builds it for each platform and attaches the
archives to the release, with their `SHA256SUMS`. `ci/leantar/release.toml`
pins the release and the SHA-256 of each archive: a download is used only if it
matches. It is kept in `$XDG_CACHE_HOME/verified-garbage/leantar/<tag>/`
(`~/.cache` by default), so only the first use downloads it. GitHub's release
downloads now and then fail with a 5xx or a dropped connection, so a download
that fails that way is tried again, after 2, 4, 8 and 16 seconds.
"""

import argparse
import hashlib
import http.client
import io
import os
import platform
import sys
import tarfile
import tempfile
import time
import tomllib
import urllib.error
import urllib.request
from pathlib import Path

RELEASE = Path(__file__).resolve().parent / "leantar" / "release.toml"
# Seconds to wait before each retry of a download that failed transiently.
BACKOFF = (2, 4, 8, 16)
TIMEOUT = 60


def urlopen(url):
    return urllib.request.urlopen(url, timeout=TIMEOUT)


def transient(e):
    """Whether a download that failed with `e` may succeed if tried again."""
    if isinstance(e, urllib.error.HTTPError):
        return e.code == 429 or e.code >= 500
    return isinstance(e, (urllib.error.URLError, http.client.HTTPException, OSError))


def download(url, opener=urlopen, sleep=time.sleep):
    """The bytes at `url`, retrying a transient failure after each `BACKOFF`."""
    for delay in (*BACKOFF, None):
        try:
            with opener(url) as r:
                return r.read()
        except Exception as e:
            if delay is None or not transient(e):
                raise
            print(f"{url}: {e}; retrying in {delay} s", file=sys.stderr)
            sleep(delay)


def target(system=None, machine=None):
    """The release's name for this platform (Rust's target triple)."""
    system = system or platform.system()
    machine = (machine or platform.machine()).lower()
    arch = {"x86_64": "x86_64", "amd64": "x86_64", "aarch64": "aarch64", "arm64": "aarch64"}.get(machine)
    os_name = {"Linux": "unknown-linux-musl", "Darwin": "apple-darwin"}.get(system)
    if arch is None or os_name is None:
        raise SystemExit(f"no leantar release for {system} {machine}: build leangz yourself "
                         "and pass its leantar with --leantar")
    return f"{arch}-{os_name}"


def release(path=RELEASE):
    with open(path, "rb") as f:
        return tomllib.load(f)


def cache_dir():
    base = os.environ.get("XDG_CACHE_HOME") or Path.home() / ".cache"
    return Path(base) / "verified-garbage" / "leantar"


def unpack_binary(data, name):
    """The `leantar` of the release archive `data` (`<name>/leantar`)."""
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as tar:
        member = tar.getmember(f"{name}/leantar")
        if not member.isfile():
            raise SystemExit(f"{name}: leantar is not a file in the archive")
        return tar.extractfile(member).read()


def fetch(rel=None, plat=None, cache=None, opener=urlopen, sleep=time.sleep):
    """The path of the release's `leantar` for `plat`, downloaded and checked
    once into `cache`."""
    rel = rel or release()
    plat = plat or target()
    tag = rel["tag"]
    want = rel["sha256"].get(plat)
    if want is None:
        raise SystemExit(f"{RELEASE.name} pins no archive for {plat}")
    dest = (cache or cache_dir()) / tag / plat / "leantar"
    if dest.is_file():
        return dest
    name = f"leantar-{tag}-{plat}"
    url = rel["url"].format(tag=tag, name=name)
    print(f"Downloading {url}", file=sys.stderr)
    data = download(url, opener, sleep)
    got = hashlib.sha256(data).hexdigest()
    if got != want:
        raise SystemExit(f"{url}: SHA-256 {got}, but {RELEASE.name} pins {want}")
    binary = unpack_binary(data, name)
    dest.parent.mkdir(parents=True, exist_ok=True)
    # Written beside it and renamed, so that a binary there is always whole.
    with tempfile.NamedTemporaryFile(dir=dest.parent, delete=False) as f:
        f.write(binary)
    os.chmod(f.name, 0o755)
    os.replace(f.name, dest)
    return dest


def main(argv=None):
    argparse.ArgumentParser(description=__doc__.split("\n")[0]).parse_args(argv)
    print(fetch())


if __name__ == "__main__":
    main()
