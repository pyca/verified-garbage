#!/usr/bin/env python3
"""Downloads the NIST ACVP test vector files of ci/acvp_vectors.toml into a
directory, the tests' `ACVP_ROOT`, checking each file's SHA-256.

Usage: python3 ci/fetch_acvp_vectors.py <dir>

A file already there with the right SHA-256 is kept. A download that fails
or is cut off is retried; one whose SHA-256 is wrong fails the script, which
leaves nothing at that file's path.
"""

from __future__ import annotations

import hashlib
import pathlib
import sys
import re
import time
import urllib.request

MANIFEST = pathlib.Path(__file__).resolve().parent / "acvp_vectors.toml"
ATTEMPTS = 5


def manifest() -> tuple[str, list[dict[str, str]]]:
    """The manifest's `base` and its files: a subset of TOML (string keys
    and `[[file]]` tables), read without `tomllib`, which the Python of some
    runners lacks."""
    base, files, table = None, [], None
    for line in MANIFEST.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if line == "[[file]]":
            table = {}
            files.append(table)
        elif m := re.fullmatch(r'(\w+) = "([^"]*)"', line):
            if table is not None:
                table[m[1]] = m[2]
            elif m[1] == "base":
                base = m[2]
    assert base and files and all({"path", "sha256"} <= f.keys() for f in files)
    return base, files


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def download(url: str) -> bytes:
    for attempt in range(1, ATTEMPTS + 1):
        try:
            with urllib.request.urlopen(url, timeout=60) as response:
                return response.read()
        except OSError as e:
            if attempt == ATTEMPTS:
                raise
            print(f"{url}: {e}; retrying", file=sys.stderr)
            time.sleep(2**attempt)
    raise AssertionError("unreachable")


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    root = pathlib.Path(sys.argv[1])
    base, files = manifest()
    for entry in files:
        dest = root / entry["path"]
        if dest.is_file() and sha256(dest.read_bytes()) == entry["sha256"]:
            continue
        url = f"{base}/{entry['path']}"
        data = download(url)
        if sha256(data) != entry["sha256"]:
            print(f"{url}: SHA-256 {sha256(data)}, not {entry['sha256']}", file=sys.stderr)
            return 1
        dest.parent.mkdir(parents=True, exist_ok=True)
        tmp = dest.with_suffix(".part")
        tmp.write_bytes(data)
        tmp.replace(dest)
    return 0


if __name__ == "__main__":
    sys.exit(main())
