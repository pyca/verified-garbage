#!/usr/bin/env python3
"""Streams the published Lean cache archive to stdout, resuming after dropped connections.

  python3 ci/fetch_lean_cache.py | zstd -dc | python3 ci/lean_cache.py unpack lean

reads ghcr.io/pyca/vg-lean-cache:latest's one layer, lean-cache.tar.zst
(lean/README.md, "Restoring the CI build cache"), with an anonymous pull
token. When the connection drops, stalls or fails, it asks for the rest of
the layer from the last byte it wrote (`Range: bytes=N-`), so the pipeline
never sees a byte twice or a gap, and gives up after RETRIES failures in a
row without progress. At the end it checks the layer's SHA-256 against its
digest and exits non-zero if they differ. It prints the cached build's
revision and its progress to stderr.

Only the standard library: an agent restoring the cache needs nothing but
`python3`, `zstd` and the Lean toolchain (whose `leantar` unpacks it).
"""

import argparse
import hashlib
import http.client
import json
import sys
import time
import urllib.request

REGISTRY = "https://ghcr.io"
REPOSITORY = "pyca/vg-lean-cache"
TAG = "latest"
CHUNK = 1 << 20
# Seconds without a byte before a connection counts as stalled: GHCR
# answers in well under a second, and time spent blocked writing to the
# pipeline does not count.
TIMEOUT = 20
RETRIES = 5
OCI_MANIFEST = "application/vnd.oci.image.manifest.v1+json"


def token(registry, repository):
    with urllib.request.urlopen(
        f"{registry}/token?scope=repository:{repository}:pull", timeout=TIMEOUT
    ) as response:
        return json.load(response)["token"]


def get(url, bearer, headers=()):
    request = urllib.request.Request(url, headers={"Authorization": f"Bearer {bearer}", **dict(headers)})
    return urllib.request.urlopen(request, timeout=TIMEOUT)


def layer(registry, repository, tag):
    """The digest and size of the manifest's one layer, and its annotations."""
    with get(f"{registry}/v2/{repository}/manifests/{tag}", token(registry, repository),
             [("Accept", OCI_MANIFEST)]) as response:
        manifest = json.load(response)
    [blob] = manifest["layers"]
    return blob["digest"], blob["size"], manifest.get("annotations", {})


def fetch(out, registry=REGISTRY, repository=REPOSITORY, tag=TAG, sleep=time.sleep, log=sys.stderr):
    digest, size, annotations = layer(registry, repository, tag)
    revision = annotations.get("org.opencontainers.image.revision", "unknown")
    print(f"Lean cache of {revision}: {size} bytes", file=log)
    url = f"{registry}/v2/{repository}/blobs/{digest}"
    sha256 = hashlib.sha256()
    offset = 0
    failures = 0
    while offset < size:
        start = offset
        try:
            # A fresh token for every attempt: an anonymous one expires.
            ranged = [("Range", f"bytes={offset}-")] if offset else []
            with get(url, token(registry, repository), ranged) as response:
                if offset and not (response.status == 206 and response.headers.get(
                        "Content-Range", "").startswith(f"bytes {offset}-")):
                    raise OSError(f"the registry did not resume at byte {offset}")
                while chunk := response.read(CHUNK):
                    chunk = chunk[:size - offset]
                    try:
                        out.write(chunk)
                    except BrokenPipeError:
                        raise SystemExit("the output was closed")
                    sha256.update(chunk)
                    offset += len(chunk)
            if offset < size:
                raise OSError("the connection closed early")
        except (OSError, http.client.HTTPException) as error:
            failures = 1 if offset > start else failures + 1
            if failures >= RETRIES:
                raise SystemExit(f"Giving up after {offset} of {size} bytes: {error}")
            delay = 2 ** failures
            print(f"Connection failed after {offset} of {size} bytes ({error}); "
                  f"resuming in {delay} s", file=log)
            sleep(delay)
    out.flush()
    if "sha256:" + sha256.hexdigest() != digest:
        raise SystemExit(f"The download does not match {digest}: restore again")
    print(f"Downloaded {size} bytes, matching {digest}", file=log)


def main(argv=None):
    # It takes no arguments, but answers --help (rather than starting a
    # 1 GB download) and refuses anything else.
    argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    ).parse_args(argv)
    fetch(sys.stdout.buffer)


if __name__ == "__main__":
    main()
