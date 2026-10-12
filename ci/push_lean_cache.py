#!/usr/bin/env python3
"""Publishes the Lean cache archive as a one-layer image, with the standard library.

  push_lean_cache.py ARCHIVE IMAGE [LABEL=VALUE ...]

pushes ghcr.io/<name>:<tag> (IMAGE) whose one uncompressed layer is a tar
holding ARCHIVE as `lean-cache.tar.zst`, and whose image config carries the
LABELs, through the registry's HTTP API (the OCI distribution spec). The
token is GH_TOKEN, for the user GITHUB_ACTOR.

This is the image `docker buildx build` made from `FROM scratch` and one
`COPY`, which `docker cp` and the README's `curl` restore read, without
Docker's copies of the archive: buildx copied all of it into its build
context, again into the layer and read it a third time to export it, before
pushing it.
"""

import base64
import hashlib
import http.client
import json
import os
import sys
import tarfile
import urllib.parse

MEMBER = "lean-cache.tar.zst"
CHUNK = 1 << 20
OCI_MANIFEST = "application/vnd.oci.image.manifest.v1+json"
OCI_CONFIG = "application/vnd.oci.image.config.v1+json"
OCI_LAYER = "application/vnd.oci.image.layer.v1.tar"


class Layer:
    """The layer tar: ARCHIVE's header, its contents, padding and the end."""

    def __init__(self, archive):
        self.archive = archive
        size = os.path.getsize(archive)
        info = tarfile.TarInfo(MEMBER)
        info.size = size
        info.mode = 0o644
        # GNU format stores sizes past ustar's 8 GiB in base 256.
        self.header = info.tobuf(tarfile.GNU_FORMAT)
        self.trailer = bytes(-size % tarfile.BLOCKSIZE + 2 * tarfile.BLOCKSIZE)
        self.size = len(self.header) + size + len(self.trailer)
        digest = hashlib.sha256()
        for chunk in self.chunks():
            digest.update(chunk)
        self.digest = "sha256:" + digest.hexdigest()

    def chunks(self):
        yield self.header
        with open(self.archive, "rb") as f:
            while chunk := f.read(CHUNK):
                yield chunk
        yield self.trailer


class Registry:
    def __init__(self, host, name, user, password, scheme="https"):
        self.host = host
        self.scheme = scheme
        self.name = name
        self.basic = base64.b64encode(f"{user}:{password}".encode()).decode()
        self.token = None

    def request(self, method, url, body=None, headers=None, ok=(200,)):
        """One request to the registry, returning (response, body).

        URL is a path, or an absolute URL the registry returned (an upload's
        Location). Gets a bearer token at the first 401, as Docker does."""
        for attempt in range(2):
            parsed = urllib.parse.urlsplit(url)
            path = urllib.parse.urlunsplit(("", "", parsed.path, parsed.query, ""))
            conn = connection(parsed.netloc or self.host, parsed.scheme or self.scheme)
            sent = dict(headers or {})
            if self.token:
                sent["Authorization"] = f"Bearer {self.token}"
            conn.request(method, path, body=body() if callable(body) else body,
                         headers=sent)
            response = conn.getresponse()
            data = response.read()
            conn.close()
            if response.status == 401 and attempt == 0 and not self.token:
                self.token = self.authenticate(response.getheader("WWW-Authenticate"))
                continue
            if response.status not in ok:
                raise SystemExit(f"{method} {path}: {response.status} {response.reason}\n"
                                 + data.decode(errors="replace"))
            return response, data
        raise SystemExit(f"{method} {url}: the registry refused the token")

    def authenticate(self, challenge):
        """The bearer token for the challenge's realm, service and scope."""
        scheme, _, params = (challenge or "").partition(" ")
        if scheme.lower() != "bearer":
            raise SystemExit(f"unsupported authentication challenge: {challenge!r}")
        fields = dict(
            (k.strip(), v.strip().strip('"'))
            for k, _, v in (p.partition("=") for p in split_params(params))
        )
        realm = urllib.parse.urlsplit(fields.pop("realm"))
        fields["scope"] = f"repository:{self.name}:pull,push"
        query = urllib.parse.urlencode(fields)
        conn = connection(realm.netloc, realm.scheme)
        conn.request("GET", f"{realm.path}?{query}",
                     headers={"Authorization": f"Basic {self.basic}"})
        response = conn.getresponse()
        data = response.read()
        conn.close()
        if response.status != 200:
            raise SystemExit(f"token: {response.status} {response.reason}")
        reply = json.loads(data)
        return reply.get("token") or reply["access_token"]

    def push_blob(self, digest, size, body, content_type="application/octet-stream"):
        response, _ = self.request("HEAD", f"/v2/{self.name}/blobs/{digest}", ok=(200, 404))
        if response.status == 200:
            return
        response, _ = self.request("POST", f"/v2/{self.name}/blobs/uploads/",
                                   headers={"Content-Length": "0"}, ok=(202,))
        location = response.getheader("Location")
        sep = "&" if "?" in location else "?"
        self.request("PUT", f"{location}{sep}digest={urllib.parse.quote(digest)}",
                     body=body, ok=(201,),
                     headers={"Content-Type": content_type, "Content-Length": str(size)})


def split_params(params):
    """The comma-separated fields of a challenge, which quote commas in scopes."""
    field, quoted = "", False
    for c in params:
        if c == '"':
            quoted = not quoted
        if c == "," and not quoted:
            yield field
            field = ""
        else:
            field += c
    if field:
        yield field


def connection(host, scheme):
    if scheme == "http":
        return http.client.HTTPConnection(host)
    return http.client.HTTPSConnection(host)


def push(archive, image, labels, user, password, scheme="https"):
    host, _, rest = image.partition("/")
    name, _, tag = rest.rpartition(":")
    registry = Registry(host, name, user, password, scheme)

    layer = Layer(archive)
    registry.push_blob(layer.digest, layer.size, layer.chunks)

    config = json.dumps({
        "architecture": "amd64",
        "os": "linux",
        "config": {"Labels": labels},
        "rootfs": {"type": "layers", "diff_ids": [layer.digest]},
    }, sort_keys=True).encode()
    config_digest = "sha256:" + hashlib.sha256(config).hexdigest()
    registry.push_blob(config_digest, len(config), config)

    manifest = json.dumps({
        "schemaVersion": 2,
        "mediaType": OCI_MANIFEST,
        "config": {"mediaType": OCI_CONFIG, "digest": config_digest, "size": len(config)},
        "layers": [{"mediaType": OCI_LAYER, "digest": layer.digest, "size": layer.size}],
    }, sort_keys=True).encode()
    registry.request("PUT", f"/v2/{name}/manifests/{tag}", body=manifest, ok=(201,),
                     headers={"Content-Type": OCI_MANIFEST,
                              "Content-Length": str(len(manifest))})
    print(f"Pushed {image}: layer {layer.digest} ({layer.size} bytes)")


def main(argv):
    if len(argv) < 2:
        raise SystemExit(__doc__)
    archive, image, *pairs = argv
    labels = dict(pair.split("=", 1) for pair in pairs)
    push(archive, image, labels, os.environ["GITHUB_ACTOR"], os.environ["GH_TOKEN"])


if __name__ == "__main__":
    main(sys.argv[1:])
