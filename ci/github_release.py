#!/usr/bin/env python3
"""Downloads a file attached to a GitHub release.

  python3 ci/github_release.py OWNER/REPO TAG NAME OUT   # TAG may be `latest`

With a token in `GH_TOKEN` (CI passes the job's own, which reads public
repositories), the download goes through the REST API, authenticated: GitHub
now and then degrades only unauthenticated traffic (its status page on
2026-11-08: "Increase in timeouts for some unauthenticated users"), which
failed CI's downloads of elan and leantar. The token is sent only to
api.github.com: the asset's bytes come from the host the API redirects to,
which a header added with `add_unredirected_header` does not reach. Without a
token, the download goes to the release's public URL.

Either way, a request that fails with a 5xx, a 429 or a dropped connection
is tried again, after 2, 4, 8 and 16 seconds.
"""

import argparse
import http.client
import json
import os
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

API = "https://api.github.com"
# Seconds to wait before each retry of a request that failed transiently.
BACKOFF = (2, 4, 8, 16)
# Seconds a connection may stay silent before an attempt is given up.
TIMEOUT = 30


def urlopen(req):
    return urllib.request.urlopen(req, timeout=TIMEOUT)


def transient(e):
    """Whether a request that failed with `e` may succeed if tried again."""
    if isinstance(e, urllib.error.HTTPError):
        return e.code == 429 or e.code >= 500
    return isinstance(e, (urllib.error.URLError, http.client.HTTPException, OSError))


def read(req, opener=urlopen, sleep=time.sleep):
    """The body of `req`, retrying a transient failure after each `BACKOFF`."""
    for delay in (*BACKOFF, None):
        try:
            with opener(req) as r:
                return r.read()
        except Exception as e:
            if delay is None or not transient(e):
                raise
            print(f"{req.full_url}: {e}; retrying in {delay} s", file=sys.stderr)
            sleep(delay)


def api_request(url, token, accept):
    """A request to the REST API, whose token is not sent on a redirect."""
    if not url.startswith(API + "/"):
        raise SystemExit(f"{url}: not a URL of {API}")
    req = urllib.request.Request(url, headers={"Accept": accept, "X-GitHub-Api-Version": "2022-11-28"})
    req.add_unredirected_header("Authorization", f"Bearer {token}")
    return req


def download(repo, tag, name, token=None, opener=urlopen, sleep=time.sleep):
    """The bytes of the file `name` of `repo`'s release `tag` (or `latest`)."""
    if not token:
        where = "latest/download" if tag == "latest" else f"download/{urllib.parse.quote(tag, safe='')}"
        url = f"https://github.com/{repo}/releases/{where}/{name}"
        print(f"Downloading {url}", file=sys.stderr)
        return read(urllib.request.Request(url), opener, sleep)
    which = "latest" if tag == "latest" else f"tags/{urllib.parse.quote(tag, safe='')}"
    release = json.loads(read(api_request(f"{API}/repos/{repo}/releases/{which}", token,
                                          "application/vnd.github+json"), opener, sleep))
    assets = [a for a in release["assets"] if a["name"] == name]
    if not assets:
        raise SystemExit(f"{repo} {release['tag_name']}: no file {name}")
    print(f"Downloading {name} of {repo} {release['tag_name']} (authenticated)", file=sys.stderr)
    return read(api_request(assets[0]["url"], token, "application/octet-stream"), opener, sleep)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("repo", help="OWNER/REPO")
    parser.add_argument("tag", help="the release's tag, or `latest`")
    parser.add_argument("name", help="the file's name")
    parser.add_argument("out", type=Path, help="where to write it")
    args = parser.parse_args(argv)
    data = download(args.repo, args.tag, args.name, os.environ.get("GH_TOKEN"), urlopen)
    # Written beside it and renamed, so that a file there is always whole.
    with tempfile.NamedTemporaryFile(dir=args.out.parent, delete=False) as f:
        f.write(data)
    os.replace(f.name, args.out)


if __name__ == "__main__":
    main()
