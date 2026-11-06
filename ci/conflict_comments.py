#!/usr/bin/env python3
"""Comments on every open pull request that conflicts with its base branch,
once per push to it: what `.github/workflows/conflicts.yml` runs after each
merge to main.

    GITHUB_TOKEN=… python3 ci/conflict_comments.py OWNER/REPO MAIN_SHA [--dry-run]

GitHub works out whether a pull request can merge in the background, after
its base moves, and reports `UNKNOWN` until it has: the script asks again
(`--attempts` times, `--delay` seconds apart) for those it has not, and skips
any still unknown at the end (the next merge checks them again).

Each comment carries a hidden marker naming the pull request's head commit.
A pull request that already has this token's comment for its current head is
skipped, so a pull request is told once that it conflicts, and again only
after a new push that still conflicts.
"""

import argparse
import json
import os
import sys
import time
import urllib.request

API = "https://api.github.com"
MARKER = "<!-- conflict-check: {head} -->"

# `comments(last: 100)`: a marker older than a pull request's last 100
# comments is missed, and the comment posted again.
QUERY = """
query($owner: String!, $name: String!, $after: String) {
  repository(owner: $owner, name: $name) {
    pullRequests(states: OPEN, first: 50, after: $after) {
      pageInfo { hasNextPage endCursor }
      nodes {
        number
        mergeable
        headRefOid
        baseRefName
        comments(last: 100) { nodes { viewerDidAuthor body } }
      }
    }
  }
}
"""

BODY = """{marker}
This pull request has conflicts with `{base}`, found after {sha} landed on \
`main`: rebase it to resolve them. Before rebasing, see [CLAUDE.md]({claude}) \
on checking how much Lean `main` changed, and on restacking a stacked pull \
request.

<sub>Posted by `.github/workflows/conflicts.yml`, once per push to a \
conflicting pull request.</sub>
"""


class Api:
    def __init__(self, token):
        self.token = token

    def request(self, method, path, payload):
        req = urllib.request.Request(
            API + path,
            data=json.dumps(payload).encode(),
            method=method,
            headers={
                "Authorization": f"Bearer {self.token}",
                "Accept": "application/vnd.github+json",
                "Content-Type": "application/json",
            },
        )
        with urllib.request.urlopen(req, timeout=60) as resp:
            return json.load(resp)

    def graphql(self, query, variables):
        out = self.request("POST", "/graphql", {"query": query, "variables": variables})
        if out.get("errors"):
            raise RuntimeError(f"GraphQL errors: {out['errors']}")
        return out["data"]

    def comment(self, repo, number, body):
        self.request("POST", f"/repos/{repo}/issues/{number}/comments", {"body": body})


def open_pulls(api, repo):
    """Every open pull request, as the GraphQL query's nodes."""
    owner, name = repo.split("/")
    pulls, after = [], None
    while True:
        page = api.graphql(QUERY, {"owner": owner, "name": name, "after": after})
        prs = page["repository"]["pullRequests"]
        pulls += prs["nodes"]
        if not prs["pageInfo"]["hasNextPage"]:
            return pulls
        after = prs["pageInfo"]["endCursor"]


def resolve(api, repo, attempts, delay, sleep=time.sleep):
    """The open pull requests whose mergeability GitHub knows, by number,
    asking again for those it does not yet; and the numbers still unknown."""
    known, unknown = {}, set()
    for attempt in range(attempts):
        if attempt:
            sleep(delay)
        unknown = set()
        for pr in open_pulls(api, repo):
            if pr["mergeable"] == "UNKNOWN":
                if pr["number"] not in known:
                    unknown.add(pr["number"])
            else:
                known[pr["number"]] = pr
        if not unknown:
            break
    return known, sorted(unknown)


def needs_comment(pr):
    """Whether `pr` conflicts and has no comment of ours for its head."""
    if pr["mergeable"] != "CONFLICTING":
        return False
    marker = MARKER.format(head=pr["headRefOid"])
    return not any(c["viewerDidAuthor"] and marker in c["body"] for c in pr["comments"]["nodes"])


def body(pr, repo, sha):
    return BODY.format(
        marker=MARKER.format(head=pr["headRefOid"]),
        base=pr["baseRefName"],
        sha=sha,
        claude=f"https://github.com/{repo}/blob/main/CLAUDE.md",
    )


def run(api, repo, sha, attempts, delay, dry_run, sleep=time.sleep, out=sys.stdout):
    known, unknown = resolve(api, repo, attempts, delay, sleep)
    for number, pr in sorted(known.items()):
        if needs_comment(pr):
            print(f"#{number}: conflicts at {pr['headRefOid']}: commenting", file=out)
            if not dry_run:
                api.comment(repo, number, body(pr, repo, sha))
        elif pr["mergeable"] == "CONFLICTING":
            print(f"#{number}: conflicts at {pr['headRefOid']}: already told", file=out)
    for number in unknown:
        print(f"#{number}: mergeability still unknown: skipped", file=out)


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("repo", help="OWNER/REPO")
    parser.add_argument("sha", help="the commit of main that was just pushed")
    parser.add_argument("--attempts", type=int, default=20)
    parser.add_argument("--delay", type=float, default=15)
    parser.add_argument("--dry-run", action="store_true", help="print what it would comment on")
    args = parser.parse_args()
    api = Api(os.environ["GITHUB_TOKEN"])
    run(api, args.repo, args.sha, args.attempts, args.delay, args.dry_run)


if __name__ == "__main__":
    main()
