import io
import unittest

import conflict_comments
from conflict_comments import MARKER, needs_comment, run


def pr(number, mergeable, head="a" * 40, comments=(), base="main"):
    return {
        "number": number,
        "mergeable": mergeable,
        "headRefOid": head,
        "baseRefName": base,
        "comments": {"nodes": [{"viewerDidAuthor": mine, "body": text} for mine, text in comments]},
    }


class FakeApi:
    """Answers each listing of the open pull requests with the next of
    `listings`, a list of pages each; records the comments posted."""

    def __init__(self, *listings):
        self.listings = list(listings)
        self.pages = []
        self.comments = []

    def graphql(self, query, variables):
        if variables["after"] is None:
            self.pages = list(self.listings.pop(0))
        nodes = self.pages.pop(0)
        return {"repository": {"pullRequests": {
            "nodes": nodes,
            "pageInfo": {"hasNextPage": bool(self.pages), "endCursor": f"c{len(self.pages)}"},
        }}}

    def comment(self, repo, number, body):
        self.comments.append((repo, number, body))


def go(api, attempts=3, dry_run=False):
    sleeps, out = [], io.StringIO()
    run(api, "o/r", "f" * 40, attempts, 7, dry_run, sleep=sleeps.append, out=out)
    return sleeps, out.getvalue()


class NeedsComment(unittest.TestCase):
    def test_mergeable(self):
        self.assertFalse(needs_comment(pr(1, "MERGEABLE")))

    def test_conflicting(self):
        self.assertTrue(needs_comment(pr(1, "CONFLICTING")))

    def test_told_about_this_head(self):
        told = (True, MARKER.format(head="a" * 40) + "\nconflicts")
        self.assertFalse(needs_comment(pr(1, "CONFLICTING", comments=[told])))

    def test_told_about_an_older_head(self):
        told = (True, MARKER.format(head="b" * 40))
        self.assertTrue(needs_comment(pr(1, "CONFLICTING", comments=[told])))

    def test_marker_from_someone_else(self):
        quoted = (False, MARKER.format(head="a" * 40))
        self.assertTrue(needs_comment(pr(1, "CONFLICTING", comments=[quoted])))


class Run(unittest.TestCase):
    def test_comments_on_new_conflicts_only(self):
        told = (True, MARKER.format(head="c" * 40))
        api = FakeApi([[pr(1, "MERGEABLE"), pr(2, "CONFLICTING", base="stack")],
                       [pr(3, "CONFLICTING", head="c" * 40, comments=[told])]])
        sleeps, out = go(api)
        self.assertEqual(sleeps, [])
        self.assertEqual([(r, n) for r, n, _ in api.comments], [("o/r", 2)])
        body = api.comments[0][2]
        self.assertTrue(body.startswith(MARKER.format(head="a" * 40) + "\n"))
        self.assertIn("conflicts with `stack`", body)
        self.assertIn("f" * 40, body)
        self.assertIn("https://github.com/o/r/blob/main/CLAUDE.md", body)
        self.assertIn("#3: conflicts at " + "c" * 40 + ": already told", out)

    def test_asks_again_for_unknown(self):
        api = FakeApi([[pr(1, "UNKNOWN"), pr(2, "CONFLICTING")]],
                      [[pr(1, "UNKNOWN"), pr(2, "UNKNOWN")]],
                      [[pr(1, "CONFLICTING"), pr(2, "UNKNOWN")]])
        sleeps, out = go(api)
        self.assertEqual(sleeps, [7, 7])
        self.assertEqual([n for _, n, _ in api.comments], [1, 2])
        self.assertNotIn("unknown", out)

    def test_gives_up_on_unknown(self):
        api = FakeApi([[pr(1, "UNKNOWN")]], [[pr(1, "UNKNOWN"), pr(2, "MERGEABLE")]])
        sleeps, out = go(api, attempts=2)
        self.assertEqual(sleeps, [7])
        self.assertEqual(api.comments, [])
        self.assertIn("#1: mergeability still unknown: skipped", out)

    def test_dry_run(self):
        api = FakeApi([[pr(1, "CONFLICTING")]])
        _, out = go(api, dry_run=True)
        self.assertEqual(api.comments, [])
        self.assertIn("#1: conflicts at " + "a" * 40 + ": commenting", out)


class Graphql(unittest.TestCase):
    def test_errors_raise(self):
        api = conflict_comments.Api("t")
        api.request = lambda *a: {"errors": [{"message": "no"}]}
        with self.assertRaises(RuntimeError):
            api.graphql("q", {})


if __name__ == "__main__":
    unittest.main()
