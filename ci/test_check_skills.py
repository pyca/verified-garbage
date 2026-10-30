import unittest

from check_skills import check_skill, frontmatter, listed

GOOD = '---\nname: foo\ndescription: "Use when: doing foo."\n---\n\n# Foo\n\nSee [x](../../../x.md#a).\n'


class Frontmatter(unittest.TestCase):
    def test_quoted(self):
        self.assertEqual(frontmatter(GOOD), ({"name": "foo", "description": "Use when: doing foo."}, []))

    def test_plain_with_colon(self):
        _, errors = frontmatter("---\nname: foo\ndescription: Use when: doing foo.\n---\n")
        self.assertEqual(len(errors), 1)

    def test_none(self):
        self.assertEqual(frontmatter("# Foo\n")[1], ["no frontmatter between `---` lines"])


class CheckSkill(unittest.TestCase):
    def test_good(self):
        self.assertEqual(check_skill("foo", GOOD, lambda p: p == "../../../x.md"), [])

    def test_broken_link(self):
        self.assertEqual(len(check_skill("foo", GOOD, lambda p: False)), 1)

    def test_name_and_fields(self):
        text = GOOD.replace("name: foo", "name: bar\nallowed-tools: Bash")
        self.assertEqual(len(check_skill("foo", text, lambda p: True)), 2)

    def test_long_description(self):
        text = GOOD.replace("Use when: doing foo.", "x" * 1025)
        self.assertEqual(len(check_skill("foo", text, lambda p: True)), 1)


class Listed(unittest.TestCase):
    def test_section_only(self):
        md = "## Skills\n\n* `a`: when a.\n* `b`: when b.\n\n## Next\n\n* `c`: not a skill.\n"
        self.assertEqual(listed(md), ["a", "b"])
        self.assertEqual(listed("# Title\n\n" + md), ["a", "b"])

    def test_no_section(self):
        self.assertIsNone(listed("## Other\n\n* `a`: when a.\n"))


if __name__ == "__main__":
    unittest.main()
