#!/usr/bin/env python3
"""Checks the agents' skills, `.agents/skills/<name>/SKILL.md` (CLAUDE.md,
"Skills"): that each has frontmatter that every tool reads (`name`, its
directory's name, and a `description`, nothing else), that every relative
link in it leads to a file, that CLAUDE.md's list of skills names exactly
these, and that `.claude/skills` links to `.agents/skills`, where Claude
Code finds them. Exits non-zero naming each problem.
"""

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SKILLS = pathlib.PurePosixPath(".agents/skills")
NAME = re.compile(r"[a-z0-9]+(-[a-z0-9]+)*")
# The limits of the Agent Skills standard, which Codex and Claude Code read.
MAX_NAME = 64
MAX_DESCRIPTION = 1024
LINK = re.compile(r"\]\(([^)\s]+)\)")
# CLAUDE.md's "Skills" section, up to the next section, and an item of its
# list: "* `<name>`: …".
SECTION = re.compile(r"^## Skills\n(.*?)(?=^## |\Z)", re.M | re.S)
LISTED = re.compile(r"^\* `([^`]+)`:", re.M)


def frontmatter(text: str) -> tuple[dict[str, str], list[str]]:
    """The fields of a skill's frontmatter, and what is wrong with it. A value
    is plain or a JSON string: a plain value may not contain `: `, which
    YAML would read as a mapping."""
    lines = text.split("\n")
    if lines[0] != "---" or "---" not in lines[1:]:
        return {}, ["no frontmatter between `---` lines"]
    fields, errors = {}, []
    for line in lines[1:lines.index("---", 1)]:
        key, sep, value = line.partition(": ")
        if not sep:
            errors.append(f"not a `key: value` line: {line!r}")
            continue
        if value.startswith('"'):
            try:
                value = json.loads(value)
            except json.JSONDecodeError:
                errors.append(f"{key}: not a valid double-quoted string")
                continue
        elif ": " in value or value[:1] in "'[{&*!|>%@`":
            errors.append(f"{key}: quote the value (\"…\"): YAML misreads it plain")
            continue
        fields[key] = value
    return fields, errors


def check_skill(name: str, text: str, exists) -> list[str]:
    """What is wrong with the skill `name` whose SKILL.md is `text`; `exists`
    tells whether a path relative to the skill's directory is a file."""
    fields, errors = frontmatter(text)
    if set(fields) - {"name", "description"}:
        errors.append("fields other than `name` and `description`: "
                      + ", ".join(sorted(set(fields) - {"name", "description"})))
    if fields.get("name") != name:
        errors.append(f"`name` is {fields.get('name')!r}, not its directory's name {name!r}")
    if not NAME.fullmatch(name) or len(name) > MAX_NAME:
        errors.append(f"the name {name!r} is not lowercase words joined by `-`, "
                      f"of at most {MAX_NAME} characters")
    description = fields.get("description", "")
    if not description:
        errors.append("no `description`")
    elif len(description) > MAX_DESCRIPTION:
        errors.append(f"`description` is longer than {MAX_DESCRIPTION} characters")
    for target in LINK.findall(text):
        path = target.split("#", 1)[0]
        if path and "://" not in path and not exists(path):
            errors.append(f"the link {target!r} leads to no file from the skill's directory")
    return errors


def listed(claude_md: str) -> list[str] | None:
    """The skills that CLAUDE.md's "Skills" section lists, or None without
    the section."""
    m = SECTION.search(claude_md)
    return LISTED.findall(m.group(1)) if m else None


def main() -> int:
    errors = []
    skills = sorted(p.parent.name for p in (ROOT / SKILLS).glob("*/SKILL.md"))
    for name in skills:
        d = ROOT / SKILLS / name
        for e in check_skill(name, (d / "SKILL.md").read_text(),
                             lambda path: (d / path).resolve().is_file()):
            errors.append(f"{SKILLS / name / 'SKILL.md'}: {e}")
    names = listed((ROOT / "CLAUDE.md").read_text())
    if names is None:
        errors.append("CLAUDE.md has no \"Skills\" section listing the skills")
        names = skills
    for name in sorted(set(names) - set(skills)):
        errors.append(f"CLAUDE.md lists the skill {name!r}, which {SKILLS} does not have")
    for name in sorted(set(skills) - set(names)):
        errors.append(f"CLAUDE.md's \"Skills\" does not list the skill {name!r}")
    link = ROOT / ".claude" / "skills"
    if not link.is_symlink() or link.readlink() != pathlib.Path("../.agents/skills"):
        errors.append(".claude/skills is not a symbolic link to ../.agents/skills")
    for e in errors:
        print(e, file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
