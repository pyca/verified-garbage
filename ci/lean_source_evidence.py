"""Resolved elaboration references from Lean's versioned .ilean index.

These supplement declaration terms: a tactic argument or #guard can name a
constant that leaves no reference in the resulting .olean. They do not prove
that syntax extensions, attributes or evaluation effects are unnecessary.
"""

import json
import pathlib
import re


class StaleIndex(ValueError):
    pass


def read(lean: pathlib.Path, mod: str, imports: list[tuple[str, bool, bool, bool]],
         build: pathlib.Path | None = None) -> dict:
    path = (build or lean / ".lake/build/lib/lean") / pathlib.Path(*mod.split(".")).with_suffix(".ilean")
    try:
        data = json.loads(path.read_text())
    except (OSError, ValueError) as error:
        raise StaleIndex(f"{mod}: cannot read elaboration index; build the module first: {error}") from error
    if data.get("version") != 5 or data.get("module") != mod:
        raise StaleIndex(f"{mod}: unsupported elaboration index version/module")
    expected = sorted((m, not public, all_, meta) for m, public, meta, all_ in imports)
    actual = sorted(tuple(row) for row in data.get("directImports", []))
    if expected != actual:
        raise StaleIndex(f"{mod}: index import header differs from source; build the module first")
    if not isinstance(data.get("references"), dict) or not isinstance(data.get("decls"), dict):
        raise StaleIndex(f"{mod}: incomplete elaboration index")
    return data


def references(data: dict) -> set[str]:
    modules = set()
    for key, info in data["references"].items():
        if not info.get("usages"):
            continue
        try:
            constant = json.loads(key).get("c")
        except (ValueError, AttributeError) as error:
            raise StaleIndex("unrecognized identifier reference in elaboration index") from error
        if constant and constant.get("m") != data["module"]:
            modules.add(constant["m"])
    return modules


def namespaces(data: dict) -> set[str]:
    result = set()
    for name in data["decls"]:
        if name.startswith("_private."):
            continue
        parts, current, quoted = [], "", False
        for char in name:
            if char == "." and not quoted:
                parts.append(current)
                current = ""
            else:
                current += char
                if char == "«":
                    quoted = True
                elif char == "»":
                    quoted = False
        parts.append(current)
        result.update(".".join(parts[:i]) for i in range(1, len(parts)))
    return result


SPECIAL = re.compile(r'''/-|--|'(?:\\(?:u\{[^}\n]*\}|[^\n])|[^'\\\n])'|r#*"|"''')
COMMENT = re.compile(r"/-|-/")
STRING = re.compile(r'\\.|"', re.S)


def code_only(text: str) -> str:
    """Mask nested comments and strings, preserving source line positions.

    This lexical guard is not a Lean parser. Backtick-quoted names remain
    identifiers. Ordinary code is copied in spans rather than character by
    character, so scanning large proof files stays cheap.
    """
    out, i, depth = [], 0, 0

    def mask(part):
        return re.sub(r"[^\n]", " ", part)

    while i < len(text):
        if depth:
            token = COMMENT.search(text, i)
            if token is None:
                out.append(mask(text[i:]))
                break
            out.append(mask(text[i:token.end()]))
            depth += 1 if token.group() == "/-" else -1
            i = token.end()
            continue
        token = SPECIAL.search(text, i)
        if token is None:
            out.append(text[i:])
            break
        out.append(text[i:token.start()])
        i = token.start()
        if token.group() == "/-":
            depth = 1
            out.append("  ")
            i += 2
        elif token.group() == "--":
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.append(" " * (end - i))
            i = end
        elif token.group().startswith("'"):
            if i and (text[i - 1].isalnum() or text[i - 1] in "_'"):
                out.append("'")
                i += 1
            else:
                out.append(mask(token.group()))
                i = token.end()
        else:
            start = i
            raw = token.group().startswith("r")
            if raw and i and (text[i - 1].isalnum() or text[i - 1] == "_"):
                out.append("r")
                i += 1
                continue
            i = token.end()
            if raw:
                delimiter = '"' + token.group()[1:-1]
                end = text.find(delimiter, i)
                i = len(text) if end < 0 else end + len(delimiter)
            else:
                while ending := STRING.search(text, i):
                    i = ending.end()
                    if ending.group() == '"':
                        break
                else:
                    i = len(text)
            out.append(mask(text[start:i]))
    return "".join(out)
