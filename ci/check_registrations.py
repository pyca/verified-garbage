#!/usr/bin/env python3
"""Checks that the files reviewed by hand only bind (step 4 of
.agents/skills/adding-a-primitive/SKILL.md). Exits non-zero on violations,
naming each.

Registration files (`Artifacts/`) under lean/VerifiedGarbage/ state what an
implementation chooses and bind proofs made under `Proof/`:

  * no theorems or lemmas;
  * no tactic proofs (`by …`) but the defaults of `Registration`
    (`by sp_safe`, `by of_sig`), each the whole of its tactic block (not
    `by sp_safe <;> decide`), which a builder of artifacts may also give
    its own arguments: a side condition a registration would decide is an
    `autoParam` of the lemma that needs it, or the algorithm's proofs state
    the instance as a theorem;
  * a module docstring of one line, its title (`/-! # SHA-256 on x86-64 -/`),
    if any: prose on the implementation restates what the code states, and
    goes stale;
  * no `consts :=`: the tables of constants the code reads are an
    implementation detail its proof's contract names, which `Registration`'s
    default (`consts_of`) finds there, so that adding or changing a table
    touches no file reviewed by hand;
  * no `stack :=`: the stack the code's calls and frames use is one too,
    which `Registration`'s default (`stack_of`) finds in that contract, so
    that code that uses more or less stack touches no file reviewed by hand.

A 64-bit RISC-V registration file (`Artifacts/*/RISCV64.lean`), whose
target's framework states its cleanup only as a theorem about named code,
binds that code and that theorem and nothing else: each
`.artifact RISCV64.target` is given a record, `{ … }`, whose `code :=` is a
definition of `Impl/` (`Impl.…`, applied to what it takes) and whose
`verified :=` is `.scrubbed` of a theorem of `Proof/` (`.scrubbed Proof.…`),
with no other fields than the choices `RISCV_FIELDS` names; and the file has
no tactic block at all, no anonymous constructor (`⟨…⟩`), no `.unscrubbed`
and nothing of `RISCV64.Scrub`, the framework's namespace.
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"

DIRS = ["Artifacts"]

# The tactics a registration may run: `Registration`'s defaults.
DEFAULTS = {"sp_safe", "of_sig"}

THEOREM = re.compile(r"(?<![\w.'])(theorem|lemma)\s")
BY = re.compile(r"(?<![\w.'])by(?![\w'])\s*([\w.']*)")
CONSTS = re.compile(r"(?<![\w.'])consts\s*:=")
STACK = re.compile(r"(?<![\w.'])stack\s*:=")
MODULE_DOC = re.compile(r"/-!.*?-/", re.S)
TITLE = re.compile(r"/-! # [^\n]+ -/")
OPEN, CLOSE = "([{⟨", ")]}⟩"

# A 64-bit RISC-V registration file, and the fields its records may give
# but `code` and `verified`: what the implementation chooses, no proof.
RISCV = re.compile(r"Artifacts/[^/]+/RISCV64\.lean")
RISCV_FIELDS = {"suffix", "tables", "extra", "vendor", "notWith"}
ARTIFACT = re.compile(r"(?<![\w'])artifact(?![\w'])")
ARTIFACT_RECORD = re.compile(r"\s+RISCV64\.target\s*\{")
FIELD = re.compile(r"(?<![\w.'])([\w']+)\s*:=")
ANON = re.compile(r"⟨")
UNSCRUBBED = re.compile(r"(?<![\w'])unscrubbed(?![\w'])")
FRAMEWORK = re.compile(r"(?<![\w.'])(?:VG\.)?RISCV64\.Scrub(?![\w'])")
CODE_OK = re.compile(r"\(?\s*Impl\.")
VERIFIED_OK = re.compile(r"\.scrubbed\s+\(?\s*Proof\.")


def code_only(text: str) -> str:
    """`text` with its comments and string literals blanked (newlines kept,
    so offsets keep their lines)."""
    out = []
    i, n = 0, len(text)
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text.startswith("/-", i):
            depth, j = 0, i
            while j < n:
                if text.startswith("/-", j):
                    depth += 1
                    j += 2
                elif text.startswith("-/", j):
                    depth -= 1
                    j += 2
                    if depth == 0:
                        break
                else:
                    j += 1
            out.append(re.sub(r"[^\n]", " ", text[i:j]))
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j += 1
            out.append(re.sub(r"[^\n]", " ", text[i:j]))
            i = j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def rest_of_block(code: str, by: int, start: int) -> str:
    """What the tactic block of the `by` at `by` holds from `start` on: up to
    the bracket that closes around it, a `,` beside it, or a line indented no
    further than the line of the `by`."""
    head = code[code.rfind("\n", 0, by) + 1:by]
    indent = len(head) - len(head.lstrip())
    depth, i, n = 0, start, len(code)
    while i < n:
        c = code[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            if depth == 0:
                break
            depth -= 1
        elif c == "," and depth == 0:
            break
        elif c == "\n" and depth == 0:
            j = i + 1
            while j < n and code[j] == "\n":
                j += 1
            end = code.find("\n", j)
            line = code[j:n if end < 0 else end]
            if not line.strip() or len(line) - len(line.lstrip()) <= indent:
                break
        i += 1
    return code[start:i].strip()


def record_fields(code: str, start: int) -> tuple[list[tuple[int, str, str]], int]:
    """The fields of the record whose `{` is at `start`, as (offset, name,
    value), and the offset of its `}`."""
    fields, marks, depth, i, n = [], [], 0, start + 1, len(code)
    while i < n:
        c = code[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            if depth == 0:
                break
            depth -= 1
        elif depth == 0:
            m = FIELD.match(code, i)
            if m:
                marks.append((i, m.group(1), m.end()))
                i = m.end()
                continue
        i += 1
    for k, (at, name, vstart) in enumerate(marks):
        vend = marks[k + 1][0] if k + 1 < len(marks) else i
        fields.append((at, name, code[vstart:vend].strip().rstrip(",").strip()))
    return fields, i


def riscv_problems(rel: str, code: str, line) -> list[str]:
    """What is wrong in the 64-bit RISC-V registration file `rel`, whose
    text without comments is `code`: anything but binding named code and a
    theorem about it."""
    out = []
    skill = "(.agents/skills/adding-a-primitive/SKILL.md)"
    for m in BY.finditer(code):
        if m.group(1) in DEFAULTS and not rest_of_block(code, m.start(), m.end()):
            out.append(f"lean/{rel}:{line(m.start())}: a tactic proof in a RISC-V registration "
                       f"file; it binds only `code := Impl.…` and `verified := .scrubbed Proof.…` "
                       f"{skill}")
    for pat, what in [(ANON, "an anonymous constructor (`⟨…⟩`)"),
                      (UNSCRUBBED, "`.unscrubbed`"),
                      (FRAMEWORK, "the scrub framework (`RISCV64.Scrub`)")]:
        for m in pat.finditer(code):
            out.append(f"lean/{rel}:{line(m.start())}: {what} in a RISC-V registration file; "
                       f"it binds only `code := Impl.…` and `verified := .scrubbed Proof.…`, "
                       f"whose proof is made under `Proof/` {skill}")
    for m in ARTIFACT.finditer(code):
        r = ARTIFACT_RECORD.match(code, m.end())
        if not r:
            out.append(f"lean/{rel}:{line(m.start())}: a RISC-V registration not given as a record; "
                       f"write `.artifact RISCV64.target {{ code := Impl.… "
                       f"verified := .scrubbed Proof.… }}` {skill}")
            continue
        fields, end = record_fields(code, r.end() - 1)
        names = [f[1] for f in fields]
        for at, name, value in fields:
            if name == "code":
                if not CODE_OK.match(value):
                    out.append(f"lean/{rel}:{line(at)}: a RISC-V registration's `code` that is not "
                               f"a definition of `Impl/`; bind `code := Impl.…` {skill}")
            elif name == "verified":
                if not VERIFIED_OK.match(value):
                    out.append(f"lean/{rel}:{line(at)}: a RISC-V registration's `verified` that is "
                               f"not a theorem of `Proof/`; bind `verified := .scrubbed Proof.…` "
                               f"{skill}")
            elif name not in RISCV_FIELDS:
                out.append(f"lean/{rel}:{line(at)}: `{name}` in a RISC-V registration; it binds "
                           f"only `code`, `verified` and what the implementation chooses "
                           f"({', '.join(sorted(RISCV_FIELDS))}) {skill}")
        for name in ("code", "verified"):
            if names.count(name) != 1:
                out.append(f"lean/{rel}:{line(m.start())}: a RISC-V registration without exactly "
                           f"one `{name} :=` {skill}")
    return out


def problems(lean: pathlib.Path) -> list[str]:
    """What is wrong under `lean` (the directory with `VerifiedGarbage/`), one
    line each."""
    out = []
    for d in DIRS:
        for f in sorted((lean / "VerifiedGarbage" / d).rglob("*.lean")):
            rel = f.relative_to(lean).as_posix()
            text = f.read_text()
            code = code_only(text)
            line = lambda i: code.count("\n", 0, i) + 1
            for m in MODULE_DOC.finditer(text):
                if not TITLE.fullmatch(m.group(0)):
                    out.append(f"lean/{rel}:{line(m.start())}: a module docstring of more than its "
                               "title in a file reviewed by hand; keep only the title, "
                               "`/-! # … -/` (.agents/skills/adding-a-primitive/SKILL.md)")
            for m in THEOREM.finditer(code):
                out.append(f"lean/{rel}:{line(m.start())}: a {m.group(1)} in a file reviewed by hand; "
                           "prove it under `Proof/` (.agents/skills/adding-a-primitive/SKILL.md)")
            for m in CONSTS.finditer(code):
                out.append(f"lean/{rel}:{line(m.start())}: `consts` in a file reviewed by hand; "
                           "the default (`consts_of`) finds the tables in the contract `verified` "
                           "proves: state them there, in `Abi.withConsts` "
                           "(.agents/skills/adding-a-primitive/SKILL.md)")
            for m in STACK.finditer(code):
                out.append(f"lean/{rel}:{line(m.start())}: `stack` in a file reviewed by hand; "
                           "the default (`stack_of`) finds it in the contract `verified` proves "
                           "(.agents/skills/adding-a-primitive/SKILL.md)")
            for m in BY.finditer(code):
                if m.group(1) in DEFAULTS and not rest_of_block(code, m.start(), m.end()):
                    continue
                out.append(f"lean/{rel}:{line(m.start())}: a tactic proof in a file reviewed by hand; "
                           "make the side condition an `autoParam` of the lemma, or prove the "
                           "instance under `Proof/` (.agents/skills/adding-a-primitive/SKILL.md)")
            if RISCV.fullmatch(rel.removeprefix("VerifiedGarbage/")):
                out += riscv_problems(rel, code, line)
    return out


def main() -> int:
    ps = problems(LEAN)
    for p in ps:
        print(p)
    return 1 if ps else 0


if __name__ == "__main__":
    sys.exit(main())
