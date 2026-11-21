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

A registration file of a target (`Artifacts/*/<T>.lean`, for every target
`TARGETS` names: x86-64, x86, AArch64, ARMv7, RISC-V64 and PPC64LE) binds
named code and a theorem about it and nothing else (`target_problems`):

  * each `.artifact <T>.target` (or `target`, opened from `VG.<T>`) is given
    a record, `{ … }`, or a choice between implementations whose every arm
    is a record or another such choice, `(match … with | … => { … } …)` or
    `(if … then { … } else …)`, as a variant's free working space or its
    instructions decide (`Artifacts/AesGcm/X86_64.lean`);
  * a record's `code :=` is a definition of `Impl/` (`Impl.…`, applied to
    what it takes) but a cleanup form (`Impl.Scrub.…`): the function as
    emitted, cleanup included, is a definition of its own; and its
    `verified :=`, `spSafe :=` and `writtenOk :=` are theorems of `Proof/`
    (`Proof.…`, applied to what they take), named in full, not through an
    `open`;
  * it has no other fields than those and the choices `CHOICES` names, which
    state what the implementation chooses and prove nothing (`written`, the
    output regions a function writes, is proven by its `writtenOk`);
  * the file has no tactic block at all, not even a default's, no anonymous
    constructor (`⟨…⟩`), no `Artifact` built by hand (`target := …`), and
    nothing of `<T>.Scrub`, the target's cleanup framework.

Two shapes are accepted explicitly, each for the reason given:

  * x86-64's streaming functions of each hash function (`StreamFnS`), whose
    code the hash function's proofs build from the variant
    (`Proof/Pbkdf2/Md/X86_64/Hashes/`), some of it defined under `Proof/`,
    so that no one definition of `Impl/` is the function as emitted: their
    record binds exactly the cleanup form `StreamFnS.scrubbed` states, of
    the function's own fields (`STREAM_CODE`), and that theorem.
  * The emitter's self-test (`SELFTEST`), which builds its one `Artifact`
    by hand: it tests the emitter on code and a contract of its own and
    registers no implementation of an `Api`. The rules above for every
    file reviewed by hand still apply to it.
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

# The targets whose registration files bind only, and the fields their records may give
# but `code` and `verified`: what the implementation chooses, no proof.
TARGETS = ["X86_64", "X86", "AArch64", "Arm", "RISCV64", "PPC64LE"]
TARGET_FILE = re.compile(r"Artifacts/[^/]+/(" + "|".join(TARGETS) + r")\.lean")
CHOICES = {"suffix", "tables", "extra", "vendor", "notWith", "written"}
ARTIFACT = re.compile(r"(?<![\w'])artifact(?![\w'])")
FIELD = re.compile(r"(?<![\w.'])([\w']+)\s*:=")
ANON = re.compile(r"⟨")
SKILL = "(.agents/skills/adding-a-primitive/SKILL.md)"
# The fields a record binds, each to a name under the directory it names.
BOUND = {
    "code": (re.compile(r"\(?\s*Impl\."), "a definition of `Impl/` (but a cleanup form, "
             "`Impl.Scrub.…`: bind the function as emitted, `Impl.<Alg>.<Target>.Fn.…`)"),
    "verified": (re.compile(r"\(?\s*Proof\."), "a theorem of `Proof/`; bind `Proof.…`"),
    "spSafe": (re.compile(r"\(?\s*Proof\."), "a theorem of `Proof/`; bind `Proof.…`"),
    "writtenOk": (re.compile(r"\(?\s*Proof\."), "a theorem of `Proof/`; bind `Proof.…`"),
}
SCRUB_FORM = re.compile(r"\(?\s*Impl\.Scrub\.")
# x86-64's streaming functions (`StreamFnS`), whose code the hash function's
# proofs build from the variant: the cleanup form of the function's fields,
# as `StreamFnS.scrubbed` states it.
STREAM_CODE = re.compile(r"Impl\.Scrub\.X86_64\.scrubSel ([\w.']+)\.sel\.level \1\.f\.retBits "
                         r"\1\.f\.stack \1\.sel\.runs\s+\1\.f\.code")
# The emitter's self-test, which builds its one `Artifact` by hand: it tests
# the emitter on code and a contract of its own, and registers no
# implementation of an `Api`.
SELFTEST = "VerifiedGarbage/Artifacts/Selftest/"
CHOICE = re.compile(r"\(\s*(?:match|if)(?![\w'])")
ARM = re.compile(r"=>|(?<![\w'])(?:then|else)(?![\w'])")
RAW = re.compile(r"(?<![\w.'])target\s*:=")


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


def choice_records(code: str, start: int) -> list[int] | None:
    """The offsets of the `{` of the records of the choice whose `(` is at
    `start` (`(match … with | … => { … } …)` or `(if … then { … } else …)`),
    each the whole of an arm; None if it is not such a choice, or an arm is
    anything but a record or another such choice."""
    m = CHOICE.match(code, start)
    if not m:
        return None
    depth, i, n = 0, start, len(code)
    while i < n:
        if code[i] in OPEN:
            depth += 1
        elif code[i] in CLOSE:
            depth -= 1
            if depth == 0:
                break
        i += 1
    inner, base = code[start + 1:i], start + 1
    out, j = [], 0
    for a in ARM.finditer(inner):
        k = a.end()
        while k < len(inner) and inner[k].isspace():
            k += 1
        if k < len(inner) and inner[k] == "{":
            out.append(base + k)
        elif inner.startswith("(", k):
            sub = choice_records(code, base + k)
            if sub is None:
                return None
            out += sub
        elif not re.match(r"(?:if|match)(?![\w'])", inner[k:]):
            return None
    return out or None


def record_problems(rel: str, target: str, code: str, line, at: int) -> list[str]:
    """What is wrong in the record whose `{` is at `at` of a registration file
    `rel` of `target`."""
    out = []
    fields, _ = record_fields(code, at)
    names = [f[1] for f in fields]
    values = dict((f[1], f[2]) for f in fields)
    stream = STREAM_CODE.fullmatch(values.get("code", ""))
    for pos, name, value in fields:
        if name == "code" and stream:
            if values.get("verified") != f"Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed {stream.group(1)}":
                out.append(f"lean/{rel}:{line(pos)}: a streaming function's code bound with the "
                           f"cleanup form, but not its theorem; bind `verified := "
                           f"Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed {stream.group(1)}` {SKILL}")
        elif name in BOUND:
            pat, what = BOUND[name]
            if not pat.match(value) or (name == "code" and SCRUB_FORM.match(value)):
                out.append(f"lean/{rel}:{line(pos)}: a registration's `{name}` that is not {what} "
                           f"{SKILL}")
        elif name not in CHOICES:
            out.append(f"lean/{rel}:{line(pos)}: `{name}` in a registration; it binds only "
                       f"{', '.join(f'`{k}`' for k in BOUND)} and what the implementation "
                       f"chooses ({', '.join(sorted(CHOICES))}) {SKILL}")
    for name in ("code", "verified"):
        if names.count(name) != 1:
            out.append(f"lean/{rel}:{line(at)}: a registration without exactly one `{name} :=` "
                       f"{SKILL}")
    return out


def target_problems(rel: str, target: str, code: str, line) -> list[str]:
    """What is wrong in the registration file `rel` of `target`, whose text
    without comments is `code`: anything but binding named code and a
    theorem about it."""
    out = []
    shape = "it binds only `code := Impl.…` and `verified := Proof.…`"
    for m in BY.finditer(code):
        if m.group(1) in DEFAULTS and not rest_of_block(code, m.start(), m.end()):
            out.append(f"lean/{rel}:{line(m.start())}: a tactic proof in a registration file; "
                       f"{shape} {SKILL}")
    framework = re.compile(r"(?<![\w.'])(?:VG\.)?" + target + r"\.Scrub(?![\w'])")
    for pat, what in [(ANON, "an anonymous constructor (`⟨…⟩`)"),
                      (framework, f"the scrub framework (`{target}.Scrub`)"),
                      (RAW, "an `Artifact` built by hand (`target := …`)")]:
        for m in pat.finditer(code):
            out.append(f"lean/{rel}:{line(m.start())}: {what} in a registration file; "
                       f"{shape}, whose proof is made under `Proof/` {SKILL}")
    record = re.compile(r"\s+(?:(?:VG\.)?" + target + r"\.)?target\s*([{(])")
    for m in ARTIFACT.finditer(code):
        r = record.match(code, m.end())
        recs = None
        if r and r.group(1) == "{":
            recs = [r.end() - 1]
        elif r:
            recs = choice_records(code, r.end() - 1)
        if not recs:
            out.append(f"lean/{rel}:{line(m.start())}: a registration not given as a record, or "
                       f"as a `match` or `if` each of whose arms is one; write `.artifact "
                       f"{target}.target {{ code := Impl.… verified := Proof.… }}` {SKILL}")
            continue
        for at in recs:
            out += record_problems(rel, target, code, line, at)
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
            t = TARGET_FILE.fullmatch(rel.removeprefix("VerifiedGarbage/"))
            if t and not rel.startswith(SELFTEST):
                out += target_problems(rel, t.group(1), code, line)
    return out


def main() -> int:
    ps = problems(LEAN)
    for p in ps:
        print(p)
    return 1 if ps else 0


if __name__ == "__main__":
    sys.exit(main())
