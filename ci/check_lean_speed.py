#!/usr/bin/env python3
"""Checks the rules in CLAUDE.md ("Keeping proofs fast") that can be checked
without building. Exits non-zero on violations.

  * No option changes a resource limit (`maxHeartbeats`, `maxRecDepth`,
    `synthInstance.maxHeartbeats`, `synthInstance.maxSize`), in a source file
    or in the lakefile.
  * No import of all of Mathlib or of `Mathlib.Tactic`.
  * No `simp` unfolds `runBlock` or `runStep` (outside `Proof/Framework/`,
    which proves the lemmas that step blocks).
  * In the statement of a theorem in `Proof/`, an instruction-list literal
    (`[.op …]`) next to `++` has a type ascription (`([.op …] : List Instr)`).
  * A module that defines meta code (a tactic or command elaborator, a
    simproc, or a function in `MetaM`, `TacticM`, ...) and could be compiled
    (it imports only Lean core and modules of precompiled libraries) is in a
    precompiled library (`NativeTactics` in the lakefile): otherwise the
    interpreter runs it, an order of magnitude slower, in every module that
    uses it.
  * No `tauto` (a Mathlib tactic, so interpreted: seconds per call in the
    large contexts of these proofs); `grind`, `simp`, `omega` or `decide`
    prove the same goals.
  * Heavy Mathlib algebra (`HEAVY_MATHLIB`) is imported only by modules that
    few others import (at most `HEAVY_IMPORTERS` modules import them,
    directly or not): every module that reaches it pays about 1.5e9 more
    instructions to import (a quarter of a typical module's build), and its
    simp lemmas slow `simp` down.
  * A module of `Proof/`, `Artifacts/`, `Generic/` or `Variants/` with a
    numeral exponent (`x ^ 32`) imports `Proof/Framework/PowLit.lean`
    (directly or through another module), whose macro elaborates it as
    `x ^ (32 : Nat)`: without it, the exponents' default instances take time
    quadratic in their number.
  * `simp (config := {decide := true})` (or `+decide`) is counted per file
    (`DECIDE_SIMP_ALLOWED`): `simp` then runs `decide` on every closed
    proposition it visits. That is cheap for small facts (`Reg.x1 = Reg.x2`,
    small `Nat` comparisons; replacing it there with simprocs measured
    slower) and costs seconds per block when the facts evaluate expensive
    definitions (AES-GCM's block runners: 3.6 s to 0.17 s per 8 instructions
    with simprocs). A new use needs a measurement showing it is the cheaper
    option before its count goes up.
  * Every use of a helper that checks a property of every instruction of a
    whole function by a default argument (`Exec.preservedV`, `WP.preservedV`,
    `WP.withPreservedV`: `c.allInstrs keepsV = true := by decide +kernel`)
    passes that argument: `(by lit_decide)`, which evaluates the code's
    literal, or a lemma. The default re-runs the code generators in the
    kernel (seconds per use).
  * A proof that unfolds a stack-depth function (`stackUse`, `Code.depth`,
    `Code.aarch64Depth`, …) into `max`es and closes the goal with `omega`
    also rewrites with `Nat.max_le` (`max a b ≤ c ↔ a ≤ c ∧ b ≤ c`), so that
    `omega` does not split cases on each `max` (seconds per proof).
    `DEFAULT_CERT_ALLOWED` and `DEPTH_OMEGA_ALLOWED` count the uses of these
    two that remain.
  * No bare `assumption` after `<;>` or as an alternative of `first | …`: it
    tries every hypothesis at default transparency, unfolding states and
    regions before each failed match (seconds in a large context). Use
    `with_reducible assumption` or name the hypothesis.
    `BARE_ASSUMPTION_ALLOWED` counts the uses that remain.
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"

LIMITS = r"(?:maxHeartbeats|maxRecDepth|synthInstance\.maxHeartbeats|synthInstance\.maxSize)"
SET_LIMIT = re.compile(rf"\bset_option\s+{LIMITS}\b")
LAKEFILE_LIMIT = re.compile(rf"^\s*{LIMITS}\s*=", re.M)
BIG_IMPORT = re.compile(r"^\s*import\s+(Mathlib|Mathlib\.Tactic)\s*$", re.M)
SIMP_ARGS = re.compile(r"\bsimp(?:_all|a)?\b[^\[\n]*\[([^\]]*)\]")
UNFOLD = re.compile(r"(?<![\w.])(runBlock|runStep)(?![\w.])")
THEOREM = re.compile(r"^(?:private |protected )?(?:theorem|lemma) ", re.M)
DOT_LIST = re.compile(r"\[\s*\.")
META = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:elab|elab_rules|simproc|dsimproc)\b"
    r"|^(?:(?:private|protected|partial|unsafe|noncomputable)\s+)*def\s[^\n]*"
    r"\b(?:CoreM|MetaM|SimpM|TermElabM|TacticM|CommandElabM)\b",
    re.M,
)
META_WORDS = ("elab", "simproc", "CoreM", "MetaM", "SimpM", "TermElabM", "TacticM", "CommandElabM")
IMPORT = re.compile(r"^import\s+([\w.]+)", re.M)
TAUTO = re.compile(r"(?<![\w.])tauto(?![\w.])")
HEAVY_MATHLIB = (
    "Mathlib.Algebra", "Mathlib.RingTheory", "Mathlib.FieldTheory", "Mathlib.NumberTheory",
    "Mathlib.Data.ZMod", "Mathlib.Data.List.Dedup", "Mathlib.Data.Nat.ModEq",
    "Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib.Tactic.Linarith",
    "Mathlib.Tactic.LinearCombination", "Mathlib.Tactic.FieldSimp", "Mathlib.Tactic.Module",
    "Mathlib.Tactic.IntervalCases", "Mathlib.Tactic.ComputeDegree", "Mathlib.Tactic.Polyrith",
)
HEAVY_IMPORTERS = 40
# Modules that import heavy algebra and more than `HEAVY_IMPORTERS` modules
# import: the Edwards group law, each curve's bridge from its specification
# to that group (the field's primality, `ZMod`), once per curve, and the Pratt
# certificates the bridges' primality proofs share. Add nothing else.
HEAVY_HUBS_ALLOWED = {
    "VerifiedGarbage.Proof.Framework.Pratt",
    "VerifiedGarbage.Proof.Edwards.Group",
    "VerifiedGarbage.Proof.Ed448.Group.Projective",
    "VerifiedGarbage.Proof.Ed25519.Group.Extended",
}
DECIDE_CONFIG = re.compile(r"\bdecide\s*:=\s*true\b")
DECIDE_FLAG = re.compile(r"\b(?:simp|simp_all|simpa|dsimp)\b[^\n]*?\+decide\b")
BARE_ASSUMPTION = re.compile(r"(?:<;>|\|)\s*(?:try\s+)?assumption\b")
# Helpers whose last argument, a check of every instruction of a function,
# defaults to `decide +kernel`; the number of explicit arguments before it.
CERT_HELPERS = {"Exec.preservedV": 1, "WP.preservedV": 1, "WP.withPreservedV": 1}
CERT_HELPER = re.compile(r"(?<![\w])(?:VG\.AArch64\.)?(Exec\.preservedV|WP\.preservedV|WP\.withPreservedV)(?![\w.'])")
CERT_HELPER_HOME = "lean/VerifiedGarbage/Proof/Framework/AArch64/VecPreserved.lean"
CLOSE = {"(": ")", "[": "]", "⟨": "⟩", "{": "}"}
STOP_WORDS = ("fun", "by", "=>", "<;>", "|", "with", "at", "using", "then", "else", "do")
DEPTH_FNS = r"(?:stackUse|(?:Code\.)?(?:depth|fdepth|x86_64Depth|aarch64Depth))"
DEPTH_UNFOLD = re.compile(
    r"\b(?:simp|simp_all|simpa|dsimp)\b[^\[\n]*\[[^\]]*(?<![\w.])" + DEPTH_FNS + r"(?![\w.])[^\]]*\]"
    r"|\bunfold\b[^\n]*(?<![\w.])" + DEPTH_FNS + r"(?![\w.])"
)
DEPTH_LEMMA = re.compile(r"[\[,]\s*" + DEPTH_FNS + r"[\s,\]]|unfold\b[^\n]*" + DEPTH_FNS)
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|instance|example)\b", re.M)
# Uses that remain, per file: replacing them broke the proof (`decide`
# evaluated a closed fact no simproc reduces, e.g. a definition applied to
# literals, or the goal's shape changed) or timed out, or (for
# `assumption`) the hypothesis matches only up to unfolding. Lower a count
# when you remove a use; never raise one or add a file.
from lean_speed_allowed import (  # noqa: E402
    BARE_ASSUMPTION_ALLOWED,
    DECIDE_SIMP_ALLOWED,
    DEFAULT_CERT_ALLOWED,
    DEPTH_OMEGA_ALLOWED,
)

POW_LIT = "VerifiedGarbage.Proof.Framework.PowLit"
POW_PREFIXES = tuple(f"VerifiedGarbage.{d}." for d in ("Proof", "Artifacts", "Generic", "Variants"))
NUM_EXP = re.compile(r"\^\s*[0-9]+(?![0-9.])")
LIB = re.compile(r"^\[\[lean_lib\]\]\n(.*?)(?=^\[\[|\Z)", re.M | re.S)


def line_of(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


def unascribed_lists(text: str):
    """Yields the offsets of instruction-list literals in theorem statements
    that are an operand of `++` without a type ascription."""
    statements = [(m.start(), text.find(":=", m.end())) for m in THEOREM.finditer(text)]
    for m in DOT_LIST.finditer(text):
        i = m.start()
        if not any(a <= i < b for a, b in statements):
            continue
        depth, k = 0, i
        while k < len(text):
            depth += {"[": 1, "]": -1}.get(text[k], 0)
            if depth == 0:
                break
            k += 1
        before, after = text[:i].rstrip(), text[k + 1 :].lstrip()
        if not (before.endswith("++") or after.startswith("++")):
            continue
        if before.endswith("(") and after.startswith(":"):
            continue
        yield i


def call_args(text: str, i: int) -> list[str]:
    """The arguments of the application whose function ends at `i`: groups in
    brackets and plain tokens, up to a closing bracket, `,`, `;`, a keyword or
    a line indented no deeper than the one the function is on."""
    line_start = text.rfind("\n", 0, i) + 1
    indent = len(text[line_start:i]) - len(text[line_start:i].lstrip(" "))
    args, k, n = [], i, len(text)
    while k < n:
        while k < n and text[k] in " \t":
            k += 1
        if k < n and text[k] == "\n":
            j = k + 1
            while j < n and text[j] == " ":
                j += 1
            if j - k - 1 <= indent:
                break
            k = j
            continue
        if k >= n or text[k] in ")]⟩},;":
            break
        if text[k] in CLOSE:
            d, j = 0, k
            while j < n:
                d += 1 if text[j] in "([⟨{" else -1 if text[j] in ")]⟩}" else 0
                j += 1
                if d == 0:
                    break
            args.append(text[k:j])
            k = j
            continue
        m = re.match(r"[^\s()\[\]⟨⟩{},;]+", text[k:])
        if not m or m.group(0) in STOP_WORDS:
            break
        args.append(m.group(0))
        k += m.end()
    return args


def default_cert(text: str, m: re.Match) -> bool:
    """Whether this use of a `CERT_HELPERS` helper leaves its certificate to
    the default `decide +kernel`, or passes `decide` itself."""
    args = call_args(text, m.end())
    named = [a for a in args if re.match(r"\(\s*hc\s*:=", a)]
    positional = [a for a in args if not re.match(r"\(\s*\w+\s*:=", a)]
    cert = named[0] if named else (positional[CERT_HELPERS[m.group(1)]]
                                   if len(positional) > CERT_HELPERS[m.group(1)] else None)
    return cert is None or ("decide" in cert and "lit_decide" not in cert)


def depth_omega(code: str) -> list[int]:
    """The offsets of declarations that unfold a stack-depth function and use
    `omega` without `Nat.max_le`."""
    if not DEPTH_LEMMA.search(code):
        return []
    starts = [m.start() for m in DECL.finditer(code)] + [len(code)]
    out = []
    for a, b in zip(starts, starts[1:]):
        body = code[a:b]
        if "omega" in body and "max_le" not in body and DEPTH_UNFOLD.search(body):
            out.append(a)
    return out


def precompiled_globs(lakefile: str) -> list[str]:
    """The module globs of the libraries with `precompileModules = true`."""
    globs = []
    for m in LIB.finditer(lakefile):
        block = m.group(1)
        if re.search(r"^precompileModules\s*=\s*true", block, re.M):
            g = re.search(r"^globs\s*=\s*\[(.*?)\]", block, re.M | re.S)
            if g:
                globs += re.findall(r'"([^"]+)"', g.group(1))
    return globs


def in_globs(module: str, globs: list[str]) -> bool:
    for g in globs:
        if g.endswith(".+") and module.startswith(g[:-1]):
            return True
        if g.endswith(".*") and (module == g[:-2] or module.startswith(g[:-1])):
            return True
        if module == g:
            return True
    return False


def uncompiled_meta(rel_module: str, text: str, globs: list[str]) -> bool:
    """Whether the module defines meta code, could be compiled (it imports only
    Lean core and precompiled modules), and is not."""
    if not any(k in text for k in META_WORDS) or not META.search(text) or in_globs(rel_module, globs):
        return False
    core = ("Init", "Std", "Lean")
    return all(i.split(".")[0] in core or in_globs(i, globs) for i in IMPORT.findall(text))


def strip_comments(text: str) -> str:
    """`text` with its comments blanked out (keeping line numbers)."""
    text = re.sub(r"/-.*?-/", lambda m: re.sub(r"[^\n]", " ", m.group(0)), text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def heavy_hubs(imports: dict[str, list[str]]) -> list[tuple[str, list[str], int]]:
    """The modules that import heavy Mathlib algebra and are imported, directly
    or not, by more than `HEAVY_IMPORTERS` modules: (module, heavy imports, importers)."""
    importers: dict[str, set[str]] = {m: set() for m in imports}
    for m, imps in imports.items():
        for i in imps:
            if i in importers:
                importers[i].add(m)
    out = []
    for m, imps in imports.items():
        heavy = [i for i in imps if i.startswith(HEAVY_MATHLIB)]
        if not heavy or m in HEAVY_HUBS_ALLOWED:
            continue
        seen, todo = set(), [m]
        while todo:
            for i in importers[todo.pop()]:
                if i not in seen:
                    seen.add(i)
                    todo.append(i)
        if len(seen) > HEAVY_IMPORTERS:
            out.append((m, heavy, len(seen)))
    return out


def imports_pow_lit(module: str, imports: dict[str, list[str]], memo: dict[str, bool]) -> bool:
    """Whether `module` imports `PowLit`, directly or through other modules."""
    if module not in memo:
        memo[module] = False
        memo[module] = any(i == POW_LIT or imports_pow_lit(i, imports, memo) for i in imports.get(module, []))
    return memo[module]


def main() -> int:
    errors = []
    imports: dict[str, list[str]] = {}
    paths: dict[str, pathlib.Path] = {}
    globs = precompiled_globs((LEAN / "lakefile.toml").read_text())
    sources = [f for f in LEAN.rglob("*.lean") if ".lake" not in f.parts]
    texts = {f: f.read_text() for f in sources}
    lean_prefix = len(str(LEAN)) + 1
    keys = {f: str(f)[lean_prefix:] for f in sources}
    modules = {f: keys[f][: -len(".lean")].replace("/", ".") for f in sources}
    for f, text in texts.items():
        imports[modules[f]] = IMPORT.findall(text)
    pow_memo: dict[str, bool] = {}
    for f in sorted(sources):
        text = texts[f]
        rel = pathlib.Path("lean") / keys[f]
        module = modules[f]
        paths[module] = rel
        depth = ("omega" in text and "max_le" not in text
                 and any(k in text for k in ("stackUse", "Depth", "depth ", "depth,", "depth]")))
        code = (strip_comments(text) if depth or any(k in text for k in ("^", "tauto", "decide", "assumption", "reservedV"))
                else "")
        if "^" in code and module.startswith(POW_PREFIXES) and module != POW_LIT:
            m = NUM_EXP.search(code)
            if m and not imports_pow_lit(module, imports, pow_memo):
                errors.append(
                    f"{rel}:{line_of(code, m.start())}: numeral exponent in a module that does not import "
                    f"{POW_LIT}; import it (or a module that does)"
                )
        key = keys[f]
        decide_uses = []
        if "decide" in code:
            decide_uses = list(DECIDE_CONFIG.finditer(code))
            if "+decide" in code:
                decide_uses += DECIDE_FLAG.finditer(code)
        assumption_uses = list(BARE_ASSUMPTION.finditer(code)) if "assumption" in code else []
        for found, allowed, what in (
            (decide_uses, DECIDE_SIMP_ALLOWED, "`decide := true` in simp; measure it against simprocs (`reduceCtorEq`, `↓reduceIte`, `Nat.reduce*`) and raise the count in ci/lean_speed_allowed.py only if it is cheaper"),
            (assumption_uses, BARE_ASSUMPTION_ALLOWED,
             "bare `assumption` after `<;>` or in `first`; use `with_reducible assumption`"),
        ):
            n = allowed.get(key, 0)
            if len(found) > n:
                for m in found:
                    errors.append(f"{rel}:{line_of(code, m.start())}: {what} ({len(found)} uses, {n} allowed)")
            elif len(found) < n:
                errors.append(f"{rel}: {len(found)} uses of {what.split(';')[0]}, fewer than the {n} allowed; lower the count")
        if "reservedV" in code and str(rel) != CERT_HELPER_HOME:
            found = [m for m in CERT_HELPER.finditer(code) if default_cert(code, m)]
            n = DEFAULT_CERT_ALLOWED.get(key, 0)
            if len(found) > n:
                for m in found:
                    errors.append(
                        f"{rel}:{line_of(code, m.start())}: `{m.group(1)}` checks every instruction by "
                        f"`decide +kernel`; pass the check: `(by lit_decide)` or a lemma ({len(found)} uses, {n} allowed)"
                    )
            elif len(found) < n:
                errors.append(f"{rel}: {len(found)} uses of a default instruction check, fewer than the {n} allowed; "
                              "lower the count")
        if depth and module.startswith("VerifiedGarbage.Proof.") and not module.startswith("VerifiedGarbage.Proof.Framework."):
            found = depth_omega(code)
            n = DEPTH_OMEGA_ALLOWED.get(key, 0)
            if len(found) > n:
                for a in found:
                    errors.append(
                        f"{rel}:{line_of(code, a)}: `omega` on an unfolded stack depth; simp with `Nat.max_le` "
                        f"first, so that it does not split cases on each `max` ({len(found)} uses, {n} allowed)"
                    )
            elif len(found) < n:
                errors.append(f"{rel}: {len(found)} uses of `omega` on an unfolded stack depth, fewer than the "
                              f"{n} allowed; lower the count")
        for m in TAUTO.finditer(code):
            errors.append(f"{rel}:{line_of(code, m.start())}: `tauto` runs interpreted; use `grind`, `simp` or `decide`")
        if uncompiled_meta(module, text, globs):
            errors.append(
                f"{rel}: defines meta code and imports only Lean core and precompiled modules; "
                "add it to `NativeTactics` in lean/lakefile.toml so that it runs compiled"
            )
        for m in (SET_LIMIT.finditer(text) if any(k in text for k in ("maxHeartbeats", "maxRecDepth", "synthInstance.max")) else ()):
            errors.append(f"{rel}:{line_of(text, m.start())}: changes a resource limit; make the proof faster instead")
        for m in (BIG_IMPORT.finditer(text) if "import Mathlib" in text else ()):
            errors.append(f"{rel}:{line_of(text, m.start())}: imports {m.group(1)}; import the modules you use")
        if module.startswith("VerifiedGarbage.Proof."):
            for i in (unascribed_lists(text) if "++" in text else ()):
                errors.append(
                    f"{rel}:{line_of(text, i)}: instruction list next to `++` in a theorem statement; "
                    "ascribe it: `([.op …] : List Instr)`"
                )
        if module.startswith("VerifiedGarbage.Proof.Framework."):
            continue
        if "runBlock" not in text and "runStep" not in text:
            continue
        for m in SIMP_ARGS.finditer(text):
            for u in UNFOLD.finditer(m.group(1)):
                errors.append(
                    f"{rel}:{line_of(text, m.start(1) + u.start())}: simp unfolds {u.group(1)}; "
                    "step with runBlock_cons, runStep_some and runBlock_nil"
                )
    for m, heavy, n in heavy_hubs(imports):
        errors.append(
            f"{paths[m]}: imports {', '.join(heavy)} and {n} modules import it (more than "
            f"{HEAVY_IMPORTERS}); move what needs that algebra into the few modules that use it"
        )
    lakefile = LEAN / "lakefile.toml"
    text = lakefile.read_text()
    for m in LAKEFILE_LIMIT.finditer(text):
        errors.append(f"{lakefile.relative_to(ROOT)}:{line_of(text, m.start())}: changes a resource limit")
    for e in errors:
        print(e, file=sys.stderr)
    if not errors:
        print("Lean proof-speed rules OK")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
