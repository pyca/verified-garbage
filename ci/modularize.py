#!/usr/bin/env python3
"""Converts Lean files to modules of Lean's module system, keeping what
every importer sees.

  modularize.py PATH...   convert each `.lean` file at PATH (a file or a
                          directory, recursively) that is not a module yet
  modularize.py check-converted
                          fail if a directory of `CONVERTED` has a file
                          that is not a module, saying what to run, or if
                          a module imports a file that is not one
  modularize.py check LOG
                          fail if a `lake build` log (LOG, `-` for stdin)
                          shows an exposed declaration referring to a
                          private one of its module, listing each

A converted file starts with `module`; its imports become `public import`
(a module may import only modules, so a layer is converted only once what it
imports is); and its body is an `@[expose] public section`, so that every
declaration stays visible to importers with its definition, as before.

A file that only defines tactics, elaborators or commands (it declares
`elab`, `syntax`, `macro` or `simproc`s, and no theorem, nor a command that
adds one, nor a structure, inductive type or instance unless it imports
`Lean`) is meta code: its
body is a `public meta section`, so that its definitions run at elaboration
time in the files that use them, and each of its imports is also a
`public meta import` (only that, for `Lean`'s), so that its code can run
theirs. A file that declares such meta code next to definitions or theorems
(marking `meta` the definitions its tactics run) imports `Lean` both ways:
`public import` and `public meta import`.

A file that evaluates code while it is elaborated (`#guard`, `#eval`,
`run_cmd`, ..., and the framework's `materialize_*` and `taint_decide`/
`taint_summary`, which run code to build literals and hints) also imports each of its imports as `meta import`, so that
what it evaluates is available to the compiler at that time.

A proof module (under `Proof/`, but not the framework) also imports the core
modules of `CORE_ALL` with `import all`, and those of `CORE_ALL_FOR` whose
definition it mentions.

A leading comment (a copyright notice) stays before `module`.

An exposed declaration may not refer to a private one of its module (Lean:
"A private declaration `x` (from the current module) exists but would need
to be public to access here"). The conversion does not change visibility:
`check` lists such declarations from a build of the layer, which become
public (or are renamed, if that would clash) in a small PR of their own
before the layer is converted. So do the definitions that meta code runs
(`meta`), and the `Lean` modules it uses, which a module sees only through
its imports' public imports: Lean accepts both edits outside modules too.

The conversion is mechanical and idempotent: rerun it on a layer after
merging, rather than editing headers by hand.
"""

import pathlib
import re
import sys

LEAN = pathlib.Path(__file__).resolve().parent.parent / "lean"

# The directories (under lean/) whose every file is a module: `D` for every
# file under D, `D/*` for D's own files (not those of its subdirectories).
# The PR that converts a layer adds its directories here, so that CI rejects
# a file added to one later without a module header (by a PR older than the
# conversion).
CONVERTED = ["VerifiedGarbage/TCB", "VerifiedGarbage/Spec", "VerifiedGarbage/Impl",
             "VerifiedGarbage/Proof/Framework",
             "VerifiedGarbage/Proof/Aes/*",
             "VerifiedGarbage/Proof/Aes/AArch64",
             "VerifiedGarbage/Proof/Aes/Arm",
             "VerifiedGarbage/Proof/Aes/Ct32",
             "VerifiedGarbage/Proof/Aes/X86",
             "VerifiedGarbage/Proof/AesCbc/*",
             "VerifiedGarbage/Proof/AesCbc/AArch64",
             "VerifiedGarbage/Proof/AesCbc/X86",
             "VerifiedGarbage/Proof/AesCfb/*",
             "VerifiedGarbage/Proof/AesCfb/AArch64",
             "VerifiedGarbage/Proof/AesCfb/X86",
             "VerifiedGarbage/Proof/AesCfb8/*",
             "VerifiedGarbage/Proof/AesCfb8/AArch64",
             "VerifiedGarbage/Proof/AesCfb8/X86",
             "VerifiedGarbage/Proof/AesOfb/*",
             "VerifiedGarbage/Proof/AesOfb/AArch64",
             "VerifiedGarbage/Proof/AesOfb/X86",
             "VerifiedGarbage/Proof/AesXts/*",
             "VerifiedGarbage/Proof/Argon2/*",
             "VerifiedGarbage/Proof/Argon2/AArch64",
             "VerifiedGarbage/Proof/Blake2/*",
             "VerifiedGarbage/Proof/Blake2/AArch64",
             "VerifiedGarbage/Proof/Camellia/*",
             "VerifiedGarbage/Proof/ChaCha20/*",
             "VerifiedGarbage/Proof/ChaCha20/Arm",
             "VerifiedGarbage/Proof/ChaCha20/X86",
             "VerifiedGarbage/Proof/Cmac/*",
             "VerifiedGarbage/Proof/CmacAes/AArch64",
             "VerifiedGarbage/Proof/CmacAes/Arm",
             "VerifiedGarbage/Proof/CmacAes/X86",
             "VerifiedGarbage/Proof/CmacTripleDes/*",
             "VerifiedGarbage/Proof/Divstep/*",
             "VerifiedGarbage/Proof/Edwards/*",
             "VerifiedGarbage/Proof/Gcm/*",
             "VerifiedGarbage/Proof/Gcm/AArch64",
             "VerifiedGarbage/Proof/Gcm/Arm",
             "VerifiedGarbage/Proof/Gcm/X86",
             "VerifiedGarbage/Proof/Md5/*",
             "VerifiedGarbage/Proof/Md5/AArch64",
             "VerifiedGarbage/Proof/Md5/Arm",
             "VerifiedGarbage/Proof/Md5/X86",
             "VerifiedGarbage/Proof/Md5/X86_64",
             "VerifiedGarbage/Proof/MdStream/*",
             "VerifiedGarbage/Proof/MdStream/AArch64",
             "VerifiedGarbage/Proof/MdStream/Arm",
             "VerifiedGarbage/Proof/MdStream/X86",
             "VerifiedGarbage/Proof/MdStream/X86_64",
             "VerifiedGarbage/Proof/Mgf1/*",
             "VerifiedGarbage/Proof/MlDsa/*",
             "VerifiedGarbage/Proof/MlDsa/Arith",
             "VerifiedGarbage/Proof/MlDsa/KeyGen",
             "VerifiedGarbage/Proof/MlDsa/Message",
             "VerifiedGarbage/Proof/MlDsa/Pack",
             "VerifiedGarbage/Proof/MlDsa/Round",
             "VerifiedGarbage/Proof/MlDsa/Sample",
             "VerifiedGarbage/Proof/MlDsa/Sign",
             "VerifiedGarbage/Proof/MlDsa/Verify",
             "VerifiedGarbage/Proof/MlKem/*",
             "VerifiedGarbage/Proof/MlKem/AArch64",
             "VerifiedGarbage/Proof/Sha256/*",
             "VerifiedGarbage/Proof/Sha3/*",
             "VerifiedGarbage/Proof/Sha3/AArch64",
             "VerifiedGarbage/Proof/Sha3/X86_64",
             "VerifiedGarbage/Proof/MlDsa/AArch64",
             "VerifiedGarbage/Proof/Bignum/*",
             "VerifiedGarbage/Proof/Bignum/AArch64",
             "VerifiedGarbage/Proof/ChaCha20Poly1305/*",
             "VerifiedGarbage/Proof/Dsa/*",
             "VerifiedGarbage/Proof/MlKem1024/AArch64",
             "VerifiedGarbage/Proof/Mont/*",
             "VerifiedGarbage/Proof/Mont/X86",
             "VerifiedGarbage/Proof/Ocb/*",
             "VerifiedGarbage/Proof/Poly1305/*",
             "VerifiedGarbage/Proof/Poly1305/Arm",
             "VerifiedGarbage/Proof/Poly1305/X86",
             "VerifiedGarbage/Proof/Rc2/*",
             "VerifiedGarbage/Proof/Rc2/AArch64",
             "VerifiedGarbage/Proof/Rc2/Arm",
             "VerifiedGarbage/Proof/Rc2/X86",
             "VerifiedGarbage/Proof/Rc2/X86_64",
             "VerifiedGarbage/Proof/Rc4/*",
             "VerifiedGarbage/Proof/Rc4/AArch64",
             "VerifiedGarbage/Proof/Rc4/Arm",
             "VerifiedGarbage/Proof/Rsa/*",
             "VerifiedGarbage/Proof/Rsa/AArch64",
             "VerifiedGarbage/Proof/RsaKeyGen/*",
             "VerifiedGarbage/Proof/RsaKeyGen/AArch64",
             "VerifiedGarbage/Proof/RsaOaep/*",
             "VerifiedGarbage/Proof/RsaPkcs1Enc/*",
             "VerifiedGarbage/Proof/RsaPkcs1Sig/*",
             "VerifiedGarbage/Proof/RsaPkcs1Sig/AArch64",
             "VerifiedGarbage/Proof/RsaPss/*",
             "VerifiedGarbage/Proof/Scrypt/*",
             "VerifiedGarbage/Proof/Seed/*",
             "VerifiedGarbage/Proof/Selftest/*",
             "VerifiedGarbage/Proof/Sha1/*",
             "VerifiedGarbage/Proof/Sha1/AArch64",
             "VerifiedGarbage/Proof/Sha1/Arm",
             "VerifiedGarbage/Proof/Sha1/X86_64",
             "VerifiedGarbage/Proof/Sha256/AArch64",
             "VerifiedGarbage/Proof/Sha256/Arm",
             "VerifiedGarbage/Proof/Sha256/X86_64",
             "VerifiedGarbage/Proof/Sha512/*",
             "VerifiedGarbage/Proof/Sha512/AArch64",
             "VerifiedGarbage/Proof/Sha512/Arm",
             "VerifiedGarbage/Proof/Sha512/X86_64",
             "VerifiedGarbage/Proof/Bignum/X86_64",
             "VerifiedGarbage/Proof/Dsa/X86_64",
             "VerifiedGarbage/Proof/Ed25519/*",
             "VerifiedGarbage/Proof/Ed25519/Group",
             "VerifiedGarbage/Proof/Ed25519/X86_64",
             "VerifiedGarbage/Proof/Ffdh/*",
             "VerifiedGarbage/Proof/Hmac/*",
             "VerifiedGarbage/Proof/Hmac/Generic",
             "VerifiedGarbage/Proof/MlDsa/X86_64",
             "VerifiedGarbage/Proof/MlKem/Arm",
             "VerifiedGarbage/Proof/MlKem/X86_64",
             "VerifiedGarbage/Proof/MlKem1024/X86_64",
             "VerifiedGarbage/Proof/Mont/X86_64",
             "VerifiedGarbage/Proof/Pbkdf2/*",
             "VerifiedGarbage/Proof/Pbkdf2/AArch64",
             "VerifiedGarbage/Proof/Pbkdf2/Md",
             "VerifiedGarbage/Proof/Pbkdf2/Stream",
             "VerifiedGarbage/Proof/Pbkdf2/X86_64",
             "VerifiedGarbage/Proof/Poly1305/X86_64",
             "VerifiedGarbage/Proof/Rc4/X86_64",
             "VerifiedGarbage/Proof/Rsa/X86_64",
             "VerifiedGarbage/Proof/RsaPss/AArch64",
             "VerifiedGarbage/Proof/RsaPss/X86_64",
             "VerifiedGarbage/Proof/Sha1/X86",
             "VerifiedGarbage/Proof/Sha256/X86",
             "VerifiedGarbage/Proof/Sha3/Arm",
             "VerifiedGarbage/Proof/Sha512/X86",
             "VerifiedGarbage/Proof/Siv/*",
             "VerifiedGarbage/Proof/Weierstrass/*",
             "VerifiedGarbage/Proof/Weierstrass/X86_64",
             "VerifiedGarbage/Proof/X25519/*",
             "VerifiedGarbage/Proof/X25519/Edwards",
             "VerifiedGarbage/Proof/X25519/X86_64",
             "VerifiedGarbage/Proof/Aes/X86_64",
             "VerifiedGarbage/Proof/AesCbc/Arm",
             "VerifiedGarbage/Proof/AesCbc/X86_64",
             "VerifiedGarbage/Proof/AesCcm/*",
             "VerifiedGarbage/Proof/AesCcm/AArch64",
             "VerifiedGarbage/Proof/AesCcm/Arm",
             "VerifiedGarbage/Proof/AesCcm/X86",
             "VerifiedGarbage/Proof/AesCcm/X86_64",
             "VerifiedGarbage/Proof/AesCfb/Arm",
             "VerifiedGarbage/Proof/AesCfb/X86_64",
             "VerifiedGarbage/Proof/AesCfb8/Arm",
             "VerifiedGarbage/Proof/AesCfb8/X86_64",
             "VerifiedGarbage/Proof/AesCtr/*",
             "VerifiedGarbage/Proof/AesCtr/AArch64",
             "VerifiedGarbage/Proof/AesCtr/Arm",
             "VerifiedGarbage/Proof/AesCtr/X86",
             "VerifiedGarbage/Proof/AesCtr/X86_64",
             "VerifiedGarbage/Proof/AesGcm/*",
             "VerifiedGarbage/Proof/AesGcm/AArch64",
             "VerifiedGarbage/Proof/AesGcm/Arm",
             "VerifiedGarbage/Proof/AesGcm/X86",
             "VerifiedGarbage/Proof/AesGcm/X86_64",
             "VerifiedGarbage/Proof/AesGcmSiv/*",
             "VerifiedGarbage/Proof/AesGcmSiv/AArch64",
             "VerifiedGarbage/Proof/AesGcmSiv/Arm",
             "VerifiedGarbage/Proof/AesGcmSiv/X86",
             "VerifiedGarbage/Proof/AesGcmSiv/X86_64",
             "VerifiedGarbage/Proof/AesOcb/*",
             "VerifiedGarbage/Proof/AesOcb/AArch64",
             "VerifiedGarbage/Proof/AesOcb/Arm",
             "VerifiedGarbage/Proof/AesOcb/X86",
             "VerifiedGarbage/Proof/AesOcb/X86_64",
             "VerifiedGarbage/Proof/AesOfb/Arm",
             "VerifiedGarbage/Proof/AesOfb/X86_64",
             "VerifiedGarbage/Proof/AesSiv/*",
             "VerifiedGarbage/Proof/AesSiv/AArch64",
             "VerifiedGarbage/Proof/AesSiv/Arm",
             "VerifiedGarbage/Proof/AesSiv/X86",
             "VerifiedGarbage/Proof/AesSiv/X86_64",
             "VerifiedGarbage/Proof/AesXts/AArch64",
             "VerifiedGarbage/Proof/AesXts/Arm",
             "VerifiedGarbage/Proof/AesXts/X86",
             "VerifiedGarbage/Proof/AesXts/X86_64",
             "VerifiedGarbage/Proof/Argon2/Arm",
             "VerifiedGarbage/Proof/Argon2/X86",
             "VerifiedGarbage/Proof/Argon2/X86_64",
             "VerifiedGarbage/Proof/Blake2/Arm",
             "VerifiedGarbage/Proof/Blake2/X86",
             "VerifiedGarbage/Proof/Blake2/X86_64",
             "VerifiedGarbage/Proof/ChaCha20/X86_64",
             "VerifiedGarbage/Proof/ChaCha20Poly1305/X86_64",
             "VerifiedGarbage/Proof/CmacAes/Stream",
             "VerifiedGarbage/Proof/CmacAes/X86_64",
             "VerifiedGarbage/Proof/Gcm/X86_64",
             "VerifiedGarbage/Proof/GcmSiv/*",
             "VerifiedGarbage/Proof/Blowfish/*",
             "VerifiedGarbage/Proof/Blowfish/AArch64",
             "VerifiedGarbage/Proof/Blowfish/Arm",
             "VerifiedGarbage/Proof/Blowfish/X86",
             "VerifiedGarbage/Proof/Blowfish/X86_64",
             "VerifiedGarbage/Proof/BrainpoolP256r1/*",
             "VerifiedGarbage/Proof/BrainpoolP384r1/*",
             "VerifiedGarbage/Proof/BrainpoolP512r1/*",
             "VerifiedGarbage/Proof/Camellia/AArch64",
             "VerifiedGarbage/Proof/Camellia/Arm",
             "VerifiedGarbage/Proof/Camellia/X86",
             "VerifiedGarbage/Proof/Camellia/X86_64",
             "VerifiedGarbage/Proof/Cast5/*",
             "VerifiedGarbage/Proof/Cast5/AArch64",
             "VerifiedGarbage/Proof/Cast5/Arm",
             "VerifiedGarbage/Proof/Cast5/X86",
             "VerifiedGarbage/Proof/Cast5/X86_64",
             "VerifiedGarbage/Proof/ChaCha20/AArch64",
             "VerifiedGarbage/Proof/ChaCha20Poly1305/AArch64",
             "VerifiedGarbage/Proof/ChaCha20Poly1305/Arm",
             "VerifiedGarbage/Proof/ChaCha20Poly1305/X86",
             "VerifiedGarbage/Proof/CmacTripleDes/AArch64",
             "VerifiedGarbage/Proof/CmacTripleDes/Arm",
             "VerifiedGarbage/Proof/CmacTripleDes/X86",
             "VerifiedGarbage/Proof/CmacTripleDes/X86_64",
             "VerifiedGarbage/Proof/Ct/*",
             "VerifiedGarbage/Proof/Curve448/AArch64",
             "VerifiedGarbage/Proof/EcKey/*",
             "VerifiedGarbage/Proof/Ed25519/AArch64",
             "VerifiedGarbage/Proof/Ed448/*",
             "VerifiedGarbage/Proof/Ed448/AArch64",
             "VerifiedGarbage/Proof/Ed448/Group",
             "VerifiedGarbage/Proof/MlDsa/X86",
             "VerifiedGarbage/Proof/MlKem/X86",
             "VerifiedGarbage/Proof/Modes/*",
             "VerifiedGarbage/Proof/Modes/AArch64",
             "VerifiedGarbage/Proof/Modes/Arm",
             "VerifiedGarbage/Proof/Modes/X86",
             "VerifiedGarbage/Proof/Modes/X86_64",
             "VerifiedGarbage/Proof/Mont/AArch64",
             "VerifiedGarbage/Proof/Poly1305/AArch64",
             "VerifiedGarbage/Proof/Sha3/X86",
             "VerifiedGarbage/Proof/Sm4/*",
             "VerifiedGarbage/Proof/Sm4/Arm",
             "VerifiedGarbage/Proof/TripleDes/*",
             "VerifiedGarbage/Proof/X448/*",
             "VerifiedGarbage/Proof/X448/AArch64",
             "VerifiedGarbage/Proof/X448/Edwards",
             "VerifiedGarbage/Proof/X448/Wide",
             "VerifiedGarbage/Proof/Zeroize/*",
             "VerifiedGarbage/Proof/EcKey/AArch64",
             "VerifiedGarbage/Proof/EcKey/Arm",
             "VerifiedGarbage/Proof/EcKey/X86",
             "VerifiedGarbage/Proof/Ecdh/*",
             "VerifiedGarbage/Proof/Ecdh/AArch64",
             "VerifiedGarbage/Proof/Ecdh/Arm",
             "VerifiedGarbage/Proof/Ecdsa/*",
             "VerifiedGarbage/Proof/Ecdsa/AArch64",
             "VerifiedGarbage/Proof/Ecdsa/Arm",
             "VerifiedGarbage/Proof/Ecdsa/X86",
             "VerifiedGarbage/Proof/Ed25519/X86",
             "VerifiedGarbage/Proof/Mont/Arm",
             "VerifiedGarbage/Proof/P192/*",
             "VerifiedGarbage/Proof/P224/*",
             "VerifiedGarbage/Proof/P256/*",
             "VerifiedGarbage/Proof/P256/VerifyAllocated",
             "VerifiedGarbage/Proof/P256/VerifySparse",
             "VerifiedGarbage/Proof/P384/*",
             "VerifiedGarbage/Proof/P521/*",
             "VerifiedGarbage/Proof/Secp256k1/*",
             "VerifiedGarbage/Proof/Weierstrass/AArch64",
             "VerifiedGarbage/Proof/Weierstrass/Arm",
             "VerifiedGarbage/Proof/Weierstrass/X86",
             "VerifiedGarbage/Proof/X25519/Arm",
             "VerifiedGarbage/Proof/X25519/X86",
             "VerifiedGarbage/Proof/EcKey/X86_64",
             "VerifiedGarbage/Proof/Ecdh/X86",
             "VerifiedGarbage/Proof/Ecdh/X86_64",
             "VerifiedGarbage/Proof/Ecdsa/Rfc6979",
             "VerifiedGarbage/Proof/Ecdsa/Verify",
             "VerifiedGarbage/Proof/Ecdsa/X86_64",
             "VerifiedGarbage/Proof/Ed25519/Arm",
             "VerifiedGarbage/Proof/Ed448/Arm",
             "VerifiedGarbage/Proof/Ed448/X86",
             "VerifiedGarbage/Proof/Ed448/X86_64",
             "VerifiedGarbage/Proof/Idea/*",
             "VerifiedGarbage/Proof/Idea/AArch64",
             "VerifiedGarbage/Proof/Idea/Arm",
             "VerifiedGarbage/Proof/Idea/X86",
             "VerifiedGarbage/Proof/Idea/X86_64",
             "VerifiedGarbage/Proof/MlDsa/Arm",
             "VerifiedGarbage/Proof/MlKem1024/Arm",
             "VerifiedGarbage/Proof/MlKem1024/X86",
             "VerifiedGarbage/Proof/P224/X86_64",
             "VerifiedGarbage/Proof/P256/Linear",
             "VerifiedGarbage/Proof/P256/X86_64",
             "VerifiedGarbage/Proof/P384/X86_64",
             "VerifiedGarbage/Proof/P521/X86_64",
             "VerifiedGarbage/Proof/Pbkdf2/Whole",
             "VerifiedGarbage/Proof/X448/Arm",
             "VerifiedGarbage/Proof/X448/X86",
             "VerifiedGarbage/Proof/X448/X86_64"]

IMPORT = re.compile(r"^import\s+(\S+)\s*$")
META_DECL = re.compile(r"^(elab|syntax|macro|macro_rules|simproc|dsimproc|elab_rules)\b", re.M)
THEOREM = re.compile(r"^(@\[[^\]]*\]\s*)?(private\s+)?(theorem|lemma)\b", re.M)
META_MARK = re.compile(r"^\s*(@\[[^\]]*\]\s*)?((public|private|protected)\s+)?meta\s+(def|instance|section|abbrev|structure)\b", re.M)
EVAL_CMD = re.compile(r"^\s*(#guard|#eval|#reduce|run_cmd|run_elab|run_meta|materialize_\w+)\b", re.M)
EVAL_NAMES = ["taint_decide", "taint_summar"]


def evaluates(text: str, names: list[str]) -> bool:
    """Whether `text` runs code while it is elaborated: an evaluating command,
    a tactic or command whose name contains one of `EVAL_NAMES`, or one of the
    other `names` (not in a docstring's backquotes, a string, or a syntax
    quotation)."""
    if EVAL_CMD.search(text):
        return True
    pre = r"(^|[\s;·>]|(?<!`)\()"
    base = "|".join(re.escape(n) for n in EVAL_NAMES)
    if re.search(pre + r"\w*(" + base + r")\w*\b", text, re.M):
        return True
    others = [n for n in names if n not in EVAL_NAMES]
    return bool(others) and re.search(pre + r"(" + "|".join(map(re.escape, others)) + r")\b(?!`)",
                                      text, re.M) is not None


# A tactic or command defined by `macro "name" … => body` or `elab "name" …`,
# or by `macro_rules`/`elab_rules` on `(tactic| name …)`: its name and body.
DEFINES = re.compile(r'^(?:macro|elab)\b[^"\n]*"(\w+)|^(?:macro_rules|elab_rules)\b', re.M)
QUOTED = re.compile(r"`\((?:tactic|command)\|\s*(\w+)")


def blocks(text: str):
    """The top-level `macro`/`elab`/`…_rules` blocks of `text`: (names, body)."""
    starts = [m for m in DEFINES.finditer(text)]
    for k, m in enumerate(starts):
        end = text.find("\n\n", m.end())
        body = text[m.start():end if end >= 0 else len(text)]
        names = [m.group(1)] if m.group(1) else [q for q in QUOTED.findall(body.split("=>")[0])]
        yield names, body.split("=>", 1)[1] if "=>" in body else body


def evaluating_names(lean: pathlib.Path) -> list[str]:
    """`EVAL_NAMES`, and the project's tactics and commands whose definition
    runs one of them or evaluates a term itself (`evalExpr`), to a fixpoint:
    e.g. `kem_wf`, a macro for `taint_decide`, and `def_literal`."""
    bs = [b for f in (lean / "VerifiedGarbage" / "Proof").rglob("*.lean") for b in blocks(f.read_text())]
    names = list(EVAL_NAMES)
    while True:
        new = {n for ns, body in bs if evaluates(body, names) or "evalExpr" in body for n in ns if n not in names}
        if not new:
            return names
        names += sorted(new)


def is_module(lines: list[str]) -> bool:
    comment = False
    for l in lines:
        s = l.strip()
        if comment:
            comment = not s.endswith("-/")
            continue
        if s.startswith("/-") and not s.startswith("/-!"):
            comment = not s.endswith("-/")
            continue
        if s == "module":
            return True
        if s and not s.startswith("--"):
            return False
    return False


# Lean core modules with definitions the proofs evaluate (with `decide`,
# `rfl` or the kernel, e.g. Spec tables built with `Array.ofFn`) but that core
# does not expose to modules. A proof module imports them with `import all`,
# so that it sees their bodies as a non-module file does.
CORE_ALL = ["Init.Data.Array.Basic", "Init.Data.Array.DecidableEq", "Init.Data.Nat.Bitwise.Basic",
            "Init.Data.Vector.Basic"]
# Core modules a proof module imports with `import all` only if it mentions
# their definition: `Nat.isPowerOfTwo`, which core states as `∃ k, n = 2 ^ k`
# but neither exposes nor gives a lemma to take apart.
CORE_ALL_FOR = {"Init.Data.Nat.Power2.Basic": "isPowerOfTwo"}

# Commands that add theorems (and definitions) to the file that runs them.
PROOF_CMD = re.compile(r"^(materialize_\w+|taint_summary)\b", re.M)


# Declarations of data (not `meta`): a file with one is meta code only if
# it imports `Lean` (a tactic's own state, as in `Framework/SigEval.lean`).
DATA = re.compile(r"^(@\[[^\]]*\]\s*)?((private|protected)\s+)?(structure|inductive|class|instance)\b", re.M)


def is_meta(text: str, imports: list[str]) -> bool:
    uses_lean = any(i == "Lean" or i.startswith("Lean.") for i in imports)
    return (META_DECL.search(text) is not None and THEOREM.search(text) is None
            and PROOF_CMD.search(text) is None and (uses_lean or DATA.search(text) is None))


def is_proof(path: str) -> bool:
    p = pathlib.PurePosixPath(path).as_posix()
    return "VerifiedGarbage/Proof/" in p and "VerifiedGarbage/Proof/Framework/" not in p


def convert(text: str, proof: bool = False, names: list[str] = EVAL_NAMES) -> str:
    lines = text.split("\n")
    if is_module(lines):
        return text
    i, n, lead = 0, len(lines), []
    # A leading comment (a copyright notice) stays before `module`.
    if lines and lines[0].startswith("/-") and not lines[0].startswith("/-!"):
        while i < n:
            lead.append(lines[i])
            i += 1
            if lines[i - 1].rstrip().endswith("-/"):
                break
    head = []
    while i < n and (IMPORT.match(lines[i]) or lines[i].strip() == "" or lines[i].startswith("--")):
        head.append(lines[i])
        i += 1
    imports = [IMPORT.match(l).group(1) for l in head if IMPORT.match(l)]
    meta = is_meta(text, imports)
    evals = not meta and evaluates(text, names)
    # Tactics next to definitions and theorems: their code needs Lean at
    # elaboration time too.
    mixed = not meta and (META_DECL.search(text) is not None or META_MARK.search(text) is not None)
    out = lead + ["module", ""]
    for l in head:
        m = IMPORT.match(l)
        if m:
            core = m.group(1) == "Lean" or m.group(1).startswith("Lean.")
            l = f"public {'meta ' if meta and core else ''}import {m.group(1)}"
            if meta and not core:
                l += f"\npublic meta import {m.group(1)}"
            if mixed and core:
                l += f"\npublic meta import {m.group(1)}"
            if evals:
                l += f"\nmeta import {m.group(1)}"
        out.append(l)
    while out and out[-1].strip() == "":
        out.pop()
    if proof and not meta:
        out += [f"import all {m}" for m in CORE_ALL]
        out += [f"import all {m}" for m, name in CORE_ALL_FOR.items() if name in text]
    out.append("")
    # The module's docstring stays right after the imports.
    if i < n and lines[i].startswith("/-!"):
        while i < n:
            out.append(lines[i])
            i += 1
            if lines[i - 1].rstrip().endswith("-/"):
                break
        out.append("")
    out.append("public meta section" if meta else "@[expose] public section")
    out.append("")
    while i < n and lines[i].strip() == "":
        i += 1
    out += lines[i:]
    return "\n".join(out)


PRIVATE_NEEDED = re.compile(
    r"^(?:error: )?(\S+\.lean):\d+:\d+: (?:error[^\n:]*: )?Unknown identifier `([^`]+)`\s*\n\s*\n?"
    r"Note: A private declaration `([^`]+)` \(from the current module\) exists", re.M)


def not_converted(lean: pathlib.Path, dirs: list[str]) -> list[tuple[str, pathlib.Path]]:
    """The (directory, file) pairs of the files under `lean`'s directories
    `dirs` that are not modules."""
    found = []
    for d in dirs:
        files = (lean / d[:-2]).glob("*.lean") if d.endswith("/*") else (lean / d).rglob("*.lean")
        found += [(d.removesuffix("/*"), f) for f in sorted(files) if not is_module(f.read_text().split("\n"))]
    return found


ANY_IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)\s*$", re.M)


def non_module_imports(lean: pathlib.Path) -> list[tuple[pathlib.Path, str]]:
    """The (file, import) pairs of the modules under `lean/VerifiedGarbage`
    that import a file of this project that is not a module (which Lean
    refuses)."""
    found = []
    for f in sorted((lean / "VerifiedGarbage").rglob("*.lean")):
        text = f.read_text()
        if not is_module(text.split("\n")):
            continue
        for m in ANY_IMPORT.finditer(text):
            dep = lean / (m.group(1).replace(".", "/") + ".lean")
            if dep.exists() and not is_module(dep.read_text().split("\n")):
                found.append((f, m.group(1)))
    return found


def needs_public(log: str) -> list[tuple[str, str]]:
    """The (file, declaration) pairs of private declarations a build log
    shows exposed declarations referring to."""
    return sorted({(m.group(1), m.group(3)) for m in PRIVATE_NEEDED.finditer(log)})


def main(args: list[str]) -> int:
    if args == ["check-converted"]:
        bad = not_converted(LEAN, CONVERTED)
        for d, f in bad:
            print(f"{f.relative_to(LEAN.parent)}: not a module, but lean/{d} is converted to modules; "
                  f"run `python3 ci/modularize.py lean/{d}`", file=sys.stderr)
        imports = non_module_imports(LEAN)
        for f, dep in imports:
            print(f"{f.relative_to(LEAN.parent)}: a module, but imports `{dep}`, which is not", file=sys.stderr)
        return 1 if bad or imports else 0
    if len(args) == 2 and args[0] == "check":
        log = sys.stdin.read() if args[1] == "-" else pathlib.Path(args[1]).read_text()
        found = needs_public(log)
        for f, name in found:
            print(f"{f}: private `{name}` is referred to by an exposed declaration", file=sys.stderr)
        return 1 if found else 0
    if not args:
        print(__doc__, file=sys.stderr)
        return 2
    files = []
    for a in args:
        p = pathlib.Path(a)
        files += sorted(p.rglob("*.lean")) if p.is_dir() else [p]
    names = evaluating_names(LEAN)
    changed = 0
    for f in files:
        text = f.read_text()
        new = convert(text, is_proof(str(f)), names)
        if new != text:
            f.write_text(new)
            changed += 1
    print(f"{changed} of {len(files)} files converted", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
