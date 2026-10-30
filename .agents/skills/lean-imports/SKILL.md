---
name: lean-imports
description: "Use when running or acting on ci/check_lean_public_imports.py or ci/trim_lean_imports.py, adding `-- shake: keep`, or narrowing the imports of many Lean modules at once."
---

# Checking and trimming Lean imports

Before pushing, after building the modules you edited, run
`ci/check_lean_public_imports.py` on them (see "Checks to run before
pushing" in `AGENTS.md`; CI does not run it, since `lake shake`
alone takes most of a minute): it names each `public import` you added of
a module of the project that the file uses only privately, with the
modules importing it that used what it passed on (they must import that
themselves), and each import you added that the file does not use at all;
`--fix` makes those changes, after which build and run it again. It counts
as public what Lean does: statements, and the bodies of exposed
definitions with the proofs inside them (a structure value's proof
fields), which `lake shake` alone counts as private. It never asks to
make private or remove a module whose effect no declaration records (an
`attribute [...]`, a `macro_rules`, a `seal`, an instance priority, a
`materialize_*` literal: its `SIDE_EFFECTS`), nor a dependency's, and when
making an import private would stop passing such a module on, it names
the `public import`s that keep doing so. With `--dependencies Mathlib`
(both scripts) it also removes the imports of Mathlib's modules that
shake finds unused, adding a narrower Mathlib module where shake names
one; `--fix` keeps each only if the module and everything importing it
still build. Mark an import that must stay as
it is for another reason `-- shake: keep`, saying why. Shake does not see
uses that leave nothing in the `.olean` (an `open` of a namespace, what
`#guard`, `materialize_*` or `taint_decide` evaluate): import what those
need directly. For a change the check does not cover (more than 3,000
modules, a refactor of many headers) or a sweep of the library,
`ci/trim_lean_imports.py` (`-m`, `--base REV` or `--all`) does the same
for every import of those modules, in rounds until nothing is left: it
never edits registrations or variants, keeps what it found by Lake's hash
of each module's build, and avoids retrying unchanged rejected trials
(`lean/.lake/trim-imports.json`); relevant context changes or
`--retry-rejected` reopen them. For fast iteration, use `--capture` once
and `--replay` while changing Python planning logic, then verify a small
scope with `--max-affected` and `--verify-batch`. Replays remain unverified;
changing the Lean reader requires a fresh capture. `--discover --no-shake`
generates independent hypotheses without shake. `--batch` bounds shake's
memory (about 3 GB per 1,000 modules), and `--read-batch` separately bounds
declaration-reader roots. See [Iterating on import narrowing](../../../lean/README.md#iterating-on-import-narrowing)
and [the evidence and verification guide](../../../ci/IMPORT_NARROWING.md).
