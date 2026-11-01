---
name: lean-modules
description: "Use before adding a Lean file or module, or changing imports; when running or acting on ci/check_lean_public_imports.py, ci/check_lean_single_importer.py or ci/trim_lean_imports.py, or adding `-- shake: keep`; or when writing a Lean file that is not a module, or about the audit records: why the rules of CLAUDE.md's \"Lean modules\" hold, and the tools that check them."
---

# Lean modules

The rules are in "Lean modules" in `AGENTS.md`; this is why they hold, and
how the tools that check them work.

## A new module costs CI time

Add a proof to the module that uses it, not to a new module of its own.
Every module is a `lean` process that first imports its whole closure,
about a second of CI's time, more than many modules' own work; the
per-declaration limits (`maxHeartbeats`, "Keeping proofs fast") apply to
declarations, not files, so splitting a file never helps them. A new proof
module is for code that several modules import, or for proofs that cost
more than their imports (`ci/lean_profile.py`), which a separate module
spares from re-checking when its importer changes. A module that only
one other proof module imports says why in a line
`-- separate module: <why>`; `ci/check_lean_single_importer.py` fails a
change that adds one without it (the modules of `Proof/Framework/` and
`Proof/Variants/`, `*Lit` and `Instances` modules, `meta` files and
those that `materialize_*` or `taint_summary` are exempt).

## Public and private imports

`public import` only what the file's statements and definitions mention
(importers see it too); a plain `import` gives the file something for its
proofs only, and importers do not see it. `@[expose] public section`
keeps every definition unfoldable by importers, as the proofs need.
Import privately whatever only proofs use: it is what keeps builds short.
Lake rebuilds a module when a module it reads changes its `.olean`, and a
module reads its imports and what they `public import`, transitively
(`ci/lean_shards.py`'s `reads`). A change to a lemma's statement rebuilds
the modules importing it, but those that import it privately produce the
`.olean` they did, and nothing beyond them rebuilds; through a
`public import` it rebuilds everything above it. (A change to a proof
alone changes no `.olean` but its own module's private part, and rebuilds
nothing else.) So import what a file uses directly, not through another
module that happens to pass it on.

## Checking and trimming imports

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

## Files that are not modules, and the audit records

Every file under `VerifiedGarbage/` and `VerifiedGarbageTest/` is a module
(`ci/check_lean_modules.py`); only Lake's scripts (`Emit.lean`,
`EmitOne.lean`) and the check of the audit's base
(`VerifiedGarbageAuditBase.lean`) are not.

A module sees the theorems it imports as axioms, without their proofs, so
the audits (`#assert_standard_axioms`, `#assert_no_compiler_overrides`,
`#assert_spec_origin`) do not read proofs: they read the records each module
of this project writes into its `.olean` when it is built
(`TCB/AuditRecords.lean`, which every library loads as a plugin): the axioms
and compiler overrides each of its constants depends on, and the `VG.Spec`
names, `initialize` and `csimp` declarations it declares. A module built
without the plugin has no records, and the audits reject what depends on
it. For Lean's and Mathlib's constants they read `TCB/AuditBase.lean`,
which `ci/audit_base.py generate` writes after a toolchain or Mathlib
update. So the emitter's drivers are modules too, which never read the
private part (`.olean.private`) of this project's modules, and CI restores
its build cache with those parts empty (`ci/lean_cache.py restore
--empty-private`). A local `ci/lean_cache.py unpack` writes them in full,
which the files in `lean/` that are not modules (`CheckLitImports.lean`,
`Check*.lean`, `Generate*.lean`) need.
