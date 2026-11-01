# Guidance for agents working on this repository

This library is written entirely by LLMs, so these rules are what keep it
trustworthy. Read `lean/README.md` first.

For a fast Lean bootstrap on Linux x86-64, restore the prebuilt GHCR cache
before compiling proofs; see [Restoring the CI build cache](lean/README.md#restoring-the-ci-build-cache).
The README streams it straight from the registry API with
`ci/fetch_lean_cache.py`, which resumes a dropped connection, into
`ci/lean_cache.py unpack`, which unpacks its per-module archives with the
toolchain's `leantar` (install the toolchain first); it needs `zstd` to
decompress the stream; without the command, `pip install zstandard` and use
the README's Python one-liner.
Restoring takes the whole cache (about 1 GB to download, 13 GB unpacked),
since optimizing a proof means rebuilding it.

After every rebase onto `main` (or pull of it), check how much Lean
changed upstream before building. Lake rebuilds each changed module and
everything that imports it, so a large merge can cost far more locally than
restoring the cache again. Before rebasing, note the old base
(`old=$(git merge-base HEAD origin/main)`), then after it list what `main`
changed under `lean/`:

```sh
git diff --name-only "$old" origin/main -- lean/ | grep -c '\.lean$'
git diff --name-only "$old" origin/main -- lean/lean-toolchain lean/lakefile.toml lean/lake-manifest.json
```

Restore the latest cache again unless the rebuild is clearly small. It is
not small when the second command prints anything (a toolchain,
dependency or lakefile change rebuilds every module), when upstream touched
`TCB/`, `Spec/` or `Proof/Framework/` (thousands of modules import them), or
when more than a handful of modules changed. A rebuild is only cheaper for a
few leaf modules (registrations, a proof nothing else imports), or a
handful that few others import. Restoring costs one download (about 1 GB); rebuilding a
shared module often costs much longer. `fetch_lean_cache.py` prints the
cached build's revision: if it does not yet include the merged change (its
CI is still running), wait for `main`'s cache rather than building. Your
own changes are rebuilt either way, on top of the restored build.

## Hard rules

* **All assembly comes from Lean.** Never write `asm!`, `naked_asm!`,
  `global_asm!`, naked functions, `extern` blocks or a `build.rs` by hand, and
  never edit the generated crates, `crates/verified-garbage-asm-<target>/`,
  by hand. Add an entry to a registration file,
  `lean/VerifiedGarbage/Artifacts/<Alg>/<Target>.lean`, and run
  `lake env lean --run Emit.lean` in `lean/`, which writes each crate's
  `src/` (whose printer emits each straight-line instruction as its machine
  code, `TCB/<ISA>/Encode.lean`, but ARM's, whose one crate serves both A32
  and Thumb, as text), and its assembly file, the text of that code,
  `assembly/<module>.s`, which is not compiled: read the code there.
* **No unverified shortcuts in proofs.** No `sorry`, `admit`, `native_decide`,
  `bv_decide` or new `axiom`s in anything an artifact depends on.
  `lake build` and the emitter enforce this (warnings are errors, and
  `#assert_standard_axioms` audits every artifact); never work around it.
* **Changes to `lean/VerifiedGarbage/TCB/` or `Spec/` are trust changes.**
  Keep them minimal, call them out explicitly in the PR description, and
  justify each ISA semantics change by citing the vendor manual (e.g. Intel SDM
  pseudocode). Never weaken a model, contract or `Verified` to make a proof go
  through: fix the proof or the code. An instruction outside the target's
  baseline ISA must list the CPU features it needs in the model's
  `requires`, citing the manual (the SDM's "CPUID Feature Flag", the Arm
  ARM's `FEAT_*`).
* **One kind of change per PR.** New specs (`Spec/`), additions to the TCB
  (`TCB/`), and new implementations (`Impl/` + `Proof/` + the registration
  file) must never be in the same PR. Trusted changes get reviewed on their
  own, and an implementation is only ever proven against a spec and TCB that
  have already been reviewed and merged.
* **100% test coverage.** CI merges the line coverage of the Rust code
  (`src/` and `tests/`) from every platform and fails below 100%, and each
  architecture's jobs alone must cover every line that architecture builds
  (`ci/merge_rust_coverage.py`). Add tests or delete dead code; only exclude
  lines that genuinely cannot run, between `// NO-COVERAGE-START` and
  `// NO-COVERAGE-END`, with a comment saying why. A branch that only one
  pointer width or architecture takes is a `cfg`, not a test at run time,
  and a test helper only some architectures call is built only for them.
  A pull request starts the Rust jobs (`ci/rust_matrix.toml`) of only the
  architectures its changes reach (`ci/rust_arches.py`: an architecture's
  crate of generated code, `crates/verified-garbage-asm-<target>/`, or shared
  code for all), and checks their coverage;
  the merge queue always runs every job.
* **Known-answer tests need clear provenance.** Never type test vectors into
  a test. Use Wycheproof (`tests/wycheproof/`), or vendor the published
  files byte for byte into a directory under `vectors/`, with a new
  `vectors/sources/<name>.toml` for that directory saying where they came
  from (`ci/check_vectors.py` checks it), and read them from there.
* **Every public API has a benchmark** in `bench/benches/primitives/`,
  next to OpenSSL's equivalent, and aws-lc-rs's if it has one. The
  Benchmarks workflow runs only by hand, never on pull requests: a change
  that could make code slower, or claims to make it faster, is measured by
  a manual run scoped to what it changed (the `benchmarking` skill),
  and its pull request links the run. Its runners are the ones CI waits
  for: never run every benchmark unless the change truly needs it, never
  run one for a change that cannot affect speed, and never rerun one to
  get a better number.
* **An optimized implementation reaches everything built on it.** An
  implementation of a function for CPU features (or, where no feature
  tells apart the CPUs it is faster on, for a compilation target; see
  below) is a *variant*: named `<function>_<suffix>` (`_shani`, `_avx2`),
  with the same signature and contract. Every function that calls a
  function with variants is generic over them (step 4 of the
  `adding-a-primitive` skill), so a new variant is emitted for its callers
  too, and their callers, without anyone listing it. The Rust code that
  chooses among implementations matches exhaustively on the primitive's
  backend enum (`streaming_hash!`'s, which `streaming_hmac!` and `whole_pbkdf2!`
  follow; `chacha20::Backend`, which ChaCha20-Poly1305 follows; a caller of
  several, like Argon2, matches on each of their enums together): a new
  backend does not compile until everything built on it handles it.
  `ci/check_variants.py` checks the generated code for this (the
  `adding-a-primitive` skill says what it checks). There are no
  exceptions: never add a caller that calls only the baseline
  implementation, or a way to excuse one.
  A variant is chosen by the CPU's features; only when no feature tells
  apart the CPUs it is faster on may the choice also depend on the
  compilation target (`vg_poly1305_update_neon`, faster on Apple's cores and
  slower on Neoverse N2, is chosen for `target_vendor = "apple"`). Then the
  choice is a function of the features and that `cfg!`, unit-tested both
  ways, and the tests force the variant on every target that can run it, so
  every CI runner of the architecture tests it.
* **Keep the README's algorithm tables current.** The tables in the
  [Algorithms](README.md#algorithms) section of `README.md`, one per family
  (hashes, MACs, AEADs, …), are generated by
  `python3 ci/algorithms_table.py` (CI fails if they are stale); never edit
  them by hand. A PR that lands a spec adds `docs/algorithms/<alg>.toml`,
  with its `family`; any PR that adds or removes support for an algorithm
  on an architecture, or adds or removes a variant, reruns the script in
  the same PR (and after merging main, rather than resolving a conflict in
  the table by hand). A cell names only what the code states, the CPU
  features of the algorithm's variants (and a variant that needs none, by
  its suffix): never describe an implementation's techniques there, or
  anywhere else that is not its code and proofs.
* The emitter runs compiled code, so it must be what the kernel checked:
  nothing the artifacts or the emitter use may carry `implemented_by`,
  `extern` or `export`, and nothing in `lean/VerifiedGarbage/` may declare a
  `csimp` theorem or an `initialize` (but `TCB/AuditRecords.lean`, which
  registers the audit records). Only `Spec/` declares definitions in
  the namespace `VG.Spec`. The emitter refuses both (`TCB/Audit.lean`),
  from the records every module writes when it is built (the
  `lean-modules` skill): never build a module without the lakefile's
  `plugins`, or edit `TCB/AuditBase.lean` but with `ci/audit_base.py`.
* Never add instructions with operand-dependent timing (e.g. `div`) to an ISA
  model.
* On x86-64, `pmuludq`, `pmullw`, `pmulhw`, `pmaddwd`, `pmulhrsw`, their VEX
  forms, `vpmadd52luq` and `vpmadd52huq` may only take secret operands
  between Intel's MXCSR prologue and epilogue (`stmxcsr`, `ldmxcsr` of
  `0x1FBF`, `lfence`, … `lfence`, `ldmxcsr` of the saved value), which the
  proofs do not check: see "MCDT" in
  `lean/VerifiedGarbage/TCB/X86_64/Isa.lean`. `ci/check_mcdt.py` checks the
  generated code instead: every instruction on Intel's MCDT list must be
  inside that exact sequence in its function, entered only through the
  prologue.
* `TCB/` holds definitions only and imports only Lean core; lemmas go in
  `Proof/`. `Spec/` and `Impl/` never import `Proof/`.
  `ci/check_lean_imports.py` checks both.

## Skills

Guidance for particular tasks is in skills, `.agents/skills/<name>/SKILL.md`
(`.claude/skills` links to the same directory). Before starting one of these
tasks, read its skill, whether or not your tool loads it for you:

* `adding-a-primitive`: before adding a primitive, a new target for one, a
  CPU-feature variant, or a file under `Artifacts/`, `Generic/` or
  `Variants/`.
* `proof-performance`: before writing or editing a proof, or when one is
  slow. The rules in "Keeping proofs fast" below are its summary: change
  the two together.
* `lean-profiling`: before making proofs or the CI Lean build faster, or
  measuring such a change.
* `lean-modules`: before adding a Lean module or changing imports, when
  `ci/check_lean_public_imports.py` reports something, before narrowing the
  imports of many modules (`ci/trim_lean_imports.py`), or before writing a
  Lean file that is not a module, or about the audit records.
* `benchmarking`: before measuring a change's speed, locally or with the
  Benchmarks workflow.
* `cpu-feature-tests`: before changing what CPU features choose, its tests,
  `ci/rust_matrix.toml` or the groups in `ci/cpu_tests.py`.
* `ci-metrics`: when asked to check or analyze CI.

Each skill is a section that used to be in this file; keep its text there,
not here, and keep this list in step with `.agents/skills/`
(`ci/check_skills.py` checks it). A skill's frontmatter has only `name`
and `description`, which every tool reads, and its links are relative to
its own file.

## Adding a primitive

This takes at least two PRs (see "One kind of change per PR"): the spec
(`Spec/<Alg>.lean` and `Spec/<Alg>/Contract.lean`) alone, then the
implementation, its proof, its registration, the regenerated crates,
the Rust API, its tests and its benchmark together. Only what the Rust code
calls has a spec: a function only verified code calls is emitted as an
internal function, with no `Api` and its contract in `Proof/`. Any TCB additions the
primitive needs (e.g. new instructions in an ISA model) go in their own PR
before either. Registration files (`Artifacts/`, `Generic/`) and variant
files (`Variants/`) are reviewed by hand, so they only bind
(`ci/check_registrations.py` checks it). The `adding-a-primitive` skill has
the steps.

## Keeping parallel PRs from conflicting

Many PRs are in flight at once, so adding an algorithm or an architecture
should add files, not edit lists that every other PR edits too.

* A Rust module states the architectures it supports in its own file, as an
  inner `#![cfg(...)]` after its `//!` docs; the parent only says
  `mod <name>;`. Supporting another architecture changes that one line of
  the algorithm's own file.
  Tests and benchmarks are gated on exactly the architectures of the
  library modules they use (`ci/check_arch_gates.py` checks it), so update
  their `cfg`s with the module's.
* Import the verified functions from `crate::arch::<module>` (the target's
  crate of generated code, `verified_garbage_asm_<target>::<module>`,
  `src/lib.rs`), once for every
  architecture, not with a `use` per architecture; only functions a target
  alone has (e.g. an x86-64 `_shani` variant) take a `#[cfg(target_arch)]`.
* Tests of one algorithm go in a file of their own (`tests/cavp/<alg>.rs`,
  `tests/wycheproof/<alg>.rs`), declared with one `mod` line. Every test
  directory is a module of the one test binary, `tests/main.rs`: a new one
  adds its `#[path = "<dir>/main.rs"] mod <dir>;` line there
  (`ci/check_arch_gates.py` fails a directory without it, which would
  never run).
* A construction over many hash functions (HMAC, PBKDF2) gets a file per
  hash everywhere: its `Api`s' `module` is `<family>_<hash>` (so
  `crates/verified-garbage-asm-<target>/src/hmac_sha256.rs`), its registration files are
  `Artifacts/<Family><Hash>/<Target>.lean`, its Rust implementation is
  `src/<family>/<hash>.rs` (the generic code stays in `src/<family>/mod.rs`),
  and its tests, benchmarks and `docs/algorithms/` row are
  `<family>_<hash>.rs` and `<family>-<hash>.toml`.

## Lean modules

Every file under `lean/VerifiedGarbage/` is a module of Lean's module
system; `python3 ci/check_lean_modules.py` checks it. Write a new file's header by hand:

```lean
/- Copyright notice, if any. -/
module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Md5

/-! # What the file is -/

@[expose] public section

namespace VG.Proof.Md5.X86_64
…
```

* Add a proof to the module that uses it, not to a new module of its own:
  every module costs CI about a second before its own work, and splitting
  a file never helps the per-declaration limits. A module that only one
  other proof module imports says why in a line `-- separate module: <why>`
  (`ci/check_lean_single_importer.py`).
* `public import` only what the file's statements and definitions mention,
  and import privately whatever only its proofs use, so that a change
  rebuilds as few modules as it can; import what a file uses directly, not
  through another module that happens to pass it on. `@[expose] public
  section` keeps every definition unfoldable by importers, as the proofs
  need. Before pushing, after building the modules you edited, run
  `ci/check_lean_public_imports.py` on them (see "Checks to run before
  pushing").
* A file that only defines tactics, elaborators or commands is a
  `public meta section`, and imports each module both ways
  (`public import X` and `public meta import X`; `Lean` only as
  `public meta import Lean`), so that its code runs at elaboration time in
  the files that use it. Mark `meta` the helpers a tactic runs, in a file
  that also has definitions or theorems.
* A file that evaluates code while it is elaborated (`#guard`, `#eval`,
  `run_cmd`, `materialize_*`, `taint_decide`, `taint_summary`) also has a
  `meta import` of each of its imports, so that what it evaluates is
  available to the compiler.
* Never `import all` a core module, but two, each only in a proof that
  needs it: `Init.Data.Nat.Bitwise.Basic` when the kernel evaluates `Nat`'s
  bitwise operations (bit vectors' `0#8`, `Mem.read`'s equations, a
  `taint_decide` over them) and fails with an "application type mismatch"
  or a failed `rfl` without it; `Init.Data.Nat.Power2.Basic` when the proof
  unfolds `Nat.isPowerOfTwo`. The kernel evaluates core's arrays and
  vectors without `import all`, which makes a module up to a quarter slower
  to build (`ci/check_lean_speed.py` checks it).
* In a structure instance, a field proven by a tactic inside a term
  (`ofSig := ⟨_, _, _, by …⟩`) is elaborated after the other fields, and
  a tactic run before its goal is known is stuck: write the field
  `by exact (…)`.
* `lake build` turns off Mathlib's style and tactic-analysis linters (the
  lakefile's `weak.` options), 5–8% of the build: never turn them back on
  in a module.
* An exposed definition may not refer to a private declaration of its file,
  and the auxiliary declarations of a theorem's proof are private to it:
  a lemma another file uses is a top-level theorem, not a `where` lemma.


## Stacking PRs

PRs are squash-merged, so once the PR below a stacked branch merges, never
`git rebase origin/main`: it replays the merged PR's commits onto their own
squash. Restack only the branch's own commits:

```sh
git fetch origin main +pull/<N>/head:stack-base   # <N>: the merged PR
git rebase --onto origin/main stack-base          # --update-refs for taller stacks
```

Keep stacks linear (never merge `main` into them) and their branches in this
repository, as GitHub's stacked PRs require. When a generated file conflicts,
take `main`'s side (`git checkout --ours`) and regenerate it after the rebase.

## Keeping proofs fast

Lean's kernel re-checks every proof term, and it is a slow evaluator: most
of the build time used to be the kernel, not tactics.

Every declaration must elaborate and pass the kernel within Lean's default
`maxHeartbeats` (200000; the largest proof needs about half of that). Never
`set_option maxHeartbeats`, `maxRecDepth` or another resource limit, in a
source file or the lakefile: a proof that hits the limit is too slow, so make
it faster.
`ci/check_lean_speed.py` enforces this, and the rules below that can be
checked without building.

The `proof-performance` skill explains each of these rules, with the
lemmas and tactics to use; read it before writing a proof:

* **Constant time:** `VG.Taint.constantTime … (by taint_decide)`, never
  `decide +kernel`. A callee that many callers share gets a taint summary
  (`taint_summary`, `Proof/Framework/TaintSum.lean`).
* **Symbolic execution:** step blocks with the ISA's `runBlock_cons`,
  `runStep_some` and `runBlock_nil`, never `simp [runBlock]`. Run each
  code shape once (generalize what differs rather than case-split), and
  compose short steps by induction (`WP.block_append_iff`) rather than
  running a long block in one `simp`.
* **Registers and frames:** never unfold `State.setReg` (`write`,
  `setFlags`, `setV`, …); read through writes, and prove frame facts, with
  the lemmas of `Proof/Framework/<ISA>/RegUpd.lean` given their arguments,
  never `rfl`.
* **What the kernel evaluates:** use `Nat` arithmetic (`RegSet`, not
  `List Reg`). Code, tables and values it evaluates get a literal
  (`materialize_code`, `materialize_table`, `materialize_value`), checked
  with `lit_decide` or `taint_decide`, never `decide +kernel`, and every
  module that evaluates the code imports its `Lit` module, registration
  files too (nothing checks this: `ci/lit_imports.py` ranks the misses
  that cost the build).
* **Arithmetic side conditions:** finite facts by one `decide` on the
  bounded statement, not `interval_cases`; nested `if`s with
  `↓ite_eq_left`/`↓ite_eq_right`; ranges at offsets with `VG.Offset`, not
  `bv_omega`; `omega_arith`/`omega_using` in a large context; `xs[i]'h` for
  a non-literal index; witnesses' regions by
  `Region.disjoint_of_sep (by decide)`.
* **Unfolding:** close goals about symbolic memory or hash values with
  explicit lemmas (`congrArg`, `rw`), not `rfl`, `congr 1` or
  `first | rfl | …`; never `rfl`, `decide` or `change` on a goal holding a
  large concrete value; rewrite tables' regions with
  `Abi.constRegions_cons`; evaluate a recursive definition that reuses a
  recursive result with a `dsimproc`; unfold a model's function on an
  instruction with its `dsimproc` (`reduceExec`, `Proof/Framework/<ISA>/Reduce.lean`),
  not by naming it in `simp`, which copies its `match`'s equation lemmas into
  every module.
* **Elaboration:** ascribe instruction-list literals next to `++`; use
  `with_reducible assumption`; import `Proof/Framework/PowLit.lean` for
  numeral exponents; prefer simprocs to `simp (config := {decide := true})`
  on expensive facts; put tactic modules that import only core in
  `NativeTactics`, and keep Mathlib's interpreted tactics (`tauto`) out of
  hot proofs.
* **Imports:** never `Mathlib.Tactic` or all of Mathlib; keep
  `IntervalCases`, `NormNum`, `Ring` and heavy algebra out of modules many
  others import; a module of one target never imports another target's,
  and a new file directly in `TCB/` is listed in `NativeTCB`
  (`ci/check_lean_imports.py`).

## Iterating on one proof

While developing, never run a bare `lake build` or the emitter: the default
targets are every module (over 8,000), and the emitter imports every
registration file. From `lean/`, build the module you're working on, which
builds only it and what it imports, and after that only what changed
(`--log-level=warning` leaves out the profile Lake replays for every module:
see the `lean-profiling` skill):

```sh
lake build --log-level=warning +VerifiedGarbage.Proof.Md5.X86_64.Compress
```

To check the artifact and regenerate its code, run `EmitOne.lean` on its
registration file: it builds only that file and what it imports, runs the
emitter's audits on its artifacts, and writes (or, with `--check`, compares)
only its files under `crates/`, in seconds once the proofs are built:

```sh
lake env lean --run EmitOne.lean Md5.X86_64
lake env lean --run EmitOne.lean --check Md5.X86_64
```

Name a generic group (`<Iface>.<Target>`, e.g. `Sha256Compress.AArch64`, or
`<Iface₁>.….<Ifaceₙ>.<Target>`, e.g. `Blake2b.Argon2Compress.X86_64`) to
emit its generic callers for each variant (or combination of variants). It
refuses a file that is new or that other registration files also emit into
(each table of constants has a file of its own, `consts/<name>.rs`, which it
writes like any other); the full emitter handles those, and the checks below
still run everything before pushing.

## Checks to run before pushing

Run every step of the `Static checks` job (`lean-imports` in
`.github/workflows/ci.yml`): they take seconds and need no build. Read the
list there, not a copy of it here; locally, give
`check_lean_single_importer.py` `--base origin/main` (CI compares the
merge commit with its first parent). Then, as a change needs them:

```sh
(cd lean && lake build --log-level=warning && lake env lean --run Emit.lean --check)
git diff --name-only origin/main -- lean/VerifiedGarbage | sed -n 's#^lean/\(.*\)\.lean$#\1#p' | tr / . \
  | xargs -r python3 ci/check_lean_public_imports.py --base origin/main -m   # after building them; --fix applies it
cargo fmt --check && cargo clippy --all-targets -- -D warnings
WYCHEPROOF_ROOT=/path/to/wycheproof cargo test
```

CI does not run `check_lean_public_imports.py`, which needs the edited
modules built: it is yours to run.

A primitive with implementations for different CPU features is tested (and
benchmarked) end to end in each configuration, never through a special API:
the `cpu-features-env` Cargo feature lets `VG_CPU_FEATURES` restrict the
features detected (see `src/cpu.rs`); the `cpu-feature-tests` skill says how
CI tests each configuration. To test the baseline ISA's implementations:

```sh
VG_CPU_FEATURES=none WYCHEPROOF_ROOT=/path/to/wycheproof cargo test --features cpu-features-env
```

Coverage on this platform (CI merges it across all of them; the merge needs
`pip install -r ci/requirements-coverage.txt`):

```sh
export RUSTFLAGS=-Cinstrument-coverage LLVM_PROFILE_FILE='.rust-cov/cov-%p-%m.profraw'
WYCHEPROOF_ROOT=/path/to/wycheproof cargo test
python3 ci/export_rust_coverage.py .rust-cov   # writes <arch>-<uuid>.lcov
python3 ci/merge_rust_coverage.py .            # reports; fails under 100%
```
