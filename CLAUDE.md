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

After rebasing a long-running session onto `main`, consider pulling and
restoring the latest cache again to avoid rebuilding upstream Lean changes.
Lake rebuilds your changes and anything not yet cached.

## Hard rules

* **All assembly comes from Lean.** Never write `asm!`, `naked_asm!`,
  `global_asm!`, naked functions, `extern` blocks or a `build.rs` by hand, and
  never edit `src/asm/` by hand. Add an entry to a registration file,
  `lean/VerifiedGarbage/Artifacts/<Alg>/<Target>.lean`, and run
  `lake env lean --run Emit.lean` in `lean/`.
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
  `src/asm/<target>/`, or shared code for all), and checks their coverage;
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
  a manual run scoped to what it changed (see "Measuring a change's
  speed"), and its pull request links the run.
* **An optimized implementation reaches everything built on it.** An
  implementation of a function for CPU features (or any other faster
  version) is a *variant*: named `<function>_<suffix>` (`_shani`, `_avx2`),
  with the same signature and contract. Every function that calls a
  function with variants is generic over them (step 4 of "Adding a
  primitive"), so a new variant is emitted for its callers too, and their
  callers, without anyone listing it. The Rust code that chooses among
  implementations matches exhaustively on the primitive's backend enum
  (`streaming_hash!`'s, which `streaming_hmac!` and `whole_pbkdf2!`
  follow; `chacha20::Backend`, which ChaCha20-Poly1305 follows; a caller of
  several, like Argon2, matches on each of their enums together): a new
  backend does not compile until everything built on it handles it.
  `ci/check_variants.py` checks the generated code: each caller of a
  function with a variant has that variant, which calls it or does its work
  itself but never calls the baseline (a helper needs none if its callers'
  variants all do its work themselves), some implementation of each caller
  calls every implementation of its callee whose features the caller has
  but the one it calls lacks (a variant chosen by hand, such as a field
  naming the callee, still follows the features), and each variant is used by the
  Rust code outside its tests (never emit one only a test calls). There are
  no exceptions: never add a caller that calls only the baseline
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
  on an architecture, or optimizes an implementation, reruns the script in
  the same PR (and after merging main, rather than resolving a conflict in
  the table by hand).
* The emitter runs compiled code, so it must be what the kernel checked:
  nothing the artifacts or the emitter use may carry `implemented_by`,
  `extern` or `export`, and nothing in `lean/VerifiedGarbage/` may declare a
  `csimp` theorem or an `initialize`. Only `Spec/` declares definitions in
  the namespace `VG.Spec`. The emitter refuses both (`TCB/Audit.lean`).
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

## Adding a primitive

This takes at least two PRs (see "One kind of change per PR"): step 1 alone,
then steps 2–5 together. Any TCB additions the primitive needs (e.g. new
instructions in an ISA model) go in their own PR before either.

1. `Spec/<Alg>.lean`: the algorithm, transcribed from the standard, with no
   target-specific imports; and `Spec/<Alg>/Contract.lean`: for each function,
   its Rust signature (`Sig`) and its `Contract` on every target, built with
   `Sig.contract` from a postcondition and any precondition the signature does
   not imply, and its `Api`: its Rust module (the file under
   `src/asm/<target>/`) and name, its signature, its contract on every target
   (`contracts := some fun A stack => fooContract A stack`, or
   `fun A _ => fooContract A` for a contract without `stack`), its
   contract's `writeArgs`, and its documentation: what it does, and the `# Safety` items but for what
   the emitter generates (what memory each buffer must be valid for:
   `Sig.validDoc`; which buffers may not overlap each other, the stack or
   the arguments on it, and that none wraps around the address space:
   `Sig.layoutDoc`). Choose
   `pub` honestly: only lengths and pointers are public unless the algorithm
   says otherwise.
2. `Impl/<Alg>/<Target>.lean`: the code.
3. `Proof/<Alg>/…`: the proof of `Verified`. A proof may be written against a
   simpler per-target contract of its own and moved to the shared one with
   `Verified.of_implies` (see `Proof/Framework/Contract.lean`).
4. An `Artifact` in the registration file `Artifacts/<Alg>/<Target>.lean`,
   which defines `VG.Artifacts.<Alg>.<Target>.artifacts` (a new file for a
   new algorithm or target; see `Artifacts/Selftest/X86_64.lean`; never
   `Artifacts.lean`, whose list is empty), made from the function's `Api`
   by `Api.artifact` (`TCB/Registration.lean`), with the file importing
   `Proof/Framework/Registration.lean` for its default proofs:

   ```lean
     Spec.<Alg>.fooApi.artifact X86_64.target {
       stack := 8
       code := Impl.<Alg>.X86_64.foo
       verified := Proof.<Alg>.X86_64.foo_verified },
   ```

   A registration states only what the implementation chooses: the Rust
   module, name, signature, `writeArgs`, documentation and contract come
   from the `Api`, so never restate them. Give a variant's name its
   `suffix` (`suffix := "_avx2"`), any notes on the implementation in
   `notes` (`notes := […]`), the stack its calls and frames use in `stack`,
   the tables of constants it reads in `consts`, and, where a caller wipes a
   writable array the function uses as working space, how much of it the
   function writes in `written` (`written := [("scratch", 1024)]`, proven by
   `writtenOk`), which the emitter exports as `<NAME>_<PARAM>_WRITTEN` for
   the caller to wipe only that much. Its contract is found
   from `verified`'s type, and must be the `Api`'s on the target for
   `consts` and `stack` (`ofApi`, by `rfl`): give `contract` only when
   `verified`'s type does not determine it. `of_sig` proves `ofSig`, and
   `sp_safe` proves `spSafe`: by `Code.all_of_forall` on ARMv7, AArch64 and
   PPC64LE,
   which evaluates nothing, and by `Code.all_of_allInstrs (by lit_decide)`
   on x86 and x86-64 (see "Code the kernel evaluates" below), falling back
   to `decide +kernel` where `lit_decide` exceeds the recursion limit, and
   for code that depends on a `Bool` or an enumeration (`adx`, a field
   variant), by cases on it. Never set
   `contracts` outside `Spec/` (the emitter refuses an artifact without
   them). If its code uses instructions outside
   the target's baseline ISA, list the CPU features they require in
   `features` (the emitter rejects anything but the exact set).
   A function that calls another one with several implementations (e.g.
   scalar and SHA-NI compression) is proven once for any of them and
   registered in `Generic/<Iface>/<Target>/<Alg>.lean`, which the emitter
   applies to every implementation in `Variants/<Iface>/<Target>/` (see
   `TCB/Emit.lean`), and so is a function that calls a generic caller
   (e.g. HMAC's `init`, calling SHA-256's `update`). A function that calls
   functions of several such interfaces is generic over all of them, in
   `Generic/<Iface₁>/…/<Ifaceₙ>/<Target>/<Alg>.lean`, whose `artifacts`
   takes a variant of each, in path order: the emitter applies it to every
   combination (e.g. Argon2's x86-64 derivation,
   `Generic/Blake2b/Argon2Compress/X86_64/Argon2.lean`, calling BLAKE2b's
   streaming functions and Argon2's `G`). Its instances are named by
   `Emit.qualifiedName`: the function's name, then a tag and the suffix of
   each interface whose variant is not the baseline, in path order
   (`vg_argon2_blake2b_avx2_g_avx512`; `vg_argon2` for the baseline),
   since variants of different interfaces may share a suffix; callers of one
   interface append the suffix alone. Never list the
   implementations in the caller: a new implementation is a new variant
   file, and its callers follow.
   Registration files (`Artifacts/`, `Generic/`) and variant files
   (`Variants/`) are reviewed by hand, so they only bind: no theorems, no
   tactic proofs beyond the defaults (not even a `(by decide)` argument),
   and no definitions but the artifacts, the variant and notes. A lemma
   whose side conditions a registration would decide takes them as
   `autoParam`s (`(hd : stackUse c ≤ 48 := by lit_decide)`), or the
   algorithm's proofs state the instance as a theorem
   (`Proof/Rsa/X86_64/Instances.lean`); `ci/check_registrations.py` checks
   it. Build a variant with its proofs under `Proof/`
   (`Proof/Variants/<Iface>/<Target>/<Name>.lean`, as the variant file's
   path) and bind it in the variant file
   (`def variant : … := Proof.Variants.<Iface>.<Target>.<Name>.variant`);
   put what a generic caller's artifacts are built from (instances of the
   functions it calls, lemmas about its code) in a module of the
   algorithm's proofs, as `Proof/AesGcm/X86_64/Instances.lean` does.
   A function whose proof takes a Weierstrass curve's group law (`Law`,
   `Proof/Weierstrass/Law.lean`) is registered generic over it the same
   way: the law is the one variant of the interface `<Curve>` on each target
   (`Variants/<Curve>/<Target>/Law.lean`, the only files that import the
   Mathlib algebra of its proof), and the registration file is
   `Generic/<Curve>/<Target>/<Alg>.lean` (`Generic/<Iface>/<Curve>/<Target>/`
   when it is generic over an implementation too). The law has no suffix.
5. Regenerate `src/asm/`, build the public Rust API on top of the primitive,
   and test it against the Wycheproof vectors in `tests/wycheproof/` (set
   `WYCHEPROOF_ROOT` to a checkout of C2SP/wycheproof). Benchmark the new
   API in `bench/benches/primitives/<alg>.rs`, next to the same operation in
   OpenSSL, at the sizes the others use.

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
  `crate::asm::<target>::<module>`, `src/lib.rs`), once for every
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
  `src/asm/<target>/hmac_sha256.rs`), its registration files are
  `Artifacts/<Family><Hash>/<Target>.lean`, its Rust implementation is
  `src/<family>/<hash>.rs` (the generic code stays in `src/<family>/mod.rs`),
  and its tests, benchmarks and `docs/algorithms/` row are
  `<family>_<hash>.rs` and `<family>-<hash>.toml`.

## Lean modules

Every file under `lean/VerifiedGarbage/` is a module of Lean's module
system, except `Artifacts.lean`; `python3 ci/check_lean_modules.py` checks
it. Write a new file's header by hand:

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

* `public import` only what the file's statements and definitions mention
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
  module that happens to pass it on. Before pushing, after building the
  modules you edited, run `ci/check_lean_public_imports.py` on them (see
  "Checks to run before pushing"; CI does not run it, since `lake shake`
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
  the `public import`s that keep doing so. Mark an import that must stay as
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
  declaration-reader roots. See [Iterating on import narrowing](lean/README.md#iterating-on-import-narrowing)
  and [the evidence and verification guide](ci/IMPORT_NARROWING.md).
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
* The audits (`#assert_standard_axioms`, `#assert_no_compiler_overrides`,
  `#assert_spec_origin`) run only in files that are not modules (the
  emitter's drivers, `Artifacts.lean`, `VerifiedGarbageTest/`), and refuse
  to run in a module: a module sees the theorems it imports as axioms,
  without their proofs. A file that is not a module sees every module's
  private imports too.
* In a structure instance, a field proven by a tactic inside a term
  (`ofSig := ⟨_, _, _, by …⟩`) is elaborated after the other fields, and
  a tactic run before its goal is known is stuck: write the field
  `by exact (…)`.
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

Avoid these patterns (each has cost tens of seconds in one proof):

* **Constant time:** use `VG.Taint.constantTime … (by taint_decide)`, never
  `decide +kernel` on a taint check: `taint_decide` precomputes loop
  invariants so the kernel does not search for them.
* **Symbolic execution:** step blocks with the ISA's `runBlock_cons`,
  `runStep_some` and `runBlock_nil` (`Proof/Framework/<ISA>/Exec.lean`), never
  `simp [runBlock]`, which runs the rest of the block from an unknown state
  after every instruction.
* **One symbolic execution per code shape:** don't case-split (e.g.
  `interval_cases` on a register rotation) and run the same block once per
  case; generalize what differs (see `round_ok` and `round_nodup`). Memory
  offsets generalize too: pass their bounds and separation from a lemma
  proved once (`round_sep`, x86), stating each pair in both orders, since
  `simp` won't match `a ∨ b` against `b ∨ a`.
* **Short symbolic executions:** don't run a long block of loads and stores
  in one `simp`; the states grow with every access. Prove one step for any
  index (`ld_ok k`, `upd_ok k`) and compose the steps by induction with
  `WP.block_append_iff`.
* **Kernel-evaluated data:** anything the kernel evaluates (a taint domain,
  a `decide +kernel` check) should use `Nat` arithmetic, which the kernel
  runs natively, not lists it searches element by element: sets of
  registers are `RegSet`s (`Proof/Framework/RegSet.lean`), not `List Reg`.
* **Finite facts:** prove a fact about a few small numbers with one `decide`
  on the bounded statement (`∀ j < 16, ∀ k < 16, wreg j = wreg k → j = k`),
  not `interval_cases j <;> interval_cases k <;> simp`. For a nested `if`
  on the same index on both sides, split the index into ranges once with
  `omega` and resolve each `if` with
  `simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]`, not `split_ifs`.
* **Nested `if`s under a discharger:** give `simp` the lemmas that resolve
  an `if` (`ite_eq_left`, `ite_eq_right`, a family's `ifp`/`ifn`) as
  pre-rewrites, `↓ite_eq_left`. Otherwise `simp` simplifies both branches of
  an `if` before the `if` itself, so its discharger (`omega`) runs, and
  usually fails twice, on the conditions of branches the outer `if` then
  discards; a failing `omega` is its slowest case (6–46% of a module's
  heartbeats in #2374). Lemmas that only rewrote inside those branches then
  show up as unused simp arguments: remove them.
* **Instruction lists under `++`:** in a theorem statement, ascribe each
  instruction-list literal next to `++`: `.block (absorb 1 ++
  ([.alu .add .esi (.imm 16)] : List Instr))`, not `absorb 1 ++ [.alu …]`.
  `++` elaborates its operands without an expected type, so every `.op`
  fails once and is elaborated again (up to seconds per statement).
* **Imports:** never import `Mathlib.Tactic` or all of Mathlib, which costs
  seconds in every module that (transitively) imports it: import the
  module of each tactic or lemma you use (e.g. `Mathlib.Tactic.IntervalCases`),
  and prefer core lemmas. The framework (`Proof/Framework/`) provides no
  Mathlib tactics, only Batteries' light ones (`by_contra`, `absurd`,
  `exacts`, `swap`, `<;> [t₁; t₂]`). `IntervalCases`, `NormNum`, `Ring` and
  `Mathlib.Data.List.*` each add about half a second to every module that
  imports them, even indirectly: keep them out of modules that many others
  import (a framework file, an algorithm's `Spec` or `Stream` lemmas).
  `ci/check_lean_speed.py` fails when a module importing heavy algebra
  (`HEAVY_MATHLIB`: `Ring`, `ZMod`, `NormNum`, `Linarith`, polynomials, …)
  is imported by more than 40 others; core `grind` proves the ring
  identities `ring` is used for.
* **Imports across targets:** a module of one target (a path with a
  directory of `TCB/`, e.g. `Proof/Sha256/Arm/…`) never imports a module of
  another target, even for a lemma that mentions no ISA: a change to one
  target (e.g. its ISA model) would then rebuild the other's proofs too, and
  a CI shard (`ci/lean_shards.py`), which builds a proof with everything it
  imports, would check both. Put what more than one target uses in
  a target-independent module (`Proof/<Alg>/…`, `Proof/Framework/…`);
  `ci/check_lean_imports.py` checks it.
* **Properties of every instruction:** prove `(instrs c).all p` with
  `rw [← Code.allInstrs_eq]; decide +kernel`, not `decide +kernel` directly.
* **Code the kernel evaluates:** code built by functions (unrolled
  compression functions, and the functions calling them) is rebuilt by the
  kernel in every check that evaluates it (constant time, `spSafe`, …), in
  every module. Give it a literal: `materialize_code foo`
  (`Proof/Framework/Lit.lean`), in a `Lit.lean` next to its proofs, defines
  `foo.lit` and checks `foo.lit_eq` once; then `taint_decide` and
  `lit_decide` (not `decide +kernel`) evaluate the literal, and the
  registration file's `spSafe := Code.all_of_allInstrs (by lit_decide)`.
  Functions that build code or tables (a register allocator, spec
  tables) get literals too: `materialize_table f n` (for `f : Nat → α`;
  `Nat`-valued tables are packed into one number, read by a shift),
  `materialize_value c` (any value with `ToExpr`). `materialize_code`,
  `lit_decide` and `taint_decide` unfold the definitions that lead to any
  constant with a literal and read it, so a generator runs once, in its own
  `lit_eq`, if every module that evaluates code using it imports the module
  with its literal (a literal module imports the literal modules of the
  code it contains). Materializing code checked only once does not pay.
* **Constant time of many callers of the same function:** prove the
  callee's taint once as a summary (`taint_summary`, `taint_decide_sum`,
  `Proof/Framework/TaintSum.lean`) rather than analysing its body in every
  caller's `taint_decide`; this needs a `Taint.Frame` instance for the ISA's
  taint domain (so far `AArch64.VectorTaint`, `Framework/AArch64/TaintMono.lean`).
  A summary pays when declarations or modules share it: within one
  `taint_decide`, the kernel already analyses identical code from the same
  taint once, so splitting one check into summaries makes it slower. Give a
  summary the smallest taint its callers need (public slots that are never
  read back as addresses cost the kernel at every store). Code that differs
  only in immediates (table selections) has the same taint: check one copy
  (`Proof/Framework/AArch64/TaintErase.lean`, `constantTime_eraseImm_of_eq`).
* **Tactics run compiled:** a module defining tactics, elaborators,
  simprocs or `MetaM` functions that imports only Lean core and precompiled
  modules goes in `NativeTactics` (lakefile); the interpreter runs it an
  order of magnitude slower in every module that uses it
  (`ci/check_lean_speed.py` checks it). Mathlib tactics run interpreted:
  keep `tauto` and similar out of hot proofs.
* **Register reads after writes:** in symbolic execution never unfold
  `State.setReg` (`write`, `setFlags`, `arithFlags`, `setV`): the registers
  become a function that `simp` re-simplifies under a binder at every
  instruction, quadratic in the block's length. Read through the writes
  with `Proof/Framework/<ISA>/RegUpd.lean`: `gpr_setReg` (an `if`, decided
  for literal registers) or `gpr_setReg_self` and `gpr_setReg_of_ne` (for
  variables), and `mem_setReg`, `gpr_setFlags`, … for the other fields.
  Keep writes folded throughout the block; expand the final state once only
  if the postcondition needs it. Preserve this behavior in shared symbolic
  execution tactics so every caller benefits.
* **Frame facts through writes:** prove `s'.mem = s.mem` (and the other
  fields a frame keeps) for a state `s'` built by writes with the `RegUpd`
  lemmas given their arguments, or `simp only [mem_setV, …]` (`upd_frame` on
  AArch64), never `rfl` or a `.trans` chain of the lemmas with `_`
  arguments: unification unfolds the writes into structure literals and
  first tries to unify the states (seconds for a few vector instructions).
  On AArch64, `Proof/Framework/AArch64/Seal.lean` makes `State.setV`
  irreducible for elaboration in the modules that import it, which rules
  this out; import it once a module's proofs no longer unfold `setV`.
* **Addresses at offsets:** don't prove that ranges at `p + BitVec.ofNat 64 d`
  are separate, disjoint or contained, or their distances, with `bv_omega`
  (a second or more each, and a large term for the kernel): use `VG.Offset`
  (`Proof/Framework/Offset.lean`: `sep`, `disjoint`, `sub`, `contains_base`,
  …), whose hypotheses are about the offsets alone, closed by `omega` or,
  for literals, `decide`. Its identities (`add_add`, `add_sub_cancel_left`,
  `ofNat_sub_ofNat`, `sub_sub_eq`, …) are in `AddrArith.lean`, which `Mem`
  imports. A local lemma for a family's own ranges is one application of
  one of these, never a proof of its own.
* **`omega` in a large context:** `omega` and `bv_omega` look at every
  hypothesis, a tenth of a second or more each call in a long proof about
  states. Clear what they cannot use: `omega_arith`, `bv_omega_arith`
  (arithmetic hypotheses only) or `omega_using [h₁, …]`,
  `bv_omega_using [h₁, …]` (those facts only), `Proof/Framework/Omega.lean`.
* **Index bounds:** `xs[i]` proves `i < xs.length` with `get_elem_tactic`,
  whose core rules rewrite every hypothesis and run `omega`.
  `Proof/Framework/GetElem.lean` (which `Mem` imports) tries `decide`
  first, for literal indices; for any other index give the bound, `xs[i]'h`.
* **Satisfiability witnesses:** the regions of a concrete witness state are
  disjoint by `Region.disjoint_of_sep (by decide)`, not `bv_omega`.
* **`decide := true` in `simp`:** `simp (config := {decide := true})` runs
  `decide` on every closed proposition it visits: cheap for small facts
  (register equalities, small `Nat` comparisons, where simprocs measured
  slower), seconds per block when those facts evaluate expensive
  definitions. There, reduce them with simprocs (`reduceCtorEq`,
  `↓reduceIte`, `Nat.reduceLT`, `Nat.reduceEqDiff`, `and_self`, …) or
  discharge side conditions with `(disch := decide)`. Measure both;
  `ci/check_lean_speed.py` counts the uses per file
  (`ci/lean_speed_allowed.py`). `set_option simprocs false` turns off every
  simproc, even those listed in `simp only [...]`.
* **`assumption` among facts about states:** `assumption` tries every
  hypothesis at default transparency, unfolding states and registers before
  each failed match; use `with_reducible assumption`, or name the hypothesis
  (`ci/check_lean_speed.py` rejects a bare `assumption` after `<;>` or in
  `first`).
* **Numeral exponents:** `2 ^ 64` elaborates in time quadratic in the number
  of numeral exponents in a statement; `Proof/Framework/PowLit.lean`'s macro
  elaborates it as `2 ^ (64 : Nat)` (the same term). A module with numeral
  exponents imports it, directly or through `Framework/GetElem.lean`
  (`ci/check_lean_speed.py` checks it).
* **Failing unfolding:** `rfl`, `trivial`, `congr 1`, `exact` and `simpa` on
  goals about symbolic memory or hash values can unfold definitions (down
  to `BitVec` internals) for seconds before failing or succeeding. Close
  such goals with explicit lemmas (`congrArg`, `rw`), and try the tactic
  that works first rather than in `first | rfl | …`. For example, on
  `compress H (blockAt m p) = compress H (parseBlock f)` or
  `bytesAt m p n ++ [0x80] = xs ++ [0x80]`, use
  `refine congrArg (compress _) ?_` or `refine congrArg (· ++ [0x80]) ?_`,
  not `congr 1`, which first tries to unify both sides. A lemma proved
  `:= rfl` is one `simp` uses by definitional unfolding, which the kernel
  then repeats; where a profile shows that (e.g. `exec` of an instruction,
  `Proof/Blake2/X86_64/Avx/Round.lean`), prove it `:= (rfl)`. Keep the
  framework's `RegUpd` lemmas `rfl`: as propositional rewrites they measured
  slower.
* **Concrete data under `rfl`:** never close a goal holding a large concrete
  value (a key schedule read from memory, a table) by `rfl`, `decide` or
  `change`, nor split a case on an index (`rcases … with rfl | rfl`) in a
  context that holds one: the kernel may evaluate the value to compare the
  two sides (Blowfish's `step_run`: a minute in the kernel, after an
  unrelated upgrade of Lean). Prove the step once with the value a
  variable, and apply it (`fAcc_step`, `Proof/Blowfish/F.lean`), or
  `generalize` the value before `rfl`.
* **Tables of constants:** the kernel evaluates a table's whole length
  (seconds for a comb's tables) when it compares `8 * words.length` with
  another form of it, such as a `Region`'s `len` projection. Never unfold
  `Abi.constRegions` with `List.map_cons` or substitute a table's region
  into a goal: rewrite with `Abi.constRegions_cons`, `Abi.constRegions_nil`
  and `Sig.forall_mem_const_single` (`Proof/Framework/Sig.lean`, which
  `sig_pre` already uses), before `List.forall_mem_cons` or `forall_eq` can
  take the region apart. A definition the kernel unfolds (a witness's
  memory) states a table's size as a literal, not as `8 * words.length`. A
  table's shape (`<curve>Comb7_length`, `_rows`) is proven once, in
  `Proof/<Curve>/Comb7Shape.lean`, not by `decide` on each target.
* **Code without its literal:** `lit_decide` and `taint_decide` read the
  literal of code only if the module imports the module that materializes
  it, or a module that `public import`s it; otherwise the kernel builds the
  code again (seconds for unrolled code). Import the code's `Lit` module
  wherever its code is evaluated: registration files too, whose default
  `sp_safe` evaluates their code. `decide +kernel` reads no literal at all:
  use `lit_decide`. `python3 ci/check_lit_imports.py` lists the checks that
  evaluate code without a literal they could import (see "Finding what to
  optimize").
* **Unfolding recursive definitions:** `simp`/`dsimp` unfolding a recursive
  definition that uses a recursive call's result twice (`let r := f …;
  (… r.1, r.2)`) duplicates the call at every level. Evaluate it in one
  step with a `dsimproc` instead (`Arm.reduceClassify`,
  `Proof/Framework/Arm/Contract.lean`).

### Finding what to optimize

Start from the build's own profile, not from a profiling build. Every
module is built with Lean's `profiler` on (`moreLeanArgs` in
`lean/lakefile.toml`): each step over a millisecond is recorded, at its
declaration, in the module's `.trace`, which the CI build cache ships. After
restoring the cache (`lean/README.md`), from the repository root:

```sh
python3 ci/lean_profile.py                        # the 30 costliest declarations
python3 ci/lean_profile.py --sort kernel          # by kernel time alone
python3 ci/lean_profile.py --by module --top 50   # the costliest modules
python3 ci/lean_profile.py --module VerifiedGarbage.Proof.Sha256 --json
python3 ci/lean_profile.py --tests                # with the known-answer tests
python3 ci/check_lit_imports.py                   # checks evaluating code without its literal
python3 ci/lean_closure.py rank                   # modules by what CI spends building them
python3 ci/lean_closure.py rank --by decl         # declarations, likewise
```

A proof's own time is not what CI spends on it: a module that the shards
of a full rebuild share is built by each of them, and one that many changes
reach is rebuilt by each run. `rank` weighs each module's (or declaration's)
time by the times CI builds it per commit, replaying the last 200 commits
of `main` through CI's plan (`--commits`), with its builds in a full
rebuild beside it (two minutes; no builds): prefer its top rows to
`lean_profile.py`'s when choosing what to make faster.

A command that generates declarations (`materialize_code`, `taint_summary`,
`run_cmd`) has no declaration range: its row is its line and the start of
that line of the source, `[line 70] taint_summary winBuildSum : …`. The
known-answer tests in `VerifiedGarbageTest`, which cost spec evaluation
rather than proofs, are left out unless `--tests` (or `--module` naming
them) is given.

Each declaration's time is `kernel` (the kernel checking it: large proof
terms, `decide +kernel`, `taint_decide`, `lit_decide`) and `elab`
(everything else: tactics, `simp`, `omega`, instances, compilation), which
point at different patterns above (kernel: literals, taint summaries,
`Nat` data; elaboration: symbolic execution, `omega`, unfolding). `blocked`
is time its task waited for another, such as the kernel checking a lemma it
uses: look at that lemma, not at the declaration. The times are wall-clock
times of one CI build, good for ranking. Pick targets from them, then study
a declaration with the per-file profiles below, and measure a change by
instructions or heartbeats, as below, never by this table. Modules you
rebuild locally record your machine's times in place of CI's.

What a module costs CI depends on its imports too: each shard
(`ci/lean_shards.py`) builds its sinks' whole import closures, so a module
two shards need is built twice. `ci/lean_closure.py` shows where (after
`python3 ci/ci_metrics.py fetch .ci-metrics 30`, and `profile` once the cache
is restored): `sinks` ranks the sinks by closure time, `dominators SINK`
gives the time each module brings into SINK's closure alone, and `score`
replays CI's plan of a full rebuild and of the recent runs with the imports
of `origin/main` and of the working tree (or `--drop A:B`; `--merge NEW=A,B`
for merged modules; `--profile-branch`, after building the branch, for
proofs it makes faster). Judge an import
cut by `score`, not by a closure's size: a subtree a sink drags in is often
built in its shard anyway, and the greedy plan moves by a few seconds with
any change.

Lake replays a module's recorded messages, the profile included, whenever
it finds the module built: build with `lake build --log-level=warning` (or
`-q`), as every command here does, to see only warnings and errors. A
module with `#guard_msgs`, which would compare the profile of its command
with the expected messages, turns the profiler off
(`set_option profiler false`; `ci/check_lean_speed.py` checks it).

To see where one declaration spends its time, profile its file (time under
`[Kernel]` is the kernel checking the term):

```sh
lake env lean -DElab.async=false -Dtrace.profiler=true -Dtrace.profiler.threshold=1000 \
  VerifiedGarbage/Proof/….lean
```

To compare two versions of a file, count its instructions, which (unlike
time) do not depend on the load of the machine; pass the lakefile's options,
as `lake build` does (it turns off Mathlib's style and tactic-analysis
linters, 5–8% of the build: never turn them back on in a module), but not
its profiler:

```sh
lake setup-file --log-level=warning VerifiedGarbage/Proof/….lean > .lake/setup.json
opts=$(grep -oE "^weak\.[A-Za-z_.]+ = (true|false)" lakefile.toml | sed -E 's/ = /=/; s/^/-D/' | tr '\n' ' ')
perf stat -e instructions:u -x, lake env lean --setup .lake/setup.json $opts -Dprofiler=false VerifiedGarbage/Proof/….lean
perf stat -e instructions:u -x, lake env true   # Lake's own startup: subtract it
```

`--setup` loads the precompiled libraries (`Native*` in the lakefile) as
`lake build` does; without it the interpreter runs their tactics, many
times slower. The setup file serves edited copies of the module too.
`lake env` starts Lake for every command (about 3.5e9 instructions), which
a build does once: subtract it before quoting a relative change.

`set_option diagnostics true in` before a slow theorem lists the
definitions unfolded while elaborating it, which finds failing unfoldings.
`#count_heartbeats in` (from `Mathlib.Util.CountHeartbeats`, imported only
while measuring) before a declaration prints the heartbeats it uses
against the 200000 budget.

For allocation-based work comparisons without adding an import, use Lean's
heartbeat profiler. From `lean/`, write the module's setup file, which
supplies the same options and imports as Lake (`lake setup-file` builds the
module's imports, not the module, and prints it; the build cache keeps none):

```sh
lake setup-file --log-level=warning VerifiedGarbage/Proof/MlKem/Arm/Mul.lean > .lake/setup.json
lake env lean --setup .lake/setup.json \
  -j1 -DElab.async=false -Dtrace.profiler=true \
  -Dtrace.profiler.useHeartbeats=true -Dtrace.profiler.threshold=1000000000 \
  -Dtrace.Elab.command=true -Dtrace.Kernel=true \
  VerifiedGarbage/Proof/MlKem/Arm/Mul.lean
```

Traces are inclusive: report the command and kernel counts separately, not
added up. Run elapsed-time benchmarks without tracing.

When changing proof or build performance, compare representative callers of
a shared helper (large proofs, different postcondition shapes), not one;
compare baseline and candidate on the same revision, toolchain, hardware and
cache state; and back a claim of an overall speedup with a clean full build,
audits and golden tests included. Keep the two compiler threads and six Lake
workers measured in [PR #367](https://github.com/pyca/verified-garbage/pull/367)
unless a controlled build comparison on the intended runner supports
changing them.

## Measuring CI

When asked to check or analyze CI metrics, follow
[Collecting and analyzing CI metrics](ci/metrics-analysis.md). Start with the
retained artifacts and their coverage, not a local build. The guide covers
time-window downloads with uv, splitting/reassembling uploads with checksums,
and streaming analysis of large bundles.

Every CI run keeps a `ci-metrics` artifact (`ci/ci_metrics.py`, the last
steps of `all-green`), for 30 days: every
job's and step's queue and run times, the Lean build's plan, and what each
shard and assembly restored and built (each module and its time). The plan
and the shards' outputs last a day; these do not. To analyse CI (shard balance,
duplicate work, failed restores, slow jobs), download them rather than
scraping logs:

```sh
python3 ci/ci_metrics.py fetch .ci-metrics 200   # the last 200 runs', as .ci-metrics/<run>.json
```

The metrics embed the full planning snapshot (including the import graph,
historical timing inputs, stale set, candidates and assignments), so a future
planner can replay it after the working plan artifact expires. Native facets
are separate from Lean module builds. See [the metrics schema and retention
limits](ci/README.md) before comparing runs or interpreting missing data.

## Iterating on one proof

While developing, never run a bare `lake build` or the emitter: the default
targets are every module (over 8,000), and the emitter imports every
registration file. From `lean/`, build the module you're working on, which
builds only it and what it imports, and after that only what changed
(`--log-level=warning` leaves out the profile Lake replays for every module:
see "Finding what to optimize"):

```sh
lake build --log-level=warning +VerifiedGarbage.Proof.Md5.X86_64.Compress
```

To check the artifact and regenerate its code, run `EmitOne.lean` on its
registration file: it builds only that file and what it imports, runs the
emitter's audits on its artifacts, and writes (or, with `--check`, compares)
only its files under `src/asm/`, in seconds once the proofs are built:

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

## Measuring a change's speed

Measure only what the change affects. `python3 ci/bench_arches.py --choices`
lists the architectures, each one's `VG_CPU_FEATURES` configurations and the
features `src/cpu.rs` detects there, and the library modules with the
benchmarks that use each (a benchmark's `USES`). On this machine, for the
features its CPU has (`/proc/cpuinfo`):

```sh
VG_CPU_FEATURES=avx,avx2 python3 ci/bench_compare.py --modules chacha20 path/to/main-checkout .
(cd bench && VG_CPU_FEATURES=none VG_BENCH_MODULES=chacha20 cargo bench -- '^chacha20/verified-garbage/')
```

A benchmark whose code reads a comb's table of hundreds of kilobytes
(P-521's) is up to about 7% faster or slower depending on which physical
pages the kernel gives the table when it first reads the binary, a draw
fixed for each binary file: comparing one run of each side compares two
draws, not the code. So `ci/bench_compare.py` runs those groups
(`FRESH_COPIES`) from `--copies` fresh copies of each side's binary and
compares the fastest of each; add a group there when its code reads such a
table.

For another architecture, or features this CPU lacks, run the Benchmarks
workflow by hand: it never runs on its own (not on pull requests, not on
`main`). Its runners are the ones CI waits for, so scope every run as
narrowly as the change allows. First ask which jobs the change needs:

```sh
git diff --name-only origin/main HEAD | python3 ci/bench_arches.py --base origin/main
```

prints a JSON list, one entry per job, each with its `arch`, `cpu-features`
and `modules` (empty: every benchmark; such architectures it leaves out,
naming them on stderr). Then run the workflow on the pushed branch with
those values, one run per architecture when they differ between
architectures:

```sh
gh workflow run bench.yml --ref my-branch -f base_commit=$(git rev-parse origin/main) \
  -f arches=aarch64 -f cpu_features='- none sha3' -f modules=ecdsa_p256
```

`--ref` is the branch (or tag) measured, at its tip; `base_commit` is any
commit to compare it with, as a full or abbreviated SHA, a branch or a tag,
which the workflow resolves to the full SHA (empty to run the branch alone,
next to OpenSSL and aws-lc-rs). `arches`, `cpu_features` (space-separated configurations,
`-` for none; empty for those choosing among the modules' implementations)
and `modules` narrow the run (`python3 ci/bench_arches.py --choices` lists
their values); `openssl=true` adds OpenSSL's and aws-lc-rs's times to a
comparison, which only costs time: leave it off. To measure a commit that
is no branch's tip, push a branch at it
(`git push origin <sha>:refs/heads/bench/<name>`) and delete it after. The
results are in each job's summary.

Never run every benchmark (`modules` empty: leaving `arches`,
`cpu_features` and `modules` all empty runs every benchmark of every
architecture in about thirty jobs, and `arches` alone every benchmark of
that architecture) unless the change truly needs it and cannot be measured
otherwise: a change to the benchmarks' shared code or `bench/Cargo.lock`,
whose architectures `bench_arches.py` names on stderr. Even then, run only
the architectures it names, and prefer a module or two that show the
change's effect over all of them. Never rerun a benchmark to get a better
number, and never run one for a change that cannot affect speed (Lean
proofs that leave `src/asm/` as it was, tests, docs, CI).

## Checks to run before pushing

```sh
(cd lean && lake build --log-level=warning && lake env lean --run Emit.lean --check)
python3 ci/check_lean_imports.py
python3 ci/check_lean_modules.py
git diff --name-only origin/main -- lean/VerifiedGarbage | sed -n 's#^lean/\(.*\)\.lean$#\1#p' | tr / . \
  | xargs -r python3 ci/check_lean_public_imports.py --base origin/main -m   # after building them; --fix applies it
python3 ci/check_registrations.py
python3 ci/check_lean_speed.py
python3 ci/check_vectors.py
python3 ci/check_arch_gates.py
python3 ci/check_variants.py
python3 ci/check_mcdt.py
python3 ci/cpu_tests.py lint ci/rust_matrix.toml
cargo fmt --check && cargo clippy --all-targets -- -D warnings
WYCHEPROOF_ROOT=/path/to/wycheproof cargo test
```

A primitive with implementations for different CPU features is tested (and
benchmarked) end to end in each configuration, never through a special API:
the `cpu-features-env` Cargo feature lets `VG_CPU_FEATURES` restrict the
features detected (see `src/cpu.rs`). CI tests each configuration that
chooses differently on a CPU that has those features: the runner's, or one
Intel SDE presents (`rust-cpu-features` in `ci.yml`, whose CPUs are the
`cpu` entries of `ci/rust_matrix.toml`; SDE runs the SHA
extensions' code very slowly, so the chips that have them run only the
tests that need them); and benchmarks each with
`VG_CPU_FEATURES` (`CPU_FEATURES` in `ci/bench_arches.py`). A configuration
to test is a line of a CPU's `runs` in `ci/rust_matrix.toml`
(`<VG_CPU_FEATURES> | <groups>`), never a step or job of its own, and
each CPU has one line per value of `VG_CPU_FEATURES` (CI checks both), so
a run never repeats another: add groups to a CPU's line for those features.
A group (`GROUPS` in `ci/cpu_tests.py`) names its tests explicitly, by the
path of each test or of the module around it, in the library's unit tests
and in `tests/main.rs`; a line runs exactly those tests, so a new test of a
primitive that varies by CPU feature goes into its group (or a new group),
never into a line by matching part of its name. CI fails a path that
selects no test on any CPU, and a group that selects none on a line's CPU.
A CPU whose lines take long runs as shards (its `shards = n`: n jobs, each
with a `shard` of `i/n`), which deal out its
lines by the CPU time each took on `main` (`ci/cpu_shards.py`): to speed
one up, add a shard, never split its lines by hand.
To test the baseline ISA's implementations:

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
