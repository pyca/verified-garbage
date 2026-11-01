# Lean: specifications, implementations and proofs

The cryptographic primitives (e.g. a block function or a field
multiplication) are assembly written in Lean as structured programs over a
Lean model of each ISA, proven correct in Lean, and printed into a crate per
target, `crates/verified-garbage-asm-<target>/`, as Rust naked functions. The
library's public APIs are Rust that composes those
primitives: this directory verifies the primitives, not the Rust around them.

## Layout

```
VerifiedGarbage/
  TCB/          Trusted computing base: definitions only, Lean core only
    Mem.lean        byte-addressed memory, regions
    Code.lean       structured programs, calls and stack frames, big-step semantics
                    with leakage, constant time
    Print.lean      lowering of structured control flow to labels and branches, of
                    calls to call instructions, and of frames to push and pop
    Sig.lean        Rust signatures and calling conventions (`Abi`)
    Artifact.lean   Target, Contract, `Verified`, `Artifact`: what "verified" means;
                    `Sig.contract`: the contract obligations a signature implies
    Registration.lean  `Api.artifact`: an `Artifact` made from an `Api` and only
                    what its implementation chooses (`Registration`)
    Rust.lean       rendering artifacts as Rust naked functions; checks that every
                    call is of the function whose code the model runs for it (an
                    artifact, or an internal function the emitter writes from that
                    code), and that each artifact declares the CPU features its
                    code needs
    Axioms.lean     `#assert_standard_axioms`
    Audit.lean      `#assert_no_compiler_overrides` (the compiled code the emitter
                    runs is what the kernel checked) and `#assert_spec_origin`
                    (`VG.Spec` definitions are declared in `Spec/`)
    Emit.lean       what is emitted (every registration file under
                    `Artifacts/`, and every generic function under `Generic/`
                    for every variant of its interface under `Variants/`), and
                    writing or checking the generated crates
    X86_64/         ISA model, printer, System V ABI target
    PPC64LE/        ISA model, printer, ELFv2 ABI target (64-bit little-endian PowerPC)
    RISCV64/        ISA model, printer, psABI target (64-bit RISC-V, RV64IM)
  Spec/         Algorithm specifications and contracts (trusted, must be reviewed)
  Impl/         Implementations: `Prog`s over an ISA model (untrusted)
  Proof/        Proofs and intermediate proof artifacts (untrusted)
    Framework/      generic lemmas: determinism, WP rules, memory frames, inlining
                    verified code, and a taint-tracking checker that proves
                    constant time by evaluation
  Artifacts/      The registry: one registration file per algorithm and target,
                  each listing the artifacts it emits
  Variants/       Implementations of an interface that generic callers call: one
                  file per implementation, `Variants/<Iface>/<Target>/<Name>.lean`
  Generic/        Callers proven for any variant of an interface, emitted once per
                  variant: `Generic/<Iface>/<Target>/<Alg>.lean`; callers of several
                  interfaces, once per combination of their variants:
                  `Generic/<Iface₁>/<Iface₂>/<Target>/<Alg>.lean`, each instance
                  named by `Emit.qualifiedName` (a tag and the suffix of each
                  interface's non-baseline variant: `vg_argon2_blake2b_avx2_g_avx512`)
VerifiedGarbageTest/  Golden tests for the (unverified) printers and calling conventions
Emit.lean       Renders every artifact into `../crates/` (see `TCB/Emit.lean`)
EmitOne.lean    The same, for the registration files named, while iterating
```

`ci/check_lean_imports.py` enforces the import discipline between these
directories: `TCB/` imports only Lean core and itself; `Spec/` and `Impl/`
never import proofs.

## The pipeline

1. **Spec** — `Spec/<Alg>.lean` defines the algorithm as a readable Lean
   function transcribed from the standard, and `Spec/<Alg>/Contract.lean`
   each function's Rust signature (`Sig`) and its `Contract`, for every
   target at once: `Sig.contract` derives from the signature and the
   target's calling convention where the arguments are, the permitted memory
   regions, disjointness and which arguments are public, and the contract
   adds a postcondition (in terms of the spec) and any further precondition.
   Each function's `Api` gives its Rust module, name and signature, its
   contract on every target (`contracts`), and its documentation, but for
   what the emitter derives from the signature.
2. **Impl** — `Impl/<Alg>/<Target>.lean` defines the code as a `Prog`.
3. **Proof** — `Proof/<Alg>/…` proves `Verified target code contract`:
   termination without faults (hence memory safety), the postcondition,
   the ABI obligations (callee-saved registers etc.), constant time (up to
   anything the contract declares the function may leak), and
   satisfiability of the precondition.
4. **Registry** — the registration files `Artifacts/<Alg>/<Target>.lean`
   list every `Artifact`, bundling target, Rust name and signature, code,
   contract and proof: a function's `Api`, with what its implementation
   chooses (`Api.artifact`, `TCB/Registration.lean`): the target, the code
   and its proof, the stack its calls and frames use (`stack`), and the
   suffix of its name. An artifact
   made from an `Api` takes the contract from it with the name and signature
   (`Api.contracts`), and must be proven against exactly that contract on its
   target (`Artifact.ofApi`), so a registration file, or a proof building
   artifacts for a generic caller, cannot pair a function's name with another
   function's contract; the emitter refuses an artifact that is not made from
   an `Api` with a contract. An `Artifact` cannot be built
   without the proof, and the emitter's `#assert_standard_axioms` rejects
   `sorry`, `native_decide` and any non-standard axiom anywhere in them. The
   emitter runs compiled code, so it also rejects anything that makes the
   compiler run other code than the definitions the kernel checked, in what
   it runs (`implemented_by`, `extern`, `export`) or anywhere in the project
   (`csimp`, `initialize`), and any `VG.Spec` definition declared outside
   `Spec/`. Each audit reads the records every module writes when it is
   built (`TCB/AuditRecords.lean`), not the proofs, which a module does not
   see in what it imports.
5. **Emit** — `Emit.lean` renders the registry into `crates/verified-garbage-asm-<target>/src/<module>.rs`,
   adding to each function's `# Safety` section what its contract requires of
   the memory each buffer is valid for (`Sig.validDoc`) and of where its
   buffers are, which depends on the target's calling convention and the
   stack it uses (`Sig.layoutDoc`), from the same signature, `stack` and
   `writeArgs` as the contract, as `Artifact.ofSig` proves.
   CI fails if the checked-in files differ from what Lean generates, so the
   Rust crate contains exactly the verified code. Every printer but ARM's
   emits each straight-line instruction as its machine code
   (`TCB/<ISA>/Encode.lean`), so that the assembler only copies those bytes;
   ARM's crate, one for both A32 and Thumb, is assembled from its text. The
   text of every function's code is in its crate's
   `assembly/<module>.s`, which the emitter writes with it and the crate does
   not compile (nor publish).

A function can call another (`Code.call name body`): the model runs the
callee's code `body` between the call and return instructions, so the
caller's proof covers it, and the emitter only emits the call if the
function it emits as `name` is `body`. A caller's proof can use the callee's
`Verified` proof rather than go through its code again.

So a function that only verified code calls, an implementation detail of
the functions it serves, needs no `Api`, no contract in `Spec/` and no
registration: when `name` is not an artifact of the target, the emitter
emits it as an *internal function* (`Rust.Internal`), from `body`, private
to the crate (`internal/<name>.rs`), where no Rust code can call it. Its
proof, and the contract it is proven against, are the caller's business, in
`Proof/`: what is trusted is only the contract of each artifact that calls
it. Give a function an `Api` only if the Rust code calls it.

Code saves registers on the stack, or passes arguments on the stack, in a
stack frame (`Code.frame push body pop`): the push moves the stack pointer
down, stores registers and makes those bytes a writable region; the pop
faults unless the stack pointer and regions are as the push left them, loads
one register and removes the region. Frames are nested by construction, so
the stack pointer is always back where it was, and the stack a function's
calls and frames use is part of its contract (`Sig.contract`'s `stack`).

Instructions outside a target's baseline ISA (e.g. SHA-NI) name the CPU
features they need (`ISA.requires`, transcribed from the vendor manual). An
artifact using them declares those features (`Artifact.features`), the
emitter checks the declaration is exact, and the generated function's
`# Safety` section makes their presence the caller's obligation. The Rust
that calls it checks for them first, using the generated `<NAME>_FEATURES`
constant.

## What you need to trust

* `TCB/` — in particular the ISA models, which must match the vendor manuals
  (including the CPU features each instruction requires), and the printers
  and encoders, which must print what the models mean.
* For each artifact: its contract in `Spec/` (and the algorithm spec it
  refers to), its `sig` and `doc` (its `Api` in `Spec/`), and
  `TCB/Emit.lean`, which decides what is emitted. Not the internal functions
  it calls, which have no contract: its proof covers their code.
* Lean's kernel, and the assembler in `rustc`/LLVM for what is printed as
  text: ARM's code, and the branches, calls, addresses of statics and
  directives of the others.

Everything in `Impl/` and `Proof/` is checked by Lean and need not be read.

To keep review of the trusted parts focused, new specs, additions to the TCB,
and new implementations are never combined in one PR: an implementation is
only proven against a spec and TCB that were reviewed and merged beforehand.

## Building

```sh
lake exe cache get                  # download prebuilt Mathlib
lake build --log-level=warning      # check every proof, run the axiom audit and golden tests
lake env lean --run Emit.lean       # regenerate ../crates
lake env lean --run Emit.lean --check
lake env lean --run EmitOne.lean [--check] Rc2.AArch64   # one registration file
```

Each emitter's driver is a module, which `Emit.lean` and `EmitOne.lean` run
with the setup Lake gives it (`lake setup-file`), as `lake build` would build
it: it loads what it imports without their private parts (`.olean.private`),
and its audits read the records every module of this project writes when it
is built (`TCB/AuditRecords.lean`; the `lean-modules` skill), so they run on
a build restored without those parts ([Without the private
parts](#without-the-private-parts)).

On Linux, `Emit.lean` needs `vm.max_map_count` above the default of many
distributions (65,530): it maps every module its drivers import. It refuses
to start below eight regions of memory per `.olean` and names the command to
raise the limit, `sudo sysctl -w vm.max_map_count=262144`, which CI runs
(`EmitOne.lean` loads far fewer). Past the limit Lean would fail with
`failed to read file '….olean'`.

Every module records a profile of its build, kept in its `.trace` file
(`moreLeanArgs` in `lakefile.toml`), which Lake prints again for each module
it finds already built: `--log-level=warning` (or `-q`) leaves it out and
shows only warnings and errors. `python3 ../ci/lean_profile.py` reads it (and,
for the modules of a restored cache, the profile `unpack --logs` writes), to
list the declarations the build spends the most on (the `lean-profiling` skill,
`.agents/skills/lean-profiling/SKILL.md`).

## Iterating on import narrowing

Use `ci/trim_lean_imports.py` from the repository root to separate expensive
evidence collection from fast planner changes. Start from a built checkout
(including the downstream modules being analyzed). A capture checks the
selected modules' builds and reads compiled declarations; it does not edit
headers or run verification builds of proposed changes:

```sh
python3 ci/trim_lean_imports.py -m VerifiedGarbage.Proof.YourModule \
  --discover --capture lean/.lake/import-evidence.json.gz \
  --report lean/.lake/import-plan.json
```

`--discover` adds hypotheses based on declaration uses, including ones
`lake shake` missed or disagrees with. Absence from compiled declarations is
only a hypothesis: tactics, namespace opens, syntax, attributes and
evaluation can require imports without leaving those references. To collect
evidence without running shake, add `--no-shake`; the selected modules are
still checked with `lake build` first. `--dry-run` produces the same analysis
without saving an evidence snapshot. Neither mode verifies the proposed edits.

After changing the Python planner, replay the same evidence without Lake,
the toolchain, build outputs, or the original source checkout:

```sh
python3 ci/trim_lean_imports.py --replay lean/.lake/import-evidence.json.gz \
  --report lean/.lake/import-plan-next.json
python3 ci/trim_lean_imports.py --replay lean/.lake/import-evidence.json.gz \
  --shake-only --report lean/.lake/import-plan-shake.json
python3 -m unittest discover -s ci -p 'test_check*import*.py'
```

Snapshots store the sources and use queries actually consulted, plus the
library's reverse import index. If a new planner needs uncaptured evidence,
replay fails explicitly: collect a new snapshot on the built checkout. A
snapshot captured with discovery usually supports more comparisons than a
shake-only capture. Replay evaluates the captured checkout, not subsequent
source changes. Capture and replay reports say `build_verified: false`. They list explicit
operations separately from human diagnostics and include candidate decisions:
proposed, retained, deferred, unsupported, or not considered. Retained decisions
name the declaration, source reference, keep marker, or opaque module effects
that prevented narrowing. A candidate absent from shake/discovery is not a
claim that its import is necessary. Snapshots ending in `.gz` are compressed.
The portable synthetic
regression in `ci/fixtures/import_narrowing/diamond.json` demonstrates a pair
of demotions that jointly require a downstream public import.

The planner combines ordinary/meta declaration dependencies, resolved source
references and exported effects. It plans downstream repairs with each narrowing
and preserves repository import rules, keep markers and reviewed boundaries.
The [design guide](../ci/IMPORT_NARROWING.md) explains the evidence, conservative
guards and plan invariants.

Reports estimate the affected library scope and recorded profile work, excluding
blocked time; neither predicts wall time or actual recompilation. Missing profiles
are counted explicitly. For scopes of at most 250 modules, `visibility_impact`
also models changes to ordinary/meta access and public re-exports, including
repairs. Larger scopes omit that calculation to bound analysis work. Emitter
checks remain separate from library verification.

Select a small batch from the report for live verification:

```sh
python3 ci/trim_lean_imports.py -m VerifiedGarbage.Proof.YourModule \
  --discover --max-affected 25 --rounds 1 --build-timeout 120 \
  --verify-attempts 3 --report lean/.lake/import-verification.json
```

`--max-affected` selects source modules within the combined target budget,
starting with smaller verification scopes and deferring the rest. Each subset
is replanned together with its repairs; repairs are never detached from their
causes. Public boundaries that would require editing reviewed registrations or
variants, or modules marked `shake: keep-all`, are retained, allowing
independent work to proceed. Pinned private imports are preserved when a
public repair needs an additional occurrence.

Live runs first build the original affected modules to distinguish existing
failures and cold dependencies from import regressions. They then apply the
explicit operations and rebuild every affected library module. Known failures
undo the nearest edited files and retry, up to `--verify-attempts` passes.
`--verify-batch` limits each baseline/verification command to 32 targets by
default; a pass stops at its first failing chunk. All chunks must pass before
any kept changes are called verified. Dependencies may still require additional
rebuilds. Unknown failures, timeouts, Ctrl-C and SIGTERM restore the whole batch.
`--build-timeout` limits each analysis, baseline and verification build and
terminates its Lean children.

Declaration readers default to 32 roots per process (`--read-batch`), independently
of shake's `--batch`, with a 120-second timeout (`--read-timeout`). Their process
groups are cancelled on timeout or interruption, and malformed, partial or failed
reader output is an error rather than an empty dependency set.
Shake invocations also have durable logs and process-group cancellation, with a
120-second default timeout; `--build-timeout` overrides it.

Every live round is included in `--report`, with proposed operations, final
kept/undone changes, verification targets, and per-attempt timings and outcomes.
Durable logs and manifests live under `lean/.lake/import-verification/`;
`lean/.lake/check-imports-build.log` remains a copy of the latest build log.
Analysis builds have separate logs under `lean/.lake/import-analysis/`. A
successful library build does not replace the final emitter/assembly checks.
Rejected or aborted trials automatically save `evidence.json.gz` beside their
verification manifest. Replay that snapshot to investigate the pre-edit plan
without rebuilding proofs. Reader logs and outcomes also live under
`lean/.lake/import-analysis/`.

Declaration and source-index evidence have separate reader/toolchain cache
keys, so Python planner changes retain reusable raw evidence. Queried downstream
roots are refreshed before cached declaration evidence is trusted. Rejection
keys include the exact operations, consulted sources, graph and affected traces,
so changed context permits a new trial.
Failed file trials also have scoped rejection keys: unrelated successful edits
do not cause the same file to be tested again. A change to its consumers,
relevant build outputs or planned dependency edits permits a new trial. Reports
link deferred trials to their previous verification and rejection snapshot.
`--retry-rejected` explicitly retries the selected modules while retaining the
raw declaration/index/shake caches.

The focused Python tests run without Lean. With the repository’s Lean toolchain
installed, the same command also runs small core-only semantic regressions
directly with `lean`, without Lake builds or cryptographic proofs. These cover
combined visibility losses, exposed proof dependencies, ordinary/meta repairs,
resolved source references and implicit core imports.

## Restoring the CI build cache

After CI passes on `main`, it publishes the Linux x86-64 project build and
Mathlib dependencies to `ghcr.io/pyca/vg-lean-cache:latest`, an OCI artifact
whose one layer is `lean-cache.tar.zst`: `.lake/build` and `.lake/packages`
relative to `lean/`, with each module's outputs in one `.ltar` archive, the
format of Lake's `ltar` facet and Mathlib's cache, and every other file (the
outputs' `.hash` files, the dependencies' checkouts) in one tar,
`.lake/ltar/files.tar`, first in the layer (`ci/lean_cache.py`). The publisher
combines the existing project and dependency module caches with
`ci/lean_cache.py bundle`, without expanding their compiled outputs. The
project cache records its dependency cache key; older caches or missing
dependency caches use the normal setup path first. Only
the latest version is retained. CI compares the checked build's cache key
with the manifest's `io.pyca.lean.cache-key` annotation and skips packaging
and publishing when it matches, so Rust- or docs-only changes do not create
a new cache version.

Restore it with `ci/fetch_lean_cache.py`, which streams the layer straight
from the registry API with an anonymous pull token, resumes from where it
stopped when the connection drops, and checks the download against the
layer's digest, and `ci/lean_cache.py unpack`, which extracts `files.tar`
with `tar` in the background and unpacks the archives with the toolchain's
`leantar` as they arrive. Install the toolchain in `lean/lean-toolchain`
first (with elan, `lean --version` in `lean/` installs it), and the `zstd`
command if you do not have it (`apt-get install zstd`, `dnf install zstd`,
`brew install zstd`). Then, with `python3`, `tar` and `zstd` installed, from
the repository root:

```sh
set -o pipefail
python3 ci/fetch_lean_cache.py | zstd -dc | python3 ci/lean_cache.py unpack lean
```

The download (about 1 GB) streams through the pipeline and is never
stored: `files.tar` and the archives, a batch at a time, are staged in
`/dev/shm` (`--tmp` for another directory), and only the unpacked build is
written. If the
pipeline fails (a connection that drops five times in a row without
progress, or a download that does not match the digest), run it again. The
manifest's `io.pyca.lean.toolchain` and `org.opencontainers.image.revision`
annotations identify the cached build. Lake rebuilds outputs that differ
from the checkout. The build's messages, with the profile CI's build
recorded that `ci/lean_profile.py` reads, are not in the modules' `.trace`
files but in one file, which `unpack --logs` writes
(`ci/lean_cache.py unpack --logs lean`, to `lean/.lake/ltar/logs.json.gz`).

Only where you cannot install the `zstd` command, `pip install zstandard`
and replace `zstd -dc` with
`python3 -c 'import sys, zstandard; zstandard.ZstdDecompressor().copy_stream(sys.stdin.buffer, sys.stdout.buffer)'`.

The cache holds the C (`.c`) only of the modules the build compiles, those
of the precompiled libraries (`lakefile.toml`): nothing reads the others',
about 1.2 GB. `unpack` writes an empty `.c` in place of each, which is all
Lake checks for. Compiling an empty one is an error (`moreLeancArgs` in
`lakefile.toml`, which says what to do if a module whose C the cache left
out is now compiled).

`unpack` leaves the files' owner alone, as `tar --no-same-owner` would: the
archive's files belong to CI's runner user, and extracting them as root (as
in a container) would keep that owner. Git then refuses the dependencies'
checkouts in `.lake/packages` as owned by someone else, so Lake clones them
again and builds Mathlib from source.

Moving the cache to a different absolute path can also make Lake relink
native libraries and rebuild affected native modules. A normal `lake build`
handles this; the restored cache need not pass `lake build --no-build` for
every project target immediately after extraction.

### Without the private parts

`unpack --empty-private` writes less than half as much, 7.5 GB rather than
18 GB (the build is 4.7 GB rather than 16 GB, and it keeps 1 GB of
archives), in less time: each module of this project but the trusted base's (`TCB/`) gets an
empty `.olean.private`, its private part, with its proofs. Lake only checks
that the file is there, and what imports a module as a module never reads
it: `lake build` (the tests too) and the emitters, whose audits read the
audit records instead (the `lean-modules` skill), work as before. CI
restores this way.

```sh
set -o pipefail
python3 ci/fetch_lean_cache.py | zstd -dc | python3 ci/lean_cache.py unpack lean --empty-private
```

It keeps the archives of this project's modules in `lean/.lake/ltar-private/`,
so that a tool that reads private parts gets them: `ci/lean_cache.py
fill-private lean <module or file>` writes those of the modules given and
everything they import (only the empty ones, in seconds: a module imports at
most about 1,200 of this project's). These run it themselves:

* `ci/check_lean_public_imports.py` and `ci/trim_lean_imports.py`, before
  `lake shake`, which reads the private part of each module it checks and of
  all they import;
* `ci/lit_imports.py`, before `CheckLitImports.lean`.

Run it yourself before what else reads them, which otherwise fails with
`failed to read file '….olean.private', invalid header`:

* a file that is not a module and imports the project's modules, run with
  `lake env lean` or opened in the editor (`fill-private lean
  GenerateP256Ecdh.lean`: a file's imports);
* a module with an `import all` of a module of this project (`fill-private`
  on that module).

Restoring again without `--empty-private` writes every private part and
deletes the kept archives. `--empty-private` needs the project's leantar, a
release of reaperhulk/leangz that `ci/leantar_release.py` downloads once (on
Linux or macOS, x86-64 or arm64) into `~/.cache/verified-garbage/leantar/`,
checked against the SHA-256 `ci/leantar/release.toml` pins.
