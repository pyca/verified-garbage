# Import planner: evidence, verification and iteration

The commands and options are in [the Lean README](../lean/README.md#iterating-on-import-narrowing).
This note describes the planner’s evidence, invariants and verification process,
and how to investigate a bad plan.

## Evidence is not verification

`lake shake` and declaration-based discovery generate hypotheses. Neither is an
oracle. The planner combines several kinds of information:

- Compiled declarations: public signatures and exposed bodies, private bodies,
  and their ordinary/meta dependencies. Exposed definitions can contain generated
  proof auxiliaries; a statement-only visit must be upgraded when an exposed
  body subsequently needs that auxiliary's proof.
- Lean's `.ilean` index: resolved declaration owners used during elaboration,
  including references absent from the final proof term. This avoids matching
  an unrelated declaration merely because its last name component appears in
  the source. Index version, module identity and import header must match.
- Source import visibility: ordinary and meta paths are distinct, and every
  non-`prelude` file implicitly imports both phases of `Init`. Private imports
  can carry public meta capabilities locally without re-exporting them.
- Exported extension metadata: instance registrations, including generated,
  scoped and default instances, and simp/congruence/grind search registries.
  Temporary evaluation or checks can use these registrations and erase the
  reference from both declarations and the source index. These providers are
  therefore conservative boundaries; decisions identify semantic registry vetoes. Metadata reads
  exported files directly and does not initialize their dependency environments.
  Unfamiliar extension data is protected too: Aesop can name its rule-set
  extensions arbitrarily (including `default`). An explicit allowlist exempts
  Lean's declaration/compiler bookkeeping. Review that classification on Lean
  upgrades; granting an unfamiliar registry an exemption needs semantic evidence.
- Runtime initialization metadata: regular initializers can be absent from
  `.olean` extension data while `meta import` executes them. The reader also
  inspects `.ir.sig`/`.ir` metadata, without running initializers. This catches
  macro-generated initializers that have no source-level `initialize` command.
  Missing IR parts fail the read rather than establishing absence of effects.
- Conservative guards: explicit keep markers, namespace opens, opaque module
  effects and dependency modules. Unrecorded effects are not inferred absent.

The Lean reader loads private data in an environment that still participates in
Lean's module system. Importing private data in a legacy environment would make
`isDeclMeta` classify every declaration as meta and corrupt the phase evidence.

## Plan invariants

An `Edit` identifies a module, action and dependency. Diagnostics are never parsed
back into instructions. The editor renders and validates the entire batch before
writing any source. It distinguishes private/public occurrences of the same
module, meta imports, and `import all`, and preserves attached comments.
Added repairs stay outside nested/multiline import comments and before module
documentation. A first import follows `prelude`, and splitting a comment-closing
line preserves the following declaration's original column.

The planner evaluates simultaneous public changes against one graph. Two
individually redundant paths can jointly hide a dependency. Repairs therefore
follow the combined losses and use public, private or meta imports as required.
Narrowing public boundaries also preserves their opaque forwarded capabilities.
Private ordinary/meta removals participate in the same downstream repair pass:
an `import all` consumer can read dependencies that its provider imports privately.
An exported empty namespace has no declaration prefix in `.ilean`. When an
`open` lacks an indexed provider, the planner reads exported namespace
registrations, retains its sole provider, or repairs downstream users. An
alternative provider can make the import removable. These additional queries
are batched before candidate checking and remain strict replay evidence.

Keeping the same visible modules is insufficient: changing import order can
change instance selection while the edited file still compiles. The planner
compares dependency initialization order in edited modules and their library
consumers. It preserves relative order among providers with opaque extension
effects. A public import may become a private initialization anchor rather than
be deleted; private ordinary/meta deletions that reorder those providers are
deferred. Structural bookkeeping can move without imposing such an anchor.
The editor preserves the earliest occurrence when demoting a public import
that also has a later private duplicate. This guard is conservative and does
not establish general semantic equivalence of arbitrary elaboration effects.
The guard also preserves opaque providers lost from a shim's private load
closure. Removing a meta import can stop a private dependency's initializer
even when an ordinary occurrence remains. Ordinary instance-registration order
is checked separately from mixed ordinary/meta runtime load order: traversing
the same modules is insufficient when their import phases change.

When repairs make a public provider locally unnecessary, `remove_public` can
replace a demotion followed by a separate deletion round. A private provider may
be replaced by direct imports of its consumed declaration owners. These private
repairs must not expand either ordinary or meta visibility and must preserve
opaque capabilities. Remaining namespace/source guards can veto the replacement.

Private `meta import` edges can also be removed. Their recorded execution uses
are checked separately from ordinary declaration uses, and exact source
references remain a conservative guard regardless of phase. The planner tests
these removals sequentially against the complete ordinary plan, retaining
transitive execution dependencies, namespace providers and opaque effects.
Public meta imports and `import all` remain outside primary narrowing scope.
The classic checker's `--base` filter compares meta imports separately too.

A verification budget selects primary source modules and replans their repairs
together. It never detaches a repair from its cause. Boundaries requiring edits
to reviewed registrations, variants or modules marked `shake: keep-all` are
deferred; independent sources can still progress. `Artifacts/`, `Generic/` and
`Variants/` are never edited. A public repair preserves a private import marked
`shake: keep`, adding a separate public occurrence when necessary. The editor
checks module keep annotations again before applying a plan.

A direct repair must also pass the repository's target and trusted-layer import
rules. A neutral provider can hide a cross-target dependency; replacing it by
an ARM-to-x86 import may compile but fail `check_lean_imports.py`. The planner
reuses that checker's rules and defers the narrowing responsible for an invalid
local or downstream repair while retaining independent changes. Reports name
the invalid repair and boundary. Target directories are inferred from the
complete captured library identities, so this check also works in portable
replay. Changes to the checker invalidate planner rejection state.

## What a successful live run means

Each round builds the original affected targets before editing. This distinguishes
pre-existing failures and cold dependencies from import regressions. Verification
then builds the affected library targets in bounded chunks. All chunks must
succeed with actual zero exit statuses before kept changes are called verified.

Known failures restore the nearest edited files and retry the remaining batch.
Unknown failures, exhausted attempt limits, timeouts, Ctrl-C and SIGTERM unwind
the transaction. Build and reader children run in cancellable process groups.
Logs and manifests record targets, elapsed time, return codes, timeouts,
interruptions, rebuilt tasks and the final kept/undone changes. Early editor
validation failures receive an abort manifest too.

Verification covers the library reverse import closure. It does not replace the
repository's final emitter and assembly checks. `EmitOne.lean --check` is useful
for self-contained artifact groups; incomplete caller/callee selections can fail
on the unchanged baseline and must not be counted as an import regression.

## Fast investigation cycle

1. Capture evidence on a built checkout, preferably with discovery enabled.
   `--no-shake` can avoid shake's cost while retaining independent hypotheses.
2. Replay the compressed snapshot while changing Python planning logic. Replay
   does not invoke Lean, Lake or the original checkout. A missing query needed
   for the plan raises an explicit error. An optional visibility-impact count
   can be omitted when an older snapshot lacks its extra source evidence.
   A snapshot freezes the reader's answers too: changing the Lean reader requires
   a new capture. Replaying historical evidence deliberately does not repair an
   old reader's answers; this is useful when reproducing a reader regression.
3. Verify a small affected scope. A rejected or aborted trial automatically saves
   its pre-edit `evidence.json.gz` beside the verification manifest. Replaying
   that evidence remains unverified, even if part of the original batch built.
4. Minimize an actual failure into a small compiled Lean regression. Keep the
   large proof case for periodic real-proof runs rather than every unit test.
5. Test interacting edits cumulatively as well as in isolated batches. Refresh
   queried downstream roots before trusting persistent declaration evidence.

The optional generated-project runner makes the compiled stress checks
reproducible without rebuilding the cryptographic library:

```sh
python3 ci/stress_lean_imports.py --kind phases --projects 160 --seed 7312931 --output /tmp/import-phases
python3 ci/stress_lean_imports.py --kind instances --projects 40 --seed 7312941 --output /tmp/import-instances
python3 ci/stress_lean_imports.py --kind initializers --projects 40 --seed 7312932 --output /tmp/import-initializers
python3 ci/stress_lean_imports.py --kind macro-initializers --projects 40 --seed 7312934 --output /tmp/import-macro-initializers
```

Put the repository's Lean toolchain on `PATH`. Each case builds the original
and edited project, saves sources, reader answers and operations, and stops at
its first failure. Instance and initializer cases additionally compare evaluated values.
Macro-initializer cases require IR evidence: their providers' sources contain
macro calls rather than initialization commands.
The output directory must be empty to preserve previous failure evidence.
These are opt-in tests; normal test discovery keeps the small minimized
regressions. `fixtures/import_narrowing/instance_order.json` freezes reader
answers from the compiled order regression for fast, process-free replay.

Declaration, index and shake caches have separate reader/toolchain fingerprints.
Planner-only changes retain reusable raw evidence. Rejected batches and file
trials have context-sensitive keys. Independent successful edits do not reopen
an unchanged failed file trial; relevant sources, build outputs, consumers and
planned dependency edits can reopen it. Deferred trials link to their previous
manifest and snapshot. `--retry-rejected` retries selected files without deleting
raw evidence caches.

The classic `check_lean_public_imports.py` entry point shares the bulk command's
cached, batched evidence reader and downstream freshness checks, while retaining
its added-import filters for `--base`. Both entry points bound declaration-reader
processes and support build/shake timeouts. Exported metadata uses a separate
32-file batch, so choosing a small declaration-root batch does not launch a
metadata process for every few provider files.

## Interpreting reports

`build_verified: false` on a capture or replay is deliberate. Candidate decisions
explain proposed, retained, deferred and unsupported imports. A retained direct
public/private use is different from an import for which no hypothesis was
considered. Keep annotations and opaque effects take precedence over discovery.

Costs use a conservative affected-library scope and deduplicate shared work.
Recorded profile work excludes blocked time; it is not a wall-time prediction.
Missing profiles are counted rather than invented.

`visibility_impact` compares the complete plan, including repairs. It separates
ordinary/meta local access from public re-exports and reports added as well as
removed consumer/dependency exposures. Narrower public boundaries can leave local
access unchanged when downstream users genuinely need direct repairs. This graph
model does not claim a measured build-time improvement or a globally minimal
import set.
