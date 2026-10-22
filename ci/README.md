# Historical Lean planning data

For a request to check or analyze CI metrics, follow the
[collection, upload, and analysis workflow](metrics-analysis.md). It includes
`ci_metrics.py fetch` time windows, offline gzip bundle export, verified upload
parts, and a streaming summary for large datasets.

Every CI run attempts to upload `ci-metrics.json` as the `ci-metrics`
artifact. Retention is explicitly 30 days. The one-day `lean-plan` and
compiled build artifacts remain short-lived: the metrics embed the plan,
not the compiled outputs. Download
metrics before the 30-day limit if a study needs a longer history; there is
no automatic archive outside Actions.

```sh
python3 ci/ci_metrics.py fetch .ci-metrics 500
python3 ci/ci_metrics.py summary .ci-metrics/<run-id>.json
```

The limit counts recent workflow runs inspected, including runs without
metrics, rather than artifacts downloaded. Fetch paginates beyond 100 runs
and skips files already present. Local fetch records coverage and provenance
in `collection.json`; use `[0-9]*.json` for metrics-only directory readers.
The CI collector is best effort and does not block the CI verdict; a cancelled run or collector timeout may have no
artifact. Do not treat the retained sample as all CI attempts.

## Version 2

The existing `run`, `jobs`, `lean.plan`, `lean.jobs[].built` and
`lean.duplicate_work` fields keep their meanings. New fields are additive;
older metrics remain readable by `summary` and the historical replay tool.

`lean.planning` has a `status`, the source `artifact_id` when available,
and the complete `plan` from that artifact. Status is `available` only when
the embedded run ID and attempt match the collection. `different_attempt`
marks a retained plan from an earlier attempt (for example, rerunning only
failed jobs); `unverified` marks a legacy plan without matching provenance.
`unavailable` includes an error category, and `not_collected` means the
caller did not request the artifact. Missing plans never erase job metrics.

`lean.planning.plan` retains `targets`, `owner`, rounded `loads`, estimated
`stale`/`work`, and `edited`. Its `diagnostics` snapshot contains:

* Version, planner source SHA-256, canonical manifest SHA-256, originating
  run ID/attempt, and measured planning duration (excluding JSON serialization).
* Exact import graph, module visibility information, current/manifest build
  inputs, and the complete historical module timing map used by the planner.
  These allow scheduling experiments without fetching old PR git objects or
  substituting today's graph/cache. Source code itself is not archived.
* Exact stale modules, number with historical timings, median/default
  fallback time, and model constants, including parallelism and overhead.
* Candidate shard counts: solo and every count attempted, finish/work scores
  for fully scored candidates, and exclusion reasons for pruned candidates.
  A pruned candidate has no measured/simulated score implied for its finish.
* Final selected score after refinement and each shard's full module
  assignment, including duplicated dependencies. An empty assignment list
  means a solo build, not that it builds no modules.

`lean.jobs` now also records the API job ID, named phase wall times, and
`facets` grouped by step. `built` still contains only module build records;
`facets` preserves full names such as `A:c.o`, `A:dynlib` and
`NativeTactics:shared`. Native facets run in parallel with module builds:
summing recorded task durations does not give elapsed time. The manifest
already combines a module's native facets into its historical estimate;
do not add them again to those estimates. `lean.duplicate_work` retains its
old definition (duplicated Lean module time only).

`lean.missing_logs` identifies finished Lean jobs whose logs could not be
read. A missing build record is not evidence that a module was cached when
the job failed, the logs are absent, or collection was incomplete. Phase
durations are null when absent/skipped, rather than zero. Job/step timestamps
and conclusions remain the source for completion and critical-path analysis.
The collector's own fallback assembly, when present, is stored separately
as `lean.fallback_assembly` from its local assembly log; its job is still
running and has no downloadable log or final job duration at collection.

The existing `lean_shard_replay.py --timing prior|observed` modes still use
observed Lean module builds and reconstructed prior timings, not the newly
retained exact planning snapshot or native facets. For future experiments,
use the snapshot's graph, stale set, historical times and settings, compare
the saved assignments against proposed assignments on identical inputs,
and evaluate using the corresponding observed module and native task data.
Report modeled changes separately from measured queue, setup, proof and
assembly wall times. Historical runner contention and missing observations
cannot establish the wall time of an unexecuted alternative plan.

## Planner estimates and timing updates

Unseen modules use the upper quartile of historical timings from at least
8 peers in the same power-of-two source-size bucket, preferring the nearest
namespace. Sparse groups and old snapshots without sizes retain the global
median/default fallback. The snapshot adds `source_bytes` and the actual
`fallback_estimates` for unseen stale modules, so this choice is replayable.
Measured module timings are never replaced by a peer estimate.

CI writes `lean_shards.py times --observations` files with separate `lean`,
`c.o` and `dynlib` components. Manifest updates take the median of duplicate
shard observations for each component, then retain up to three build samples
per component in `timing_history`. The estimate is the sum of component
medians, not whichever artifact happens to be read last. A final assembly
log containing only native work cannot replace the module's full time.
Source, library-membership, or toolchain/options changes start fresh histories; unmeasured
changed modules are not attributed their old source's measurement. Legacy
flat timing files and manifests remain readable. Native-only observations
preserve an unsplittable legacy total until a Lean measurement is available.

Meta imports are recorded separately in snapshot `import_modes`. Lake's
meta trace includes interpreter IR through private transitive imports, even
when the imported module's public `.olean` stays unchanged. Public meta
imports pass those dependencies to ordinary downstream imports; a private
meta import does not become public merely because the same module also has
a public ordinary import. The planner keeps these modes separate and follows
nested `import all` traces too. Old snapshots without import modes remain
readable, but cannot recover this distinction from visibility alone.

The planner also accounts for native shared-library hashes in Lake's traces.
A native module can rebuild when an otherwise unrelated member of a library
it loads changes. Ordinary proof/test libraries use `platformIndependent =
true` and must keep their existing narrower invalidation behavior. Snapshots
retain `precompiled_libraries` and `native_trace_modules` for replay. The
scheduler includes whole-library imports, as selective cache restore already
did, so extra native members participate in work/duplication scores.

Scoped `+Module` targets already resolve correctly. Live tests found no
benefit from prepending native library targets, so the target command remains
unchanged. `test_check_lean_native_invalidation.py` builds a small two-library
fixture with both trace settings and checks the predicted stale set against
actual compilations. The real-cache check used Lean 4.35.0 and the published
cache at revision `85044619e`: an unrelated TCB native-library change rebuilt
`Spec.Cast5`, while an unrelated native-tactics change left an ordinary proof
cached. These are dependency checks, not measured CI speedups.

Metrics add `lean.rebuild_check`. It is `available` only with a verified
same-attempt snapshot containing the stale set. Its `jobs` list records
observed module compilations outside that set, grouped by step, alongside
cache alignment. Missing logs stay unknown, and native facets are excluded.
The check reports discrepancies, not their causes; use subsequent CI runs
to verify the corrected predictions and investigate any remaining unplanned work.

## Version 3: Rust timing observations

The existing `ci-metrics` artifact also retains Rust timing observations.
There are no new jobs, upload steps, artifacts or producer network calls.
The collector still runs in `all-green` under its existing 30-second timeout.
It fetches one log per completed, non-skipped Rust matrix job on PR and
merge-queue runs, sharing the existing eight-worker pool with Lean. The
current full matrix adds 21 log downloads; architecture-filtered PRs add
fewer. Main pushes only build caches, so their Rust logs are not fetched.
A terminal-color rejection can require a second request for a log.

Requests during collection have a five-second timeout and share a 22-second
budget, leaving headroom for parsing and serialization. Failed or timed-out
log requests leave other observations intact. The outer workflow timeout
remains the hard limit: collection can still fail before uploading an artifact.

New fields (existing fields retain their meanings):

| Field | Meaning |
|---|---|
| `jobs[].status` | API job status at the snapshot |
| `collection.collected_at` | UTC snapshot timestamp |
| `collection.jobs_complete` | Whether all observed jobs have completion timestamps |
| `collection.unfinished_job_ids` | Jobs without completion timestamps, normally including `all-green` |
| `collection.finished_runner_s` | Sum of finished, non-skipped job durations; excludes unfinished jobs and is not billed time |
| `collection.missing_log_job_ids` | Finished Lean/Rust jobs whose requested logs were unavailable; excludes Rust cache-only main pushes |
| `rust.jobs[].job_id`, `.name` | Join to the existing API job records |
| `rust.jobs[].tests[]` | `name`, `outcome`, `elapsed_s`, `binary`, `feature_line`, `step` for each explicitly timed test observation |
| `rust.jobs[].feature_runs[]` | `features`, `groups`, `user_s`, `system_s`, `start_offset_s`, `wall_s`, `exit_code` for each CPU-feature line |

Per-test records depend on libtest's `--report-time` output (introduced by
PR #3004); the collector does not enable unstable flags or change test
execution. Untimed or filtered-out zero-duration tests do not become zero
observations. Repeated test names are retained, with binary/step/feature-line
context where the log supplies it. `binary` retains Cargo's identifying log
line rather than assuming a stable path across platforms. Ordered libtest
stdout blocks are matched to Cargo headers, since piped stdout can arrive
after multiple stderr headers. Runner command boundaries keep buffered
output in its producing step when API timestamps share a second. Missing context
is null. An empty list is not proof that no tests ran, and successfully
fetching a log does not establish that GitHub retained it without truncation.

CPU-feature user/system times come from the existing Bash `time` output.
The new `CI_FEATURE_TIME_V1` log record adds line index, start/end timestamps,
scheduling origin (all integer microseconds), and exit code. Bash's built-in
`EPOCHREALTIME` avoids launching clock processes. Offsets are measured from
just before dispatching the lines, not job start; these are wall-clock
observations, subject to host clock adjustments. Invalid/reversed records
leave wall times unknown. Old CPU-only logs retain null wall/offset/exit fields.
The existing CPU timing cache and scheduling inputs are unchanged.

Feature runs overlap, and timed tests may run concurrently. Neither sum is
an elapsed job duration. This snapshot cannot report the collector's own
final duration, final workflow conclusion, or every cancelled attempt.

Import-narrowing reports keep declaration visibility separate from Lake source
dependencies. The latter uses the sharder trace rules, including private IR
behind meta imports, and counts added/removed dependency-reader pairs within
the verification scope. It excludes native-library dependencies and does not
estimate wall time or the rebuilds caused by applying the import edit itself.
