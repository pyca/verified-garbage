# Historical Lean planning data

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
and skips files already present. Collection is best effort and does not
block the CI verdict; a cancelled run or collector timeout may have no
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
