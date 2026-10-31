# The `ci-metrics` document

Every CI run tries to upload `ci-metrics.json` (`ci/ci_metrics.py collect`,
in `all-green`) as its `ci-metrics` artifact, kept for 30 days. The
one-day `lean-plan` artifact and the shards' outputs expire sooner: the
metrics embed the plan, not the compiled outputs. Nothing archives the
metrics outside Actions, so download them before the 30 days are up if a
study needs a longer history ([collecting.md](collecting.md)).

Collection is best effort and never blocks the CI verdict: a cancelled run
or a collector timeout can leave no artifact, so the retained sample is not
every CI attempt. The collector runs under a 30-second timeout; its log
requests time out after five seconds each and share a 22-second budget.
A failed request leaves the other observations intact.

The document's `version` is 3. Each version only added fields, so `summary`
and `lean_shard_replay.py` read older documents; a field an older document
lacks is absent, not empty.

## Top level

| Field | Meaning |
|---|---|
| `version` | The schema's version |
| `run` | `id`, `run_attempt`, `event`, `head_branch`, `head_sha`, `created_at`, `run_started_at`, `base_ref` |
| `jobs[]` | Every job and step: queue, start and finish times, conclusion, runner; `status` is the API status at the snapshot |
| `collection.collected_at` | UTC time of the snapshot |
| `collection.jobs_complete` | Whether every job has a completion time |
| `collection.unfinished_job_ids` | Jobs without one, normally including `all-green` itself |
| `collection.finished_runner_s` | Sum of finished, non-skipped job durations: not billed time, and without unfinished jobs |
| `collection.missing_log_job_ids` | Finished Lean and Rust jobs whose logs were unavailable (not Rust jobs of `main` pushes, whose logs are not fetched) |
| `rust.jobs[]` | Rust timing observations (below) |
| `lean.plan` | The plan's summary: `targets`, `owner`, rounded `loads`, estimated `stale`/`work`, `edited` |
| `lean.planning` | The full planning snapshot (below) |
| `lean.jobs[]` | Each Lean job: `name`, `job_id`, `phases`, `restored`, `restored_planned`, `built`, `facets` |
| `lean.missing_logs` | Finished Lean jobs whose logs could not be read |
| `lean.duplicate_work` | Lean module time the shards built more than once (native facets excluded) |
| `lean.rebuild_check` | Modules built that the plan did not predict (below) |
| `lean.fallback_assembly` | The collector's own fallback assembly, from its local log, when there is one |

## Lean jobs

`phases` holds named phase wall times, null when a phase was absent or
skipped (not zero). `restored` is the cache key the job restored, and
`restored_planned` whether it is the plan's build or the sources' own.

`built` holds, per step, each Lean module the job built and its time.
`facets` holds the native work separately, under full names such as
`A:c.o`, `A:dynlib` and `NativeTactics:shared`. Native facets run in
parallel with module builds, so summing task durations does not give
elapsed time. The manifest's estimate of a module already includes its
native facets: do not add them again.

A missing build record is not evidence that a module came from the cache
when the job failed, its log is missing, or collection was incomplete. The
job and step timestamps and conclusions are the source for completion and
critical-path analysis.

`fallback_assembly` comes from the collector's local log: its job is still
running at collection, so it has no downloadable log or final duration.

## Planning snapshot

`lean.planning.status` is:

* `available`: the plan's embedded run ID and attempt match this run's;
* `different_attempt`: a plan kept from an earlier attempt (rerunning only
  the failed jobs, say);
* `unverified`: a plan without matching provenance;
* `unavailable`: with an error category;
* `not_collected`: the caller did not request the artifact.

A missing plan never removes the job metrics. `planning` also has the
source `artifact_id` when known, and the complete `plan`, whose
`diagnostics` hold:

* the planner's version and source SHA-256, the canonical manifest SHA-256,
  the originating run and attempt, and the planning time (without JSON
  serialization);
* the exact import graph, `import_modes` (ordinary and meta imports kept
  apart), module visibility, `precompiled_libraries` and
  `native_trace_modules`, the current and manifest build inputs, and the
  complete map of historical module times the planner used, so scheduling
  experiments need neither old pull requests' git objects nor today's graph
  or cache (the source code itself is not kept);
* the exact stale modules, how many have historical times, the fallback
  time, `source_bytes` and the `fallback_estimates` of unseen stale modules,
  and the model's constants, including parallelism and overhead;
* the candidate shard counts: solo and every count tried, finish and work
  scores for the fully scored ones, and why the others were pruned (a pruned
  candidate's finish is not scored);
* the final score after refinement, and each shard's module assignment,
  including duplicated dependencies (an empty list is a solo build, not one
  that builds nothing).

How the planner uses these is in `ci/lean_shards.py` (`timing_estimates`,
`manifest`, `reads`).

## Rebuild check

`lean.rebuild_check` is `available` only with a verified same-attempt
snapshot that has the stale set. Its `jobs` list records, by step, the
modules compiled outside that set, with the cache restore each job made.
Missing logs stay unknown, and native facets are left out. It reports
discrepancies, not their causes.

## Rust jobs

Each of `rust.jobs[]` is fetched from one completed, non-skipped Rust job
of a pull request or merge-queue run.

| Field | Meaning |
|---|---|
| `job_id`, `name` | Join to `jobs[]` |
| `tests[]` | Each timed test: `name`, `outcome`, `elapsed_s`, `binary`, `feature_line`, `step` |
| `feature_runs[]` | Each CPU-feature line: `features`, `groups`, `user_s`, `system_s`, `start_offset_s`, `wall_s`, `exit_code` |

Test times come from libtest's `--report-time` output; the collector does
not change how tests run. Untimed or filtered-out tests are left out, not
recorded as zero, and a repeated test name is kept with its binary, step
and feature line where the log gives them (null otherwise). `binary` is
Cargo's line naming the binary, not a path. An empty list is not proof that
no tests ran.

`user_s` and `system_s` come from Bash's `time`; the `CI_FEATURE_TIME_V1`
log record adds each line's start and end (from just before the lines are
dispatched, not from the job's start) and exit code. These are wall-clock
readings: an invalid or reversed record leaves the wall time unknown, and
older logs have null wall, offset and exit fields. Feature lines overlap and
timed tests can run concurrently, so neither sum is the job's elapsed time.

## Replaying a plan

`lean_shard_replay.py --timing prior|observed` replays observed module
builds and reconstructed prior timings, not the planning snapshot. To test
a scheduling change, use the snapshot's graph, stale set, historical times
and settings, compare its saved assignments with the proposed ones on the
same inputs, and evaluate both with the observed module and native times.
Report modeled changes apart from measured queue, setup, proof and assembly
times: past runner contention and missing observations cannot establish the
wall time of a plan that never ran.
