# Choosing Lean build shards

The planner minimizes repeated module work among plans whose estimated finish
is within 5% of the fastest candidate. Candidates include the single-runner
build and every useful count from 2 through 12. A fixed 90-second incremental
overhead applies to sharded candidates. Counts are no longer capped by
`ceil(module_work / 800)`.

## Rebuild scope and build dependencies are different graphs

`reads` still determines invalidation: a private import can stop a source
change from rebuilding downstream modules. Nothing in this change alters
that rule or the final whole-project proof check, audit, tests, or emitter.

After finding the stale modules, target the ones that no other stale module
imports, directly or transitively. These targets cover every stale module.
Their shards build the **full import closure**, including private imports;
private imports limit invalidation, not what is needed to build a target.

For example, if unchanged `Top` imports `Left` and `Right`, and private
imports mean only `Left` and `Right` need rebuilding, the old whole-project
sink is `Top`. Targeting `Top` bundles both rebuilds together. Targeting
`Left` and `Right` lets separate runners build them when that saves enough.
For a full rebuild, these targets are the same whole-project sinks as before.

## Estimate and choose a plan

1. Keep the existing closure-aware greedy packing as a fast starting point.
   Its lower bound combines total work / 5.4 with the longest import chain,
   and its assignment cost penalizes imports built again on another runner.
2. Simulate each packing. Modules wait for their imports, and ready modules
   on the longest remaining chains run first. Six concurrent modules share
   the observed throughput of 5.4; fewer than six run at their full measured
   rate. This includes serial phases around parallel work, which the old
   `max(work / 5.4, longest_chain)` bound could miss.
3. Compare the slowest simulated shard plus overhead with a solo build of
   the same affected closure. Skip sharding if even the solo build is shorter
   than the overhead, or if there is only one rebuild target.
4. Within 5% of the fastest finish, prefer the lowest total module work,
   counting imports on every runner that builds them. Break ties by fewer
   runners, then lower latency. Solo takes part in this same comparison.
5. Refine the selected packing by moving targets to reuse shared imports.
   Rank moves by work saved, reject impossible moves with the lower bound,
   and simulate the two affected shards before accepting. Never exceed the
   selected finish-time budget or leave a shard without targets. The search
   permits at most 16 simulated move attempts and three accepted moves.

Summation, target ordering, simulation ties, and refinement order are
deterministic. The plan's JSON interface and output ownership remain the same.
`lean_closure.py` uses the same simulator when scoring import changes, including
single-runner builds, which now report their time and zero duplicate work.

## Historical evaluation

The initial evaluation used 28 retained successful merge-queue runs and their
exact historical source graphs, against baseline
`a5a0afb3825d658d9696bdbc353cdd12ce8e7fb4`. There were 63 measured shard builds.
The simulator's mean absolute relative error on those assignments was 6.0%,
with a median simulated/actual ratio of 1.017. The largest underestimate was
22.5%; the largest overestimate was 8.6%. These are calibration measurements,
not evidence that every alternative packing will perform that closely.

With each run's observed module times supplied identically to both planners:

| Aggregate modeled quantity | Baseline | Proposed | Change |
| --- | ---: | ---: | ---: |
| Module work | 99,389 s | 95,569 s | -3.8% |
| Duplicate module work | 24,340 s | 20,804 s | -14.5% |
| Finish time, summed across runs | 6,539 s | 6,614 s | +1.2% |

The small latency tradeoff is intentional: reuse imports within the existing
5% tolerance instead of buying every marginal second with repeated work.
A second replay selected plans using only timing observations from Lean jobs
finished before each run started, and evaluated them using that run's observed
times:

| Aggregate modeled quantity | Baseline | Proposed | Change |
| --- | ---: | ---: | ---: |
| Module work | 95,796 s | 94,321 s | -1.5% |
| Duplicate module work | 20,747 s | 19,556 s | -5.7% |
| Finish time, summed across runs | 7,459 s | 7,008 s | -6.0% |

This prior-observation replay still uses the observed rebuild scope and cannot
reconstruct the exact cached manifest. Early runs have sparse or absent timing
history: one run with no earlier module observations regressed by 8.6% in the
evaluation. This is stronger evidence than hindsight alone, but still a model
comparison rather than a measured end-to-end improvement.

In the hindsight replay, the median scheduling time was 0.20 s and the maximum 2.37 s,
excluding graph loading and closure construction. A cold plan for the
19,314-module checkout, including graph loading, took 11.8 s in the development
environment. These are observations, not performance limits.

Four illustrative runs from the original 15-merge investigation:

| PR | Run | Recorded shards | Baseline replay shards | Proposed replay shards |
| --- | --- | ---: | ---: | ---: |
| #2942 | 39494407343 | 8 | 9 | 8 |
| #2941 | 39494457169 | 7 | 9 | 9 |
| #2943 | 39494505756 | 8 | 6 | 6 |
| #2948 | 39510175698 | 9 | 12 | 12 |

The recorded counts used the manifest available at the time; hindsight replay
uses observed times. The differences between those columns must not be
attributed entirely to the new algorithm. Narrow rebuilds do not imply a
uniformly lower shard count: some remain solo, dependency-limited builds need
fewer shards, and broad rebuilds can still use twelve.

### Reproduce

Put retained `ci-metrics` artifacts in `.ci-metrics/<run-id>.json`, as with
`ci/ci_metrics.py fetch`. For an individual run, for example:

```sh
mkdir -p .ci-metrics/download
gh run download 39494505756 --repo pyca/verified-garbage \
  --name ci-metrics --dir .ci-metrics/download
mv .ci-metrics/download/ci-metrics.json .ci-metrics/39494505756.json
python3 ci/lean_shard_replay.py .ci-metrics \
  --baseline-ref a5a0afb3825d658d9696bdbc353cdd12ce8e7fb4 --timing observed \
  > .ci-metrics/replay-observed.json
python3 ci/lean_shard_replay.py .ci-metrics \
  --baseline-ref a5a0afb3825d658d9696bdbc353cdd12ce8e7fb4 --timing prior \
  > .ci-metrics/replay-prior.json
```

The 28 run IDs were:

```text
39451469219 39451981506 39452069158 39452119592 39459266195 39467869884
39473493182 39475905878 39475960495 39475963422 39476045583 39480901904
39488473175 39494340291 39494407343 39494457169 39494505756 39505642596
39510175698 39513566193 39515204845 39515205977 39515249538 39515278076
39516004855 39519490128 39519492767 39524126110
```

`observed` mode evaluates partitioning and counts with hindsight. `prior`
mode chooses plans using only module observations from Lean jobs completed
before the run began, then evaluates those plans using observed times. It
reports the fraction of rebuilt modules with earlier observations. Both
modes use the observed rebuild set; neither reconstructs the exact cached
manifest or measures a new build. Runs with failed Lean jobs are excluded.
Missing historical git objects cause an error rather than substitution of
the current graph.

Retained metrics omit native compile/link facets, and the observed rebuild set
can differ from the planned set. Replay estimates exclude queue fluctuations,
artifact size effects, and planner time. Module timing history, throughput,
and overhead retain their existing production behavior/constants; this small
sample does not justify fitting a new queue penalty for each count. Validate
the selected plans in live CI before claiming end-to-end speedups.

### Checks

The Python suite covers serial barriers, partially occupied runners, private
invalidation boundaries, cached modules between stale modules, full rebuild
coverage, empty-target prevention, solo-versus-sharded choices, and refinement
that respects its latency budget. Random DAG tests check closure coverage;
plans were also compared under four Python hash seeds. All 287 Python tests
and the repository's eight structural/provenance checks passed. No Lean or
Rust implementation changed, and no proof rebuild was needed for these checks.
