---
name: ci-metrics
description: "Use when asked to check or analyze CI: job and step times, shard balance, duplicate work, failed cache restores, slow jobs, or the Lean build's plan."
---

# Measuring CI

When asked to check or analyze CI metrics, follow
[Collecting and analyzing CI metrics](collecting.md). Start with the
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
limits](schema.md) before comparing runs or interpreting missing data.
