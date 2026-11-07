# RSA-4096 concurrency diagnostic

Native run [42395215555](https://github.com/pyca/verified-garbage/actions/runs/42395215555).
Worker CPU time is measured using `CLOCK_THREAD_CPUTIME_ID` and summed across
workers, separately from elapsed wall time. The table reports per-operation
medians and paired-round reductions; positive percentages mean less time.

| Variant | Workers | Wall ms/op | Worker CPU ms/op | Paired CPU reduction: median [min, max] |
|---|---:|---:|---:|---:|
| base | 1 | 33.434 | 33.357 | +0.00% [+0.00, +0.00] |
| base | 4 | 11.610 | 33.575 | +0.00% [+0.00, +0.00] |
| combined | 1 | 32.459 | 32.394 | +2.91% [+2.66, +3.37] |
| combined | 4 | 10.417 | 32.530 | +3.12% [+2.65, +3.66] |
| pubsquare | 1 | 33.327 | 33.282 | +0.07% [-0.32, +0.48] |
| pubsquare | 4 | 11.302 | 33.482 | +0.34% [-0.33, +0.85] |

The combination reduces four-worker CPU time in all seven rounds (2.65–3.66%,
median 3.12%), close to its single-thread CPU reduction (median 2.91%). The
public-square-only control changes private-operation CPU time by less than 1%,
yet its paired four-worker wall-time changes range from a 24% regression to a
15% reduction. This supports treating the earlier large wall-time swings as
inconclusive rather than attributing them to the arithmetic change. The exact
source of runner scheduling/availability variation is not established.

Four-worker combined wall-time reductions still range from -6.02% to +24.91%;
there is no robust four-worker wall-throughput claim. No CPU affinity or runner
configuration was changed to obtain these results. The previous single-thread
wall-time evidence and this CPU-time evidence are different metrics.
