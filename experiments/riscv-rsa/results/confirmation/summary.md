# Native RISC-V RSA experiments

Seven alternating-order rounds; elapsed time per operation. Positive delta means faster. Full raw samples accompany this table.

| Workload | Variant | Bits | Threads | Median µs/op | Paired time reduction, median [min, max] |
|---|---|---:|---:|---:|---:|
| public | base | 2048 | 1 | 126.05 | +0.00% [+0.00, +0.00] |
| public | base | 3072 | 1 | 271.56 | +0.00% [+0.00, +0.00] |
| public | base | 4096 | 1 | 476.48 | +0.00% [+0.00, +0.00] |
| public | combined | 2048 | 1 | 101.92 | +18.81% [+18.40, +21.41] |
| public | combined | 3072 | 1 | 214.16 | +21.17% [+20.97, +21.70] |
| public | combined | 4096 | 1 | 372.57 | +21.92% [+21.38, +22.09] |
| public | pubsquare | 2048 | 1 | 103.33 | +17.96% [+17.17, +20.41] |
| public | pubsquare | 3072 | 1 | 219.06 | +19.42% [+18.79, +19.79] |
| public | pubsquare | 4096 | 1 | 379.40 | +20.30% [+17.59, +20.81] |
| rsa | base | 2048 | 1 | 5221.34 | +0.00% [+0.00, +0.00] |
| rsa | base | 2048 | 4 | 1824.17 | +0.00% [+0.00, +0.00] |
| rsa | base | 3072 | 1 | 15484.17 | +0.00% [+0.00, +0.00] |
| rsa | base | 3072 | 4 | 4017.23 | +0.00% [+0.00, +0.00] |
| rsa | base | 4096 | 1 | 33455.62 | +0.00% [+0.00, +0.00] |
| rsa | base | 4096 | 4 | 8614.13 | +0.00% [+0.00, +0.00] |
| rsa | combined | 2048 | 1 | 5029.68 | +3.78% [+3.23, +5.01] |
| rsa | combined | 2048 | 4 | 1401.74 | +9.36% [-60.73, +36.02] |
| rsa | combined | 3072 | 1 | 14941.09 | +3.37% [+3.14, +5.15] |
| rsa | combined | 3072 | 4 | 4044.79 | -4.19% [-70.52, +6.39] |
| rsa | combined | 4096 | 1 | 32725.61 | +2.69% [+1.20, +3.54] |
| rsa | combined | 4096 | 4 | 9359.22 | -9.70% [-60.30, +2.95] |
| rsa | pipeline | 2048 | 1 | 5184.31 | +0.88% [-0.42, +1.80] |
| rsa | pipeline | 2048 | 4 | 1812.56 | +3.87% [-54.58, +33.82] |
| rsa | pipeline | 3072 | 1 | 15254.85 | +1.48% [+0.22, +2.87] |
| rsa | pipeline | 3072 | 4 | 3893.43 | -0.04% [-43.37, +6.22] |
| rsa | pipeline | 4096 | 1 | 33089.70 | +1.09% [+0.39, +1.36] |
| rsa | pipeline | 4096 | 4 | 10812.28 | -28.30% [-35.49, +0.80] |
| rsa | pubsquare | 2048 | 1 | 5230.13 | +0.37% [-2.46, +1.67] |
| rsa | pubsquare | 2048 | 4 | 1773.07 | +2.40% [-38.12, +33.91] |
| rsa | pubsquare | 3072 | 1 | 15375.73 | +0.70% [-0.08, +2.57] |
| rsa | pubsquare | 3072 | 4 | 4014.65 | -3.41% [-44.93, +5.39] |
| rsa | pubsquare | 4096 | 1 | 33457.32 | +0.19% [-0.78, +1.04] |
| rsa | pubsquare | 4096 | 4 | 10718.23 | -24.73% [-60.56, +0.22] |
| rsa | select | 2048 | 1 | 5119.71 | +2.21% [+1.78, +2.42] |
| rsa | select | 2048 | 4 | 1733.16 | +4.99% [-40.51, +27.09] |
| rsa | select | 3072 | 1 | 15205.49 | +1.65% [+0.47, +3.32] |
| rsa | select | 3072 | 4 | 4203.34 | -5.95% [-49.23, +6.00] |
| rsa | select | 4096 | 1 | 33131.40 | +1.05% [+0.56, +1.53] |
| rsa | select | 4096 | 4 | 11156.49 | -29.51% [-41.38, +2.10] |

The C one-row control and C two-row candidate share the same call wrapper. Comparing them isolates the row-fusion idea better than comparing either directly with the emitted inline baseline. C column squaring also includes a call wrapper. No result is a formal proof or a complete constant-time audit.
