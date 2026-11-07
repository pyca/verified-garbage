# Native RISC-V RSA experiments

Seven alternating-order rounds; elapsed time per operation. Positive delta means faster. Full raw samples accompany this table.

| Workload | Variant | Bits | Threads | Median µs/op | Paired time reduction, median [min, max] |
|---|---|---:|---:|---:|---:|
| rsa | base | 4096 | 1 | 33434.23 | +0.00% [+0.00, +0.00] |
| rsa | base | 4096 | 4 | 11609.65 | +0.00% [+0.00, +0.00] |
| rsa | combined | 4096 | 1 | 32459.21 | +2.79% [+1.55, +4.71] |
| rsa | combined | 4096 | 4 | 10416.78 | +4.19% [-6.02, +24.91] |
| rsa | pubsquare | 4096 | 1 | 33327.29 | +0.19% [-0.15, +0.70] |
| rsa | pubsquare | 4096 | 4 | 11302.43 | +5.10% [-24.21, +15.49] |

The C one-row control and C two-row candidate share the same call wrapper. Comparing them isolates the row-fusion idea better than comparing either directly with the emitted inline baseline. C column squaring also includes a call wrapper. No result is a formal proof or a complete constant-time audit.
