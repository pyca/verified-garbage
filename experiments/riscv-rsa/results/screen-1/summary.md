# Native RISC-V RSA experiments

Seven alternating-order rounds; elapsed time per operation. Positive delta means faster. Full raw samples accompany this table.

| Workload | Variant | Bits | Threads | Median µs/op | Paired time reduction, median [min, max] |
|---|---|---:|---:|---:|---:|
| micro | base_mont | 1024 | 1 | 1.88 | +0.00% [+0.00, +0.00] |
| micro | base_mont | 1536 | 1 | 4.01 | +0.00% [+0.00, +0.00] |
| micro | base_mont | 2048 | 1 | 6.90 | +0.00% [+0.00, +0.00] |
| micro | base_square | 1024 | 1 | 1.61 | +0.00% [+0.00, +0.00] |
| micro | base_square | 1536 | 1 | 3.31 | +0.00% [+0.00, +0.00] |
| micro | base_square | 2048 | 1 | 5.52 | +0.00% [+0.00, +0.00] |
| micro | column_square | 1024 | 1 | 3.58 | -122.22% [-127.91, -118.15] |
| micro | column_square | 1536 | 1 | 7.62 | -130.07% [-132.54, -126.42] |
| micro | column_square | 2048 | 1 | 13.00 | -135.36% [-136.75, -131.99] |
| micro | one_mont | 1024 | 1 | 1.86 | +1.17% [+0.18, +2.36] |
| micro | one_mont | 1536 | 1 | 4.00 | +0.23% [-0.89, +0.38] |
| micro | one_mont | 2048 | 1 | 7.39 | -7.24% [-14.59, -6.65] |
| micro | pair_mont | 1024 | 1 | 1.84 | +1.53% [+1.26, +3.27] |
| micro | pair_mont | 1536 | 1 | 3.86 | +3.00% [+2.62, +3.66] |
| micro | pair_mont | 2048 | 1 | 6.63 | +3.97% [+3.58, +4.15] |
| micro | pair_square | 1024 | 1 | 1.65 | -2.21% [-2.49, -1.39] |
| micro | pair_square | 1536 | 1 | 3.39 | -2.56% [-5.06, -1.74] |
| micro | pair_square | 2048 | 1 | 5.69 | -2.84% [-3.43, -2.32] |
| micro | two_mont | 1024 | 1 | 2.03 | -8.16% [-11.78, -3.42] |
| micro | two_mont | 1536 | 1 | 4.18 | -4.70% [-5.16, -3.99] |
| micro | two_mont | 2048 | 1 | 7.24 | -4.79% [-5.32, -3.97] |
| rsa | base | 2048 | 1 | 5213.08 | +0.00% [+0.00, +0.00] |
| rsa | base | 2048 | 4 | 2182.89 | +0.00% [+0.00, +0.00] |
| rsa | base | 4096 | 1 | 33568.48 | +0.00% [+0.00, +0.00] |
| rsa | base | 4096 | 4 | 13161.53 | +0.00% [+0.00, +0.00] |
| rsa | column | 2048 | 1 | 9297.27 | -78.05% [-79.83, -76.29] |
| rsa | column | 2048 | 4 | 3649.73 | -81.02% [-104.52, -7.38] |
| rsa | column | 4096 | 1 | 64242.88 | -91.34% [-93.86, -91.05] |
| rsa | column | 4096 | 4 | 23294.37 | -80.94% [-95.56, -39.94] |
| rsa | one | 2048 | 1 | 5241.21 | -0.79% [-2.09, +0.57] |
| rsa | one | 2048 | 4 | 2384.50 | -6.66% [-30.52, +17.90] |
| rsa | one | 4096 | 1 | 34102.91 | -1.75% [-2.57, -1.44] |
| rsa | one | 4096 | 4 | 13359.99 | +4.09% [-15.42, +27.46] |
| rsa | pair | 2048 | 1 | 5273.13 | -1.37% [-1.96, +0.27] |
| rsa | pair | 2048 | 4 | 2153.82 | -3.09% [-18.43, +9.62] |
| rsa | pair | 4096 | 1 | 33700.90 | -0.56% [-1.58, -0.03] |
| rsa | pair | 4096 | 4 | 12936.98 | +1.54% [-5.90, +30.11] |
| rsa | two | 2048 | 1 | 5295.29 | -1.58% [-2.14, -0.17] |
| rsa | two | 2048 | 4 | 2159.20 | +1.09% [-32.44, +39.83] |
| rsa | two | 4096 | 1 | 33958.65 | -1.16% [-3.55, -0.24] |
| rsa | two | 4096 | 4 | 12759.95 | +6.42% [-12.09, +29.45] |

The C one-row control and C two-row candidate share the same call wrapper. Comparing them isolates the row-fusion idea better than comparing either directly with the emitted inline baseline. C column squaring also includes a call wrapper. No result is a formal proof or a complete constant-time audit.
