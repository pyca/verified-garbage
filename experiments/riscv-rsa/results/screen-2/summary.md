# Native RISC-V RSA experiments

Seven alternating-order rounds; elapsed time per operation. Positive delta means faster. Full raw samples accompany this table.

| Workload | Variant | Bits | Threads | Median µs/op | Paired time reduction, median [min, max] |
|---|---|---:|---:|---:|---:|
| micro | base_mont | 1024 | 1 | 1.88 | +0.00% [+0.00, +0.00] |
| micro | base_mont | 1536 | 1 | 3.99 | +0.00% [+0.00, +0.00] |
| micro | base_mont | 2048 | 1 | 6.88 | +0.00% [+0.00, +0.00] |
| micro | base_square | 1024 | 1 | 1.64 | +0.00% [+0.00, +0.00] |
| micro | base_square | 1536 | 1 | 3.32 | +0.00% [+0.00, +0.00] |
| micro | base_square | 2048 | 1 | 5.49 | +0.00% [+0.00, +0.00] |
| micro | column_square | 1024 | 1 | 3.46 | -110.91% [-113.97, -105.95] |
| micro | column_square | 1536 | 1 | 7.39 | -123.13% [-123.34, -119.15] |
| micro | column_square | 2048 | 1 | 12.53 | -128.07% [-128.97, -127.64] |
| micro | one_mont | 1024 | 1 | 1.85 | +1.58% [+0.48, +3.30] |
| micro | one_mont | 1536 | 1 | 3.98 | +0.16% [-0.21, +0.42] |
| micro | one_mont | 2048 | 1 | 7.28 | -6.04% [-10.12, -3.72] |
| micro | pair_mont | 1024 | 1 | 1.83 | +2.54% [-9.00, +4.87] |
| micro | pair_mont | 1536 | 1 | 3.87 | +2.96% [+2.31, +3.58] |
| micro | pair_mont | 2048 | 1 | 6.61 | +3.89% [+3.69, +5.78] |
| micro | pair_square | 1024 | 1 | 1.67 | -1.89% [-2.85, +0.40] |
| micro | pair_square | 1536 | 1 | 3.39 | -2.16% [-3.31, -0.66] |
| micro | pair_square | 2048 | 1 | 5.65 | -2.74% [-3.84, -2.43] |
| micro | pipeline_square | 1024 | 1 | 1.57 | +4.04% [+2.89, +6.43] |
| micro | pipeline_square | 1536 | 1 | 3.26 | +1.71% [+1.25, +3.30] |
| micro | pipeline_square | 2048 | 1 | 5.44 | +0.93% [-0.02, +1.43] |
| micro | two_mont | 1024 | 1 | 2.10 | -11.91% [-13.20, -4.17] |
| micro | two_mont | 1536 | 1 | 4.18 | -4.74% [-6.58, -3.24] |
| micro | two_mont | 2048 | 1 | 7.18 | -4.39% [-4.73, -2.37] |
| rsa | base | 2048 | 1 | 5221.02 | +0.00% [+0.00, +0.00] |
| rsa | base | 2048 | 4 | 1907.18 | +0.00% [+0.00, +0.00] |
| rsa | base | 3072 | 1 | 15456.04 | +0.00% [+0.00, +0.00] |
| rsa | base | 3072 | 4 | 6364.13 | +0.00% [+0.00, +0.00] |
| rsa | base | 4096 | 1 | 33725.95 | +0.00% [+0.00, +0.00] |
| rsa | base | 4096 | 4 | 11871.34 | +0.00% [+0.00, +0.00] |
| rsa | montpair | 2048 | 1 | 5170.10 | +1.02% [-0.44, +2.53] |
| rsa | montpair | 2048 | 4 | 1843.90 | +4.02% [-8.63, +31.45] |
| rsa | montpair | 3072 | 1 | 15370.50 | +0.46% [-6.28, +3.77] |
| rsa | montpair | 3072 | 4 | 6809.91 | -0.58% [-32.84, +9.23] |
| rsa | montpair | 4096 | 1 | 33710.16 | +0.56% [-2.25, +1.45] |
| rsa | montpair | 4096 | 4 | 12417.09 | -1.63% [-7.28, +19.04] |
| rsa | pipeline | 2048 | 1 | 5152.97 | +1.16% [+0.56, +4.07] |
| rsa | pipeline | 2048 | 4 | 1816.88 | +5.08% [-0.00, +42.24] |
| rsa | pipeline | 3072 | 1 | 15336.46 | +0.17% [-4.16, +5.29] |
| rsa | pipeline | 3072 | 4 | 6285.67 | +1.23% [-26.89, +11.66] |
| rsa | pipeline | 4096 | 1 | 33701.49 | -0.03% [-1.12, +1.81] |
| rsa | pipeline | 4096 | 4 | 12382.81 | +3.62% [-41.98, +12.64] |
| rsa | select | 2048 | 1 | 5083.39 | +2.27% [+1.32, +5.48] |
| rsa | select | 2048 | 4 | 1823.63 | +2.13% [-22.31, +42.79] |
| rsa | select | 3072 | 1 | 15399.50 | +0.85% [-5.00, +1.65] |
| rsa | select | 3072 | 4 | 6607.47 | -0.55% [-13.88, +13.44] |
| rsa | select | 4096 | 1 | 33499.78 | +0.58% [-2.77, +1.50] |
| rsa | select | 4096 | 4 | 12216.41 | +2.27% [-25.82, +21.56] |

The C one-row control and C two-row candidate share the same call wrapper. Comparing them isolates the row-fusion idea better than comparing either directly with the emitted inline baseline. C column squaring also includes a call wrapper. No result is a formal proof or a complete constant-time audit.
