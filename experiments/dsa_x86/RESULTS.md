# Native unproven prototype results

No proof or production-readiness claim. Verified branch: `dsa-x86-generation` at `784473529`.

## Sweep 1

Run: https://github.com/pyca/verified-garbage/actions/runs/39511238676
Commit: `c39879869`. Native i686, Intel Xeon Platinum 8573C, OpenSSL 3.5.7.
Three alternating-order rounds, 25 samples per key-generation workload. Values are medians of round medians.
Compare within this run: the earlier verified-branch comparison ran on AMD EPYC 7763.

| p/q bits | Baseline ms | Best prototype ms | OpenSSL ms | Prototype/OpenSSL |
|---|---:|---:|---:|---:|
| 1024/160 | 2.1301 | 0.8891 (dwpr8) | 0.8064 | 1.102 |
| 2048/160 | 8.0086 | 3.3737 (dwpr8) | 3.0730 | 1.098 |
| 2048/224 | 10.5884 | 4.3079 (dwpr4) | 4.1261 | 1.044 |
| 2048/256 | 12.0671 | 4.7031 (dwpr8) | 4.6758 | 1.006 |
| 3072/256 | 26.8679 | 10.6092 (dwpr8) | 10.4553 | 1.015 |

Four/eight-word chunks outperform full expansion. Prefer four-word chunks provisionally for code size; eight-word chunks gain only about 0–2% in key generation. Fixed-tape parameter searches improve 41–46%; these are not OpenSSL comparisons. The next sweeps test squares, word-wise masked scans, and public-modulus setup fast paths.

Raw tables and logs are retained in the run artifact `unproven-dsa-results`.
