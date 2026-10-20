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

## Full stack and wider public windows

Run: https://github.com/pyca/verified-garbage/actions/runs/39515283992
Commit: `eaa147c6f`. Native i686, AMD EPYC 9V45, OpenSSL 3.5.7.
The full stack beats OpenSSL in all five key-generation cases on this machine.

| p/q bits | Full stack, 4-bit public windows ms | Full stack, wider public windows ms | OpenSSL ms |
|---|---:|---:|---:|
| 1024/160 | 0.4633 | 0.4619 | 0.5593 |
| 2048/160 | 1.7454 | 1.7198 | 2.4045 |
| 2048/224 | 2.3600 | 2.3653 | 3.2563 |
| 2048/256 | 2.5524 | 2.6041 | 3.6491 |
| 3072/256 | 5.8064 | 5.8623 | 8.3499 |

Wider windows affect only parameter generation; keygen differences are run noise
and/or code placement, not an algorithm change. Fixed parameter searches improve
another 1.9%, 5.8%, and 6.4% over the four-bit-public-window stack.
DSA symbol bytes: baseline 524,288; full stack 670,336; wider windows 704,512.
The direct-RSA-helper alternative is being measured separately for code size.

| Parameter bits | Wider-window stack median ms (95% bootstrap CI) | OpenSSL median ms (95% bootstrap CI) |
|---|---:|---:|
| 1024 | 233.4 (182.0–277.3) | 191.8 (118.5–327.7) |
| 2048 | 1116.6 (885.7–2016.9) | 2151.8 (1121.5–2859.6) |
| 3072 | 8460.7 (7033.7–14547.1) | 10076.5 (8231.3–13372.5) |

Ten random searches per case are insufficient to resolve the 1024-bit gap.
A focused 100-sample follow-up also tests windowing the padded 192-bit exponent
used by the 160-bit subgroup-prime test. Do not claim the all-workload OpenSSL
submission gate is met from this run.
