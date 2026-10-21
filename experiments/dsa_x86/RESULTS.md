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

## Earlier square/table variants on EPYC 7763

Run: https://github.com/pyca/verified-garbage/actions/runs/39513288946
Commit: `5e1c48c43`. Native i686, AMD EPYC 7763, OpenSSL 3.5.7.
This sweep predates the setup fast path and deferred-carry square.

- Four-word rows: 646,784 DSA symbol bytes; full expansion: 1,497,152 bytes.
  Full expansion is only 1.6–3.3% faster on this CPU, unlike the Intel sweep.
- Register-accumulating private table scans improve keygen by less than 1%.
- The first square's full high-word carry scans regress keygen by about 4–7%.
  Expanding its outer loop adds code without recovering the loss.
- Neither earlier combination beats OpenSSL keygen on this older CPU.
  Do not extrapolate the newer EPYC's result to this machine.

The initial square variants are rejected. The final design must be evaluated
using the corrected deferred-carry square and setup fast paths, or the compact
shared-RSA alternative. Full raw results are retained with the run.

## Corrected setup and square isolation on Intel

Run: https://github.com/pyca/verified-garbage/actions/runs/39514892425
Commit: `308e27f4d`. Native i686, Intel Xeon Platinum 8573C.
The fast setup removes about 20–25% of keygen latency after the initial stack;
corrected squaring adds about 3–6%. The four-word-row full stack beats OpenSSL
keygen by 18–22%, with 670,336 DSA bytes. Full row expansion roughly doubles its
code without improving the large keygen cases. Fast setup has little impact on
fixed parameter searches, where setup is amortized across many primality rounds.

## Shared RSA helper on the original EPYC 7763

Run: https://github.com/pyca/verified-garbage/actions/runs/39516177538
Commit: `b4f24f53d`. Native i686, AMD EPYC 7763.

| p/q bits | Full stack ms | Shared RSA ms | OpenSSL ms |
|---|---:|---:|---:|
| 1024/160 | 0.7457 | 0.9232 | 0.6274 |
| 2048/160 | 2.8295 | 3.4273 | 2.4007 |
| 2048/224 | 3.8049 | 4.6242 | 3.2296 |
| 2048/256 | 4.2901 | 5.2169 | 3.6424 |
| 3072/256 | 9.4601 | 11.6317 | 8.1393 |

DSA bytes: verified baseline 524,288; full stack 704,512; shared RSA 530,944.
Direct reuse saves 24.6% of the full stack's DSA code, but costs 21–24% keygen
latency. The full stack is still 16–19% slower than OpenSSL on this CPU.
Random parameter medians for full stack/OpenSSL were 300.5/210.5 ms,
2536.7/2019.7 ms, and 13278.6/9260.6 ms (10 samples; wide intervals).

## 100-sample 1024-bit parameter comparison

Run: https://github.com/pyca/verified-garbage/actions/runs/39517098507
Commit: `60f20a6dd`. Native i686, AMD EPYC 9V74.

| Variant | Median ms | 95% bootstrap CI ms |
|---|---:|---:|
| OpenSSL | 154.084 | 142.713–175.587 |
| Full stack | 280.096 | 256.838–304.545 |
| Also window the padded subgroup exponent | 263.057 | 239.490–305.663 |

The subgroup-window change only improves the fixed 1024-bit search by 0.3%,
so its random-search median difference is not a convincing incremental win.
The 1024-bit gap against OpenSSL is real. Full-stack keygen is 12–18% slower
than OpenSSL on this CPU too. The portable OpenSSL submission gate is unmet.
The next experiment chunks the square's triangular inner loop, retaining a
compact outer loop and comparing four/eight-product chunks.

## Seventh native sweep: chunked triangular square

Run [39519470801](https://github.com/pyca/verified-garbage/actions/runs/39519470801),
commit `0ebfba6c9`, AMD EPYC 7763. Three alternating keygen rounds;
100 random 1024-bit parameter samples per candidate.

| Candidate | 1024/160 ms | 2048/160 | 2048/224 | 2048/256 | 3072/256 | DSA bytes |
|---|---:|---:|---:|---:|---:|---:|
| OpenSSL | .6265 | 2.3981 | 3.2034 | 3.6382 | 8.1427 | — |
| Previous stack | .7462 | 2.8275 | 3.8069 | 4.2874 | 9.4550 | 708736 |
| Square chunk 4 | .7325 | 2.7204 | 3.6536 | 4.1203 | 9.0578 | 747456 |
| Square and row chunk 8 | .7269 | 2.6907 | 3.6108 | 4.0616 | 8.9604 | 832768 |

Chunking improves keygen 2–5%, but remains 10–16% slower than OpenSSL.
The larger chunk has a weak code-size tradeoff: another 85 KB for about 1%.
Fixed-search parameter times improve 2–5%. Random 1024-bit medians:
OpenSSL 172.473 ms (95% CI 158.479–206.022), previous stack 268.868
(246.150–310.295), chunk 4 303.840 (273.940–352.840), chunk 8 307.593
(264.830–328.419). Random intervals overlap between prototypes; these
results do not establish a parameter-generation improvement. All remain
behind OpenSSL. Keep the fixed-search and random-API conclusions separate.

## Parameter-gap investigation

Source inspection of OpenSSL 3.5.7 identifies a concrete next experiment,
not a measured attribution: its IA-32 Montgomery implementation in
[`crypto/bn/asm/x86-mont.pl`](https://github.com/openssl/openssl/blob/openssl-3.5.7/crypto/bn/asm/x86-mont.pl)
uses SSE2 `pmuludq` and scheduled accumulation. Our x86 SSE model explicitly
omits vector integer multiplication with the MCDT hazard. A controlled
OpenSSL SSE2-on/off comparison and an isolated vector-kernel prototype would
separate this hardware-path difference from the scalar algorithm changes.
Any production ISA support requires a separately reviewed TCB change and
correct MXCSR handling; the current prototype does not change that model.

OpenSSL's
[`ffc_params_generate.c`](https://github.com/openssl/openssl/blob/openssl-3.5.7/crypto/ffc/ffc_params_generate.c)
uses `BN_check_prime` with the same 64/128 minimum round policy. Reducing the
round count is not a valid optimization of our existing contract. Witness
sampling and trial-division work still differ and need separate profiling;
the source comparison does not prove that SSE2 accounts for the entire gap.
