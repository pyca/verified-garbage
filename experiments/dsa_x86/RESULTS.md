# Native unproven prototype results

No proof or production-readiness claim. Verified branch: `dsa-x86-generation` at `784473529`.

**Current result:** shared-comb keygen beats OpenSSL by 19–24% on EPYC 7763.
The keygen-only four-word candidate keeps that speed with 26% less total DSA
code than the combined experiment. The DSA comb contracts merged in #2963;
implementation proofs are in progress. Random 1024-bit parameter generation
remains slower than OpenSSL and is outside the keygen implementation scope.

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

## Shared keygen comb: first consistent win on the older AMD runner

Run [39521854499](https://github.com/pyca/verified-garbage/actions/runs/39521854499),
commit `787e52f76`, native i686 AMD EPYC 7763. All candidates passed their
DSA tests; comb candidates include the algebraic reuse/ABI check. Three
alternating keygen rounds, 25 samples each. No random-parameter rerun here:
comb reuse changes keygen only.

| Candidate | 1024/160 ms | 2048/160 | 2048/224 | 2048/256 | 3072/256 | DSA bytes |
|---|---:|---:|---:|---:|---:|---:|
| Verified baseline | 2.2692 | 8.7063 | 11.4494 | 12.8271 | 28.5781 | 524288 |
| OpenSSL | .6267 | 2.4047 | 3.2016 | 3.6350 | 8.1409 | — |
| Previous chunk-4 stack | .7338 | 2.7216 | 3.6573 | 4.1210 | 9.0718 | 747456 |
| Shared comb, chunk 4 | .5097 | 1.8802 | 2.5038 | 2.8359 | 6.2184 | 832128 |
| Shared comb, chunk 8 | .5042 | 1.8550 | 2.4712 | 2.7960 | 6.1517 | 932352 |

The fastest stack beats OpenSSL keygen by 19.5–24.4% on the CPU where earlier
stacks were slower. The shared table cuts 30.5–31.6% from the corresponding
chunk-4 prototype and gives 4.5–4.6x verified-baseline throughput. Prefer
chunk 4 for promotion: chunk 8 gains only 1.1–1.4% while adding 100,224 bytes.
This measures the complete keygen API, including validation and precomputation;
it does not assume a cached table from a prior API call.

Fixed-search parameter timings are unchanged within noise, as expected.
The random 1024-bit parameter deficit from sweeps 6/7 remains unresolved;
this keygen result alone does not satisfy the all-workload PR gate.

## Controlled OpenSSL SSE2 dispatch diagnostic

Run [39522670146](https://github.com/pyca/verified-garbage/actions/runs/39522670146),
commit `4e4e89a7e`, AMD EPYC 7763, same OpenSSL binary for both configurations.
Only the first capability word's SSE2 bit 26 is masked; the remaining four
64-bit capability vectors are preserved (`~0x4000000:~0x0:~0x0:~0x0:~0x0`).
Default uses no capability override. This changes dispatch, not the binary's
baseline ISA. It is diagnostic, not the submission baseline.

| Workload | Normal OpenSSL ms | SSE2 dispatch disabled ms | Slowdown |
|---|---:|---:|---:|
| Keygen 1024/160 | .6276 | .7889 | 25.7% |
| Keygen 2048/160 | 2.3925 | 3.0963 | 29.4% |
| Keygen 2048/224 | 3.2026 | 4.1304 | 29.0% |
| Keygen 2048/256 | 3.6354 | 4.6976 | 29.2% |
| Keygen 3072/256 | 8.1566 | 10.5027 | 28.8% |
| Parameters 1024 | 184.1914 | 246.1156 | 33.6% |

Keygen has 25 samples per case; parameters have 100. Parameter median 95% CIs
are 160.728–206.692 ms and 212.322–268.630 ms. The two parameter searches use
independent random inputs, so the exact percentage remains noisy. The
keygen result provides a much tighter hardware-path comparison.

The next high-value prototype is a shared SSE2 Montgomery kernel for RSA
and DSA, with the necessary timing mitigation. This experiment supports a
substantial vector-path contribution but does not establish that it explains
the whole parameter gap: our chunk-4 parameter median in sweep 7 was 303.840
ms (different random workload/run). Witness handling and trial division
remain profiling targets. Do not reduce primality rounds or present the
masked OpenSSL result as the acceptance comparison.

## Keygen-only promotion sweep

Run: https://github.com/pyca/verified-garbage/actions/runs/39526788245
Commit: `6957d3ef4`. Native i686, AMD EPYC 7763, normal OpenSSL capabilities.
Three alternating-order rounds, 25 samples per workload; medians of round medians.
Every candidate passed 27 DSA tests, including comb arithmetic, dense exponents,
context reuse and ABI checks (baseline: 26). No random parameter timing was requested.

| Candidate | 1024/160 ms | 2048/160 ms | 2048/224 ms | 2048/256 ms | 3072/256 ms | Total DSA symbol bytes |
|---|---:|---:|---:|---:|---:|---:|
| Verified baseline | 2.2702 | 8.7008 | 11.4564 | 12.8319 | 28.7014 | 524288 |
| OpenSSL | 0.6271 | 2.3969 | 3.2021 | 3.6392 | 8.1363 | — |
| `mk`: comb | 0.7484 | 2.8273 | 3.5941 | 3.9945 | 8.9062 | 595776 |
| `mfk`: comb + public setup | 0.6081 | 2.2404 | 2.9851 | 3.3866 | 7.4559 | 603264 |
| `mfkr4`: add four-word rows | 0.5719 | 2.1818 | 2.9187 | 3.3069 | 7.3533 | 610176 |
| `mfkscvru4`: add compact squares | 0.5103 | 1.8812 | 2.5030 | 2.8326 | 6.2168 | 617408 |
| `mfkh`: existing shared RSA multiplier | 0.6331 | 2.3238 | 3.1110 | 3.5279 | 7.8190 | 580672 |
| Previous combined experiment | 0.5094 | 1.8813 | 2.5036 | 2.8337 | 6.2172 | 832128 |

The keygen-only compact-square candidate matches the previous winner within
0.2%, beats OpenSSL by 18.6–23.6%, and removes 214720 DSA symbol bytes (25.8%).
Its ordinary power, signing, verification, external derivation, and parameter
bodies retain the checked baseline; fixed CAVP parameter timings confirm the
parameter code is unchanged. This is the performance target for the optimized
keygen implementation, not a claim that its proof is finished.

The simpler `mfk` candidate already beats OpenSSL by 3.0–8.4% using the existing
multiplication body. It provides a smaller proof scope for the initial comb
integration. Four-word rows improve that to 8.8–9.6%; compact squares then give
a further 11–15% reduction in keygen time for only 7232 more symbol bytes.
The shared runtime RSA helper is the smallest candidate, but is 1.0% slower
than OpenSSL at 1024 bits, so it does not meet the all-width acceptance target.
The proofs should share the existing arithmetic lemmas and comb mathematics;
there is no reason to promote unrelated parameter/window experiments.

## Scratch-memory masks

Run: https://github.com/pyca/verified-garbage/actions/runs/39530128608
Commit: `1468edcf7`. Native i686, AMD EPYC 7763, normal OpenSSL capabilities.
Three alternating-order rounds, 25 samples per workload. Keygen/DSA correctness,
dense comb arithmetic, retained-context reuse and ABI checks all passed.

| Candidate | 1024/160 ms | 2048/160 ms | 2048/224 ms | 2048/256 ms | 3072/256 ms | Total DSA symbol bytes |
|---|---:|---:|---:|---:|---:|---:|
| OpenSSL | 0.6274 | 2.3938 | 3.2018 | 3.6381 | 8.1450 | — |
| `mfk` stack masks | 0.6113 | 2.2480 | 2.9860 | 3.4037 | 7.4713 | 603264 |
| `mfko` workspace masks | 0.6057 | 2.2340 | 2.9818 | 3.3828 | 7.4752 | 603904 |
| `mfkscvru4` stack masks | 0.5094 | 1.8829 | 2.5056 | 2.8329 | 6.2141 | 617408 |
| `mfkscvruo4` workspace masks | 0.5091 | 1.8794 | 2.5053 | 2.8369 | 6.2222 | 618048 |

Use workspace masks for promotion. They remove the 128-byte stack frame by
reusing Montgomery temporary slot 1, which is dead during selection. The
fastest candidate changes by at most 0.2% and remains 18.9–23.6% faster than
OpenSSL. Total symbol size grows by 640 bytes (0.1%). This small cost removes
stack allocation/release from the private core and allows the existing taint
checker to verify its entire constant-time control flow in one proof. These
are still unproven prototype timings; production acceptance must measure the
exact emitted, fully verified implementation.
