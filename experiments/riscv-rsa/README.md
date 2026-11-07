# Unproven native RISC-V RSA experiments

Experimental branch based on CI revision `44db4d9cafe88709715eb344d84fd76dfe3f7341`.
Run `experiments/riscv-rsa/run.sh` on native RV64GC Linux with GCC and OpenSSL development headers.

These standalone assembly reconstructions and C prototypes are **unproven**.
They never replace the generated crates or participate in the library build.
The measurement commits temporarily repurpose the manually dispatched `bench.yml`
workflow. The final results commit restores that workflow unchanged. A copy of
the experimental dispatch workflow is retained as `workflow.yml`.

Variants: emitted baseline; eligible `mulhu`/`mul` reordering; one-row C control;
two-row C Montgomery scan inspired by ARMv7; column-integrated C Montgomery
squaring inspired by i686 SSE2; multiplication-only instruction reordering;
two-product assembly scheduling for squaring; word-wise constant-time table
selection; specialized public squaring; and their combination. The C experiments include a conservative wrapper
that saves all registers; interpret their absolute comparison with the inline
baseline accordingly. The two C multiplication variants use identical wrappers.

Correctness is checked against OpenSSL for arithmetic at 11 widths, boundary
operands and output aliasing; complete checked private RSA at 2048/3072/4096 bits
uses published Wycheproof keys (source URLs and SHA-256 in `fixtures/fixtures.json`).
Valid, zero, one, n-1 and rejected inputs are included. Public operations are
also checked against OpenSSL in the confirmation run. Seven alternating-order
rounds measure kernels and complete checked private operations at one and four
threads. The confirmation run focuses on private and public operations, with
longer private-operation batches of 64/24/12 iterations per thread for
RSA-2048/3072/4096; public batches use 1000/500/250 iterations. The latter uses separate caller workspaces and a shared immutable key;
it measures arithmetic concurrency, not the Rust scratch-buffer leasing API.

Output includes compiler, CPU, revision, transforms, correctness logs, disassembly,
raw CSV samples and paired-round summaries. No coverage instrumentation is used.
Measurements are evidence for choosing proof work; they are not formal proofs or
an audit of constant-time execution. No production source, proofs, specifications,
or generated crates are modified.


Results are retained under `results/`, each with its exact revision and Actions
URL. The first run (42393623794) exposed a harness replacement-boundary bug:
the copied square epilogue was initially left outside the replacement, causing
a crash during RSA checks. It produced no timing conclusions. The corrected
screening runs are 42393735988 and 42394121117; confirmation is 42394606660.

The C column implementation was substantially slower than the emitted square;
the C two-row implementation did not establish an end-to-end win. Whole-kernel
multiply-pair reordering helped multiplication but hurt squaring, so the later
candidate applies it only to multiplication. These observations reject these
specific prototypes; they do not establish that every implementation of the
underlying techniques would be slower.


## Confirmed single-thread results

Confirmation run [42394606660](https://github.com/pyca/verified-garbage/actions/runs/42394606660),
revision `101ede95dd`, uses GCC 13.3.0 (`-O3 -march=rv64gc -mabi=lp64d`) on a
native RISE RISC-V runner. Exact host/kernel/ISA details are in
`results/confirmation/machine.txt`. The baseline is an assembly reconstruction
of emitted code from `44db4d9`; candidate and baseline are linked into the same
binary and measured with identical inputs in seven alternating-order rounds.
These are wall-clock measurements, not instruction counts or simulated timings.

| Operation | Bits | Baseline median | Combined median | Median paired elapsed-time reduction |
|---|---:|---:|---:|---:|
| Precomputed public exponentiation | 2048 | 126.05 µs | 101.92 µs | 18.81% |
| Precomputed public exponentiation | 3072 | 271.56 µs | 214.16 µs | 21.17% |
| Precomputed public exponentiation | 4096 | 476.48 µs | 372.57 µs | 21.92% |
| Checked private CRT operation | 2048 | 5221.34 µs | 5029.68 µs | 3.78% |
| Checked private CRT operation | 3072 | 15484.17 µs | 14941.09 µs | 3.37% |
| Checked private CRT operation | 4096 | 33455.62 µs | 32725.61 µs | 2.69% |

The public-squaring change alone reduces public-operation elapsed time by
17.96%, 19.42%, and 20.30% respectively. It reuses the existing specialized square
in the public-exponent path, taking the now-dead R-squared array as scratch.
The combination additionally uses square-product scheduling, word-wise table
selection and multiplication-only pair reordering. Their combined private-operation
time reductions are 3.78%, 3.37%, and 2.69%.

Confirmation passes 4,224 arithmetic checks plus 240 private and 240 public RSA
checks against OpenSSL, including output aliasing and invalid inputs. These
standalone checks do not establish formal correctness or a constant-time proof.
Four-thread results in this run are noisy and include apparent regressions;
do not infer a concurrency improvement from the single-thread table.

The operations exclude Rust key construction, scratch-buffer leasing, padding,
and Rust wrapper allocation/cleanup. Public precomputation is outside the public
operation's timed loop. Checked private operations include CRT preparation,
exponentiation, recombination, public precomputation and the public fault check.
The multithreaded workload shares immutable key bytes and gives each worker its
own scratch workspace. Allocation counts and hardware instruction counts were
not measured. The square-scheduling candidate adds a 16-byte stack frame; the
C controls have extra register-saving call wrappers and are not production code.

No source under `src/`, `lean/`, or the generated crates is changed. No Lean
proofs have been attempted. The normal benchmark workflow is restored in the
final evidence commit; all experiment outputs stay under this directory.


## Concurrency diagnostic and recommendation

The focused [native diagnostic](https://github.com/pyca/verified-garbage/actions/runs/42395215555)
uses RSA-4096, seven interleaved rounds, and 32 operations per single-thread batch
or 128 per worker at four workers. Run it with
`RSA_DIAGNOSTIC=1 experiments/riscv-rsa/run.sh`. Full CPU-time analysis is in
`results/concurrency/cpu-summary.md`; raw samples retain both elapsed seconds
and summed worker CPU seconds.

The combination reduces worker CPU time by 2.91% at one worker and 3.12% at four
workers; every four-worker round improves by 2.65–3.66%. The wall-time result at
four workers remains noisy (-6.02% to +24.91%), so no robust aggregate-throughput
gain is claimed. The public-square-only control has essentially unchanged
private-operation CPU cost while its wall time swings widely, supporting the
interpretation that those large wall-time changes are inconclusive. The exact
cause of the runner's availability variation is not established.

Prioritize proof integration of **specialized public squaring**: alone, it cuts
public-operation elapsed time by 18–20% and reuses an existing arithmetic kernel.
Then consider word-wise table selection (1–2% private-operation elapsed-time
reduction) and the combined scheduling changes (roughly 3% for private RSA).
The column-C and two-row-C prototypes are not candidates for proof work on the
basis of these measurements. Multiplication reordering should never be applied
to squaring indiscriminately: the screening measurements show a regression.

All measured candidate code remains unproven and outside the library. Correctness
checks, native timing, worker CPU time, and formal proofs are separate evidence;
only the first three have been performed here.
