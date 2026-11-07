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
