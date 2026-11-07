# Unproven native RISC-V RSA experiments

Experimental branch based on CI revision `44db4d9cafe88709715eb344d84fd76dfe3f7341`.
Run `experiments/riscv-rsa/run.sh` on native RV64GC Linux with GCC and OpenSSL development headers.

These standalone assembly reconstructions and C prototypes are **unproven**.
They never replace the generated crates or participate in the library build.
The branch temporarily repurposes the manually dispatched `bench.yml` workflow;
this workflow change is not intended for merging.

Variants: emitted baseline; eligible `mulhu`/`mul` reordering; one-row C control;
two-row C Montgomery scan inspired by ARMv7; column-integrated C Montgomery
squaring inspired by i686 SSE2. The C experiments include a conservative wrapper
that saves all registers; interpret their absolute comparison with the inline
baseline accordingly. The two C multiplication variants use identical wrappers.

Correctness is checked against OpenSSL for arithmetic at 11 widths, boundary
operands and output aliasing; complete checked private RSA at 2048/3072/4096 bits
uses published Wycheproof keys (source URLs and SHA-256 in `fixtures/fixtures.json`).
Valid, zero, one, n-1 and rejected inputs are included. Seven alternating-order
rounds measure kernels and complete checked private operations at one and four
threads. The latter uses separate caller workspaces and a shared immutable key;
it measures arithmetic concurrency, not the Rust scratch-buffer leasing API.

Output includes compiler, CPU, revision, transforms, correctness logs, disassembly,
raw CSV samples and paired-round summaries. No coverage instrumentation is used.
Measurements are evidence for choosing proof work; they are not formal proofs or
an audit of constant-time execution. No production source, proofs, specifications,
or generated crates are modified.
