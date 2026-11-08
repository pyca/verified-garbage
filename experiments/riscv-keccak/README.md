# Unproven native RISC-V Keccak experiments

These C candidates are experiments, not verified library implementations.
The library and generated crates are unchanged. The experiment branch adds an isolated native job to
the manual benchmark workflow; that workflow change will not enter a PR.

Baseline: `4f9873e9eb526aeb3aa3ad151b86329a4cb57ae6`. `generate.py` translates the
current lane-complemented round schedule to C, then tests caching selected lanes
in separate banks for the two alternating states. It also tests a canonical
scalar implementation with one, two, or four rounds per loop. The cache variants
remove memory accesses, not rotations or other required work. No extra ISA
extensions, inline assembly instructions, or handwritten machine code are used.

The reference is the exact existing Lean-emitted RISC-V assembly. The harness
resolves its printed call placeholders and adds ELF symbol directives, without
changing any executable instruction. Separate objects and the linker wrap
`vg_keccak_f1600` so that the full, existing SHAKE, ML-KEM-768 and ML-DSA-65
programs exercise a selected C permutation. Correctness checks assert the hook
is actually called, compare arbitrary states and unaligned inputs with an
independent FIPS 202 reference, compare SHAKE outputs with OpenSSL, and compare
PQC outputs and rejection behavior with the unchanged verified baseline.

Each C wrapper uses identical copy and round-constant setup. The memory-backed
C translation is a control for compiler and wrapper effects; only native
comparisons with the original assembly count as evidence for a library win.
A separate translation unit supplies the constants so the C optimizer cannot
replace the round's dynamic constant loads with a different schedule.

Seven interleaved rounds record both elapsed time and thread CPU time. Kernel
and SHAKE timings select the best two candidates for a later, independent
measurement process on complete PQC operations. Selection cannot use client
results. Raw samples, machine/compiler information, disassembly, correctness
reports and the selection rule are retained as workflow artifacts.

Run `experiments/riscv-keccak/run.sh` on a real RV64GC Linux host with GCC and
OpenSSL development headers. `-march=rv64gc -mabi=lp64d -O3` is fixed for all C
candidates. Host x86-64 builds check correctness only and do not establish speed.

The second sweep adds `v_` variants: volatile accesses keep uncached lanes in
memory, avoiding whole-state promotion and register spills observed in GCC 13
in the first native run. Cached lanes remain ordinary scalar variables.

First run: https://github.com/pyca/verified-garbage/actions/runs/42477203913
All eleven initial candidates regressed against verified assembly: permutation
latency increased 18.7–58.1%; the selected row3/cache5 variants also regressed
on every measured PQC operation. These are rejected, not speedup evidence.

The third sweep adds `f_` integrated functions: the core is always inlined,
8-byte-aligned input uses explicit 8-byte copies (with the same unaligned
fallback), and these wrappers have no compiler stack protector, matching the
verified assembly. A contiguous constants/state frame also lets the constant
pointer terminate at the state pointer, as in the verified loop, without an
extra loop-limit register. Uncached lanes still use volatile accesses; constants still
come from a separate translation unit. The earlier wrappers remain controls.
Second run: https://github.com/pyca/verified-garbage/actions/runs/42477860812
The best volatile candidates were still 2.7–3.1% slower per permutation and
showed no repeatable end-to-end gain. They do not satisfy the proof gate.

`f_parity` carries the five full column parities across rounds. The first
plane assigns their new values; later output planes XOR into them as lanes are
stored. The next theta reads those scalar parities instead of reloading twenty
lanes. All state stores remain, and lane complementing and rotation work match
the baseline. This is an algorithmic scheduling experiment, distinct from
caching lanes in two banks.
