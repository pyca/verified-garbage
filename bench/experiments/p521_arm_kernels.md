# ARMv7 P-521 kernel investigation

Recommendation: pursue a packed 32-bit Montgomery multiplication implementation
for P-521. Start with the baseline kernel; keep UMAAL integration as a separate
change so its feature dispatch and caller generalization can be reviewed alone.

Native CI run: https://github.com/pyca/verified-garbage/actions/runs/39857029606

Measured revision: `6654167ecfbdce806a9736ca410b864fa25a8501`.
The experiment imports existing Lean-emitted assembly unchanged. No production
implementation or proof is changed by this experiment.

Hardware: Neoverse N2, implementer `0x41`, part `0xd49`, revision 0; ARMv7
A32 binaries executed directly on the ubuntu-26.04-arm runner in the existing
`armv7-cross` container. Rust 1.99.1, LLVM 23.1.1, edition 2024,
`-C opt-level=3`, single benchmark thread.

Median latency in nanoseconds per Montgomery multiplication, dense inputs:

| Modulus | Current P-521 | RSA baseline | Reduction | RSA UMAAL | Reduction |
| --- | ---: | ---: | ---: | ---: | ---: |
| Field p | 1640.840 | 1096.951 | 33.1% | 359.380 | 78.1% |
| Order n | 1640.800 | 1096.862 | 33.1% | 358.482 | 78.2% |

Near-modulus and full-width-A inputs produced the same reductions. Each
kernel/modulus/input measurement has 11 interleaved samples of 100,000 calls,
with 2,000 warm-up calls before each sample. Kernel order rotates each round.
Across all 18 configurations, the largest sample range relative to its median
was 0.52%. Every sample and each min/median/max is in the linked job log and
workflow summary; no timing run was discarded. Two earlier jobs failed before
timing because of container Git ownership and a missing diagnostic utility.

Correctness: 1,603 cases per modulus (zero, near-modulus, maximal 576-bit A,
all single-bit A inputs, and 1,024 deterministic random pairs), with three
kernels and three output placements (separate, alias A, alias B): 28,854 output
comparisons passed against the current verified P-521 kernel. Earlier Unicorn
checks also compared all three kernels to Python big-integer arithmetic.

These are warm kernel microbenchmarks, not ECDSA/ECDH measurements. RSA header,
modulus, inverse, and operand setup are outside the timed region; its existing
calling convention and stack frame are included. The current P-521 kernel's
own modulus materialization is included. A future P-521 adapter is unmeasured.
Operand indices are distinct, so this does not exercise RSA's specialized
same-index squaring path. Allocation metrics were not measured; timing itself
does not allocate. Results establish value on N2 running AArch32, not on older
ARMv7 cores or M-profile systems.

Integration requires Lean implementations and proofs preserving the P-521
workspace layout, arbitrary permitted operand/output overlap, r10/r11, the
r12 workspace pointer, and the existing stack contract. Reuse the verified
Montgomery pipeline core rather than copying RSA's entire workspace ABI.
UMAAL additionally requires feature-specific variants through all ECDSA/ECDH
callers and Rust dispatch, retaining the baseline fallback. Both moduli matter:
the field drives point arithmetic; the order drives scalar arithmetic.

Before merging an implementation, measure public-key derivation, ECDH,
ECDSA signing and verification end to end in the existing ARM/Thumb benchmark
harness, and run correctness and constant-time proof checks. No end-to-end
speedup is claimed here.

Reproduce:

```sh
gh workflow run bench.yml --ref codex/p521-kernel-investigation \
  -f arches=arm -f modules=p521-kernels
```

The experiment job compiles `bench/experiments/p521_arm_kernels.rs` directly
with rustc for `armv7-unknown-linux-gnueabihf`, using
`arm-linux-gnueabihf-gcc` as linker. It validates the ELF32 ARM header and runs
the executable directly, without the optional emulator runner wrapper.
