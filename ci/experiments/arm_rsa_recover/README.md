# ARMv7 RSA recovery experiment

**The C prototype remains unproven and outside the library.** It must not be
linked into the library; its compiler output is not certified constant time.
The production implementation is generated separately from
`Impl/Rsa/Arm/RecoverFused.lean` and verified by
`Proof/Rsa/Arm/FusedVerified.lean` against the unchanged RSA contract.

The CI metrics identified `wycheproof::rsa_keys::rsa_keys_from_components` as
an expensive ARMv7 test: median 70 s in Linux stable and 143 s in the forced
baseline feature job. These test times include concurrent work, many keys,
and other operations. They are not isolated timings of this experiment.

## Target and source comparison

The prior ARMv7 `Impl/Rsa/Arm/Recover.lean` baseline computed a candidate's odd power
with a square and a product for each public-width exponent bit, then makes a
second fixed-width squaring pass to find a nontrivial square root of one.
That is three Montgomery operations per bit, plus setup and final gcd/division.

OpenSSL 3.5.4 uses word-based Montgomery multiplication and windowed
exponentiation:

- [ARM Montgomery assembly generator](https://github.com/openssl/openssl/blob/openssl-3.5.4/crypto/bn/asm/armv4-mont.pl)
- [fixed-window constant-time exponentiation](https://github.com/openssl/openssl/blob/openssl-3.5.4/crypto/bn/bn_exp.c)
- [gcd and modular inversion](https://github.com/openssl/openssl/blob/openssl-3.5.4/crypto/bn/bn_gcd.c)

Those are useful comparisons, but this repository already has native-word
Montgomery kernels and windowed RSA implementations. Copying them would
duplicate work. Some OpenSSL paths also permit timing behavior that the
existing recovery contract does not permit; they cannot simply replace it.

Instead reuse the algorithm already implemented for x86 in
`Impl/Rsa/X86/RecoverRt.lean` and proven independent of architecture in
`Proof/Rsa/RecoverFused.lean`: scan the full `ed - 1` most significant bit
first, combining exponentiation and root detection. A set bit starts a new
trailing-zero chain and discards the previous chain's root. A zero bit may
record a nontrivial root. This preserves the specification even for invalid
keys; merely finding *some* factor of a valid RSA modulus is insufficient.

For candidates 2 and 3, multiply the squared Montgomery value by the public
candidate with modular additions. For later candidates, use the same existing
Montgomery kernel. An earlier bounded-binary-multiplication experiment lost
to UMAAL at small sizes, so it was rejected.

## What is measured

Both schedules call exactly the same Lean-generated `vg_rsa_mont_mul` or
`vg_rsa_mont_mul_umaal`. `run.py` extracts the emitted instructions verbatim;
there is no handwritten assembly. It supplies an independent Python `pow`
reference for the expected root, plus fresh OpenSSL-generated RSA factors
and synthetic invalid-key cases (zero and even exponents, long trailing-zero
chains). Fixtures are recorded so each run can be reproduced.

Only the recovery candidate's arithmetic core is timed. Both sides include
candidate setup; modulus/context setup, factor-of-two extraction on the real
baseline, final gcd/division, and the Rust API's surrounding checks are not a
whole-API comparison. The C baseline follows the prior two-pass schedule,
not the complete emitted recovery function. In particular, both sides use the
callable Montgomery helper's specialized square. **Do not translate these
ratios into a claimed `from_components` or CI speedup.**

Warm both schedules, alternate their order, and report the median of five
paired samples. Save every sample, exact inputs, compiler/version, source
hashes, runner mode, and source revision. Never treat QEMU's ratios as native
performance results.

Example local correctness and exploratory run, with a cross compiler,
OpenSSL, Python and QEMU installed:

```sh
python3 ci/experiments/arm_rsa_recover/run.py \
  --work /tmp/arm-rsa-recovery \
  --runner 'qemu-arm -L /usr/arm-linux-gnueabihf'
python3 ci/experiments/arm_rsa_recover/summarize.py /tmp/arm-rsa-recovery
```

Native measurements use only one manually dispatched job of the existing
Benchmarks workflow; the regular benchmark matrix is skipped:

```sh
gh workflow run bench.yml --ref BRANCH -f arm_rsa_recovery_prototype=true
```

That job refuses a host without native AArch32 rather than timing emulation.
It uploads the inputs, samples, binaries, source hashes and CSVs.

## Production proof

`Proof/Rsa/Arm/FusedVerified.lean` proves the emitted ARM implementation
against the unchanged recovery contract, including invalid-key behavior,
memory safety, termination, the ABI and constant-time traces. The UMAAL
variant reuses the same verified row transformation as private RSA.

The implementation reads the preserved `ed - 1` a byte at a time and uses
one specialized Montgomery square per bit. Candidate multiplication reuses
the modular-addition proofs for 2 and 3 and the existing Montgomery proof
for later candidates. A set bit clears the saved root through a masked
selection, making its state exact even when recovery fails.

The shared architecture-independent fused theory supplies the result.
Both ARM recovery schedules reuse the same generalized factor-extraction,
output, validation and ABI proofs. No specification, ISA model, contract,
leakage allowance or proof-resource limit changes are needed.

Use the regular scoped benchmark matrix to measure the emitted public API;
the prototype input above measures only the historical C experiment:

```sh
gh workflow run bench.yml --ref BRANCH -f base_commit=BASE \
  -f arches=arm -f cpu_features='none umaal' -f modules=rsa
```
