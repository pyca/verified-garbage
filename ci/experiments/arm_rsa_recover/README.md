# ARMv7 RSA recovery experiment

**Unproven prototype, outside the library.** No generated Rust, specification,
ISA model or artifact registration changes. The C program is not verified and
must not be linked into the library. Its compiler output is not certified
constant time.

The CI metrics identified `wycheproof::rsa_keys::rsa_keys_from_components` as
an expensive ARMv7 test: median 70 s in Linux stable and 143 s in the forced
baseline feature job. These test times include concurrent work, many keys,
and other operations. They are not isolated timings of this experiment.

## Target and source comparison

ARMv7 `Impl/Rsa/Arm/Recover.lean` currently computes a candidate's odd power
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
whole-API comparison. The C baseline follows the current two-pass schedule,
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

## Proof progress and remaining work

Kernel-checked, with standard-axiom audits:

- `Proof/Rsa/RecoverFusedMont.lean` lifts the existing fused algorithm into
  Montgomery representation and reuses its exact root/none result theorem.
  It assumes the multiplication kernel's contract and does not verify C.
- `Impl/Rsa/Arm/RecoverScalar.lean` and its proof reuse the existing modular
  addition to prove arithmetic, allowed memory changes, memory safety, and
  constant time for multiplication by candidates 2 and 3. They are unregistered.

Before production integration: implement the fixed-width exponent-byte loop,
prove each ARM state transition and its memory/ABI obligations, prove trace
equality under the existing leakage contract, connect factor extraction and
all unsuccessful/invalid-key paths, run the emitter audits and ARM tests,
and measure the public API against the base revision on native hardware.
No new trusted spec or ISA instruction is needed for this approach.
