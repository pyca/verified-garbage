module

public import VerifiedGarbage.Proof.Variants.Argon2Compress.X86_64.Avx2
public import VerifiedGarbage.Proof.Variants.Argon2Compress.X86_64.Avx512
public import VerifiedGarbage.Proof.Variants.Argon2Compress.X86_64.Scalar
public import VerifiedGarbage.Proof.Variants.Blake2b.X86_64

/-! # The implementations of `Argon2Compress` on x86-64

And the pairs of a BLAKE2b backend and one of them that Argon2's
derivation is emitted for (`withBlake2b`). -/

@[expose] public section

namespace VG.Proof.Variants.Argon2Compress.X86_64

open VG.Proof.Argon2.X86_64 (CompressImpl)

open VG VG.X86_64 VG.Proof.Argon2.X86_64 in
@[instance_reducible] def avx2 : CompressImpl := Proof.Variants.Argon2Compress.X86_64.Avx2.variant

open VG VG.X86_64 VG.Proof.Argon2.X86_64 in
@[instance_reducible] def avx512 : CompressImpl := Proof.Variants.Argon2Compress.X86_64.Avx512.variant

open VG VG.X86_64 VG.Proof.Argon2.X86_64 in
@[instance_reducible] def scalar : CompressImpl := Proof.Variants.Argon2Compress.X86_64.Scalar.variant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [avx512, avx2, scalar]

/-- The pairs of a BLAKE2b backend and an implementation of G that Argon2's
derivation is emitted for, best first: those of the same suffix (the
baseline with the baseline, `_avx2` with `_avx2`, `_avx512` with
`_avx512`), and BLAKE2b's `_avx2` with G's `_avx512`, for CPUs with
AVX-512F but not AVX512VL (Intel's Knights Landing), which BLAKE2b's
`_avx512` needs. Any other pair needs the features of one of these, which
runs both its parts with them. -/
def withBlake2b : List (Proof.Blake2.X86_64.Backend × CompressImpl) :=
  Proof.Variants.Blake2b.X86_64.variants.flatMap fun v => variants.filterMap fun c =>
    if v.suffix == c.suffix || (v.suffix == "_avx2" && c.suffix == "_avx512") then some (v, c) else none

end VG.Proof.Variants.Argon2Compress.X86_64
