module

public import VerifiedGarbage.Proof.Variants.Argon2Compress.X86_64.Avx2
public import VerifiedGarbage.Proof.Variants.Argon2Compress.X86_64.Avx512
public import VerifiedGarbage.Proof.Variants.Argon2Compress.X86_64.Scalar

/-! # The implementations of `Argon2Compress` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.Argon2Compress.X86_64

open VG VG.X86_64 VG.Proof.Argon2.X86_64 in
@[instance_reducible] def avx2 : CompressImpl := Proof.Variants.Argon2Compress.X86_64.Avx2.variant

open VG VG.X86_64 VG.Proof.Argon2.X86_64 in
@[instance_reducible] def avx512 : CompressImpl := Proof.Variants.Argon2Compress.X86_64.Avx512.variant

open VG VG.X86_64 VG.Proof.Argon2.X86_64 in
@[instance_reducible] def scalar : CompressImpl := Proof.Variants.Argon2Compress.X86_64.Scalar.variant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this). -/
def variants := [avx512, avx2, scalar]

end VG.Proof.Variants.Argon2Compress.X86_64
