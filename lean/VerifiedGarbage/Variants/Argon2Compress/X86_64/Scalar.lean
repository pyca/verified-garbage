module

public import VerifiedGarbage.Proof.Variants.Argon2Compress.X86_64.Scalar

/-! # Argon2's G on baseline x86-64 -/

@[expose] public section

namespace VG.Variants.Argon2Compress.X86_64.Scalar

open VG VG.X86_64 VG.Proof.Argon2.X86_64

@[instance_reducible] def variant : CompressImpl := Proof.Variants.Argon2Compress.X86_64.Scalar.variant

end VG.Variants.Argon2Compress.X86_64.Scalar
