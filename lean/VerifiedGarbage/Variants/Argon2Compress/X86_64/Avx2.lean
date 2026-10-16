module

public import VerifiedGarbage.Proof.Variants.Argon2Compress.X86_64.Avx2

/-!
# Argon2's G on x86-64 with AVX2

A variant of `Argon2Compress` on x86-64 (see `TCB/Emit.lean`):
`vg_argon2_compress_avx2`, which needs AVX and AVX2; the derivation calling
it needs them too.
-/

@[expose] public section

namespace VG.Variants.Argon2Compress.X86_64.Avx2

open VG VG.X86_64 VG.Proof.Argon2.X86_64

@[instance_reducible] def variant : CompressImpl := Proof.Variants.Argon2Compress.X86_64.Avx2.variant

end VG.Variants.Argon2Compress.X86_64.Avx2
