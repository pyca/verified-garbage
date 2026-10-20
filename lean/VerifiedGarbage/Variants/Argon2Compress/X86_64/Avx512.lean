module

public import VerifiedGarbage.Proof.Variants.Argon2Compress.X86_64.Avx512

/-!
# Argon2's G on x86-64 with AVX-512

A variant of `Argon2Compress` on x86-64 (see `TCB/Emit.lean`):
`vg_argon2_compress_avx512`, which needs AVX512F (and AVX, for its closing
`vzeroupper`); the derivation calling it needs them too.
-/

@[expose] public section

namespace VG.Variants.Argon2Compress.X86_64.Avx512

open VG VG.X86_64 VG.Proof.Argon2.X86_64

@[instance_reducible] def variant : CompressImpl := Proof.Variants.Argon2Compress.X86_64.Avx512.variant

end VG.Variants.Argon2Compress.X86_64.Avx512
