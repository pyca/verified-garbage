module

public import VerifiedGarbage.Proof.Variants.Blake2b.X86_64.Avx2

/-!
# BLAKE2b on x86-64 with AVX2

A variant of `Blake2b` on x86-64 (see `TCB/Emit.lean`):
`vg_blake2b_compress_avx2`, the work vector in four 256-bit registers, which
needs AVX and AVX2; the streaming functions calling it, and everything
built on them (Argon2's H′ and derivation, whose instances are named by
`Emit.qualifiedName`, e.g. `vg_argon2_blake2b_avx2_g_avx512`), need them too.
-/

@[expose] public section

namespace VG.Variants.Blake2b.X86_64.Avx2

def variant : Proof.Blake2.X86_64.Backend := Proof.Variants.Blake2b.X86_64.Avx2.variant

end VG.Variants.Blake2b.X86_64.Avx2
