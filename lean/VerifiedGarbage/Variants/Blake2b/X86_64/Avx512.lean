module

public import VerifiedGarbage.Proof.Variants.Blake2b.X86_64.Avx512

/-!
# BLAKE2b on x86-64 with AVX-512

A variant of `Blake2b` on x86-64 (see `TCB/Emit.lean`):
`vg_blake2b_compress_avx512`, the work vector in four 256-bit registers and
each rotation one `vprorq` (its EVEX.256 form), which needs AVX, AVX2,
AVX512F and AVX512VL; the streaming functions calling it, and everything
built on them (Argon2's H′ and derivation, whose instances are named by
`Emit.qualifiedName`, e.g. `vg_argon2_blake2b_avx512_g_avx512`), need them
too.
-/

@[expose] public section

namespace VG.Variants.Blake2b.X86_64.Avx512

def variant : Proof.Blake2.X86_64.Backend := Proof.Variants.Blake2b.X86_64.Avx512.variant

end VG.Variants.Blake2b.X86_64.Avx512
