import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant

/-!
# `vg_chacha20_xor` on x86-64: with AVX-512, for CPUs with AVX-512 IFMA

A variant of `ChaCha20Xor` on x86-64 (see `TCB/Emit.lean`):
`vg_chacha20_xor_avx512`, which needs AVX and AVX-512F, for the CPUs that
also have AVX512_IFMA, whose instances of ChaCha20-Poly1305 call
`vg_poly1305_blocks_ifma`.
-/

namespace VG.Variants.ChaCha20Xor.X86_64.Ifma

def variant : Proof.ChaCha20.X86_64.XorImpl := .ifma

end VG.Variants.ChaCha20Xor.X86_64.Ifma
