module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant

/-!
# `vg_chacha20_xor` on x86-64: with AVX-512, short data in `ymm` registers

A variant of `ChaCha20Xor` on x86-64 (see `TCB/Emit.lean`):
`vg_chacha20_xor_avx512vl`, which needs AVX, AVX2, AVX-512F and AVX-512VL.
-/

@[expose] public section

namespace VG.Variants.ChaCha20Xor.X86_64.Avx512Vl

def variant : Proof.ChaCha20.X86_64.XorImpl := .avx512vl

end VG.Variants.ChaCha20Xor.X86_64.Avx512Vl
