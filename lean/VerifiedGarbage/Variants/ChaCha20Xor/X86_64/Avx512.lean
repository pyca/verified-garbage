module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant

/-! # `vg_chacha20_xor` on x86-64: with AVX-512 -/

@[expose] public section

namespace VG.Variants.ChaCha20Xor.X86_64.Avx512

def variant : Proof.ChaCha20.X86_64.XorImpl := .avx512

end VG.Variants.ChaCha20Xor.X86_64.Avx512
