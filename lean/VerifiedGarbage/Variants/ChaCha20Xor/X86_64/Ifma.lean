module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant

/-! # `vg_chacha20_xor` on x86-64: with AVX-512, for CPUs with AVX-512 IFMA -/

@[expose] public section

namespace VG.Variants.ChaCha20Xor.X86_64.Ifma

def variant : Proof.ChaCha20.X86_64.XorImpl := .ifma

end VG.Variants.ChaCha20Xor.X86_64.Ifma
