module

public import VerifiedGarbage.Proof.ChaCha20.X86.Variant

/-! # `vg_chacha20_xor` on x86: with SSSE3 -/

@[expose] public section

namespace VG.Variants.ChaCha20Xor.X86.Ssse3

def variant : Proof.ChaCha20.X86.XorImpl := .ssse3

end VG.Variants.ChaCha20Xor.X86.Ssse3
