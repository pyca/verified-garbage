module

public import VerifiedGarbage.Proof.ChaCha20.X86.Variant

/-! # `vg_chacha20_xor` on x86: with SSE2 -/

@[expose] public section

namespace VG.Variants.ChaCha20Xor.X86.Sse2

def variant : Proof.ChaCha20.X86.XorImpl := .sse2

end VG.Variants.ChaCha20Xor.X86.Sse2
