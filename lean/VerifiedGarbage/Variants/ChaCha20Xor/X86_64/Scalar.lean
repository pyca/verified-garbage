module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant

/-! # `vg_chacha20_xor` on x86-64: the scalar implementation -/

@[expose] public section

namespace VG.Variants.ChaCha20Xor.X86_64.Scalar

def variant : Proof.ChaCha20.X86_64.XorImpl := .scalar

end VG.Variants.ChaCha20Xor.X86_64.Scalar
