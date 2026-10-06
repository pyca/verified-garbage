import VerifiedGarbage.Proof.ChaCha20.X86.Variant

/-!
# `vg_chacha20_xor` on x86: with SSSE3

A variant of `ChaCha20Xor` on x86 (see `TCB/Emit.lean`):
`vg_chacha20_xor_ssse3`, which needs SSSE3.
-/

namespace VG.Variants.ChaCha20Xor.X86.Ssse3

def variant : Proof.ChaCha20.X86.XorImpl := .ssse3

end VG.Variants.ChaCha20Xor.X86.Ssse3
