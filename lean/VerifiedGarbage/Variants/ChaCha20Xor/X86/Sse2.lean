import VerifiedGarbage.Proof.ChaCha20.X86.Variant

/-!
# `vg_chacha20_xor` on x86: with SSE2

A variant of `ChaCha20Xor` on x86 (see `TCB/Emit.lean`): `vg_chacha20_xor`,
in the baseline ISA.
-/

namespace VG.Variants.ChaCha20Xor.X86.Sse2

def variant : Proof.ChaCha20.X86.XorImpl := .sse2

end VG.Variants.ChaCha20Xor.X86.Sse2
