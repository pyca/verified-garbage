module

public import VerifiedGarbage.Proof.ChaCha20.X86.Variant

/-! # The implementations of `ChaCha20Xor` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.ChaCha20Xor.X86

def sse2 : Proof.ChaCha20.X86.XorImpl := .sse2

def ssse3 : Proof.ChaCha20.X86.XorImpl := .ssse3

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [sse2, ssse3]

end VG.Proof.Variants.ChaCha20Xor.X86
