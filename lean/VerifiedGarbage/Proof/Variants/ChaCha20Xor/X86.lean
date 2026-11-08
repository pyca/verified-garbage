module

public import VerifiedGarbage.Proof.ChaCha20.X86.Variant

/-! # The implementations of `ChaCha20Xor` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.ChaCha20Xor.X86

def sse2 : Proof.ChaCha20.X86.XorImpl := .sse2

def ssse3 : Proof.ChaCha20.X86.XorImpl := .ssse3

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [ssse3, sse2]

end VG.Proof.Variants.ChaCha20Xor.X86
