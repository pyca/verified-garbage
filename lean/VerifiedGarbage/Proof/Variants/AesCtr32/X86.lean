module

public import VerifiedGarbage.Proof.Aes.X86.VariantProof
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86.Ssse3

/-! # The implementations of `AesCtr32` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.AesCtr32.X86

def aesNi : Proof.Aes.X86.Ctr32Impl := .aesni

def ssse3 : Proof.Aes.X86.Ctr32Impl := Ssse3.variant

def scalar : Proof.Aes.X86.Ctr32Impl := .scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [aesNi, ssse3, scalar]

end VG.Proof.Variants.AesCtr32.X86
