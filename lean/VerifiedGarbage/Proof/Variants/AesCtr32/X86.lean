module

public import VerifiedGarbage.Proof.Aes.X86.VariantProof

/-! # The implementations of `AesCtr32` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.AesCtr32.X86

def aesNi : Proof.Aes.X86.Ctr32Impl := .aesni

def scalar : Proof.Aes.X86.Ctr32Impl := .scalar

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [aesNi, scalar]

end VG.Proof.Variants.AesCtr32.X86
