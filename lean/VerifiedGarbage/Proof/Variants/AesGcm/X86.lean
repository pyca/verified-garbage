module

public import VerifiedGarbage.Proof.AesGcm.X86.Callee
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86

/-! # The implementations of `AesGcm` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.AesGcm.X86

def aesNi : Proof.AesGcm.X86.GcmVariant := ⟨.aesni, .scalar⟩

def aesNiPclmul : Proof.AesGcm.X86.GcmVariant := ⟨.aesni, .pclmul⟩

def ssse3Pclmul : Proof.AesGcm.X86.GcmVariant := ⟨AesCtr32.X86.ssse3, .pclmul⟩

def ssse3 : Proof.AesGcm.X86.GcmVariant := ⟨AesCtr32.X86.ssse3, .scalar⟩

def scalar : Proof.AesGcm.X86.GcmVariant := ⟨.scalar, .scalar⟩

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [aesNiPclmul, aesNi, ssse3Pclmul, ssse3, scalar]

end VG.Proof.Variants.AesGcm.X86
