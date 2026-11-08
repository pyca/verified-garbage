module

public import VerifiedGarbage.Proof.AesGcm.X86.Callee
public import VerifiedGarbage.Proof.Aes.X86.VariantProof

/-! # The implementations of `AesGcm` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.AesGcm.X86

def aesNi : Proof.AesGcm.X86.GcmVariant := ⟨.aesni, .scalar⟩

def aesNiPclmul : Proof.AesGcm.X86.GcmVariant := ⟨.aesni, .pclmul⟩

def pclmul : Proof.AesGcm.X86.GcmVariant := ⟨.scalar, .pclmul⟩

def scalar : Proof.AesGcm.X86.GcmVariant := ⟨.scalar, .scalar⟩

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [aesNiPclmul, aesNi, pclmul, scalar]

end VG.Proof.Variants.AesGcm.X86
