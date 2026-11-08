module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee

/-! # The implementations of `AesGcm` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.AesGcm.AArch64

def aes : Proof.AesGcm.AArch64.GcmVariant := ⟨.aese, .aese, .aes, false⟩

def aesSha3 : Proof.AesGcm.AArch64.GcmVariant := ⟨.aese, .aese, .aes, true⟩

def scalar : Proof.AesGcm.AArch64.GcmVariant := ⟨.scalar, .scalar, .scalar, false⟩

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [aesSha3, aes, scalar]

end VG.Proof.Variants.AesGcm.AArch64
