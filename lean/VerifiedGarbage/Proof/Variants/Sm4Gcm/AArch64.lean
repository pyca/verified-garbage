module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Instances

/-! # The implementations of `Sm4Gcm` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.Sm4Gcm.AArch64

def sm4Aes : Proof.Sm4Gcm.AArch64.GcmVariant := ⟨.sm4, .aes⟩

def sm4 : Proof.Sm4Gcm.AArch64.GcmVariant := ⟨.sm4, .scalar⟩

def aes : Proof.Sm4Gcm.AArch64.GcmVariant := ⟨.scalar, .aes⟩

def neon : Proof.Sm4Gcm.AArch64.GcmVariant := ⟨.scalar, .neon⟩

def scalar : Proof.Sm4Gcm.AArch64.GcmVariant := ⟨.scalar, .scalar⟩

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [sm4Aes, sm4, aes, neon, scalar]

end VG.Proof.Variants.Sm4Gcm.AArch64
