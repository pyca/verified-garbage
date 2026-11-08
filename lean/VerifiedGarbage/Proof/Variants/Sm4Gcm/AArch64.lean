module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Instances

/-! # The implementations of `Sm4Gcm` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.Sm4Gcm.AArch64

def aes : Proof.Sm4Gcm.AArch64.GcmVariant := ⟨.aes⟩

def scalar : Proof.Sm4Gcm.AArch64.GcmVariant := ⟨.scalar⟩

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this). -/
def variants := [aes, scalar]

end VG.Proof.Variants.Sm4Gcm.AArch64
