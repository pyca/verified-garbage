module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Instances

/-! # The functions SM4-GCM calls on AArch64: Scalar -/

@[expose] public section

namespace VG.Variants.Sm4Gcm.AArch64.Scalar

def variant : Proof.Sm4Gcm.AArch64.GcmVariant := ⟨.scalar⟩

end VG.Variants.Sm4Gcm.AArch64.Scalar
