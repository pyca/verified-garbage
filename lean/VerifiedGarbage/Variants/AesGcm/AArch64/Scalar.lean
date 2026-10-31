module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee

/-! # The functions AES-GCM calls on AArch64: Scalar -/

@[expose] public section

namespace VG.Variants.AesGcm.AArch64.Scalar

def variant : Proof.AesGcm.AArch64.GcmVariant := ⟨.scalar, .scalar, .scalar, false⟩

end VG.Variants.AesGcm.AArch64.Scalar
