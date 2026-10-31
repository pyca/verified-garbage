module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Instances

/-! # The functions SM4-GCM calls on AArch64: Aes -/

@[expose] public section

namespace VG.Variants.Sm4Gcm.AArch64.Aes

def variant : Proof.Sm4Gcm.AArch64.GcmVariant := ⟨.aes⟩

end VG.Variants.Sm4Gcm.AArch64.Aes
