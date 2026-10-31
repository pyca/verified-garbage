module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee

/-! # The functions AES-GCM calls on AArch64: Aes -/

@[expose] public section

namespace VG.Variants.AesGcm.AArch64.Aes

def variant : Proof.AesGcm.AArch64.GcmVariant := ⟨.aese, .aese, .aes, false⟩

end VG.Variants.AesGcm.AArch64.Aes
