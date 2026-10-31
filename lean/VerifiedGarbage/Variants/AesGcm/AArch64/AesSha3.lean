module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee

/-! # The functions AES-GCM calls on AArch64: AesSha3 -/

@[expose] public section

namespace VG.Variants.AesGcm.AArch64.AesSha3

def variant : Proof.AesGcm.AArch64.GcmVariant := ⟨.aese, .aese, .aes, true⟩

end VG.Variants.AesGcm.AArch64.AesSha3
