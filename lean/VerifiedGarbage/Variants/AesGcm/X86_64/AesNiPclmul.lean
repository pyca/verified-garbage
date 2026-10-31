module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Variant

/-! # The functions AES-GCM calls on x86-64: AesNiPclmul -/

@[expose] public section

namespace VG.Variants.AesGcm.X86_64.AesNiPclmul

def variant : Proof.AesGcm.X86_64.GcmVariant := ⟨.aesni, .aesni, .pclmul, none⟩

end VG.Variants.AesGcm.X86_64.AesNiPclmul
