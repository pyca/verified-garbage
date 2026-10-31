module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Variant

/-! # The functions AES-GCM calls on x86-64: AesNi -/

@[expose] public section

namespace VG.Variants.AesGcm.X86_64.AesNi

def variant : Proof.AesGcm.X86_64.GcmVariant := ⟨.aesni, .aesni, .scalar, none⟩

end VG.Variants.AesGcm.X86_64.AesNi
