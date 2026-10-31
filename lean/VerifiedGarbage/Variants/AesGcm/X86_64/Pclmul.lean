module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Variant

/-! # The functions AES-GCM calls on x86-64: Pclmul -/

@[expose] public section

namespace VG.Variants.AesGcm.X86_64.Pclmul

def variant : Proof.AesGcm.X86_64.GcmVariant := ⟨.scalar, .scalar, .pclmul, none⟩

end VG.Variants.AesGcm.X86_64.Pclmul
