module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Variant

/-! # The functions AES-GCM calls on x86-64: Scalar -/

@[expose] public section

namespace VG.Variants.AesGcm.X86_64.Scalar

def variant : Proof.AesGcm.X86_64.GcmVariant := ⟨.scalar, .scalar, .scalar, none⟩

end VG.Variants.AesGcm.X86_64.Scalar
