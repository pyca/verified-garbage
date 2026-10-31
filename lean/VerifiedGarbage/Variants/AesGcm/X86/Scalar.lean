module

public import VerifiedGarbage.Proof.AesGcm.X86.Callee
public import VerifiedGarbage.Proof.Aes.X86.VariantProof

/-! # The functions AES-GCM calls on x86: Scalar -/

@[expose] public section

namespace VG.Variants.AesGcm.X86.Scalar

def variant : Proof.AesGcm.X86.GcmVariant := ⟨.scalar, .scalar⟩

end VG.Variants.AesGcm.X86.Scalar
