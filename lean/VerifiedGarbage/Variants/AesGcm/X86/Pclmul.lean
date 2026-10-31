module

public import VerifiedGarbage.Proof.AesGcm.X86.Callee
public import VerifiedGarbage.Proof.Aes.X86.VariantProof

/-! # The functions AES-GCM calls on x86: Pclmul -/

@[expose] public section

namespace VG.Variants.AesGcm.X86.Pclmul

def variant : Proof.AesGcm.X86.GcmVariant := ⟨.scalar, .pclmul⟩

end VG.Variants.AesGcm.X86.Pclmul
