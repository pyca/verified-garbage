module

public import VerifiedGarbage.Proof.AesGcm.X86.Callee
public import VerifiedGarbage.Proof.Aes.X86.VariantProof

/-! # The functions AES-GCM calls on x86: AesNiPclmul -/

@[expose] public section

namespace VG.Variants.AesGcm.X86.AesNiPclmul

def variant : Proof.AesGcm.X86.GcmVariant := ⟨.aesni, .pclmul⟩

end VG.Variants.AesGcm.X86.AesNiPclmul
