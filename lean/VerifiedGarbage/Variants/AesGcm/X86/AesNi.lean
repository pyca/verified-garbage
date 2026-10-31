module

public import VerifiedGarbage.Proof.AesGcm.X86.Callee
public import VerifiedGarbage.Proof.Aes.X86.VariantProof

/-! # The functions AES-GCM calls on x86: AesNi -/

@[expose] public section

namespace VG.Variants.AesGcm.X86.AesNi

def variant : Proof.AesGcm.X86.GcmVariant := ⟨.aesni, .scalar⟩

end VG.Variants.AesGcm.X86.AesNi
