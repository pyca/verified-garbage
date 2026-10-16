module

public import VerifiedGarbage.Proof.AesGcm.X86.Callee
public import VerifiedGarbage.Proof.Aes.X86.VariantProof

/-!
# The functions AES-GCM calls on x86: AesNi

A variant of `AesGcm` on x86 (see `TCB/Emit.lean`): AES-NI for the cipher (`vg_aes_ctr32_aesni`, `vg_aes_expand_key_scratch_aesni`) and `vg_ghash`.
-/

@[expose] public section

namespace VG.Variants.AesGcm.X86.AesNi

def variant : Proof.AesGcm.X86.GcmVariant := ⟨.aesni, .scalar⟩

end VG.Variants.AesGcm.X86.AesNi
