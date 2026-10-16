module

public import VerifiedGarbage.Proof.AesGcm.X86.Callee
public import VerifiedGarbage.Proof.Aes.X86.VariantProof

/-!
# The functions AES-GCM calls on x86: Pclmul

A variant of `AesGcm` on x86 (see `TCB/Emit.lean`): `vg_aes_ctr32` and `vg_aes_expand_key_scratch`, and PCLMULQDQ for the hash (`vg_ghash_pclmul`).
-/

@[expose] public section

namespace VG.Variants.AesGcm.X86.Pclmul

def variant : Proof.AesGcm.X86.GcmVariant := ⟨.scalar, .pclmul⟩

end VG.Variants.AesGcm.X86.Pclmul
