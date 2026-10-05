import VerifiedGarbage.Proof.AesGcm.X86.Callee

/-!
# The functions AES-GCM calls on x86: Pclmul

A variant of `AesGcm` on x86 (see `TCB/Emit.lean`): `vg_aes_ctr32` and `vg_aes_expand_key_scratch`, and PCLMULQDQ for the hash (`vg_ghash_pclmul`).
-/

namespace VG.Variants.AesGcm.X86.Pclmul

def variant : Proof.AesGcm.X86.GcmVariant := ⟨.scalar, .pclmul⟩

end VG.Variants.AesGcm.X86.Pclmul
