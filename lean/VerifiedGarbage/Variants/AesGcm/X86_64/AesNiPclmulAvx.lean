import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Ok
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee

/-!
# The functions AES-GCM calls on x86-64: AesNiPclmulAvx

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): AES-NI for the cipher (`vg_aes_ctr32_aesni`, `vg_aes_expand_key_aesni`) and PCLMULQDQ for the hash (`vg_ghash_pclmul`), with counter mode and GHASH interleaved in `vg_aes_gcm_encrypt_blocks_aesni_pclmul_avx` and `_decrypt_blocks_aesni_pclmul_avx` (`Impl.Gcm.X86_64.StitchAvx`, on 128-bit registers in `VEX.128`, which need AVX beyond the callees' features).
-/

namespace VG.Variants.AesGcm.X86_64.AesNiPclmulAvx

open VG VG.X86_64

/-- The interleaved loops of `Impl.Gcm.X86_64.StitchAvx`, from their proof. -/
def stitch : Proof.AesGcm.X86_64.StitchImpl where
  suffix := "_avx"
  features := ["avx"]
  enc := Impl.Gcm.X86_64.StitchAvx.enc
  dec := Impl.Gcm.X86_64.StitchAvx.dec
  ok := Proof.Gcm.X86_64.StitchAvx.stitch_ok
  encP := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide, ⟨_, by taint_decide⟩⟩
  decP := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide, ⟨_, by taint_decide⟩⟩

def variant : Proof.AesGcm.X86_64.GcmVariant := ⟨.aesni, .aesni, .pclmul, some stitch⟩

end VG.Variants.AesGcm.X86_64.AesNiPclmulAvx
