import VerifiedGarbage.Proof.AesGcm.X86_64.Variant
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Ct

/-!
# The functions AES-GCM calls on x86-64: AesNiPclmulAvx

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): AES-NI for the cipher (`vg_aes_ctr32_aesni`, `vg_aes_expand_key_scratch_aesni`) and PCLMULQDQ for the hash (`vg_ghash_pclmul`), with counter mode and GHASH interleaved in `vg_aes_gcm_encrypt_blocks_aesni_pclmul_avx` and `_decrypt_blocks_aesni_pclmul_avx` (`Impl.Gcm.X86_64.StitchAvx8`, on 128-bit registers in `VEX.128`, which need AVX beyond the callees' features).
-/

namespace VG.Variants.AesGcm.X86_64.AesNiPclmulAvx

open VG VG.X86_64

/-- The eight-state interleaved loops of `Impl.Gcm.X86_64.StitchAvx8` (their proof is `StitchName.ok`). -/
def stitch : Proof.AesGcm.X86_64.StitchPart where
  name := .aesniAvx
  suffix := "_avx"
  features := ["avx"]
  encP := Proof.Gcm.X86_64.StitchAvx8.enc_piece
  decP := Proof.Gcm.X86_64.StitchAvx8.dec_piece

def variant : Proof.AesGcm.X86_64.GcmVariant := ⟨.aesni, .aesni, .pclmul, some stitch⟩

end VG.Variants.AesGcm.X86_64.AesNiPclmulAvx
