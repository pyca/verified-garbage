import VerifiedGarbage.Proof.AesGcm.X86_64.Variant

/-!
# The functions AES-GCM calls on x86-64: AesNiPclmulAvx

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): AES-NI for the cipher (`vg_aes_ctr32_aesni`, `vg_aes_expand_key_scratch_aesni`) and PCLMULQDQ for the hash (`vg_ghash_pclmul`), with counter mode and GHASH interleaved in `vg_aes_gcm_encrypt_blocks_aesni_pclmul_avx` and `_decrypt_blocks_aesni_pclmul_avx` (`Impl.Gcm.X86_64.StitchAvx`, on 128-bit registers in `VEX.128`, which need AVX beyond the callees' features).
-/

namespace VG.Variants.AesGcm.X86_64.AesNiPclmulAvx

open VG VG.X86_64

theorem encPiece : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchAvx.enc :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide +kernel, ⟨_, by taint_decide⟩⟩

theorem decPiece : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchAvx.dec :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide +kernel, ⟨_, by taint_decide⟩⟩

/-- The interleaved loops of `Impl.Gcm.X86_64.StitchAvx` (their proof is `StitchName.ok`). -/
def stitch : Proof.AesGcm.X86_64.StitchPart where
  name := .aesniAvx
  suffix := "_avx"
  features := ["avx"]
  encP := encPiece
  decP := decPiece
  encPP := encPiece
  decPP := decPiece

def variant : Proof.AesGcm.X86_64.GcmVariant := ⟨.aesni, .aesni, .pclmul, some stitch⟩

end VG.Variants.AesGcm.X86_64.AesNiPclmulAvx
