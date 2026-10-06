import VerifiedGarbage.Proof.AesGcm.X86_64.Variant

/-!
# The functions AES-GCM calls on x86-64: VaesVpclmulAvx512

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): VAES for the cipher (`vg_aes_ctr32_vaes`, with `vg_aes_expand_key_scratch_aesni`) and VPCLMULQDQ for the hash (`vg_ghash_vpclmul`), with counter mode and GHASH interleaved in `vg_aes_gcm_encrypt_blocks_vaes_vpclmul_avx512` and `_decrypt_blocks_vaes_vpclmul_avx512` on 512-bit registers (`Impl.Gcm.X86_64.StitchZ`), which need AVX512F and AVX512BW too.
-/

namespace VG.Variants.AesGcm.X86_64.VaesVpclmulAvx512

open VG VG.X86_64

theorem encPiece : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchZ.enc :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide +kernel, ⟨_, by taint_decide⟩⟩

theorem decPiece : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchZ.dec :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide +kernel, ⟨_, by taint_decide⟩⟩

/-- The interleaved loops of `Impl.Gcm.X86_64.StitchZ` (their proof is `StitchName.ok`). -/
def stitch : Proof.AesGcm.X86_64.StitchPart where
  name := .vaesAvx512
  suffix := "_avx512"
  features := ["avx512f", "avx512bw"]
  encP := encPiece
  decP := decPiece
  encPP := (⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide +kernel, ⟨_, by taint_decide⟩⟩ : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchZP.enc)
  decPP := (⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide +kernel, ⟨_, by taint_decide⟩⟩ : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchZP.dec)

def variant : Proof.AesGcm.X86_64.GcmVariant := ⟨.vaes, .aesni, .vpclmul, some stitch⟩

end VG.Variants.AesGcm.X86_64.VaesVpclmulAvx512
