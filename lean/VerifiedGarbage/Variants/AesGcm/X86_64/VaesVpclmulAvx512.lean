import VerifiedGarbage.Proof.AesGcm.X86_64.Variant
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Lit

/-!
# The functions AES-GCM calls on x86-64: VaesVpclmulAvx512

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): VAES for the cipher (`vg_aes_ctr32_vaes`, with `vg_aes_expand_key_scratch_aesni`) and VPCLMULQDQ for the hash (`vg_ghash_vpclmul`), with counter mode and GHASH interleaved in `vg_aes_gcm_encrypt_blocks_vaes_vpclmul_avx512` and `_decrypt_blocks_vaes_vpclmul_avx512` on 512-bit registers (`Impl.Gcm.X86_64.StitchZ`), which need AVX512F and AVX512BW too, and out of place in `vg_aes_gcm_encrypt_blocks_to_vaes_vpclmul_avx512` (`Impl.Gcm.X86_64.StitchZTo`).
-/

namespace VG.Variants.AesGcm.X86_64.VaesVpclmulAvx512

open VG VG.X86_64

/-- The interleaved loops of `Impl.Gcm.X86_64.StitchZ` (their proof is `StitchName.ok`). -/
def stitch : Proof.AesGcm.X86_64.StitchPart where
  name := .vaesAvx512
  suffix := "_avx512"
  features := ["avx512f", "avx512bw"]
  encP := (⟨by lit_decide, by lit_decide, by lit_decide, by decide, by lit_decide, ⟨_, by taint_decide⟩⟩ : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchZ.enc)
  decP := (⟨by lit_decide, by lit_decide, by lit_decide, by decide, by lit_decide, ⟨_, by taint_decide⟩⟩ : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchZ.dec)
  pieceP := some
    ⟨(⟨by lit_decide, by lit_decide, by lit_decide, by decide, by lit_decide, ⟨_, by taint_decide⟩⟩ : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchZP.enc),
     (⟨by lit_decide, by lit_decide, by lit_decide, by decide, by lit_decide, ⟨_, by taint_decide⟩⟩ : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchZP.dec)⟩
  pieceR := some
    ⟨(⟨by lit_decide, by lit_decide, by lit_decide, by decide, by lit_decide, ⟨_, by taint_decide⟩⟩ : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchZH.encR true true),
     (⟨by lit_decide, by lit_decide, by lit_decide, by decide, by lit_decide, ⟨_, by taint_decide⟩⟩ : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchZH.dec true)⟩
  toPart := some
    { name := .vaesAvx512
      piece := ⟨by lit_decide, by lit_decide, by lit_decide, by decide, by lit_decide,
        ⟨_, by taint_decide⟩⟩
      pieceP := some ⟨⟨by lit_decide, by lit_decide, by lit_decide, by decide, by lit_decide,
        ⟨_, by taint_decide⟩⟩⟩
      pieceR := some ⟨⟨by lit_decide, by lit_decide, by lit_decide, by decide, by lit_decide,
        ⟨_, by taint_decide⟩⟩⟩ }

def variant : Proof.AesGcm.X86_64.GcmVariant := ⟨.vaes, .aesni, .vpclmul, some stitch⟩

end VG.Variants.AesGcm.X86_64.VaesVpclmulAvx512
