import VerifiedGarbage.Proof.AesGcm.X86_64.Variant

/-!
# The functions AES-GCM calls on x86-64: VaesVpclmul

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): VAES for the cipher (`vg_aes_ctr32_vaes`, with `vg_aes_expand_key_scratch_aesni`) and VPCLMULQDQ for the hash (`vg_ghash_vpclmul`), with counter mode and GHASH interleaved in `vg_aes_gcm_encrypt_blocks_vaes_vpclmul` and `_decrypt_blocks_vaes_vpclmul` (`Impl.Gcm.X86_64.Stitch`, on 256-bit registers, which need no CPU features beyond the callees').
-/

namespace VG.Variants.AesGcm.X86_64.VaesVpclmul

open VG VG.X86_64

theorem encPiece : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.Stitch.enc :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide +kernel, ⟨_, by taint_decide⟩⟩

theorem decPiece : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.Stitch.dec :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide +kernel, ⟨_, by taint_decide⟩⟩

/-- The interleaved loops of `Impl.Gcm.X86_64.Stitch` (their proof is `StitchName.ok`). -/
def stitch : Proof.AesGcm.X86_64.StitchPart where
  name := .vaes
  suffix := ""
  features := []
  encP := encPiece
  decP := decPiece
  encPP := encPiece
  decPP := decPiece

def variant : Proof.AesGcm.X86_64.GcmVariant := ⟨.vaes, .aesni, .vpclmul, some stitch⟩

end VG.Variants.AesGcm.X86_64.VaesVpclmul
