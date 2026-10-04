import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls

/-!
# The functions AES-GCM calls on x86-64: VaesVpclmulAvx512

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): VAES for the cipher (`vg_aes_ctr32_vaes`, with `vg_aes_expand_key_aesni`) and VPCLMULQDQ for the hash (`vg_ghash_vpclmul`), with counter mode and GHASH interleaved in `vg_aes_gcm_encrypt_blocks_vaes_vpclmul_avx512` and `_decrypt_blocks_vaes_vpclmul_avx512` on 512-bit registers (`Impl.Gcm.X86_64.StitchZ`), which need AVX512F and AVX512BW too.
-/

namespace VG.Variants.AesGcm.X86_64.VaesVpclmulAvx512

open VG VG.X86_64

/-- The interleaved loops of `Impl.Gcm.X86_64.StitchZ`, from their proof. -/
def stitch : Proof.AesGcm.X86_64.StitchImpl where
  suffix := "_avx512"
  features := ["avx512f", "avx512bw"]
  enc := Impl.Gcm.X86_64.StitchZ.enc
  dec := Impl.Gcm.X86_64.StitchZ.dec
  ok := Proof.Gcm.X86_64.StitchZ.stitch_ok
  encP := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide, ⟨_, by taint_decide⟩⟩
  decP := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide, ⟨_, by taint_decide⟩⟩

def variant : Proof.AesGcm.X86_64.GcmImpl := ⟨.vaes, .aesni, .vpclmul, some stitch⟩

end VG.Variants.AesGcm.X86_64.VaesVpclmulAvx512
