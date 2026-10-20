module

public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64.VaesVpclmulAvx512

/-!
# The functions AES-GCM calls on x86-64: VaesVpclmulAvx512

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): VAES for the cipher (`vg_aes_ctr32_vaes`, with `vg_aes_expand_key_scratch_aesni`) and VPCLMULQDQ for the hash (`vg_ghash_vpclmul`), with counter mode and GHASH interleaved in `vg_aes_gcm_encrypt_blocks_vaes_vpclmul_avx512` and `_decrypt_blocks_vaes_vpclmul_avx512` on 512-bit registers (`Impl.Gcm.X86_64.StitchZ`), which need AVX512F and AVX512BW too, and out of place in `vg_aes_gcm_encrypt_blocks_to_vaes_vpclmul_avx512` (`Impl.Gcm.X86_64.StitchZTo`).
-/

@[expose] public section

namespace VG.Variants.AesGcm.X86_64.VaesVpclmulAvx512

open VG VG.X86_64

def variant : Proof.AesGcm.X86_64.GcmVariant := Proof.Variants.AesGcm.X86_64.VaesVpclmulAvx512.variant

end VG.Variants.AesGcm.X86_64.VaesVpclmulAvx512
