module

public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64.AesNiPclmulAvx

/-!
# The functions AES-GCM calls on x86-64: AesNiPclmulAvx

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): AES-NI for the cipher (`vg_aes_ctr32_aesni`, `vg_aes_expand_key_scratch_aesni`) and PCLMULQDQ for the hash (`vg_ghash_pclmul`), with counter mode and GHASH interleaved in `vg_aes_gcm_encrypt_blocks_aesni_pclmul_avx` and `_decrypt_blocks_aesni_pclmul_avx` (`Impl.Gcm.X86_64.StitchAvx8`, on 128-bit registers in `VEX.128`, which need AVX beyond the callees' features); with a prepared key context, `StitchAvx8.encR` and `StitchAvx8.decR`, which load the powers of the hash subkey from it.
-/

@[expose] public section

namespace VG.Variants.AesGcm.X86_64.AesNiPclmulAvx

open VG VG.X86_64

def variant : Proof.AesGcm.X86_64.GcmVariant := Proof.Variants.AesGcm.X86_64.AesNiPclmulAvx.variant

end VG.Variants.AesGcm.X86_64.AesNiPclmulAvx
