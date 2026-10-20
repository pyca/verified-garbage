module

public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64.VaesVpclmul

/-!
# The functions AES-GCM calls on x86-64: VaesVpclmul

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): VAES for the cipher (`vg_aes_ctr32_vaes`, with `vg_aes_expand_key_scratch_aesni`) and VPCLMULQDQ for the hash (`vg_ghash_vpclmul`), with counter mode and GHASH interleaved in `vg_aes_gcm_encrypt_blocks_vaes_vpclmul` and `_decrypt_blocks_vaes_vpclmul` (`Impl.Gcm.X86_64.Stitch`, on 256-bit registers, which need no CPU features beyond the callees'), and out of place in `vg_aes_gcm_encrypt_blocks_to_vaes_vpclmul` (`Impl.Gcm.X86_64.StitchTo`).
-/

@[expose] public section

namespace VG.Variants.AesGcm.X86_64.VaesVpclmul

open VG VG.X86_64

def variant : Proof.AesGcm.X86_64.GcmVariant := Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant

end VG.Variants.AesGcm.X86_64.VaesVpclmul
