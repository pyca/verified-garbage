import VerifiedGarbage.Proof.CmacAes.X86_64.Variant

/-!
# `vg_cmac_aes_update` on x86-64: the chaining in AES-NI registers

A variant of `CmacAesUpdate` on x86-64 (see `TCB/Emit.lean`):
`vg_cmac_aes_update_aesni_cbc`, which needs AES-NI, with
`vg_aes_ctr32_aesni` (which needs SSSE3 too) for its callers' counter mode.
-/

namespace VG.Variants.CmacAesUpdate.X86_64.AesNiCbc

def variant : Proof.CmacAes.X86_64.UpdateImpl := .aesniCbc

end VG.Variants.CmacAesUpdate.X86_64.AesNiCbc
