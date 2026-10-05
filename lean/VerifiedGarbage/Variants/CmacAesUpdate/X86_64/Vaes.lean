import VerifiedGarbage.Proof.CmacAes.X86_64.Variant

/-!
# `vg_cmac_aes_update` on x86-64: by calls of `vg_aes_ctr32_vaes`

A variant of `CmacAesUpdate` on x86-64 (see `TCB/Emit.lean`):
`vg_cmac_aes_update_vaes`, which needs VAES and AVX2 (and AES-NI and SSSE3).
-/

namespace VG.Variants.CmacAesUpdate.X86_64.Vaes

def variant : Proof.CmacAes.X86_64.UpdateImpl := .ctr32 .vaes

end VG.Variants.CmacAesUpdate.X86_64.Vaes
