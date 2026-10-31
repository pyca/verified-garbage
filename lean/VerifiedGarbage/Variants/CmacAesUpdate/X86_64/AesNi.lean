module

public import VerifiedGarbage.Proof.CmacAes.X86_64.Variant

/-! # `vg_cmac_aes_update` on x86-64: by calls of `vg_aes_ctr32_aesni` -/

@[expose] public section

namespace VG.Variants.CmacAesUpdate.X86_64.AesNi

def variant : Proof.CmacAes.X86_64.UpdateImpl := .ctr32 .aesni

end VG.Variants.CmacAesUpdate.X86_64.AesNi
