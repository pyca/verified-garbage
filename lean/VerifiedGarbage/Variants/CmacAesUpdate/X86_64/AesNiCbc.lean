module

public import VerifiedGarbage.Proof.CmacAes.X86_64.Variant

/-! # `vg_cmac_aes_update` on x86-64: the chaining in AES-NI registers -/

@[expose] public section

namespace VG.Variants.CmacAesUpdate.X86_64.AesNiCbc

def variant : Proof.CmacAes.X86_64.UpdateImpl := .aesniCbc

end VG.Variants.CmacAesUpdate.X86_64.AesNiCbc
