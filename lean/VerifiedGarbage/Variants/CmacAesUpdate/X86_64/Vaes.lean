module

public import VerifiedGarbage.Proof.CmacAes.X86_64.Variant

/-! # `vg_cmac_aes_update` on x86-64: by calls of `vg_aes_ctr32_vaes` -/

@[expose] public section

namespace VG.Variants.CmacAesUpdate.X86_64.Vaes

def variant : Proof.CmacAes.X86_64.UpdateImpl := .ctr32 .vaes

end VG.Variants.CmacAesUpdate.X86_64.Vaes
