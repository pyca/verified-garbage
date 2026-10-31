module

public import VerifiedGarbage.Proof.CmacAes.X86_64.Variant

/-! # `vg_cmac_aes_update` on x86-64: by calls of the bitsliced `vg_aes_ctr32` -/

@[expose] public section

namespace VG.Variants.CmacAesUpdate.X86_64.Scalar

def variant : Proof.CmacAes.X86_64.UpdateImpl := .ctr32 .scalar

end VG.Variants.CmacAesUpdate.X86_64.Scalar
