module

public import VerifiedGarbage.Proof.CmacAes.AArch64.Variant

@[expose] public section

namespace VG.Variants.CmacAesUpdate.AArch64.Aese
def variant : Proof.CmacAes.AArch64.UpdateImpl := .ctr32 .aese
end VG.Variants.CmacAesUpdate.AArch64.Aese
