module

public import VerifiedGarbage.Proof.Aes.AArch64.Variant

/-! # `vg_aes_ctr32` on AArch64: the bitsliced implementation -/

@[expose] public section

namespace VG.Variants.AesCtr32.AArch64.Scalar

def variant : Proof.Aes.AArch64.Ctr32Impl := .scalar

end VG.Variants.AesCtr32.AArch64.Scalar
