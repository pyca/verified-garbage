module

public import VerifiedGarbage.Proof.AesXts.AArch64.Variant

/-! # XTS-AES of whole blocks on AArch64: by calls of the bitsliced `vg_aes_encrypt_blocks` -/

@[expose] public section

namespace VG.Variants.AesXts.AArch64.Scalar

def variant : Proof.AesXts.AArch64.XtsImpl := .blocks .scalar

end VG.Variants.AesXts.AArch64.Scalar
