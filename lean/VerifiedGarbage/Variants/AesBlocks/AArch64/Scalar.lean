module

public import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant

/-! # `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` on AArch64: bitsliced -/

@[expose] public section

namespace VG.Variants.AesBlocks.AArch64.Scalar

def variant : Proof.Aes.AArch64.BlocksImpl := .scalar

end VG.Variants.AesBlocks.AArch64.Scalar
