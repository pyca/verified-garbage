module

public import VerifiedGarbage.Proof.Aes.X86.BlocksVariant

/-! # `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` on x86: bitsliced -/

@[expose] public section

namespace VG.Variants.AesBlocks.X86.Scalar

def variant : Proof.Aes.X86.BlocksImpl := .scalar

end VG.Variants.AesBlocks.X86.Scalar
