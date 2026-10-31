module

public import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant

/-! # `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` on x86-64: with VAES -/

@[expose] public section

namespace VG.Variants.AesBlocks.X86_64.Vaes

def variant : Proof.Aes.X86_64.BlocksImpl := .vaes

end VG.Variants.AesBlocks.X86_64.Vaes
