module

public import VerifiedGarbage.Proof.Aes.X86.BlocksVariant

/-! # `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` on x86: AES-NI -/

@[expose] public section

namespace VG.Variants.AesBlocks.X86.AesNi

def variant : Proof.Aes.X86.BlocksImpl := .aesni

end VG.Variants.AesBlocks.X86.AesNi
