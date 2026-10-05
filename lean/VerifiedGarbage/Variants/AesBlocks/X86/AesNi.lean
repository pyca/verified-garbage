import VerifiedGarbage.Proof.Aes.X86.BlocksVariant

/-!
# `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` on x86: AES-NI

A variant of `AesBlocks` on x86 (see `TCB/Emit.lean`):
`vg_aes_encrypt_blocks_aesni`, `vg_aes_decrypt_blocks_aesni` and
`vg_aes_expand_key_aesni`.
-/

namespace VG.Variants.AesBlocks.X86.AesNi

def variant : Proof.Aes.X86.BlocksImpl := .aesni

end VG.Variants.AesBlocks.X86.AesNi
