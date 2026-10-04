import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant

/-!
# `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` on x86-64: with AES-NI

A variant of `AesBlocks` on x86-64 (see `TCB/Emit.lean`):
`vg_aes_encrypt_blocks_aesni`, `vg_aes_decrypt_blocks_aesni` and
`vg_aes_expand_key_aesni`, which need AES-NI.
-/

namespace VG.Variants.AesBlocks.X86_64.AesNi

def variant : Proof.Aes.X86_64.BlocksImpl := .aesni

end VG.Variants.AesBlocks.X86_64.AesNi
