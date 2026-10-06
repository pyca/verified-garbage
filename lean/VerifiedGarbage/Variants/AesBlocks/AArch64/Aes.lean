import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant

/-!
# `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` on AArch64: with the Cryptographic Extension

A variant of `AesBlocks` on AArch64 (see `TCB/Emit.lean`):
`vg_aes_encrypt_blocks_aes`, `vg_aes_decrypt_blocks_aes` and
`vg_aes_expand_key_scratch_aes`, which need the AES instructions (`FEAT_AES`).
-/

namespace VG.Variants.AesBlocks.AArch64.Aes

def variant : Proof.Aes.AArch64.BlocksImpl := .aese

end VG.Variants.AesBlocks.AArch64.Aes
