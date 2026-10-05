import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant

/-!
# `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` on AArch64: bitsliced

A variant of `AesBlocks` on AArch64 (see `TCB/Emit.lean`):
`vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks` and `vg_aes_expand_key_scratch`, in
the baseline ISA.
-/

namespace VG.Variants.AesBlocks.AArch64.Scalar

def variant : Proof.Aes.AArch64.BlocksImpl := .scalar

end VG.Variants.AesBlocks.AArch64.Scalar
