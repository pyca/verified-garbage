import VerifiedGarbage.Proof.Aes.X86.BlocksVariant

/-!
# `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` on x86: bitsliced

A variant of `AesBlocks` on x86 (see `TCB/Emit.lean`):
`vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks` and `vg_aes_expand_key_scratch`, in
the baseline ISA.
-/

namespace VG.Variants.AesBlocks.X86.Scalar

def variant : Proof.Aes.X86.BlocksImpl := .scalar

end VG.Variants.AesBlocks.X86.Scalar
