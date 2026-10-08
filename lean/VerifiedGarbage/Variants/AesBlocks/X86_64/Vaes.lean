import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant

/-!
# `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` on x86-64: with VAES

A variant of `AesBlocks` on x86-64 (see `TCB/Emit.lean`):
`vg_aes_encrypt_blocks_vaes` and `vg_aes_decrypt_blocks_vaes`, which need
VAES and AVX2 (and AES-NI), with `vg_aes_expand_key_scratch_aesni`.
-/

namespace VG.Variants.AesBlocks.X86_64.Vaes

def variant : Proof.Aes.X86_64.BlocksImpl := .vaes

end VG.Variants.AesBlocks.X86_64.Vaes
