module

public import VerifiedGarbage.Proof.AesXts.X86_64.Variant

/-!
# XTS-AES of whole blocks on x86-64: by calls of `vg_aes_encrypt_blocks_aesni`

A variant of `AesXts` on x86-64 (see `TCB/Emit.lean`): `vg_aes_xts_encrypt_aesni` and `vg_aes_xts_decrypt_aesni`, which need AES-NI.
-/

@[expose] public section

namespace VG.Variants.AesXts.X86_64.AesNi

def variant : Proof.AesXts.X86_64.XtsImpl := .blocks .aesni

end VG.Variants.AesXts.X86_64.AesNi
