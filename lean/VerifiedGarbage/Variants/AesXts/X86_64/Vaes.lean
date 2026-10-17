module

public import VerifiedGarbage.Proof.AesXts.X86_64.Variant

/-!
# XTS-AES of whole blocks on x86-64: by calls of `vg_aes_encrypt_blocks_vaes`

A variant of `AesXts` on x86-64 (see `TCB/Emit.lean`): `vg_aes_xts_encrypt_vaes` and `vg_aes_xts_decrypt_vaes`, which need VAES and AVX2 (and AES-NI and AVX).
-/

@[expose] public section

namespace VG.Variants.AesXts.X86_64.Vaes

def variant : Proof.AesXts.X86_64.XtsImpl := .blocks .vaes

end VG.Variants.AesXts.X86_64.Vaes
