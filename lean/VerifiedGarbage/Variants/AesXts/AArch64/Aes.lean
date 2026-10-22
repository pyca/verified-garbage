module

public import VerifiedGarbage.Proof.AesXts.AArch64.Variant

/-!
# XTS-AES of whole blocks on AArch64: in one pass, with the Cryptographic Extension

A variant of `AesXts` on AArch64 (see `TCB/Emit.lean`): `vg_aes_xts_encrypt_aes` and `vg_aes_xts_decrypt_aes`, which need the AES instructions (`FEAT_AES`).
-/

@[expose] public section

namespace VG.Variants.AesXts.AArch64.Aes

def variant : Proof.AesXts.AArch64.XtsImpl := .aes

end VG.Variants.AesXts.AArch64.Aes
