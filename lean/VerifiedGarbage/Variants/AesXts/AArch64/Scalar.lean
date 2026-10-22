module

public import VerifiedGarbage.Proof.AesXts.AArch64.Variant

/-!
# XTS-AES of whole blocks on AArch64: by calls of the bitsliced `vg_aes_encrypt_blocks`

A variant of `AesXts` on AArch64 (see `TCB/Emit.lean`): `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt`, in the baseline ISA.
-/

@[expose] public section

namespace VG.Variants.AesXts.AArch64.Scalar

def variant : Proof.AesXts.AArch64.XtsImpl := .blocks .scalar

end VG.Variants.AesXts.AArch64.Scalar
