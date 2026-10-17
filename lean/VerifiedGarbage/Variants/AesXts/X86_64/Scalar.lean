module

public import VerifiedGarbage.Proof.AesXts.X86_64.Variant

/-!
# XTS-AES of whole blocks on x86-64: by calls of the bitsliced `vg_aes_encrypt_blocks`

A variant of `AesXts` on x86-64 (see `TCB/Emit.lean`): `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt`, in the baseline ISA.
-/

@[expose] public section

namespace VG.Variants.AesXts.X86_64.Scalar

def variant : Proof.AesXts.X86_64.XtsImpl := .blocks .scalar

end VG.Variants.AesXts.X86_64.Scalar
