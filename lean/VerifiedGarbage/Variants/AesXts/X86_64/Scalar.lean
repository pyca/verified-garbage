module

public import VerifiedGarbage.Proof.AesXts.X86_64.Variant

/-! # XTS-AES of whole blocks on x86-64: by calls of the bitsliced `vg_aes_encrypt_blocks` -/

@[expose] public section

namespace VG.Variants.AesXts.X86_64.Scalar

def variant : Proof.AesXts.X86_64.XtsImpl := .blocks .scalar

end VG.Variants.AesXts.X86_64.Scalar
