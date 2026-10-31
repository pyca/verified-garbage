module

public import VerifiedGarbage.Proof.AesXts.X86_64.Variant

/-! # XTS-AES of whole blocks on x86-64: by calls of `vg_aes_encrypt_blocks_vaes` -/

@[expose] public section

namespace VG.Variants.AesXts.X86_64.Vaes

def variant : Proof.AesXts.X86_64.XtsImpl := .blocks .vaes

end VG.Variants.AesXts.X86_64.Vaes
