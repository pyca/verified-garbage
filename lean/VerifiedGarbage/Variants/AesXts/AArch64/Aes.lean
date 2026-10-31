module

public import VerifiedGarbage.Proof.AesXts.AArch64.Variant

/-! # XTS-AES of whole blocks on AArch64: in one pass, with the Cryptographic Extension -/

@[expose] public section

namespace VG.Variants.AesXts.AArch64.Aes

def variant : Proof.AesXts.AArch64.XtsImpl := .aes

end VG.Variants.AesXts.AArch64.Aes
