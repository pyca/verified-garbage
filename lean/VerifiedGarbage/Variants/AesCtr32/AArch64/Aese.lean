module

public import VerifiedGarbage.Proof.Aes.AArch64.Variant

/-! # `vg_aes_ctr32` on AArch64: with the Cryptographic Extension -/

@[expose] public section

namespace VG.Variants.AesCtr32.AArch64.Aese

def variant : Proof.Aes.AArch64.Ctr32Impl := .aese

end VG.Variants.AesCtr32.AArch64.Aese
