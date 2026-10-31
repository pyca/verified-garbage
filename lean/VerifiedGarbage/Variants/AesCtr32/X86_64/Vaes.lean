module

public import VerifiedGarbage.Proof.Aes.X86_64.Variant

/-! # `vg_aes_ctr32` on x86-64: with VAES -/

@[expose] public section

namespace VG.Variants.AesCtr32.X86_64.Vaes

def variant : Proof.Aes.X86_64.Ctr32Impl := .vaes

end VG.Variants.AesCtr32.X86_64.Vaes
