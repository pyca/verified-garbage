module

public import VerifiedGarbage.Proof.Aes.X86_64.Variant

/-! # `vg_aes_ctr32` on x86-64: with AES-NI -/

@[expose] public section

namespace VG.Variants.AesCtr32.X86_64.AesNi

def variant : Proof.Aes.X86_64.Ctr32Impl := .aesni

end VG.Variants.AesCtr32.X86_64.AesNi
