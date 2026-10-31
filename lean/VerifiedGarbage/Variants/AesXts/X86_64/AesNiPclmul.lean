module

public import VerifiedGarbage.Proof.AesXts.X86_64.Variant

/-! # XTS-AES of whole blocks on x86-64: in one pass, with AES-NI and PCLMULQDQ -/

@[expose] public section

namespace VG.Variants.AesXts.X86_64.AesNiPclmul

def variant : Proof.AesXts.X86_64.XtsImpl := .aesniPclmul

end VG.Variants.AesXts.X86_64.AesNiPclmul
