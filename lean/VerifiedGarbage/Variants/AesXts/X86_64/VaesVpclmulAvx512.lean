module

public import VerifiedGarbage.Proof.AesXts.X86_64.Variant

/-! # XTS-AES of whole blocks on x86-64: in one pass, sixteen blocks at a time, with AVX-512 VAES and VPCLMULQDQ -/

@[expose] public section

namespace VG.Variants.AesXts.X86_64.VaesVpclmulAvx512

def variant : Proof.AesXts.X86_64.XtsImpl := .vaesVpclmulAvx512

end VG.Variants.AesXts.X86_64.VaesVpclmulAvx512
