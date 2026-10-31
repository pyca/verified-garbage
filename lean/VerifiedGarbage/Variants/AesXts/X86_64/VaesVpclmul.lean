module

public import VerifiedGarbage.Proof.AesXts.X86_64.Variant

/-! # XTS-AES of whole blocks on x86-64: in one pass, with VAES and VPCLMULQDQ -/

@[expose] public section

namespace VG.Variants.AesXts.X86_64.VaesVpclmul

def variant : Proof.AesXts.X86_64.XtsImpl := .vaesVpclmul

end VG.Variants.AesXts.X86_64.VaesVpclmul
