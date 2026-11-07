module

public import VerifiedGarbage.Proof.Variants.FfdhExp.X86_64.Ifma

/-! # FFDH's exponentiation with AVX512_IFMA on x86-64 -/

@[expose] public section

namespace VG.Variants.FfdhExp.X86_64.Ifma

def variant : Proof.Ffdh.X86_64.ExpImpl := Proof.Variants.FfdhExp.X86_64.Ifma.variant

end VG.Variants.FfdhExp.X86_64.Ifma
