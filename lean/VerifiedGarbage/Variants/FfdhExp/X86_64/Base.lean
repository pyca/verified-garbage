module

public import VerifiedGarbage.Proof.Variants.FfdhExp.X86_64.Base

/-! # FFDH's baseline exponentiation on x86-64 -/

@[expose] public section

namespace VG.Variants.FfdhExp.X86_64.Base

def variant : Proof.Ffdh.X86_64.ExpImpl := Proof.Variants.FfdhExp.X86_64.Base.variant

end VG.Variants.FfdhExp.X86_64.Base
