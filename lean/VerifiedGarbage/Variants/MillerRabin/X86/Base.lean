module

public import VerifiedGarbage.Proof.Variants.MillerRabin.X86.Base

/-! # The baseline shared round on i686 -/

@[expose] public section
namespace VG.Variants.MillerRabin.X86.Base

def variant : Proof.MillerRabin.X86.RoundImpl := Proof.Variants.MillerRabin.X86.Base.variant

end VG.Variants.MillerRabin.X86.Base
