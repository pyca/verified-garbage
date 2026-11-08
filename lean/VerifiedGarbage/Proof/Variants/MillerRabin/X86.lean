module

public import VerifiedGarbage.Proof.Variants.MillerRabin.X86.Base

/-! # The implementations of `MillerRabin` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.MillerRabin.X86

def base : Proof.MillerRabin.X86.RoundImpl := Proof.Variants.MillerRabin.X86.Base.variant

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [base]

end VG.Proof.Variants.MillerRabin.X86
