module

public import VerifiedGarbage.Proof.Variants.MillerRabin.X86.Base

/-! # The implementations of `MillerRabin` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.MillerRabin.X86

def base : Proof.MillerRabin.X86.RoundImpl := Proof.Variants.MillerRabin.X86.Base.variant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [base]

end VG.Proof.Variants.MillerRabin.X86
