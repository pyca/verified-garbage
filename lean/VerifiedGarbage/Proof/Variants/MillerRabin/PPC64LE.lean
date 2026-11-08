module

public import VerifiedGarbage.Proof.Variants.MillerRabin.PPC64LE.Base

/-! # The implementations of `MillerRabin` on PPC64LE -/

@[expose] public section

namespace VG.Proof.Variants.MillerRabin.PPC64LE

def base : Proof.MillerRabin.PPC64LE.RoundImpl := Proof.Variants.MillerRabin.PPC64LE.Base.variant

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [base]

end VG.Proof.Variants.MillerRabin.PPC64LE
