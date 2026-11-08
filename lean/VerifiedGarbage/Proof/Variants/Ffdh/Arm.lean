module

public import VerifiedGarbage.Proof.Variants.Ffdh.Arm.Base
public import VerifiedGarbage.Proof.Variants.Ffdh.Arm.Umaal

/-! # The implementations of `Ffdh` on 32-bit ARM -/

@[expose] public section

namespace VG.Proof.Variants.Ffdh.Arm

def base : Proof.Ffdh.Arm.Backend := Proof.Variants.Ffdh.Arm.Base.variant

def umaal : Proof.Ffdh.Arm.Backend := Proof.Variants.Ffdh.Arm.Umaal.variant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this). -/
def variants := [umaal, base]

end VG.Proof.Variants.Ffdh.Arm
