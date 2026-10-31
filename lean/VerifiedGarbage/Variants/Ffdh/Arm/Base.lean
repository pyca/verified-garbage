module

public import VerifiedGarbage.Proof.Variants.Ffdh.Arm.Base

/-! # The Base implementation of native ARMv7 FFDH -/

@[expose] public section
namespace VG.Variants.Ffdh.Arm.Base

def variant : Proof.Ffdh.Arm.Backend := Proof.Variants.Ffdh.Arm.Base.variant

end VG.Variants.Ffdh.Arm.Base
