module

public import VerifiedGarbage.Proof.Variants.Ffdh.Arm.Umaal

/-! # The Umaal implementation of native ARMv7 FFDH -/

@[expose] public section
namespace VG.Variants.Ffdh.Arm.Umaal

def variant : Proof.Ffdh.Arm.Backend := Proof.Variants.Ffdh.Arm.Umaal.variant

end VG.Variants.Ffdh.Arm.Umaal
