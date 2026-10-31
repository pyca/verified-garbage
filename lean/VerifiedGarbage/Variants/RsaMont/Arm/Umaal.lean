module

public import VerifiedGarbage.Proof.Variants.RsaMont.Arm.Umaal

/-! # The Umaal callable ARMv7 Montgomery arithmetic backend -/

@[expose] public section
namespace VG.Variants.RsaMont.Arm.Umaal

def variant : Proof.Bignum.Arm.MontBackend := Proof.Variants.RsaMont.Arm.Umaal.variant

end VG.Variants.RsaMont.Arm.Umaal
