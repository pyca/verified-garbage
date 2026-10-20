module

public import VerifiedGarbage.Proof.Variants.RsaMont.Arm.Base

/-! The Base callable ARMv7 Montgomery arithmetic backend. -/

@[expose] public section
namespace VG.Variants.RsaMont.Arm.Base

def variant : Proof.Bignum.Arm.MontBackend := Proof.Variants.RsaMont.Arm.Base.variant

end VG.Variants.RsaMont.Arm.Base
