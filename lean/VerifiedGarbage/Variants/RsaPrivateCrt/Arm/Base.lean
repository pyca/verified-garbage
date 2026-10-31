module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm.Base

/-! # `vg_rsa_private_crt` on ARMv7: the baseline -/

@[expose] public section

namespace VG.Variants.RsaPrivateCrt.Arm.Base

def variant : Proof.Rsa.Arm.CrtImpl := Proof.Variants.RsaPrivateCrt.Arm.Base.variant

end VG.Variants.RsaPrivateCrt.Arm.Base
