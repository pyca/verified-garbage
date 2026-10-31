module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm.Umaal

/-! # `vg_rsa_private_crt` on ARMv7: with `umaal` -/

@[expose] public section

namespace VG.Variants.RsaPrivateCrt.Arm.Umaal

def variant : Proof.Rsa.Arm.CrtImpl := Proof.Variants.RsaPrivateCrt.Arm.Umaal.variant

end VG.Variants.RsaPrivateCrt.Arm.Umaal
