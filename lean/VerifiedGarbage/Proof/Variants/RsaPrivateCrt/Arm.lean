module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm.Base
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm.Umaal

/-! # The implementations of `RsaPrivateCrt` on 32-bit ARM -/

@[expose] public section

namespace VG.Proof.Variants.RsaPrivateCrt.Arm

def base : Proof.Rsa.Arm.CrtImpl := Proof.Variants.RsaPrivateCrt.Arm.Base.variant

def umaal : Proof.Rsa.Arm.CrtImpl := Proof.Variants.RsaPrivateCrt.Arm.Umaal.variant

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [base, umaal]

end VG.Proof.Variants.RsaPrivateCrt.Arm
