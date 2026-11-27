module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm.Backend
public import VerifiedGarbage.Proof.Variants.RsaMont.Arm

/-! # The implementations of `RsaPrivateCrt` on 32-bit ARM -/

@[expose] public section

namespace VG.Proof.Variants.RsaPrivateCrt.Arm

/-- Every implementation, best first, one for each Montgomery product it
calls (`RsaMont.Arm.variants`): each function generic over them is emitted
with each (the registration files that import this), and its dispatcher
tries them in this order. -/
def variants : List Proof.Rsa.Arm.CrtImpl :=
  Proof.Variants.RsaMont.Arm.variants.map Proof.Variants.RsaPrivateCrt.Arm.Backend.variant

end VG.Proof.Variants.RsaPrivateCrt.Arm
