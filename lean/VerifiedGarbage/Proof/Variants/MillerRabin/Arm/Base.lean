module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.Variants.RsaMont.Arm.Base
public import VerifiedGarbage.Proof.MillerRabin.Arm.Verified

import VerifiedGarbage.Proof.Framework.Lit

/-!
# The baseline shared round on ARMv7: the variant's code and proofs

The variant `VG.Variants.MillerRabin.Arm.Base.variant`
(`Variants/MillerRabin/Arm/Base.lean`), with the proofs its interface asks
for.
-/

@[expose] public section

namespace VG.Proof.Variants.MillerRabin.Arm.Base

open VG.Proof.MillerRabin.Arm

def variant : RoundImpl where
  code := Impl.MillerRabin.Arm.code
  verified := round_verified_lite
  stack := by decide +kernel
  icallFree := by lit_decide
  mont := Proof.Variants.RsaMont.Arm.Base.variant
  suffix := ""
  features := []

end VG.Proof.Variants.MillerRabin.Arm.Base
