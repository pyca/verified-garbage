module

public import VerifiedGarbage.Proof.Variants.MillerRabin.Arm.Base
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal

/-!
# The shared round on ARMv7 with `umaal`: the variant's code and proofs

The variant `VG.Variants.MillerRabin.Arm.Umaal.variant`
(`Variants/MillerRabin/Arm/Umaal.lean`): the baseline's code with each row
by `rowU` (`umaalRows`), whose proofs are the baseline's
(`umaalRows_verified`).
-/

@[expose] public section

namespace VG.Proof.Variants.MillerRabin.Arm.Umaal

open VG.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm VG.Proof.MillerRabin.Arm

theorem round_verified : Verified target (umaalRows Impl.MillerRabin.Arm.code) roundContract :=
  umaalRows_verified round_verified_lite

def variant : RoundImpl where
  code := umaalRows Impl.MillerRabin.Arm.code
  verified := round_verified
  stack := (armStack_umaalRows _).trans Base.variant.stack
  suffix := "_umaal"
  features := ["umaal"]

end VG.Proof.Variants.MillerRabin.Arm.Umaal
