module

public import VerifiedGarbage.Impl.Secp256k1.Point

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.Arm.PointSecp256k1
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.Impl.Weierstrass.Arm.Point
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves

/-!
# secp256k1's point addition and doubling on 32-bit ARM

`vg_secp256k1_point_add` and `vg_secp256k1_point_double`
(`Spec/Weierstrass/Point.lean`), calling the Montgomery functions of
secp256k1's prime. A generic file (see `TCB/Emit.lean`) over secp256k1's group law
`h`, the variant `Variants/Secp256k1/Arm/Law.lean`, which gives Fermat's little
theorem in `Fin p`, so that `R⁻¹ = R^(p-2)` in the contracts.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.Arm.PointSecp256k1

open VG.Proof.Weierstrass.Arm.Point

/-- How the functions work. -/
def notes : List String := ["The function saves `lr` in its own working space and keeps `ws` in \
  `r12`, and computes Renes, Costello and Batina's 40 steps by calls of `vg_secp256k1_mul_mod_p`, \
  `vg_secp256k1_add_mod_p` and `vg_secp256k1_sub_mod_p` on fixed offsets of `ws`, `movw` immediates in \
  `r1`–`r3`. It writes no register but `r0`–`r3`, `r12` and `lr`."]

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Impl.Secp256k1.point.addApi.artifact Arm.target {
    notes := notes
    code := Impl.Weierstrass.Arm.Point.pointAdd Impl.Secp256k1.point
    verified := secp256k1_add_verified (fermat_of_law h.law) },
  Impl.Secp256k1.point.doubleApi.artifact Arm.target {
    notes := notes
    code := Impl.Weierstrass.Arm.Point.pointDouble Impl.Secp256k1.point
    verified := secp256k1_double_verified (fermat_of_law h.law) }]

end VG.Generic.Secp256k1.Arm.PointSecp256k1
