module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.Arm.PointBrainpoolP384r1
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.Impl.Weierstrass.Arm.Point
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves

/-!
# brainpoolP384r1's point addition and doubling on 32-bit ARM

`vg_brainpoolp384r1_point_add` and `vg_brainpoolp384r1_point_double`
(`Spec/Weierstrass/Point.lean`), calling the Montgomery functions of
brainpoolP384r1's prime. A generic file (see `TCB/Emit.lean`) over brainpoolP384r1's group law
`h`, the variant `Variants/BrainpoolP384r1/Arm/Law.lean`, which gives Fermat's little
theorem in `Fin p`, so that `R⁻¹ = R^(p-2)` in the contracts.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.Arm.PointBrainpoolP384r1

open VG.Proof.Weierstrass.Arm.Point

/-- How the functions work. -/
def notes : List String := ["The function saves `lr` in its own working space and keeps `ws` in \
  `r12`, and computes Renes, Costello and Batina's 40 steps by calls of `vg_brainpoolp384r1_mul_mod_p`, \
  `vg_brainpoolp384r1_add_mod_p` and `vg_brainpoolp384r1_sub_mod_p` on fixed offsets of `ws`, `movw` immediates in \
  `r1`–`r3`. It writes no register but `r0`–`r3`, `r12` and `lr`."]

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Weierstrass.Point.brainpoolp384r1.addApi.artifact Arm.target {
    notes := notes
    code := Impl.Weierstrass.Arm.Point.pointAdd Spec.Weierstrass.Point.brainpoolp384r1
    verified := brainpoolp384r1_add_verified (fermat_of_law h.law) },
  Spec.Weierstrass.Point.brainpoolp384r1.doubleApi.artifact Arm.target {
    notes := notes
    code := Impl.Weierstrass.Arm.Point.pointDouble Spec.Weierstrass.Point.brainpoolp384r1
    verified := brainpoolp384r1_double_verified (fermat_of_law h.law) }]

end VG.Generic.BrainpoolP384r1.Arm.PointBrainpoolP384r1
