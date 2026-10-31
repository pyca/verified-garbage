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
public import VerifiedGarbage.Proof.Weierstrass.Arm.PointBrainpoolP384r1
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Mont.Arm.Csub
public import VerifiedGarbage.Proof.Mont.Arm.Row
public import VerifiedGarbage.Proof.Mont.Arm.Step
public import VerifiedGarbage.Proof.Weierstrass.Arm.Fprog
public import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
public import VerifiedGarbage.Proof.Weierstrass.Arm.PointVerified
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Mont.Arm.Row
import VerifiedGarbage.Proof.Mont.Arm.Step
import VerifiedGarbage.Proof.Weierstrass.Arm.Fprog
import VerifiedGarbage.Proof.Weierstrass.Arm.PointVerified

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

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Weierstrass.Point.brainpoolp384r1.addApi.artifact Arm.target {
    code := Impl.Weierstrass.Arm.Point.pointAdd Spec.Weierstrass.Point.brainpoolp384r1
    verified := brainpoolp384r1_add_verified (fermat_of_law h.law) },
  Spec.Weierstrass.Point.brainpoolp384r1.doubleApi.artifact Arm.target {
    code := Impl.Weierstrass.Arm.Point.pointDouble Spec.Weierstrass.Point.brainpoolp384r1
    verified := brainpoolp384r1_double_verified (fermat_of_law h.law) }]

end VG.Generic.BrainpoolP384r1.Arm.PointBrainpoolP384r1
