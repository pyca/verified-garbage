module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.Impl.Weierstrass.Arm.Point
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.Spec.X25519
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

public import VerifiedGarbage.Proof.Weierstrass.Arm.PointP224Umaal

/-! # P-224's point addition and doubling on 32-bit ARM -/

@[expose] public section

namespace VG.Generic.P224.Arm.PointP224

open VG.Proof.Weierstrass.Arm.Point

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.Weierstrass.Point.p224.addApi.artifact Arm.target {
    code := Impl.Weierstrass.Arm.Point.pointAdd Spec.Weierstrass.Point.p224
    verified := p224_add_verified (fermat_of_law h.law) },
  Spec.Weierstrass.Point.p224.doubleApi.artifact Arm.target {
    code := Impl.Weierstrass.Arm.Point.pointDouble Spec.Weierstrass.Point.p224
    verified := p224_double_verified (fermat_of_law h.law) },
  Spec.Weierstrass.Point.p224.addApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Weierstrass.Arm.Point.pointAdd Spec.Weierstrass.Point.p224 true
    verified := p224_addU_verified (fermat_of_law h.law)
    features := ["umaal"] },
  Spec.Weierstrass.Point.p224.doubleApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Weierstrass.Arm.Point.pointDouble Spec.Weierstrass.Point.p224 true
    verified := p224_doubleU_verified (fermat_of_law h.law)
    features := ["umaal"] }]

end VG.Generic.P224.Arm.PointP224
