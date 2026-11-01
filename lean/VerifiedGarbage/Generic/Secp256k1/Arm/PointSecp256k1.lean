module

public import VerifiedGarbage.Impl.Secp256k1.Point
public import VerifiedGarbage.Spec.Weierstrass.Point0

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.Arm.PointSecp256k1
public import VerifiedGarbage.Proof.Weierstrass.Arm.PointSecp256k1Umaal
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.Impl.Weierstrass.Arm.Point
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves
public import VerifiedGarbage.Proof.Weierstrass.Arm.PointSecp256k1
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

/-! # secp256k1's point functions on 32-bit ARM -/

@[expose] public section

namespace VG.Generic.Secp256k1.Arm.PointSecp256k1

open VG.Proof.Weierstrass.Arm.Point

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Impl.Secp256k1.point.addApi.artifact Arm.target {
    code := Impl.Weierstrass.Arm.Point.pointAdd Impl.Secp256k1.point
    verified := secp256k1_add_verified (fermat_of_law h.law) },
  Impl.Secp256k1.point.double0Api.artifact Arm.target {
    code := Impl.Weierstrass.Arm.Point.pointDouble0 Impl.Secp256k1.point
    verified := secp256k1_double0_verified (fermat_of_law h.law) },
  Impl.Secp256k1.point.add0mApi.artifact Arm.target {
    code := Impl.Weierstrass.Arm.Point.pointAdd0m Impl.Secp256k1.point
    verified := secp256k1_add0m_verified (fermat_of_law h.law) },
  Impl.Secp256k1.point.addApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Weierstrass.Arm.Point.pointAdd Impl.Secp256k1.point true
    verified := secp256k1_addU_verified (fermat_of_law h.law)
    features := ["umaal"] },
  Impl.Secp256k1.point.double0Api.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Weierstrass.Arm.Point.pointDouble0 Impl.Secp256k1.point true
    verified := secp256k1_double0U_verified (fermat_of_law h.law)
    features := ["umaal"] },
  Impl.Secp256k1.point.add0mApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Weierstrass.Arm.Point.pointAdd0m Impl.Secp256k1.point true
    verified := secp256k1_add0mU_verified (fermat_of_law h.law)
    features := ["umaal"] }]

end VG.Generic.Secp256k1.Arm.PointSecp256k1
