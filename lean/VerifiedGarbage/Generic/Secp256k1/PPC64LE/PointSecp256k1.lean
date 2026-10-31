module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointSecp256k1
public import VerifiedGarbage.Impl.Secp256k1.Point
public import VerifiedGarbage.Spec.Weierstrass.Point0
public import VerifiedGarbage.Proof.Framework.Registration

/-! # secp256k1's point doubling and affine addition on PPC64LE -/

@[expose] public section

namespace VG.Generic.Secp256k1.PPC64LE.PointSecp256k1

open VG.Proof.Weierstrass.PPC64LE.Point

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Impl.Secp256k1.point.double0Api.artifact PPC64LE.target {
    code := Impl.Weierstrass.PPC64LE.Point.pointDouble0 Impl.Secp256k1.point
    verified := secp256k1_double0_verified (fermat_of_law h.law) },
  Impl.Secp256k1.point.add0mApi.artifact PPC64LE.target {
    code := Impl.Weierstrass.PPC64LE.Point.pointAdd0m Impl.Secp256k1.point
    verified := secp256k1_add0m_verified (fermat_of_law h.law) }]

end VG.Generic.Secp256k1.PPC64LE.PointSecp256k1
