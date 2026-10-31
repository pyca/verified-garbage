module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointP192
public import VerifiedGarbage.Proof.Framework.Registration

/-! # P-192's point addition and doubling on PPC64LE -/

@[expose] public section

namespace VG.Generic.P192.PPC64LE.PointP192

open VG.Proof.Weierstrass.PPC64LE.Point

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact := [
  Spec.Weierstrass.Point.p192.addApi.artifact PPC64LE.target {
    code := Impl.Weierstrass.PPC64LE.Point.pointAdd Spec.Weierstrass.Point.p192
    verified := p192_add_verified (fermat_of_law h.law) },
  Spec.Weierstrass.Point.p192.doubleApi.artifact PPC64LE.target {
    code := Impl.Weierstrass.PPC64LE.Point.pointDouble Spec.Weierstrass.Point.p192
    verified := p192_double_verified (fermat_of_law h.law) }]

end VG.Generic.P192.PPC64LE.PointP192
