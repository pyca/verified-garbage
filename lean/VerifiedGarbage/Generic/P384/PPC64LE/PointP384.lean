module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointP384
public import VerifiedGarbage.Proof.Framework.Registration

/-! # P-384's point addition and doubling on PPC64LE -/

@[expose] public section

namespace VG.Generic.P384.PPC64LE.PointP384

open VG.Proof.Weierstrass.PPC64LE.Point

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Weierstrass.Point.p384.addApi.artifact PPC64LE.target {
    code := Impl.Weierstrass.PPC64LE.Point.pointAdd Spec.Weierstrass.Point.p384
    verified := p384_add_verified (fermat_of_law h.law) },
  Spec.Weierstrass.Point.p384.doubleApi.artifact PPC64LE.target {
    code := Impl.Weierstrass.PPC64LE.Point.pointDouble Spec.Weierstrass.Point.p384
    verified := p384_double_verified (fermat_of_law h.law) }]

end VG.Generic.P384.PPC64LE.PointP384
