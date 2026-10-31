module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointBrainpoolP256r1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # brainpoolP256r1's point addition and doubling on PPC64LE -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.PPC64LE.PointBrainpoolP256r1

open VG.Proof.Weierstrass.PPC64LE.Point

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.Weierstrass.Point.brainpoolp256r1.addApi.artifact PPC64LE.target {
    code := Impl.Weierstrass.PPC64LE.Point.pointAdd Spec.Weierstrass.Point.brainpoolp256r1
    verified := brainpoolp256r1_add_verified (fermat_of_law h.law) },
  Spec.Weierstrass.Point.brainpoolp256r1.doubleApi.artifact PPC64LE.target {
    code := Impl.Weierstrass.PPC64LE.Point.pointDouble Spec.Weierstrass.Point.brainpoolp256r1
    verified := brainpoolp256r1_double_verified (fermat_of_law h.law) }]

end VG.Generic.BrainpoolP256r1.PPC64LE.PointBrainpoolP256r1
