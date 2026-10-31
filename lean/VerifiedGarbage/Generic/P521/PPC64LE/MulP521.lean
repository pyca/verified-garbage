module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.MulLit

/-! # P-521's point multiplication on PPC64LE -/

@[expose] public section

namespace VG.Generic.P521.PPC64LE.MulP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p521.mulApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.PPC64LE.mulP521
    verified := Proof.Ecdsa.PPC64LE.P521.Mul.mul_verified h.law }]

end VG.Generic.P521.PPC64LE.MulP521
