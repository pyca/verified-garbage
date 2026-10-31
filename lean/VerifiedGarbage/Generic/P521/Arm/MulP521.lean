module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Arm.P521.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.MulLit

/-! # P-521's point multiplication on 32-bit ARM -/

@[expose] public section

namespace VG.Generic.P521.Arm.MulP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p521.mulApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.mulP521
    verified := Proof.Ecdsa.Arm.P521.Mul.mul_verified h.law }]

end VG.Generic.P521.Arm.MulP521
