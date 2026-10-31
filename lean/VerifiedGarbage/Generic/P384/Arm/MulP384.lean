module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.Arm.P384.MulLit

public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Umaal

/-! # P-384's point multiplication on 32-bit ARM -/

@[expose] public section

namespace VG.Generic.P384.Arm.MulP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p384.mulApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.mulP384
    verified := Proof.Ecdsa.Arm.P384.Mul.mul_verified h.law },
  Spec.Weierstrass.Mul.p384.mulApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.mulP384U
    verified := Proof.Ecdsa.Arm.P384.Mul.mulU_verified h.law
    features := ["umaal"] }]

end VG.Generic.P384.Arm.MulP384
