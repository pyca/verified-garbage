module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P384.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print

/-! # ECDSA over P-384 (FIPS 186-5) on 32-bit ARM -/

@[expose] public section

namespace VG.Generic.P384.Arm.EcdsaP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Ecdsa.P384.verifyHashApi.artifact Arm.target {
    consts := Impl.Weierstrass.Arm.p384CombConsts
    code := Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false
      Impl.Ecdsa.Arm.verifyP384Comb
    stack := 96
    verified := Proof.Ecdsa.Verify.Arm.P384.verifyHash_verified h.law },
  Spec.Ecdsa.P384.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    consts := Impl.Weierstrass.Arm.p384CombConsts
    code := Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false
      Impl.Ecdsa.Arm.verifyP384CombU
    stack := 96
    verified := Proof.Ecdsa.Verify.Arm.P384.verifyHashU_verified h.law
    features := ["umaal"] }]

end VG.Generic.P384.Arm.EcdsaP384
