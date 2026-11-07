module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P256.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print

/-! # ECDSA over P-256 (FIPS 186-5) on 32-bit ARM -/

@[expose] public section

namespace VG.Generic.P256.Arm.EcdsaP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Ecdsa.P256.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false
      Impl.Ecdsa.Arm.verifyP256Comb
    stack := 96
    verified := Proof.Ecdsa.Verify.Arm.P256.verifyHash_verified h.law },
  Spec.Ecdsa.P256.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false
      Impl.Ecdsa.Arm.verifyP256CombU
    stack := 96
    verified := Proof.Ecdsa.Verify.Arm.P256.verifyHashU_verified h.law
    features := ["umaal"] }]

end VG.Generic.P256.Arm.EcdsaP256
