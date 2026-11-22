module

public import VerifiedGarbage.Proof.Dsa.Arm.Verified
public import VerifiedGarbage.Proof.Dsa.Arm.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.Arm.ValidatePrivateVerified
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateVerified
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Verified
public import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedVerified
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Init
public import VerifiedGarbage.Proof.Dsa.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Instances

/-! # DSA (FIPS 186-4) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Dsa.Arm

open VG Proof.Dsa.Arm.Gen

def artifacts : List Artifact :=
  [Spec.Dsa.parameterInitApi.artifact Arm.target {
    code := Impl.Dsa.Arm.Fn.parameterInit
    verified := Proof.Dsa.Arm.Fn.parameterInit }] ++
  (VG.Proof.Variants.DsaArithmetic.Arm.variants.flatMap fun (v : Proof.Variants.DsaArithmetic.Arm.Variant) => [
    Spec.Dsa.randomSignPrevalidatedApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Dsa.Arm.Fn.randomSignPrevalidated v.umaal
      verified := Proof.Dsa.Arm.Fn.randomSignPrevalidated v.umaal },
    Spec.Dsa.validatePrivateKeyApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Dsa.Arm.Fn.validatePrivateKey v.umaal
      verified := Proof.Dsa.Arm.Fn.validatePrivateKey v.umaal },
    Spec.Dsa.deriveKeyApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Dsa.Arm.Fn.deriveKey v.umaal
      verified := Proof.Dsa.Arm.Fn.deriveKey v.umaal },
    Spec.Dsa.generateKeyApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Dsa.Arm.Fn.generateKey v.umaal
      verified := Proof.Dsa.Arm.Fn.generateKey v.umaal },
    Spec.Dsa.validatePublicKeyApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Dsa.Arm.Fn.validatePublicKey v.umaal
      verified := Proof.Dsa.Arm.Fn.validatePublicKey v.umaal },
    Spec.Dsa.verifyPrevalidatedApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Dsa.Arm.Fn.verifyPrevalidated v.umaal
      verified := Proof.Dsa.Arm.Fn.verifyPrevalidated v.umaal }]) ++
  (searchPairs.map fun (p : Proof.Variants.DsaArithmetic.Arm.Variant × Proof.MillerRabin.Arm.RoundImpl) =>
    Spec.Dsa.parameterSearchApi.artifact Arm.target {
      suffix := p.1.suffix
      code := Impl.Dsa.Arm.Fn.parameterSearch p.1.umaal p.2.suffix p.2.code p.2.mont.callOp.op p.2.mont.dbl
      verified := Proof.Dsa.Arm.Fn.parameterSearch p.1.umaal p.2 })

end VG.Artifacts.Dsa.Arm
