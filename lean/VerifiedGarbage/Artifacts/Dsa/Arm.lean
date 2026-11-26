module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Spec.Dsa.Prevalidated
import VerifiedGarbage.Proof.Dsa.Arm.Verified
import VerifiedGarbage.Proof.Dsa.Arm.RandomSignVerified
import VerifiedGarbage.Proof.Dsa.Arm.ValidatePrivateVerified
import VerifiedGarbage.Proof.Dsa.Arm.GenerateVerified
import VerifiedGarbage.Proof.Dsa.Arm.Key.Verified
import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedVerified
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Init
import VerifiedGarbage.Proof.Dsa.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Instances
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # DSA (FIPS 186-4) on ARMv7 -/

namespace VG.Artifacts.Dsa.Arm

open VG Proof.Dsa.Arm.Gen

public def artifacts : List (Artifact Arm.target) :=
  [Spec.Dsa.parameterInitApi.artifact Arm.target {
    code := Impl.Dsa.Arm.Fn.parameterInit
    verified := Proof.Dsa.Arm.Fn.parameterInit
    publicOutOk := Proof.Dsa.Arm.Fn.parameterInit_public }] ++
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
      verified := Proof.Dsa.Arm.Fn.parameterSearch p.1.umaal p.2
      publicOutOk := Proof.Dsa.Arm.Fn.parameterSearch_public p.1.umaal p.2 })

spec_apis artifacts

end VG.Artifacts.Dsa.Arm
