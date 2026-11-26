module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.X448.Arm.Scrub
import VerifiedGarbage.Proof.Ed448.CombFacts
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.Curve448Field.Arm
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # X448 (RFC 7748) on ARMv7 -/

namespace VG.Artifacts.X448.Arm

public def artifacts : List (Artifact Arm.target) :=
  VG.Proof.Variants.Curve448Field.Arm.variants.flatMap fun (v : Proof.Variants.Curve448Field.Arm.Variant) => [
    Spec.X448.exchangeApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.X448.Arm.Fn.exchange v.um
      verified := Proof.X448.Arm.Fn.exchange v.um },
    Spec.X448.x448BaseApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.X448.Arm.Fn.x448Base v.um
      verified := Proof.X448.Arm.Fn.x448Base v.um }]

spec_apis artifacts

end VG.Artifacts.X448.Arm
