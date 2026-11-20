module

public import VerifiedGarbage.Proof.X448.Arm.Scrub
public import VerifiedGarbage.Proof.Ed448.CombFacts
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Variants.Curve448Field.Arm

/-! # X448 (RFC 7748) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.X448.Arm

def artifacts : List Artifact :=
  VG.Proof.Variants.Curve448Field.Arm.variants.flatMap fun (v : Proof.Variants.Curve448Field.Arm.Variant) => [
    Spec.X448.exchangeApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.X448.Arm.Fn.exchange v.um
      verified := .scrubbed (Proof.X448.Arm.Fn.exchange v.um) },
    Spec.X448.x448BaseApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.X448.Arm.Fn.x448Base v.um
      verified := .scrubbed (Proof.X448.Arm.Fn.x448Base v.um) }]

end VG.Artifacts.X448.Arm
