module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Poly1305.Contract
import VerifiedGarbage.Proof.Poly1305.Arm.Scrub
import VerifiedGarbage.Proof.Variants.Poly1305Blocks.Arm
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Poly1305 (RFC 8439 §2.5) on ARMv7 -/

namespace VG.Artifacts.Poly1305.Arm

public def artifacts : List (Artifact Arm.target) :=
  [Spec.Poly1305.initApi.artifact Arm.target {
    code := Impl.Poly1305.Arm.Fn.init
    verified := Proof.Poly1305.Arm.Fn.init }] ++
  (Proof.Variants.Poly1305Blocks.Arm.variants.flatMap fun (v : Proof.Variants.Poly1305Blocks.Arm.Variant) => [
    Spec.Poly1305.updateApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Poly1305.Arm.Fn.update v.umaal
      verified := Proof.Poly1305.Arm.Fn.update v.umaal },
    Spec.Poly1305.finalizeApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Poly1305.Arm.Fn.finalize v.umaal
      verified := Proof.Poly1305.Arm.Fn.finalize v.umaal }])

spec_apis artifacts

end VG.Artifacts.Poly1305.Arm
